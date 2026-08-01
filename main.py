import json
import random
import shutil
import time
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo

from astrbot.api import AstrBotConfig, logger
from astrbot.api.event import AstrMessageEvent, filter
from astrbot.api.provider import ProviderRequest
from astrbot.api.star import Context, Star, register
from astrbot.core.star.star_tools import StarTools

AVATAR_EXTS = {".jpg", ".jpeg"}  # Telegram 头像接口只收 JPEG
PHOTO_EXTS = {".jpg", ".jpeg", ".png", ".webp"}
MEDIA_GROUP_MAX = 10  # Telegram 一组媒体最多 10 张
CAPTION_MAX = 1024  # 图片 caption 上限；纯文字消息上限是 4096


@register(
    "astrbot_plugin_tg_presence",
    "chine",
    "让角色自己发动态到频道、换头像、改简介、对消息点表情",
    "0.1.0",
)
class TgPresence(Star):
    def __init__(self, context: Context, config: AstrBotConfig):
        super().__init__(context)
        self.conf = config
        self.data_dir = StarTools.get_data_dir("astrbot_plugin_tg_presence")
        self.state_path = self.data_dir / "state.json"
        self.state = self._load_state()

    # ------------------------------------------------------------------ 状态

    def _load_state(self) -> dict:
        if not self.state_path.exists():
            return {"moments": [], "last": {}, "daily": {}}
        try:
            state = json.loads(self.state_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as e:
            logger.error(f"[tg_presence] 状态文件读取失败，按空状态启动: {e}")
            return {"moments": [], "last": {}, "daily": {}}
        state.setdefault("moments", [])
        state.setdefault("last", {})
        state.setdefault("daily", {})
        return state

    def _save_state(self) -> None:
        tmp = self.state_path.with_suffix(".json.tmp")
        tmp.write_text(
            json.dumps(self.state, ensure_ascii=False, indent=2), encoding="utf-8"
        )
        tmp.replace(self.state_path)

    @staticmethod
    def _moment_photos(moment: dict) -> list[str]:
        """兼容旧格式：v0.1.1 及以前是单个 photo 字段，之后是 photos 列表。"""
        if moment.get("photos"):
            return list(moment["photos"])
        single = moment.get("photo")
        return [single] if single else []

    def _tz(self) -> ZoneInfo:
        name = self.conf.get("timezone") or "Asia/Shanghai"
        try:
            return ZoneInfo(name)
        except Exception:
            logger.warning(f"[tg_presence] 时区 {name} 无效，回退 Asia/Shanghai")
            return ZoneInfo("Asia/Shanghai")

    # --------------------------------------------------------------- 频率控制

    def _cooldown_left(self, key: str, minutes: int) -> int:
        """返回还要等几分钟；0 表示现在就能做。"""
        if minutes <= 0:
            return 0
        last = self.state["last"].get(key, 0)
        remain = minutes * 60 - (time.time() - last)
        return max(0, -(-int(remain) // 60))  # 向上取整

    def _mark_done(self, key: str) -> None:
        self.state["last"][key] = time.time()

    def _daily_left(self, key: str, limit: int) -> int:
        """返回今天还剩几次；limit<=0 视为不限制，返回 -1。"""
        if limit <= 0:
            return -1
        today = datetime.now(self._tz()).strftime("%Y-%m-%d")
        used = self.state["daily"].get(key, {}).get(today, 0)
        return max(0, limit - used)

    def _bump_daily(self, key: str) -> None:
        today = datetime.now(self._tz()).strftime("%Y-%m-%d")
        bucket = self.state["daily"].setdefault(key, {})
        bucket[today] = bucket.get(today, 0) + 1
        # 只留最近 7 天，避免无限增长
        for day in sorted(bucket)[:-7]:
            del bucket[day]

    # ----------------------------------------------------------------- 工具函数

    def _client(self, event: AstrMessageEvent):
        """拿底层 telegram ExtBot。telegram 适配器把它挂在 event.client 上。"""
        if event.get_platform_name() != "telegram":
            return None
        return getattr(event, "client", None)

    def _chat_id(self, event: AstrMessageEvent):
        """当前会话的 telegram chat_id。适配器用 chat.id 作为 session_id。"""
        umo = event.unified_msg_origin
        parts = umo.split(":", 2)
        if len(parts) == 3:
            return parts[2].split("#", 1)[0]  # 话题群是 {chat_id}#{thread_id}
        return event.get_sender_id()

    def _pick_image(self, base_dir: str, category: str, exts: set) -> Path | None:
        root = Path(base_dir).expanduser()
        if not root.is_dir():
            return None
        search = root / category if category else root
        if not search.is_dir():
            search = root  # 分类不存在就退回根目录
        files = [
            p for p in search.rglob("*") if p.is_file() and p.suffix.lower() in exts
        ]
        return random.choice(files) if files else None

    def _list_categories(self, base_dir: str) -> list[str]:
        root = Path(base_dir).expanduser()
        if not root.is_dir():
            return []
        return sorted(p.name for p in root.iterdir() if p.is_dir())

    async def _attached_images(self, event: AstrMessageEvent) -> list[Path]:
        """取出当前消息里附带的图片，拷进插件数据目录长期保存。

        平台给的图片通常落在 AstrBot 的临时目录，会被清理；而历史动态注入
        可能在很久以后才读它，所以必须自己留一份。
        """
        import astrbot.api.message_components as Comp

        store = self.data_dir / "moment_photos"
        store.mkdir(parents=True, exist_ok=True)

        saved: list[Path] = []
        for seg in event.get_messages():
            if not isinstance(seg, Comp.Image):
                continue
            try:
                src = Path(await seg.convert_to_file_path())
            except Exception as e:
                logger.warning(f"[tg_presence] 附带图片取路径失败: {e}")
                continue
            if not src.exists():
                logger.warning(f"[tg_presence] 附带图片不存在: {src}")
                continue
            suffix = src.suffix.lower() or ".jpg"
            dst = store / f"{int(time.time() * 1000)}_{len(saved)}{suffix}"
            try:
                shutil.copy2(src, dst)
            except OSError as e:
                logger.warning(f"[tg_presence] 附带图片保存失败: {e}")
                continue
            saved.append(dst)
        return saved

    # ------------------------------------------------------- 历史动态注入上下文

    @filter.on_llm_request()
    async def inject_moments(self, event: AstrMessageEvent, req: ProviderRequest):
        if not self.conf.get("inject_history", True):
            return
        moments = self.state.get("moments", [])
        if not moments:
            return

        limit = int(self.conf.get("inject_history_limit", 0) or 0)
        selected = moments[-limit:] if limit > 0 else moments

        tz = self._tz()
        lines = []
        for m in selected:
            stamp = datetime.fromtimestamp(m["ts"], tz).strftime("%m-%d %H:%M")
            n = len(self._moment_photos(m))
            mark = f"[配图 {n} 张] " if n else ""
            lines.append(f"{stamp} {mark}{m['text']}")

        req.system_prompt += (
            "\n\n# 你发过的动态\n"
            "以下是你已经发到自己频道的全部动态，按时间先后排列。\n"
            "这些是你自己发的，你记得它们。不要重复发内容相近的动态。\n\n"
            + "\n".join(lines)
            + "\n"
        )

        if not self.conf.get("inject_history_images", False):
            return

        # 配图注入：ProviderRequest.image_urls 是 list[str]
        img_limit = int(self.conf.get("inject_images_limit", 10) or 0)
        paths = [p for m in selected for p in self._moment_photos(m)]
        if img_limit > 0:
            paths = paths[-img_limit:]
        for raw in paths:
            path = Path(raw)
            if not path.exists():
                continue
            try:
                req.image_urls.append(path.as_uri())
            except Exception as e:
                logger.warning(f"[tg_presence] 配图注入失败 {path}: {e}")

    # --------------------------------------------------------------- 发动态

    async def _do_post(
        self,
        event: AstrMessageEvent,
        text: str,
        category: str,
        enforce_limits: bool = True,
    ) -> str:
        """enforce_limits=False 用于手动指令：冷却和每日上限只约束角色自主行为。"""
        client = self._client(event)
        if client is None:
            return "发动态失败：这个功能只能在 Telegram 上用。"

        channel = (self.conf.get("channel_id") or "").strip()
        if not channel:
            return "发动态失败：还没有配置频道 ID，去插件配置里填上。"

        if enforce_limits:
            wait = self._cooldown_left(
                "post", int(self.conf.get("post_cooldown_minutes", 180))
            )
            if wait:
                return f"现在还发不了动态，距离上一条还差 {wait} 分钟。等会儿再说。"

            if self._daily_left("post", int(self.conf.get("post_daily_limit", 5))) == 0:
                return "今天的动态已经发够了，明天再发。"

        # 优先用这条消息里随手附带的图；没有再从配置目录挑
        photos = await self._attached_images(event)
        source = "附带" if photos else ""
        if not photos:
            photo_dir = (self.conf.get("moment_photo_dir") or "").strip()
            if photo_dir:
                picked = self._pick_image(photo_dir, category, PHOTO_EXTS)
                if picked:
                    photos = [picked]
                    source = "图库"

        photos = photos[:MEDIA_GROUP_MAX]

        try:
            await self._send_to_channel(client, channel, text, photos)
        except Exception as e:
            logger.error(f"[tg_presence] 发动态失败: {e}")
            return f"发动态失败了：{e}"

        # 手动发的也记进历史——她需要知道自己频道上有这条，才不会重复发
        self.state["moments"].append(
            {
                "ts": time.time(),
                "text": text,
                "photos": [str(p) for p in photos],
            }
        )
        if enforce_limits:
            self._mark_done("post")
            self._bump_daily("post")
        self._save_state()

        if not photos:
            return "动态已经发出去了。"
        return f"动态已经发出去了，带了 {len(photos)} 张{source}图。"

    async def _send_to_channel(self, client, channel: str, text: str, photos: list[Path]):
        """按图片张数选择发送方式。caption 超长时图文分两条发。"""
        if not photos:
            await client.send_message(chat_id=channel, text=text)
            return

        caption = text if len(text) <= CAPTION_MAX else None

        handles = []
        try:
            if len(photos) == 1:
                f = open(photos[0], "rb")
                handles.append(f)
                await client.send_photo(chat_id=channel, photo=f, caption=caption)
            else:
                from telegram import InputMediaPhoto

                media = []
                for i, p in enumerate(photos):
                    f = open(p, "rb")
                    handles.append(f)
                    media.append(
                        InputMediaPhoto(media=f, caption=caption if i == 0 else None)
                    )
                await client.send_media_group(chat_id=channel, media=media)
        finally:
            for f in handles:
                f.close()

        if caption is None:  # 正文太长塞不进 caption，补发一条纯文字
            await client.send_message(chat_id=channel, text=text)

    @filter.llm_tool(name="post_moment")
    async def post_moment(self, event: AstrMessageEvent, text: str, category: str = ""):
        """发一条动态到你自己的频道。当此刻发生了值得记录的事、你有情绪想表达、或者你想让对方看到你的近况时使用。像发朋友圈那样，不需要每次聊天都发。如果对方这条消息里带了图片，那些图会自动作为这条动态的配图。

        Args:
            text(string): 动态的正文，用你自己的口吻写
            category(string): 可选，配图分类名。仅在对方没带图时才用它去图库里挑；留空则发纯文字
        """
        return await self._do_post(event, text, category)

    @filter.command("moment")
    async def cmd_moment(self, event: AstrMessageEvent, text: str = ""):
        """手动发一条动态。用法：/moment 正文"""
        if self.conf.get("admin_only_commands", True) and event.role != "admin":
            yield event.plain_result("只有管理员能用这个指令。")
            return
        if not text:
            yield event.plain_result("用法：/moment 动态正文")
            return
        yield event.plain_result(await self._do_post(event, text, "", enforce_limits=False))

    # --------------------------------------------------------------- 换头像

    async def _do_avatar(
        self, event: AstrMessageEvent, category: str, enforce_limits: bool = True
    ) -> str:
        """enforce_limits=False 用于手动指令。"""
        client = self._client(event)
        if client is None:
            return "换头像失败：这个功能只能在 Telegram 上用。"

        if not hasattr(client, "set_my_profile_photo"):
            return (
                "换头像失败：当前 python-telegram-bot 版本太低，"
                "需要 22.7 以上才有这个接口。"
            )

        avatar_dir = (self.conf.get("avatar_dir") or "").strip()
        if not avatar_dir:
            return "换头像失败：还没有配置头像目录。"

        if enforce_limits:
            wait = self._cooldown_left(
                "avatar", int(self.conf.get("avatar_cooldown_minutes", 720))
            )
            if wait:
                return f"刚换过头像，{wait} 分钟内不能再换。"

        pic = self._pick_image(avatar_dir, category, AVATAR_EXTS)
        if pic is None:
            cats = self._list_categories(avatar_dir)
            hint = f"（可用分类：{'、'.join(cats)}）" if cats else ""
            return f"换头像失败：目录里没找到 jpg 图片{hint}。"

        try:
            from telegram import InputProfilePhotoStatic

            with open(pic, "rb") as f:
                await client.set_my_profile_photo(photo=InputProfilePhotoStatic(photo=f))
        except Exception as e:
            logger.error(f"[tg_presence] 换头像失败: {e}")
            return f"换头像失败了：{e}"

        if enforce_limits:
            self._mark_done("avatar")
            self._save_state()
        return f"头像换好了，用的是 {pic.name}。"

    @filter.llm_tool(name="change_avatar")
    async def change_avatar(self, event: AstrMessageEvent, category: str = ""):
        """换一张自己的头像。当你心情变了、换了造型、或者只是想换换感觉的时候使用。

        Args:
            category(string): 可选，头像分类名，对应头像目录下的子文件夹。留空则从全部头像里随机挑
        """
        return await self._do_avatar(event, category)

    @filter.command("avatar")
    async def cmd_avatar(self, event: AstrMessageEvent, category: str = ""):
        """手动换头像。用法：/avatar [分类]"""
        if self.conf.get("admin_only_commands", True) and event.role != "admin":
            yield event.plain_result("只有管理员能用这个指令。")
            return
        yield event.plain_result(
            await self._do_avatar(event, category, enforce_limits=False)
        )

    # ------------------------------------------------------------- 表情回应

    @filter.llm_tool(name="react_message")
    async def react_message(self, event: AstrMessageEvent, emoji: str):
        """给对方刚发的那条消息打一个表情，作为轻量回应。适合不需要说话、但想让对方知道你看到了的时候——比如他说了句好笑的、或者你只是想戳他一下。

        Args:
            emoji(string): 一个表情符号，例如 ❤️ 👍 😂 🔥 🥰 😭 🤔
        """
        if not self.conf.get("enable_reaction", True):
            return None

        client = self._client(event)
        if client is None:
            return "打表情失败：这个功能只能在 Telegram 上用。"

        message_id = getattr(event.message_obj, "message_id", None)
        if not message_id:
            logger.warning("[tg_presence] 取不到 message_id，跳过表情回应")
            return "打表情失败：找不到那条消息。"

        try:
            from telegram import ReactionTypeEmoji

            await client.set_message_reaction(
                chat_id=self._chat_id(event),
                message_id=int(message_id),
                reaction=[ReactionTypeEmoji(emoji=emoji.strip())],
            )
        except Exception as e:
            logger.error(f"[tg_presence] 表情回应失败: {e}")
            return f"打表情失败了：{e}"

        return None  # 不回喂给模型，避免她再啰嗦一句

    # --------------------------------------------------------------- 查看状态

    @filter.command("presence")
    async def cmd_presence(self, event: AstrMessageEvent):
        """查看插件状态：已发动态数、各项冷却剩余。"""
        if self.conf.get("admin_only_commands", True) and event.role != "admin":
            yield event.plain_result("只有管理员能用这个指令。")
            return

        moments = self.state.get("moments", [])
        post_left = self._daily_left("post", int(self.conf.get("post_daily_limit", 5)))
        lines = [
            f"已发动态：{len(moments)} 条",
            f"今日剩余：{'不限' if post_left < 0 else post_left} 条",
            f"发动态冷却：{self._cooldown_left('post', int(self.conf.get('post_cooldown_minutes', 180)))} 分钟",
            f"换头像冷却：{self._cooldown_left('avatar', int(self.conf.get('avatar_cooldown_minutes', 720)))} 分钟",
        ]
        if moments:
            last = moments[-1]
            stamp = datetime.fromtimestamp(last["ts"], self._tz()).strftime("%m-%d %H:%M")
            lines.append(f"最近一条：{stamp} {last['text'][:40]}")
        yield event.plain_result("\n".join(lines))
