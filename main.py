import base64
import binascii
import hashlib
import json
import random
import re
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
SIGNATURE_MAX = 120  # setMyShortDescription 的上限

# 角色自己消息的时间戳格式，形如 [08-01 14:30]
STAMP_FMT = "[%m-%d %H:%M]"
STAMP_RE = re.compile(r"^\[\d{2}-\d{2} \d{2}:\d{2}\]")

# AstrBot 把当前时间写进 user 消息正文（astr_main_agent.py:980），
# 这是历史里唯一可靠的时间锚点，用来给动态定位插入点
CTX_TIME_RE = re.compile(r"Current datetime:\s*(\d{4}-\d{2}-\d{2} \d{2}:\d{2})")

DATA_URL_RE = re.compile(r"^data:image/(?P<ext>[\w+.-]+);base64,(?P<b64>.+)$", re.S)

# 角色在回复末尾附的图片描述，会被剥掉不发给用户
IMG_NOTE_RE = re.compile(
    r"<img_note\s+id=[\"']?#?(?P<id>\w+)[\"']?\s*>(?P<desc>.*?)</img_note>", re.S
)


@register(
    "astrbot_plugin_tg_presence",
    "chine",
    "让角色自己发动态到频道、换头像、改签名、对消息点表情",
    "0.8.0",
)
class TgPresence(Star):
    def __init__(self, context: Context, config: AstrBotConfig):
        super().__init__(context)
        self.conf = config
        self.data_dir = StarTools.get_data_dir("astrbot_plugin_tg_presence")
        self.state_path = self.data_dir / "state.json"
        self.state = self._load_state()
        # 角色最近一次出站的时刻。只在内存里，进程重启丢一次戳无所谓
        self._pending_sent: float | None = None

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

    @staticmethod
    def _seal_command(event: AstrMessageEvent) -> None:
        """让这条指令消息不进对话上下文。

        AstrBot 的 ProcessStage 在指令 handler 没产生输出时，会把原始消息
        （含未剥离的指令名和附带图片）丢给默认 LLM，并写进 conversation history。
        指令消息里的图片会以 base64 形式永久留在历史里，之后每轮都重新发给模型，
        表现就是"角色把你发指令时带的图当成你在聊天里发的照片"。

        should_call_llm 的语义是反的 —— 传 True 才是禁止。
        """
        event.should_call_llm(True)

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

    # --------------------------------------------------------- 上下文图片瘦身

    @filter.on_llm_request(priority=-50)
    async def prune_context_images(
        self, event: AstrMessageEvent, req: ProviderRequest
    ):
        """只保留最近 N 张真图，更早的换成文字占位。

        AstrBot 把图片以 base64 data URL 的形式写进 conversation history
        (entities.py:207-222 → internal.py:531)，之后每一轮都原样重发。
        累积几十张之后既吃 token 又稀释注意力。

        换下来的图先存盘再替换，正文里留 [图片 #N] 的编号，
        需要重新看时用 recall_photo 工具按编号取回。

        priority=-50 让它在其它注入之后跑，只处理真正的历史图片。
        """
        keep = int(self.conf.get("max_context_images", 0) or 0)
        if keep <= 0:
            return

        slots: list[tuple[dict, int]] = []
        for msg in req.contexts or []:
            content = msg.get("content")
            if not isinstance(content, list):
                continue
            for i, part in enumerate(content):
                if isinstance(part, dict) and part.get("type") == "image_url":
                    slots.append((msg, i))

        if len(slots) <= keep:
            return

        store = self.data_dir / "context_photos"
        store.mkdir(parents=True, exist_ok=True)
        desc = self.state.get("photo_desc") or {}

        pruned = 0
        for msg, i in slots[:-keep]:
            part = msg["content"][i]
            url = (part.get("image_url") or {}).get("url") or ""
            pid = self._stash_photo(url, store)
            when = self._context_time(msg)
            stamp = (
                datetime.fromtimestamp(when, self._tz()).strftime("%m-%d %H:%M")
                if when
                else "时间不详"
            )
            bits = [f"图片 #{pid or '?'}", stamp]
            # 优先用角色自己存过的描述，它是靠内容检索的唯一依据
            if pid and desc.get(pid):
                bits.append(desc[pid])
            # 没有描述时退而求其次，用发图时说的那句话
            elif said := self._msg_own_text(msg):
                who = "他" if msg.get("role") == "user" else "你"
                bits.append(f"{who}当时说「{said[:60]}」")
            bits.append("已折叠")
            msg["content"][i] = {"type": "text", "text": "[" + " · ".join(bits) + "]"}
            # 记下拍摄时间，find_photo 要用——占位可能被 llm_compress 吃掉，
            # 但这份档案在 state.json 里，压缩动不到
            if pid and when:
                self.state.setdefault("photo_time", {})[pid] = when
            pruned += 1

        if pruned:
            self._save_state()
            logger.info(
                f"[tg_presence] 上下文图片瘦身：折叠 {pruned} 张，保留最近 {keep} 张"
            )

    @staticmethod
    def _msg_own_text(msg: dict) -> str:
        """取消息自己的正文，排除 AstrBot 注入的 system_reminder 和已有占位。"""
        content = msg.get("content")
        if isinstance(content, str):
            return content.strip()
        if not isinstance(content, list):
            return ""
        bits = []
        for part in content:
            if not (isinstance(part, dict) and part.get("type") == "text"):
                continue
            t = (part.get("text") or "").strip()
            if not t or "<system_reminder>" in t or t.startswith("[图片 #"):
                continue
            bits.append(t)
        return " ".join(bits)

    @staticmethod
    def _photo_key(data_url: str) -> str | None:
        """图片的稳定标识。

        必须用 sha256：内置 hash() 对字符串每次进程启动都不同，
        重启后同一张图会被当成新图。
        """
        hit = DATA_URL_RE.match((data_url or "").strip())
        if not hit:
            return None
        return hashlib.sha256(hit.group("b64").encode()).hexdigest()[:16]

    def _photo_id(self, data_url: str) -> str | None:
        """给图片分配（或取回）一个短编号。第一次见到就登记。"""
        key = self._photo_key(data_url)
        if key is None:
            return None
        index = self.state.setdefault("photo_index", {})
        if key not in index:
            index[key] = str(len(index) + 1)
        return index[key]

    def _stash_photo(self, data_url: str, store: Path) -> str | None:
        """把 base64 图片解码存盘，返回编号。已存过的直接复用。"""
        pid = self._photo_id(data_url)
        if pid is None:
            return None
        paths = self.state.setdefault("photo_paths", {})
        if pid in paths and Path(paths[pid]).exists():
            return pid

        hit = DATA_URL_RE.match(data_url.strip())
        ext = hit.group("ext").split("+")[0]
        if ext == "jpeg":
            ext = "jpg"
        path = store / f"{pid}.{ext}"
        try:
            path.write_bytes(base64.b64decode(hit.group("b64")))
        except (binascii.Error, ValueError, OSError) as e:
            logger.warning(f"[tg_presence] 折叠图片存盘失败 #{pid}: {e}")
            return None
        paths[pid] = str(path)
        return pid

    # ----------------------------------------------------- 让角色自己描述图片

    @filter.on_llm_request(priority=-40)
    async def ask_for_descriptions(
        self, event: AstrMessageEvent, req: ProviderRequest
    ):
        """把上下文里还没有描述的图片列出来，请角色在这次回复里顺带描述。

        比折叠时另起一次视觉调用便宜得多，而且此刻她正看着图、
        也知道当时聊的是什么，描述会带上她自己的视角。
        """
        if not self.conf.get("describe_images", True):
            return

        desc = self.state.get("photo_desc") or {}
        pending: list[str] = []
        for msg in req.contexts or []:
            content = msg.get("content")
            if not isinstance(content, list):
                continue
            for part in content:
                if not (isinstance(part, dict) and part.get("type") == "image_url"):
                    continue
                pid = self._photo_id((part.get("image_url") or {}).get("url") or "")
                if pid and pid not in desc and pid not in pending:
                    pending.append(pid)

        if not pending:
            return
        self._save_state()  # 编号是刚分配的，落盘

        ids = "、".join(f"#{p}" for p in pending)
        self._inject_text(
            req,
            "<describe_images>\n"
            f"上下文里这几张图还没有存过描述：{ids}\n"
            "请在这次回复的最末尾，为每张各写一条：\n"
            '  <img_note id="编号">这张图是什么</img_note>\n'
            "按图片在对话里出现的先后顺序对应编号。描述要具体到能靠它认出这张图——\n"
            "画面内容、谁拍的、什么场合，用你自己的说法就行。\n"
            "这几行会被系统抽走存档，对方看不到，也不算进你的回复。\n"
            "正常说你的话，把这些附在最后即可。\n\n"
            "另外：对方提起某张旧图时（「昨天那张」「黑丝那张」），\n"
            "先看对话里的 [图片 #N ...] 占位——描述就在里面，直接认出来即可。\n"
            "上下文里找不到再用 find_photo 查存档。\n"
            "**符合的不止一张时，问他是哪张，不要自己挑一张然后当成就是那张。**\n"
            "</describe_images>",
        )
        logger.debug(f"[tg_presence] 请求描述图片 {ids}")

    @filter.on_llm_response()
    async def capture_descriptions(self, event: AstrMessageEvent, resp):
        """抽出 <img_note> 存档，并从要发出去的内容里剥掉。"""
        if not self.conf.get("describe_images", True):
            return
        chain = getattr(getattr(resp, "result_chain", None), "chain", None)
        if not chain:
            return

        desc = self.state.setdefault("photo_desc", {})
        found = 0
        for comp in chain:
            text = getattr(comp, "text", None)
            if not isinstance(text, str) or "<img_note" not in text:
                continue
            for hit in IMG_NOTE_RE.finditer(text):
                body = hit.group("desc").strip()
                if body:
                    desc[hit.group("id")] = body[:200]
                    found += 1
            comp.text = IMG_NOTE_RE.sub("", text).strip()

        if found:
            self._save_state()
            logger.info(f"[tg_presence] 收到 {found} 条图片描述")

    @filter.llm_tool(name="find_photo")
    async def find_photo(
        self, event: AstrMessageEvent, keywords: str = "", day: str = ""
    ):
        """在你存过描述的旧图片里找。对话里能直接看到的那些占位不用查这个——只有当对方提起一张你在当前上下文里找不到的旧图时才用。返回候选列表，如果不止一张，问对方是哪张，别自己瞎猜。

        Args:
            keywords(string): 描述里的关键词，空格分隔，例如「黑丝 足底」。会取交集
            day(string): 限定日期，格式 MM-DD 或 YYYY-MM-DD。留空则不限
        """
        desc = self.state.get("photo_desc") or {}
        times = self.state.get("photo_time") or {}
        if not desc:
            return "还没有存过任何图片描述。"

        words = [w for w in keywords.replace("，", " ").split() if w]
        day = day.strip()

        hits = []
        for pid, text in desc.items():
            if words and not all(w in text for w in words):
                continue
            ts = times.get(pid)
            stamp = (
                datetime.fromtimestamp(ts, self._tz()).strftime("%Y-%m-%d %H:%M")
                if ts
                else ""
            )
            if day and day not in stamp:
                continue
            hits.append((ts or 0, pid, stamp or "时间不详", text))

        if not hits:
            return "没找到符合的图片。换个说法再试，或者问问对方是哪张。"

        hits.sort(reverse=True)
        lines = [f"#{pid} · {stamp} · {text}" for _, pid, stamp, text in hits[:12]]
        head = f"找到 {len(hits)} 张" + ("，只列最近 12 张：" if len(hits) > 12 else "：")
        tail = (
            "\n不止一张，先问清楚是哪张再取。"
            if len(hits) > 1
            else "\n用 recall_photo 加编号可以把它取回来重新看。"
        )
        return head + "\n" + "\n".join(lines) + tail

    @filter.llm_tool(name="recall_photo")
    async def recall_photo(self, event: AstrMessageEvent, photo_id: str):
        """重新看一张之前被折叠掉的图片。对话里出现 [图片 #12 ...] 这样的占位时，如果你需要真的再看一眼那张图的内容，用这个把它取回来。取回后在下一次回复时你就能看到它。

        Args:
            photo_id(string): 占位里的编号，比如 12
        """
        pid = photo_id.strip().lstrip("#")
        path = (self.state.get("photo_paths") or {}).get(pid)
        if not path or not Path(path).exists():
            return f"找不到 #{pid} 这张图。"
        self.state.setdefault("recall_queue", [])
        if pid not in self.state["recall_queue"]:
            self.state["recall_queue"].append(pid)
            self._save_state()
        return f"#{pid} 已取回，你现在能看到它了。"

    @filter.on_llm_request(priority=-60)
    async def serve_recalled(self, event: AstrMessageEvent, req: ProviderRequest):
        """把被 recall_photo 点名的图片重新塞进本轮请求。"""
        queue = self.state.get("recall_queue") or []
        if not queue:
            return
        paths = self.state.get("photo_paths") or {}
        for pid in queue:
            p = paths.get(pid)
            if p and Path(p).exists():
                try:
                    req.image_urls.append(Path(p).as_uri())
                except Exception as e:
                    logger.warning(f"[tg_presence] 取回图片 #{pid} 失败: {e}")
        logger.info(f"[tg_presence] 本轮取回 {len(queue)} 张折叠图片")
        self.state["recall_queue"] = []
        self._save_state()

    # ------------------------------------------------------- 角色消息打时间戳

    @filter.after_message_sent()
    async def record_sent_time(self, event: AstrMessageEvent):
        """记下角色刚说话的时刻，下次组请求时给那条 assistant 消息补戳。"""
        self._pending_sent = time.time()

    @filter.on_llm_request()
    async def stamp_assistant(self, event: AstrMessageEvent, req: ProviderRequest):
        """给角色自己的消息加时间戳。

        AstrBot 只给 user 消息带时间（datetime_system_prompt 那段 system_reminder
        会随 content 落库），assistant 消息是模型输出、没有任何时间锚点。
        主动消息尤其严重——前面没有 user 消息，等于完全没有时间参照。

        这里改的是 req.contexts，而 _save_to_history 保存的正是它派生出的
        run_context.messages，所以戳会落库、只需要打一次。
        """
        if not self.conf.get("stamp_own_messages", True):
            return
        sent_at = self._pending_sent
        if sent_at is None:
            return
        self._pending_sent = None

        gap = int(self.conf.get("stamp_min_gap_minutes", 5)) * 60
        last = self.state.get("last", {}).get("stamp", 0)
        if gap > 0 and sent_at - last < gap:
            return  # 距上次打戳不够久，这条不标

        target = next(
            (m for m in reversed(req.contexts or []) if m.get("role") == "assistant"),
            None,
        )
        if target is None:
            return

        stamp = datetime.fromtimestamp(sent_at, self._tz()).strftime(STAMP_FMT)
        if not self._prepend_stamp(target, stamp):
            return

        self.state["last"]["stamp"] = sent_at
        self._save_state()
        logger.debug(f"[tg_presence] 已给角色消息打戳 {stamp}")

    @staticmethod
    def _prepend_stamp(msg: dict, stamp: str) -> bool:
        """把时间戳插到 assistant 消息正文最前面。已有戳则跳过，返回是否真的打了。"""
        content = msg.get("content")

        if isinstance(content, str):
            if STAMP_RE.match(content.lstrip()):
                return False
            msg["content"] = f"{stamp} {content}"
            return True

        if isinstance(content, list):
            for part in content:
                if isinstance(part, dict) and part.get("type") == "text":
                    text = part.get("text") or ""
                    if STAMP_RE.match(text.lstrip()):
                        return False
                    part["text"] = f"{stamp} {text}"
                    return True
        return False

    # ------------------------------------------------------- 历史动态注入上下文

    @filter.on_llm_request()
    async def inject_moments(self, event: AstrMessageEvent, req: ProviderRequest):
        if not self.conf.get("inject_history", True):
            logger.debug("[tg_presence] 历史动态注入已关闭，跳过")
            return
        moments = self.state.get("moments", [])
        if not moments:
            logger.debug("[tg_presence] 暂无历史动态可注入")
            return

        limit = int(self.conf.get("inject_history_limit", 0) or 0)
        selected = moments[-limit:] if limit > 0 else moments

        anchors, tail = self._interleave_moments(req, selected)

        self._inject_text(
            req,
            "<your_own_moments>\n"
            "你发过的动态以【我发了条动态】的形式出现在对话时间线里，按实际时间插在当时的位置。\n"
            "那些都是你自己发的，你记得内容、配图和当时为什么发，也知道前后正在聊什么。\n"
            "对方提起时不要表现得像第一次看到，也不要重复发内容相近的动态。\n\n"
            "标着「当时没跟他提」的，是你发的时候故意没在聊天里说的。\n"
            "他要是自己刷到来问，说不说、什么时候说，看你当时心情——\n"
            "但你一直是知情的那个。\n"
            "</your_own_moments>",
        )
        logger.info(
            f"[tg_presence] {len(selected)} 条动态插入时间线"
            f"（历史时间锚点 {anchors} 个，其中 {tail} 条排在全部历史之后）"
        )
        if req.contexts and anchors == 0 and len(req.contexts) > len(selected):
            logger.warning(
                "[tg_presence] 历史里一个时间锚点都没有，动态只能全部堆在末尾，顺序不可信。"
                "可能原因：datetime_system_prompt 被关掉、这段历史早于该配置开启、"
                "或者已被 llm_compress 压缩过（摘要会吃掉正文里的时间戳）"
            )

        if not self.conf.get("inject_history_images", False):
            return

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

    def _interleave_moments(
        self, req: ProviderRequest, moments: list[dict]
    ) -> tuple[int, int]:
        """把动态按时间插进 req.contexts 的对应位置。

        返回 (历史里找到的时间锚点数, 排在全部历史之后的动态数)。
        动态一定会全部插入——找不到锚点时就按时间顺序堆在末尾，
        所以真正需要警惕的信号是「有历史但锚点为 0」，那时顺序不可信。

        插入项带 "_no_save": True —— bind_checkpoint_messages 会读这个 key
        (agent/message.py:338-339)，所以只发给模型、不写进对话历史。
        每次请求重新编排，不会重复堆积，也不怕 /new 之后历史被清空。
        """
        pending = sorted(moments, key=lambda m: m["ts"])
        if not pending:
            return 0, 0

        merged: list[dict] = []
        idx = 0
        anchors = 0
        for msg in req.contexts or []:
            when = self._context_time(msg)
            if when is not None:
                anchors += 1
                while idx < len(pending) and pending[idx]["ts"] < when:
                    merged.append(self._moment_entry(pending[idx]))
                    idx += 1
            merged.append(msg)

        # 比所有历史消息都新的（或压根没有锚点可比的），排在最后
        tail = len(pending) - idx
        while idx < len(pending):
            merged.append(self._moment_entry(pending[idx]))
            idx += 1

        req.contexts = merged
        return anchors, tail

    def _moment_entry(self, moment: dict) -> dict:
        """把一条动态渲染成时间线里的一个事件。"""
        stamp = datetime.fromtimestamp(moment["ts"], self._tz()).strftime(STAMP_FMT)
        bits = [f"{stamp}【我发了条动态】{moment['text']}"]
        n = len(self._moment_photos(moment))
        if n:
            bits.append(f"配图 {n} 张")
        if moment.get("quiet"):
            bits.append("当时没跟他提")
        return {"role": "assistant", "content": " · ".join(bits), "_no_save": True}

    def _context_time(self, msg: dict) -> float | None:
        """解析一条历史消息的时间。

        只认 user 消息正文里的 Current datetime —— assistant 那侧的
        [MM-DD HH:MM] 不带年份，跨年会错，不值得为它冒险。
        """
        if msg.get("role") != "user":
            return None
        content = msg.get("content")
        if isinstance(content, str):
            text = content
        elif isinstance(content, list):
            text = " ".join(
                p.get("text") or ""
                for p in content
                if isinstance(p, dict) and p.get("type") == "text"
            )
        else:
            return None
        hit = CTX_TIME_RE.search(text)
        if not hit:
            return None
        try:
            naive = datetime.strptime(hit.group(1), "%Y-%m-%d %H:%M")
            return naive.replace(tzinfo=self._tz()).timestamp()
        except (ValueError, TypeError):
            return None

    @staticmethod
    def _inject_text(req: ProviderRequest, block: str) -> str:
        """优先塞进 user turn 末尾，回退 system_prompt。返回实际落点，便于排障。

        system_prompt 的追加位置在 TOOL_CALL_PROMPT 之后，离当前问题很远，
        内容容易被稀释；extra_user_content_parts 贴着当前 user turn，
        而且 mark_as_temp() 之后不会落进 conversation history。
        """
        try:
            from astrbot.core.agent.message import TextPart

            req.extra_user_content_parts.append(TextPart(text=block).mark_as_temp())
            return "extra_user_content_parts"
        except Exception as e:
            logger.debug(f"[tg_presence] TextPart 不可用，回退 system_prompt: {e}")
            req.system_prompt += "\n\n" + block + "\n"
            return "system_prompt"

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
        quiet: bool = False,
    ) -> str:
        """enforce_limits=False 用于手动指令：冷却和每日上限只约束角色自主行为。

        quiet=True 表示"发了但不主动在聊天里提"，会体现在返回值和历史注入里。
        """
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
                "quiet": quiet,
            }
        )
        if enforce_limits:
            self._mark_done("post")
            self._bump_daily("post")
        self._save_state()

        # 返回值直接决定她接下来在聊天里的反应，所以要说清"要不要提"
        detail = f"，带了 {len(photos)} 张{source}图" if photos else ""
        if quiet:
            return (
                f"动态发出去了{detail}。这条你没打算主动说——"
                "接下来正常聊你的，别提这件事。他要是自己看到来问你，再决定说不说。"
            )
        return f"动态发出去了{detail}。可以顺口跟他说一声。"

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
    async def post_moment(
        self,
        event: AstrMessageEvent,
        text: str,
        category: str = "",
        mention_now: bool = True,
    ):
        """发一条动态到你自己的频道。当此刻发生了值得记录的事、你有情绪想表达、或者你想让对方看到你的近况时使用。像发朋友圈那样，不需要每次聊天都发。如果对方这条消息里带了图片，那些图会自动作为这条动态的配图。

        Args:
            text(string): 动态的正文，用你自己的口吻写
            category(string): 可选，配图分类名。仅在对方没带图时才用它去图库里挑；留空则发纯文字
            mention_now(boolean): 发完要不要在这次聊天里主动提这件事。真人不是每条动态都会特意说一嘴——想让他立刻知道就传 true；想让他自己刷到、或者这条你暂时不想解释，就传 false，然后正常聊别的
        """
        return await self._do_post(event, text, category, quiet=not mention_now)

    @filter.command("moment")
    async def cmd_moment(self, event: AstrMessageEvent, text: str = ""):
        """手动发一条动态。用法：/moment 正文"""
        self._seal_command(event)
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
        self._seal_command(event)
        if self.conf.get("admin_only_commands", True) and event.role != "admin":
            yield event.plain_result("只有管理员能用这个指令。")
            return
        yield event.plain_result(
            await self._do_avatar(event, category, enforce_limits=False)
        )

    # --------------------------------------------------------------- 改签名

    async def _do_signature(
        self,
        event: AstrMessageEvent,
        text: str,
        enforce_limits: bool = True,
        quiet: bool = False,
    ) -> str:
        """签名用 setMyShortDescription —— 它显示在资料页上，点开头像随时能看到。

        注意别用 setMyDescription：那个只在用户还没和 bot 对话过时显示一次，
        聊过之后永远不再出现，改了没人看得见。
        """
        client = self._client(event)
        if client is None:
            return "改签名失败：这个功能只能在 Telegram 上用。"

        text = text.strip()
        if not text:
            return "改签名失败：内容是空的。"
        if len(text) > SIGNATURE_MAX:
            return (
                f"改签名失败：上限 {SIGNATURE_MAX} 字符，你这条有 {len(text)} 个。"
                "签名要短，长的内容发动态。"
            )

        if enforce_limits:
            wait = self._cooldown_left(
                "signature", int(self.conf.get("signature_cooldown_minutes", 360))
            )
            if wait:
                return f"刚改过签名，{wait} 分钟内不能再改。"

        try:
            await client.set_my_short_description(short_description=text)
        except Exception as e:
            logger.error(f"[tg_presence] 改签名失败: {e}")
            return f"改签名失败了：{e}"

        if enforce_limits:
            self._mark_done("signature")
            self._save_state()

        if quiet:
            return (
                "签名换好了。改签名本来就没有通知，他不点开你资料页是看不到的——"
                "这条你没打算说，接着聊别的。"
            )
        return "签名换好了。可以顺口跟他说一声，或者等他自己发现。"

    @filter.llm_tool(name="update_signature")
    async def update_signature(
        self, event: AstrMessageEvent, text: str, mention_now: bool = False
    ):
        """改自己资料页上的个性签名。那是一句短话，对方点开你的头像就能看到，会一直挂在那儿直到你再改。它会覆盖上一句、没有历史记录，所以适合放此刻的状态或心情；想记录某件事、想让对方收到通知，用发动态。

        Args:
            text(string): 新的签名，120 字符以内，一句话就够
            mention_now(boolean): 要不要在聊天里主动说自己换了签名。默认不说——改签名没有通知，让他自己发现更自然
        """
        return await self._do_signature(event, text, quiet=not mention_now)

    @filter.command("signature", alias={"bio"})
    async def cmd_signature(self, event: AstrMessageEvent, text: str = ""):
        """手动改签名。用法：/signature 新签名"""
        self._seal_command(event)
        if self.conf.get("admin_only_commands", True) and event.role != "admin":
            yield event.plain_result("只有管理员能用这个指令。")
            return
        if not text:
            yield event.plain_result("用法：/signature 新的签名内容")
            return
        yield event.plain_result(
            await self._do_signature(event, text, enforce_limits=False)
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
        self._seal_command(event)
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
            f"改签名冷却：{self._cooldown_left('signature', int(self.conf.get('signature_cooldown_minutes', 360)))} 分钟",
        ]
        if moments:
            last = moments[-1]
            stamp = datetime.fromtimestamp(last["ts"], self._tz()).strftime("%m-%d %H:%M")
            lines.append(f"最近一条：{stamp} {last['text'][:40]}")
        yield event.plain_result("\n".join(lines))
