import asyncio
import base64
import binascii
import hashlib
import json
import mimetypes
import random
import re
import shutil
import sqlite3
import time
from datetime import datetime
from pathlib import Path
from zoneinfo import ZoneInfo

import aiohttp

from astrbot.api import AstrBotConfig, logger
from astrbot.api.event import AstrMessageEvent, filter
from astrbot.api.provider import ProviderRequest
from astrbot.api.star import Context, Star, register
from astrbot.core.star.star_tools import StarTools

try:
    from .tag_schema import ALIAS, FIELDS, OWNER
except ImportError:  # 单文件加载时的兜底，关掉标签校验但插件照常跑
    FIELDS, OWNER, ALIAS = [], {}, {}

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

DEFAULT_VISION_SYSTEM = (
    "你是图像标注助手。只输出对画面的客观描述，"
    "不做评价、不加开场白、不加免责声明、不复述这段要求。"
)

DEFAULT_VISION_PROMPT = (
    "详细描述这张图片，供以后按内容检索用。请覆盖：\n"
    "1. 画面主体是什么，人物的姿态、衣着、配饰（材质和颜色都要写）\n"
    "2. 场景环境、光线、拍摄角度和距离\n"
    "3. 画面里出现的所有物品，以及任何文字、标志、招牌、屏幕内容\n"
    "4. 整体色调和氛围\n"
    "5. 凡是有常见口语简称的，把简称也一并写进去，格式如"
    "「黑色丝袜（黑丝）」「白色丝袜（白丝）」「高跟鞋（高跟）」「过膝袜（膝上袜）」——"
    "检索是按词面匹配的，只写「黑色丝袜」的话，别人搜「黑丝」就找不到这张\n"
    "直接写描述，不要加任何开场白或总结句。名词尽量具体，"
    "宁可啰嗦也不要笼统——「黑色丝袜」比「深色袜子」有用。"
)

# 视觉解析连续失败这么多次就不再自动重试，避免坏图无限撞 API
VISION_MAX_FAILS = 3
VISION_TIMEOUT = 120  # 秒。图片请求比纯文本慢，给宽裕些
VISION_FORMATS = ("openai", "anthropic", "gemini")

# 一轮最多请求几条图片描述。要多了模型容易敷衍，或写到一半被 max_tokens 截断
NOTES_PER_TURN = 5

GALLERY_SCHEMA = """
CREATE TABLE IF NOT EXISTS photos (
    id      INTEGER PRIMARY KEY AUTOINCREMENT,
    path    TEXT    NOT NULL UNIQUE,   -- 相对图库根目录；来源非图库时存绝对路径
    folder  TEXT    NOT NULL DEFAULT '',
    source  TEXT    NOT NULL DEFAULT 'gallery',  -- gallery / moment
    descr   TEXT,                      -- 视觉 API 的描述；NULL = 还没索引
    fails   INTEGER NOT NULL DEFAULT 0,
    sent    INTEGER NOT NULL DEFAULT 0,
    last_sent REAL,
    added   REAL    NOT NULL,
    tag_state  TEXT,               -- ok / 缺失 / 段数不齐 / 有问题
    tag_issues TEXT
);
CREATE INDEX IF NOT EXISTS idx_folder  ON photos(folder);
CREATE INDEX IF NOT EXISTS idx_pending ON photos(fails) WHERE descr IS NULL;
CREATE INDEX IF NOT EXISTS idx_sent    ON photos(last_sent);
"""
ANTHROPIC_VERSION = "2023-06-01"


class VisionError(Exception):
    """视觉解析失败，消息直接进失败日志。"""


@register(
    "astrbot_plugin_tg_presence",
    "chine",
    "让角色自己发动态到频道、换头像、改签名、对消息点表情，并把图片记成可检索的两层文字",
    "0.16.0",
)
class TgPresence(Star):
    def __init__(self, context: Context, config: AstrBotConfig):
        super().__init__(context)
        self.conf = config
        self.data_dir = StarTools.get_data_dir("astrbot_plugin_tg_presence")
        self.state_path = self.data_dir / "state.json"
        self.state = self._load_state()
        self.vision_path = self.data_dir / "vision.json"
        self.vision = self._load_vision()
        # 角色最近一次出站的时刻。只在内存里，进程重启丢一次戳无所谓
        self._pending_sent: float | None = None
        # 在跑的视觉解析任务，持引用防止 asyncio 中途回收
        self._vision_tasks: set[asyncio.Task] = set()
        self._vision_gate: asyncio.Semaphore | None = None
        # base64 指纹 -> sha256，省掉每轮对全部图片重算哈希
        self._key_cache: dict[str, str] = {}
        self.db_path = self.data_dir / "gallery.db"
        self._db: sqlite3.Connection | None = None

    async def terminate(self):
        """插件卸载或热重载时收尾，别把数据库句柄漏掉。"""
        if self._db is not None:
            try:
                self._db.commit()
                self._db.close()
            except sqlite3.Error:
                pass
            self._db = None

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

    def _load_vision(self) -> dict:
        """视觉详解单独存一个文件，不跟 state.json 混。

        一张图的详解几百字，几百张之后这份档案会很大；而 state.json
        每发一条动态、每次冷却都要全量重写，混在一起等于每次把详解也抄一遍。
        """
        if not self.vision_path.exists():
            return {}
        try:
            data = json.loads(self.vision_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as e:
            logger.error(f"[tg_presence] 视觉档案读取失败，按空档案启动: {e}")
            return {}
        return data if isinstance(data, dict) else {}

    def _save_vision(self) -> None:
        tmp = self.vision_path.with_suffix(".json.tmp")
        tmp.write_text(
            json.dumps(self.vision, ensure_ascii=False, indent=2), encoding="utf-8"
        )
        tmp.replace(self.vision_path)

    # ------------------------------------------------------------ 图库索引库

    def db(self) -> sqlite3.Connection:
        """图库索引。上万张图用 JSON 存不下——批量索引时每张都要落盘，
        全量重写一次几 MB 的文件，跑一万张就是几十 GB 的无谓 IO。
        SQLite 是标准库，增量写、按需查，不引入任何依赖。
        """
        if self._db is None:
            self._db = sqlite3.connect(self.db_path)
            self._db.row_factory = sqlite3.Row
            self._db.executescript(GALLERY_SCHEMA)
            # 老库补列：CREATE TABLE IF NOT EXISTS 不会给已存在的表加字段
            have = {r["name"] for r in self._db.execute("PRAGMA table_info(photos)")}
            for col in ("tag_state", "tag_issues"):
                if col not in have:
                    self._db.execute(f"ALTER TABLE photos ADD COLUMN {col} TEXT")
            self._db.commit()
        return self._db

    def _gallery_root(self) -> Path | None:
        raw = (self.conf.get("gallery_dir") or "").strip()
        if not raw:
            return None
        root = Path(raw).expanduser()
        return root if root.is_dir() else None

    def _photo_file(self, row: sqlite3.Row) -> Path | None:
        """把库里的记录还原成磁盘路径。图库项存相对路径，其余存绝对路径。"""
        p = Path(row["path"])
        if p.is_absolute():
            return p if p.exists() else None
        root = self._gallery_root()
        if not root:
            return None
        full = root / p
        return full if full.exists() else None

    def gallery_register(self, path: Path, source: str, folder: str = "") -> int | None:
        """登记一张图片，返回行号。已登记的直接返回原行号，不会重复建。"""
        # 图库内的图一律用相对路径当键，跟 scan 写进去的对齐。
        # 否则从图库挑出来的配图会以绝对路径再插一条，同一张图两个编号
        key, root = str(path), self._gallery_root()
        if root:
            try:
                rel = path.resolve().relative_to(root.resolve())
                key = rel.as_posix()
                folder = rel.parts[0] if len(rel.parts) > 1 else ""
                source = "gallery"
            except (ValueError, OSError):
                pass  # 不在图库目录下，按绝对路径存
        try:
            db = self.db()
            cur = db.execute(
                "INSERT OR IGNORE INTO photos(path, folder, source, added) "
                "VALUES (?,?,?,?)",
                (key, folder, source, time.time()),
            )
            db.commit()
            if cur.lastrowid and cur.rowcount:
                return cur.lastrowid
            row = db.execute("SELECT id FROM photos WHERE path = ?", (key,)).fetchone()
            return row["id"] if row else None
        except sqlite3.Error as e:
            logger.warning(f"[tg_presence] 图片登记失败 {path}: {e}")
            return None

    def gallery_scan(self) -> tuple[int, int]:
        """扫描图库目录，把新文件登记进库。返回 (新增, 总数)。

        只登记路径，不调视觉 API —— 那一步交给 /gallery index 慢慢跑。
        """
        root = self._gallery_root()
        if not root:
            return 0, 0
        db = self.db()
        added = 0
        rows = []
        for p in root.rglob("*"):
            if not p.is_file() or p.suffix.lower() not in PHOTO_EXTS:
                continue
            rel = p.relative_to(root)
            # 顶层子目录当作分类（一个博主一个文件夹）；直接放根目录的归空分类
            folder = rel.parts[0] if len(rel.parts) > 1 else ""
            rows.append((rel.as_posix(), folder, "gallery", time.time()))
            if len(rows) >= 500:
                added += db.executemany(
                    "INSERT OR IGNORE INTO photos(path, folder, source, added) "
                    "VALUES (?,?,?,?)",
                    rows,
                ).rowcount
                db.commit()
                rows.clear()
        if rows:
            added += db.executemany(
                "INSERT OR IGNORE INTO photos(path, folder, source, added) VALUES (?,?,?,?)",
                rows,
            ).rowcount
        db.commit()
        total = db.execute("SELECT COUNT(*) c FROM photos").fetchone()["c"]
        return added, total

    def gallery_search(
        self, keywords: str = "", folder: str = "", limit: int = 8
    ) -> list[sqlite3.Row]:
        """按关键词和分类找图，按命中词数排序。

        不用 AND 取交集：一句「酒店里穿灰丝踩红底细高跟」拆出六七个词，
        只要一个词跟描述里的用词对不上（说「足底」而档案里写「脚底」），
        交集就是空，整句话什么都搜不到。改成打分——命中 5 个词的图排在
        命中 2 个的前面，漏词只降排名不至于让图消失。
        """
        words = [w for w in keywords.replace("，", " ").split() if w][:8]
        args: list = []
        if words:
            score = " + ".join(["(descr LIKE ?)"] * len(words))  # SQLite 里布尔就是 0/1
            args += [f"%{w}%" for w in words]
        else:
            score = "0"

        sql = f"SELECT *, ({score}) AS score FROM photos WHERE descr IS NOT NULL"
        if folder.strip():
            sql += " AND folder LIKE ?"
            args.append(f"%{folder.strip()}%")
        # 命中多的优先；同分时最近发过的排后面，免得反复发同一张
        sql += " ORDER BY score DESC, COALESCE(last_sent, 0) ASC, sent ASC, RANDOM() LIMIT ?"
        args.append(max(1, min(limit, 50)))

        try:
            rows = self.db().execute(sql, args).fetchall()
        except sqlite3.Error as e:
            logger.warning(f"[tg_presence] 图库检索失败: {e}")
            return []
        # 一个词都没中的没意义（没给关键词时例外，那是随手翻）
        return [r for r in rows if not words or r["score"] > 0]

    async def _pick_best(
        self, want: str, rows: list[sqlite3.Row], top: int
    ) -> list[sqlite3.Row]:
        """把候选的完整描述交给模型精排。失败就原样返回粗筛结果。

        粗筛只会数命中了几个词，分不出「M腿岔开坐在椅子上」和
        「M腿岔开躺在床上」——词几乎一样，画面完全不同。让模型读完整
        描述来判断，这一步不看标签，所以标签错位也不影响。
        """
        cfg = self._vision_conf()
        if not cfg or not rows:
            return rows[:top]
        model = (self.conf.get("picker_model") or "").strip()
        cfg = dict(cfg, model=model or cfg["model"], max_tokens=200, stream=False)
        cfg["system"] = (
            "你是图片检索助手。只输出编号，用逗号分隔，不要解释、不要输出别的任何字。"
        )

        blocks = []
        for i, r in enumerate(rows, 1):
            blocks.append(f"[{i}] {(r['descr'] or '')[:900]}")
        prompt = (
            f"用户想找的画面：\n{want}\n\n"
            f"下面是 {len(rows)} 张候选图片的描述：\n\n"
            + "\n\n".join(blocks)
            + f"\n\n把与用户描述最吻合的挑出来，按吻合程度从高到低排序，"
            f"最多 {top} 个。明显不符的不要列。\n"
            "只输出编号，例如：3,7,1"
        )

        try:
            raw = await self._api_post(cfg, self._text_payload(cfg, prompt))
        except VisionError as e:
            logger.warning(f"[tg_presence] 选图精排失败，退回粗筛结果：{e}")
            return rows[:top]

        picked, seen = [], set()
        for n in re.findall(r"\d+", raw or ""):
            i = int(n) - 1
            if 0 <= i < len(rows) and i not in seen:
                seen.add(i)
                picked.append(rows[i])
        if not picked:
            logger.warning(f"[tg_presence] 精排没返回有效编号：{(raw or '')[:80]}")
            return rows[:top]
        logger.info(f"[tg_presence] 精排 {len(rows)} -> {len(picked)} 张")
        return picked[:top]

    def gallery_stat(self) -> dict:
        db = self.db()
        row = db.execute(
            "SELECT COUNT(*) total,"
            " SUM(descr IS NOT NULL) indexed,"
            " SUM(descr IS NULL AND fails < ?) pending,"
            " SUM(descr IS NULL AND fails >= ?) stuck,"
            " SUM(sent) sent"
            " FROM photos",
            (VISION_MAX_FAILS, VISION_MAX_FAILS),
        ).fetchone()
        folders = db.execute(
            "SELECT COUNT(DISTINCT folder) c FROM photos WHERE folder <> ''"
        ).fetchone()["c"]
        return {k: (row[k] or 0) for k in row.keys()} | {"folders": folders}

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

    def _photo_key(self, data_url: str) -> str | None:
        """图片的稳定标识。

        必须用 sha256：内置 hash() 对字符串每次进程启动都不同，
        重启后同一张图会被当成新图。

        但上下文里几十张图时，每轮请求光算哈希就要过几十 MB 的 base64，
        而且要过好几遍（登记一遍、请求描述一遍、折叠一遍），所以缓存一层。
        缓存键用长度加首尾各 32 字符：尾部是 JPEG 压缩数据的末段，
        不同图几乎必然不同，再叠上长度，撞不到一起。
        """
        hit = DATA_URL_RE.match((data_url or "").strip())
        if not hit:
            return None
        b64 = hit.group("b64")
        probe = f"{len(b64)}:{b64[:32]}:{b64[-32:]}"
        if (cached := self._key_cache.get(probe)) is not None:
            return cached
        key = hashlib.sha256(b64.encode()).hexdigest()[:16]
        if len(self._key_cache) > 512:
            self._key_cache.clear()
        self._key_cache[probe] = key
        return key

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

    # --------------------------------------------------------- 独立视觉 API 层

    def _vision_conf(self) -> dict | None:
        """视觉 API 的配置。三项必填齐了才算配好，否则返回 None。"""
        base = (self.conf.get("vision_base_url") or "").strip().rstrip("/")
        key = (self.conf.get("vision_api_key") or "").strip()
        model = (self.conf.get("vision_model") or "").strip()
        if not (base and key and model):
            return None

        fmt = (self.conf.get("vision_api_format") or "openai").strip().lower()
        if fmt not in VISION_FORMATS:
            logger.warning(f"[tg_presence] 接口格式 {fmt} 不认识，按 openai 处理")
            fmt = "openai"

        window = max(1024, int(self.conf.get("vision_context_window", 128000) or 128000))
        out = max(64, int(self.conf.get("vision_max_tokens", 1024) or 1024))
        if out >= window:
            # 输出上限吃掉整个窗口的话，图片根本塞不进去
            out = max(64, window // 4)
            logger.warning(
                f"[tg_presence] 最大输出长度不能接近上下文窗口，已压到 {out}"
            )

        extra = {}
        if raw := (self.conf.get("vision_extra_body") or "").strip():
            try:
                extra = json.loads(raw)
                if not isinstance(extra, dict):
                    raise ValueError("顶层必须是 JSON 对象")
            except (json.JSONDecodeError, ValueError) as e:
                logger.warning(f"[tg_presence] 附加请求参数不是合法 JSON，已忽略：{e}")
                extra = {}

        return {
            "fmt": fmt,
            "base": base,
            "key": key,
            "model": model,
            "window": window,
            "max_tokens": out,
            "stream": bool(self.conf.get("vision_stream", False)),
            "extra": extra,
            "system": (self.conf.get("vision_system_prompt") or "").strip()
            or DEFAULT_VISION_SYSTEM,
            "prompt": (self.conf.get("vision_prompt") or "").strip()
            or DEFAULT_VISION_PROMPT,
        }

    # ----------------------------------------------- 三种接口格式的请求与解析

    @staticmethod
    def _vision_url(cfg: dict) -> str:
        """按格式拼出请求地址。各家路径约定不同，都允许只填到根。"""
        base, fmt = cfg["base"], cfg["fmt"]
        if fmt == "openai":
            # 填到 /v1 或填全都认
            return base if base.endswith("/chat/completions") else base + "/chat/completions"
        if fmt == "anthropic":
            if base.endswith("/messages"):
                return base
            return base + ("/messages" if base.endswith("/v1") else "/v1/messages")
        # gemini：模型名在路径里，流式和非流式是两个不同的方法
        method = "streamGenerateContent?alt=sse" if cfg["stream"] else "generateContent"
        head = base if base.rsplit("/", 1)[-1].startswith("v1") else base + "/v1beta"
        return f"{head}/models/{cfg['model']}:{method}"

    @staticmethod
    def _vision_headers(cfg: dict) -> dict:
        """鉴权方式三家各不相同。"""
        fmt = cfg["fmt"]
        if fmt == "anthropic":
            return {
                "x-api-key": cfg["key"],
                "anthropic-version": ANTHROPIC_VERSION,
                "Content-Type": "application/json",
            }
        if fmt == "gemini":
            # 走 header 而不是 ?key=，免得密钥出现在 URL 里被各级日志抄走
            return {"x-goog-api-key": cfg["key"], "Content-Type": "application/json"}
        return {
            "Authorization": f"Bearer {cfg['key']}",
            "Content-Type": "application/json",
        }

    @staticmethod
    def _vision_payload(cfg: dict, mime: str, b64: str) -> dict:
        """按格式组装请求体。图片的位置和字段名三家完全不同。"""
        fmt = cfg["fmt"]
        if fmt == "anthropic":
            body = {
                "model": cfg["model"],
                "max_tokens": cfg["max_tokens"],
                "system": cfg["system"],
                "messages": [
                    {
                        "role": "user",
                        "content": [
                            {
                                "type": "image",
                                "source": {
                                    "type": "base64",
                                    "media_type": mime,
                                    "data": b64,
                                },
                            },
                            {"type": "text", "text": cfg["prompt"]},
                        ],
                    }
                ],
            }
        elif fmt == "gemini":
            body = {
                "system_instruction": {"parts": [{"text": cfg["system"]}]},
                "contents": [
                    {
                        "role": "user",
                        "parts": [
                            {"text": cfg["prompt"]},
                            {"inline_data": {"mime_type": mime, "data": b64}},
                        ],
                    }
                ],
                "generationConfig": {"maxOutputTokens": cfg["max_tokens"]},
            }
        else:
            body = {
                "model": cfg["model"],
                "max_tokens": cfg["max_tokens"],
                "messages": [
                    {"role": "system", "content": cfg["system"]},
                    {
                        "role": "user",
                        "content": [
                            {"type": "text", "text": cfg["prompt"]},
                            {
                                "type": "image_url",
                                "image_url": {
                                    "url": f"data:{mime};base64,{b64}"
                                },
                            },
                        ],
                    },
                ],
            }

        if cfg["stream"] and fmt != "gemini":  # gemini 靠 URL 上的方法名区分
            body["stream"] = True
        # 附加参数最后合并，允许覆盖上面任何一项（如 Gemini 的 safetySettings）
        for k, v in (cfg["extra"] or {}).items():
            if isinstance(v, dict) and isinstance(body.get(k), dict):
                body[k].update(v)
            else:
                body[k] = v
        return body

    @staticmethod
    def _resp_text(fmt: str, data: dict) -> str:
        """从非流式响应里取正文。"""
        try:
            if fmt == "anthropic":
                blocks = data["content"]
            elif fmt == "gemini":
                blocks = data["candidates"][0]["content"]["parts"]
            else:
                content = data["choices"][0]["message"].get("content")
                if isinstance(content, str):
                    return content.strip()
                blocks = content or []  # 部分网关返回分块列表
        except (KeyError, IndexError, TypeError):
            return ""
        if not isinstance(blocks, list):
            return ""
        # 只要 text，丢掉推理模型的 thinking 块——那是思考过程不是描述
        bits = [
            t.strip()
            for b in blocks
            if isinstance(b, dict)
            and b.get("type", "text") == "text"
            and isinstance(t := b.get("text"), str)
            and t.strip()
        ]
        return " ".join(bits)

    @staticmethod
    def _delta_text(fmt: str, obj: dict) -> str:
        """从一个 SSE 数据块里取增量文本。取不到就返回空串。"""
        try:
            if fmt == "anthropic":
                if obj.get("type") != "content_block_delta":
                    return ""
                delta = obj.get("delta") or {}
                # thinking_delta 不要，只要正文
                return delta.get("text", "") if delta.get("type") == "text_delta" else ""
            if fmt == "gemini":
                parts = obj["candidates"][0]["content"]["parts"]
                return "".join(
                    p["text"] for p in parts if isinstance(p.get("text"), str)
                )
            return obj["choices"][0].get("delta", {}).get("content") or ""
        except (KeyError, IndexError, TypeError):
            return ""

    def _vision_ready(self) -> bool:
        return self._vision_conf() is not None

    def _gate(self) -> asyncio.Semaphore:
        """并发闸。懒创建——插件 __init__ 时不一定已经有事件循环。"""
        if self._vision_gate is None:
            n = max(1, int(self.conf.get("vision_concurrency", 2) or 2))
            self._vision_gate = asyncio.Semaphore(n)
        return self._vision_gate

    @filter.on_llm_request(priority=-35)
    async def register_context_photos(
        self, event: AstrMessageEvent, req: ProviderRequest
    ):
        """给上下文里每张图登记编号、存盘，并派发视觉解析。

        存盘不能等到折叠时才做：llm_compress 会把整轮对话连同图片一起压掉，
        /new 也会清空上下文，那之后原图就再也拿不回来了。图片一旦进入视野
        就先落盘，后面无论上下文怎么变，档案都还在。

        priority=-35 让它排在请求描述(-40)和折叠(-50)前面，
        这样那两步拿到的编号都是这里分配好的。
        """
        # 存盘只为两件事：折叠后能取回、给视觉模型读。都不需要就别占磁盘
        if not self._vision_ready() and (
            int(self.conf.get("max_context_images", 0) or 0) <= 0
        ):
            return

        store = self.data_dir / "context_photos"
        store.mkdir(parents=True, exist_ok=True)

        seen: list[str] = []
        for msg in req.contexts or []:
            content = msg.get("content")
            if not isinstance(content, list):
                continue
            for part in content:
                if not (isinstance(part, dict) and part.get("type") == "image_url"):
                    continue
                url = (part.get("image_url") or {}).get("url") or ""
                pid = self._stash_photo(url, store)
                if not pid:
                    continue
                if pid not in seen:
                    seen.append(pid)
                # 顺手补时间，别等折叠——压缩可能先一步把这轮吃掉
                if when := self._context_time(msg):
                    self.state.setdefault("photo_time", {}).setdefault(pid, when)

        if seen:
            self._save_state()
        self._dispatch_vision(seen)

    def _dispatch_vision(self, pids: list[str]) -> int:
        """给还没有详解的图派发解析任务。返回派了几个。"""
        if not self._vision_ready():
            return 0
        paths = self.state.get("photo_paths") or {}
        fails = self.state.get("vision_fail") or {}
        running = {t.get_name() for t in self._vision_tasks}

        n = 0
        for pid in pids:
            if pid in self.vision or f"vision:{pid}" in running:
                continue
            if fails.get(pid, 0) >= VISION_MAX_FAILS:
                continue
            path = paths.get(pid)
            if not path or not Path(path).exists():
                continue
            task = asyncio.create_task(
                self._vision_describe(pid, path), name=f"vision:{pid}"
            )
            self._vision_tasks.add(task)
            task.add_done_callback(self._vision_tasks.discard)
            n += 1
        if n:
            logger.debug(f"[tg_presence] 派发 {n} 张图的视觉解析")
        return n

    @staticmethod
    def _read_image(path: str) -> tuple[str, str] | None:
        """把本地图片读成 (mime, base64)。远端 API 拿不到本机路径。

        三种格式对图片的包装不同（data URL / source 对象 / inline_data），
        所以这里只出原料，拼装交给各自的 payload 构造。
        """
        try:
            raw = Path(path).read_bytes()
        except OSError as e:
            logger.warning(f"[tg_presence] 读不到图片 {path}: {e}")
            return None
        mime = mimetypes.guess_type(path)[0] or "image/jpeg"
        return mime, base64.b64encode(raw).decode()

    @staticmethod
    def _text_payload(cfg: dict, prompt: str) -> dict:
        """纯文本请求体。选图精排不需要传图，只比对文字描述。"""
        fmt = cfg["fmt"]
        if fmt == "anthropic":
            body = {
                "model": cfg["model"],
                "max_tokens": cfg["max_tokens"],
                "system": cfg["system"],
                "messages": [{"role": "user", "content": prompt}],
            }
        elif fmt == "gemini":
            body = {
                "system_instruction": {"parts": [{"text": cfg["system"]}]},
                "contents": [{"role": "user", "parts": [{"text": prompt}]}],
                "generationConfig": {"maxOutputTokens": cfg["max_tokens"]},
            }
        else:
            body = {
                "model": cfg["model"],
                "max_tokens": cfg["max_tokens"],
                "messages": [
                    {"role": "system", "content": cfg["system"]},
                    {"role": "user", "content": prompt},
                ],
            }
        if cfg["stream"] and fmt != "gemini":
            body["stream"] = True
        return body

    async def _vision_post(self, cfg: dict, mime: str, b64: str) -> str:
        return await self._api_post(cfg, self._vision_payload(cfg, mime, b64))

    async def _api_post(self, cfg: dict, payload: dict) -> str:
        """发一次请求，返回正文。失败抛 VisionError。

        三种接口格式的传输、流式拼接、错误分类都在这儿，
        图片解析和选图精排共用同一条链路。
        """
        url = self._vision_url(cfg)
        headers = self._vision_headers(cfg)
        fmt = cfg["fmt"]
        timeout = aiohttp.ClientTimeout(total=VISION_TIMEOUT)

        try:
            async with aiohttp.ClientSession(timeout=timeout) as sess:
                async with sess.post(url, json=payload, headers=headers) as r:
                    if r.status != 200:
                        body = await r.text()
                        # 带上响应体，光看状态码分不清是 key 错还是模型名错
                        raise VisionError(f"HTTP {r.status} {body[:300]}")
                    if not cfg["stream"]:
                        return self._resp_text(fmt, json.loads(await r.text()))

                    # 流式：逐行收 SSE，把增量拼回完整文本。
                    # 有些中转网关对非流式长响应直接 504，只有流式能跑通
                    bits: list[str] = []
                    async for raw_line in r.content:
                        line = raw_line.decode("utf-8", "ignore").strip()
                        if not line.startswith("data:"):
                            continue  # event: / 空行 / 注释心跳都跳过
                        chunk = line[5:].strip()
                        if chunk == "[DONE]":
                            break
                        try:
                            bits.append(self._delta_text(fmt, json.loads(chunk)))
                        except json.JSONDecodeError:
                            continue
                    return "".join(bits).strip()
        except asyncio.TimeoutError:
            raise VisionError(f"超时（{VISION_TIMEOUT} 秒）") from None
        except (aiohttp.ClientError, json.JSONDecodeError, ValueError) as e:
            raise VisionError(f"{type(e).__name__}: {e}") from e

    def _note_fail(self, pid: str, why: str) -> None:
        fails = self.state.setdefault("vision_fail", {})
        fails[pid] = fails.get(pid, 0) + 1
        self._save_state()
        logger.warning(
            f"[tg_presence] 视觉解析 #{pid} 失败"
            f"（第 {fails[pid]} 次，满 {VISION_MAX_FAILS} 次后不再自动重试）：{why}"
        )

    async def _vision_of(self, path: str, skip_check=None) -> str | None:
        """调独立视觉 API 拿一张图的描述。失败抛 VisionError。

        支持 OpenAI 兼容、Anthropic 原生、Gemini 原生三种接口格式，
        配置全在插件自己这儿，跟 AstrBot 的服务提供商互不干扰 ——
        主对话模型贵、这个便宜，本来就不该共用一套配置。

        上下文图片和图库图片走的是同一条链路，只是描述存去不同地方。
        skip_check 在拿到并发闸之后再判一次，避免排队期间白跑一趟。
        """
        cfg = self._vision_conf()
        if not cfg:
            raise VisionError("视觉 API 没配全")
        image = self._read_image(path)
        if not image:
            raise VisionError("图片读不出来")

        async with self._gate():
            if skip_check and skip_check():
                return None
            text = await self._vision_post(cfg, *image)

        if not text:
            raise VisionError("返回内容为空，可能是模型拒答或触发了内容过滤")
        return text[: max(100, int(self.conf.get("vision_max_chars", 600) or 600))]

    async def _vision_describe(self, pid: str, path: str) -> bool:
        """给上下文里的一张图做视觉解析，存进 vision.json。"""
        if pid in self.vision:
            return True
        try:
            text = await self._vision_of(path, lambda: pid in self.vision)
        except VisionError as e:
            self._note_fail(pid, str(e))
            return False
        if text is None:  # 排队期间已经被别的任务做掉了
            return True

        self.vision[pid] = text
        self._save_vision()
        if (self.state.get("vision_fail") or {}).pop(pid, None) is not None:
            self._save_state()
        logger.info(f"[tg_presence] 视觉解析 #{pid} 完成，{len(text)} 字")
        return True

    @staticmethod
    def audit_tags(descr: str) -> tuple[str, list[str]]:
        """校验描述末尾的 44 项标签行。返回 (归类, 问题列表)。

        归类：ok / 缺失 / 段数不齐 / 有问题
        模型在这 44 项上会犯几类固定错误——32/33/34 三项候选值前缀雷同
        （都有"不可见""被衣物覆盖""裸露-"）经常互填，25 项要填鞋款却填成
        第 11 项的"穿鞋"，还有"中"→"中等"这种简写。这里只诊断不改数据：
        非法值往往仍是有意义的词（"项圈"），删了反而丢信息，留着还能被
        substring 检索命中。
        """
        if not FIELDS:
            return "ok", []
        line = ""
        for raw in reversed((descr or "").splitlines()):
            if "---" in raw and re.match(r"^\s*1\.", raw):
                line = raw.strip()
                break
        if not line:
            return "缺失", ["整行标签没输出"]

        segs = line.split("---")
        issues, nums = [], []
        for seg in segs:
            m = re.match(r"^(\d+)\.(.*)$", seg.strip(), re.S)
            if not m:
                continue
            i = int(m.group(1))
            nums.append(i)
            if not 1 <= i <= len(FIELDS):
                continue
            name, cand = FIELDS[i - 1]
            allowed = set(cand.split("|"))
            for one in m.group(2).split(","):
                one = ALIAS.get(one.strip(), one.strip())
                if not one or one in allowed:
                    continue
                owners = OWNER.get(one)
                if owners:
                    who = "、".join(f"{o}.{FIELDS[o - 1][0]}" for o in owners[:3])
                    issues.append(f"{i}.{name}「{one}」是 {who} 的值")
                else:
                    issues.append(f"{i}.{name}「{one}」不在候选集")

        if nums != list(range(1, len(FIELDS) + 1)):
            issues.insert(0, f"编号不连续：{len(nums)} 项")
            return "段数不齐", issues
        return ("有问题" if issues else "ok"), issues

    async def _gallery_describe(self, row_id: int, path: str) -> bool:
        """给图库里的一张图做视觉解析，存进索引库。"""
        db = self.db()
        try:
            text = await self._vision_of(path)
        except VisionError as e:
            db.execute("UPDATE photos SET fails = fails + 1 WHERE id = ?", (row_id,))
            db.commit()
            logger.warning(f"[tg_presence] 图库 g{row_id} 索引失败：{e}")
            return False

        verdict, issues = self.audit_tags(text)
        db.execute(
            "UPDATE photos SET descr = ?, fails = 0, tag_state = ?, tag_issues = ? "
            "WHERE id = ?",
            (text, verdict, "; ".join(issues[:8]), row_id),
        )
        db.commit()
        if verdict != "ok":
            logger.warning(
                f"[tg_presence] g{row_id} 标签{verdict}：{'; '.join(issues[:3])}"
            )
        return True

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
        if len(pending) > NOTES_PER_TURN:
            # 折叠是从最旧的开始的，所以最旧的那几张最急着要描述——留它们，
            # 新图这轮先放着，下一轮自然会再排到
            rest = len(pending) - NOTES_PER_TURN
            pending = pending[:NOTES_PER_TURN]
            logger.debug(f"[tg_presence] 本轮只请求 {NOTES_PER_TURN} 条描述，还剩 {rest} 张")
        self._save_state()  # 编号是刚分配的，落盘

        ids = "、".join(f"#{p}" for p in pending)
        has_vision = self._vision_ready()
        # 有独立视觉层时，她这句话只负责「认出是哪张」，细节交给系统记，
        # 所以要求写一句就够；没有视觉层时这句是唯一的检索依据，得写全
        if has_vision:
            howto = (
                "一句话就行，抓最能认出这张图的那个点——谁拍的、什么场合、\n"
                "画面里最显眼的是什么。用你自己的说法。画面里的琐碎细节\n"
                "系统会另外记一份，你不用写。\n"
            )
        else:
            howto = (
                "描述要具体到能靠它认出这张图——画面内容、谁拍的、什么场合，\n"
                "用你自己的说法就行。\n"
            )

        recall = (
            "另外：对方提起某张旧图时（「昨天那张」「黑丝那张」），\n"
            "先看对话里的 [图片 #N ...] 占位——描述就在里面，直接认出来即可。\n"
            "上下文里找不到再用 find_photo 查存档。\n"
            "**符合的不止一张时，问他是哪张，不要自己挑一张然后当成就是那张。**\n"
        )
        if has_vision:
            recall += (
                "他要是问起某张图里的具体东西（画面里有什么、什么颜色、写了什么字），\n"
                "用 inspect_photo 查那张图的细节记录，别硬猜也别急着 recall_photo——\n"
                "recall_photo 是把原图整个搬回来，只有真的需要亲眼再看一遍才用。\n"
            )

        self._inject_text(
            req,
            "<describe_images>\n"
            f"上下文里这几张图还没有存过描述：{ids}\n"
            "请在这次回复的最末尾，为每张各写一条：\n"
            '  <img_note id="编号">这张图是什么</img_note>\n'
            "按图片在对话里出现的先后顺序对应编号。\n" + howto + "这几行会被系统抽走存档，对方看不到，也不算进你的回复。\n"
            "正常说你的话，把这些附在最后即可。\n\n" + recall + "</describe_images>",
        )
        logger.debug(f"[tg_presence] 请求描述图片 {ids}")

    def _harvest_notes(self, text: str) -> int:
        """把文本里的 <img_note> 存进档案，返回条数。"""
        desc = self.state.setdefault("photo_desc", {})
        found = 0
        for hit in IMG_NOTE_RE.finditer(text):
            body = hit.group("desc").strip()
            if body:
                desc[hit.group("id")] = body[:200]
                found += 1
        if found:
            self._save_state()
        return found

    @filter.on_llm_response()
    async def capture_descriptions(self, event: AstrMessageEvent, resp):
        """抽出 <img_note> 存档，并从要发出去的内容里剥掉。

        必须走 completion_text 这个 property，不能直接摸 result_chain：
        LLMResponse.result_chain 默认是 None（provider 一般只填 _completion_text，
        setter 在 result_chain 为 None 时就写那个私有字段），所以
        result_chain.chain 多半取不到，判空一 return 就等于整个钩子没跑。
        property 的 getter/setter 两种存储形态都覆盖，而且 result_chain 存在时
        setter 只替换 Plain 组件、不动图片之类的其它组件。
        """
        if not self.conf.get("describe_images", True):
            return
        text = getattr(resp, "completion_text", None)
        if not isinstance(text, str) or "<img_note" not in text:
            return

        if found := self._harvest_notes(text):
            logger.info(f"[tg_presence] 收到 {found} 条图片描述")
        resp.completion_text = IMG_NOTE_RE.sub("", text).strip()

    @filter.on_decorating_result()
    async def strip_notes_before_send(self, event: AstrMessageEvent):
        """发送前最后一道闸：确保 <img_note> 不会漏进聊天窗口。

        上一步已经剥过一次，但文本抵达发送阶段的路径不止一条（其它插件改写、
        分段回复重组等），这里照最终要发的内容再兜一次底。
        正常情况下这里什么都匹配不到 —— 一旦日志里出现，说明上一步漏了。
        """
        if not self.conf.get("describe_images", True):
            return
        result = event.get_result()
        chain = getattr(result, "chain", None)
        if not chain:
            return

        keep, found = [], 0
        for comp in chain:
            text = getattr(comp, "text", None)
            if not isinstance(text, str) or "<img_note" not in text:
                keep.append(comp)
                continue
            found += self._harvest_notes(text)
            comp.text = IMG_NOTE_RE.sub("", text).strip()
            # 整条只有描述标记时剥完是空的，别把空消息发出去
            if comp.text:
                keep.append(comp)

        if found:
            logger.warning(f"[tg_presence] 发送前兜底剥掉 {found} 条图片描述")
        if len(keep) != len(chain):
            result.chain = keep

    @filter.llm_tool(name="find_photo")
    async def find_photo(
        self, event: AstrMessageEvent, keywords: str = "", day: str = "", **_extra
    ):
        """在存档的旧图片里找。对话里能直接看到的那些 [图片 #N] 占位不用查这个——只有当对方提起一张你在当前上下文里找不到的旧图时才用。会同时搜你自己写的那句描述和系统存的画面细节记录。返回候选列表，如果不止一张，问对方是哪张，别自己瞎猜。

        Args:
            keywords(string): 关键词，空格分隔，例如「黑丝 足底」。会取交集。画面里的东西也能搜，比如「咖啡杯」
            day(string): 限定日期，格式 MM-DD 或 YYYY-MM-DD。留空则不限
        """
        desc = self.state.get("photo_desc") or {}
        times = self.state.get("photo_time") or {}
        if not desc and not self.vision:
            return "还没有存过任何图片描述。"

        words = [w for w in keywords.replace("，", " ").split() if w]
        day = day.strip()

        hits = []
        for pid in set(desc) | set(self.vision):
            mine = desc.get(pid, "")
            detail = self.vision.get(pid, "")
            if words and not all(w in mine or w in detail for w in words):
                continue
            ts = times.get(pid)
            stamp = (
                datetime.fromtimestamp(ts, self._tz()).strftime("%Y-%m-%d %H:%M")
                if ts
                else ""
            )
            if day and day not in stamp:
                continue
            # 只在细节记录里命中的，标出来——她好知道自己为什么想起这张
            only_detail = bool(words) and not all(w in mine for w in words)
            label = mine or (detail[:60] + "…" if len(detail) > 60 else detail)
            hits.append((ts or 0, pid, stamp or "时间不详", label, only_detail))

        if not hits:
            return "没找到符合的图片。换个说法再试，或者问问对方是哪张。"

        hits.sort(reverse=True)
        lines = [
            f"#{pid} · {stamp} · {label}"
            + (" ←靠画面细节匹配到的" if only_detail else "")
            for _, pid, stamp, label, only_detail in hits[:12]
        ]
        head = f"找到 {len(hits)} 张" + ("，只列最近 12 张：" if len(hits) > 12 else "：")
        tail = (
            "\n不止一张，先问清楚是哪张再取。"
            if len(hits) > 1
            else "\ninspect_photo 加编号能看这张图的画面细节，recall_photo 是把原图取回来重新看。"
        )
        return head + "\n" + "\n".join(lines) + tail

    @filter.llm_tool(name="inspect_photo")
    async def inspect_photo(self, event: AstrMessageEvent, photo_id: str, **_extra):
        """查一张图的画面细节记录。当你想知道某张图里的具体东西（画面里有什么、什么颜色、写了什么字），而这张图现在不在你眼前时用这个。它只给你文字记录，不会把图重新塞进来，比 recall_photo 省得多。确实需要亲眼再看一遍原图才用 recall_photo。

        Args:
            photo_id(string): 图片编号，比如 12
        """
        pid = photo_id.strip().lstrip("#")
        detail = self.vision.get(pid)
        mine = (self.state.get("photo_desc") or {}).get(pid)
        if not detail and not mine:
            known = pid in (self.state.get("photo_paths") or {})
            return (
                f"#{pid} 还没有细节记录，可以用 recall_photo 把原图取回来看。"
                if known
                else f"找不到 #{pid} 这张图。"
            )

        ts = (self.state.get("photo_time") or {}).get(pid)
        stamp = (
            datetime.fromtimestamp(ts, self._tz()).strftime("%Y-%m-%d %H:%M")
            if ts
            else "时间不详"
        )
        lines = [f"#{pid} · {stamp}"]
        if mine:
            lines.append(f"你当时记的：{mine}")
        if detail:
            lines.append(f"画面细节：{detail}")
        else:
            lines.append("（没有细节记录，需要的话用 recall_photo 看原图）")
        return "\n".join(lines)

    @filter.llm_tool(name="recall_photo")
    async def recall_photo(self, event: AstrMessageEvent, photo_id: str, **_extra):
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

    # --------------------------------------------------------------- 发图给对方

    @filter.llm_tool(name="browse_gallery")
    async def browse_gallery(
        self, event: AstrMessageEvent, keywords: str = "", want: str = "",
        folder: str = "", **_extra
    ):
        """在你自己的相册里翻，找一张想发给他的照片。想给他看点什么、或者他描述了某个画面让你找的时候用。返回的编号形如 g123，再用 send_photo 发出去。

        Args:
            keywords(string): 检索词，空格分隔，例如「酒店 灰丝 细高跟 M腿」。词尽量多给几个，命中越多排得越前，个别词没对上也不影响
            want(string): 可选但强烈建议填：把想找的画面用一句话原样描述出来。给了这个会再让模型逐张比对完整描述，挑出真正吻合的那张
            folder(string): 可选，限定某个相册分类
        """
        pool = max(4, int(self.conf.get("picker_candidates", 20) or 20))
        rows = self.gallery_search(keywords or want, folder, limit=pool)
        if not rows:
            stat = self.gallery_stat()
            if not stat["indexed"]:
                return "相册还没建好索引，现在挑不了。"
            return "没找到合适的。换几个词再翻翻，或者把想找的画面整句说出来。"

        picked, reranked = rows[:8], False
        if want.strip() and self.conf.get("picker_enable", True) and len(rows) > 1:
            picked = await self._pick_best(want.strip(), rows, top=8)
            reranked = True

        lines = []
        for r in picked:
            tag = f"[{r['folder']}] " if r["folder"] else ""
            seen = f" · 发过{r['sent']}次" if r["sent"] else ""
            lines.append(f"g{r['id']} · {tag}{(r['descr'] or '')[:70]}{seen}")
        head = (
            f"从 {len(rows)} 张里挑出这 {len(picked)} 张，最吻合的排在前面："
            if reranked
            else f"翻到 {len(picked)} 张："
        )
        return head + "\n" + "\n".join(lines) + "\n用 send_photo 加编号发出去。"

    @filter.llm_tool(name="send_photo")
    async def send_photo(
        self, event: AstrMessageEvent, photo_id: str, caption: str = "", **_extra
    ):
        """把一张照片发给对方。编号有两种：browse_gallery 给的 g123 是你相册里的；对话里 [图片 #3] 那种 #3 是之前聊天里出现过的图，想重发某张旧图就用它。发完照常说你的话，别把发照片这件事当成一次汇报。

        Args:
            photo_id(string): 照片编号，g123 或 #3
            caption(string): 可选，跟照片一起发的一句话。留空则只发图
        """
        return await self._do_send_photo(event, photo_id, caption)

    async def _do_send_photo(
        self, event: AstrMessageEvent, photo_id: str, caption: str = "",
        enforce_limits: bool = True,
    ) -> str:
        client = self._client(event)
        if client is None:
            return "这个平台发不了照片。"

        raw = (photo_id or "").strip()
        row = None
        if raw.lower().startswith("g") and raw[1:].isdigit():
            row = self.db().execute(
                "SELECT * FROM photos WHERE id = ?", (int(raw[1:]),)
            ).fetchone()
            path = self._photo_file(row) if row else None
        else:  # 聊天里出现过的图，走上下文那套编号
            pid = raw.lstrip("#")
            stored = (self.state.get("photo_paths") or {}).get(pid)
            path = Path(stored) if stored and Path(stored).exists() else None
        if not path:
            return f"找不到 {raw} 这张照片。"

        if enforce_limits:
            cd = self._cooldown_left(
                "photo", int(self.conf.get("photo_cooldown_minutes", 10))
            )
            if cd:
                return f"刚发过照片，等 {cd} 分钟再发。先正常聊。"
            left = self._daily_left("photo", int(self.conf.get("photo_daily_limit", 20)))
            if left == 0:
                return "今天发的照片够多了，明天再说。"

        try:
            with open(path, "rb") as fp:
                await client.send_photo(
                    chat_id=self._chat_id(event),
                    photo=fp,
                    caption=(caption or "")[:CAPTION_MAX] or None,
                )
        except Exception as e:
            logger.error(f"[tg_presence] 发照片失败 {path}: {e}")
            return f"照片没发出去：{e}"

        if row is not None:
            self.db().execute(
                "UPDATE photos SET sent = sent + 1, last_sent = ? WHERE id = ?",
                (time.time(), row["id"]),
            )
            self.db().commit()
        if enforce_limits:
            self._mark_done("photo")
            self._bump_daily("photo")
        logger.info(f"[tg_presence] 已发送照片 {raw} -> {path.name}")
        return f"照片发出去了（{raw}）。"

    @filter.command("photo")
    async def cmd_photo(self, event: AstrMessageEvent, photo_id: str = "", *, caption: str = ""):
        """手动发一张照片。用法：/photo g123 [附言]"""
        self._seal_command(event)
        if self.conf.get("admin_only_commands", True) and event.role != "admin":
            yield event.plain_result("只有管理员能用这个指令。发 /whoami 看是哪儿没对上。")
            return
        if not photo_id:
            yield event.plain_result("用法：/photo g123 [附言]，编号从 /gallery search 查。")
            return
        yield event.plain_result(
            await self._do_send_photo(event, photo_id, caption, enforce_limits=False)
        )

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

        # 动态配图登记进相册库，之后能被翻到、也能重新发给他。
        # 从图库挑的那些扫描时已经在库里了，INSERT OR IGNORE 会跳过
        for p in photos:
            self.gallery_register(p, source="moment", folder="动态配图")

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
        **_extra,
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
            yield event.plain_result("只有管理员能用这个指令。发 /whoami 看是哪儿没对上。")
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
    async def change_avatar(self, event: AstrMessageEvent, category: str = "", **_extra):
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
            yield event.plain_result("只有管理员能用这个指令。发 /whoami 看是哪儿没对上。")
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
        self, event: AstrMessageEvent, text: str, mention_now: bool = False, **_extra
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
            yield event.plain_result("只有管理员能用这个指令。发 /whoami 看是哪儿没对上。")
            return
        if not text:
            yield event.plain_result("用法：/signature 新的签名内容")
            return
        yield event.plain_result(
            await self._do_signature(event, text, enforce_limits=False)
        )

    # ------------------------------------------------------------- 表情回应

    @filter.llm_tool(name="react_message")
    async def react_message(self, event: AstrMessageEvent, emoji: str, **_extra):
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
            yield event.plain_result("只有管理员能用这个指令。发 /whoami 看是哪儿没对上。")
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

        paths = self.state.get("photo_paths") or {}
        if paths:
            desc_n = len(self.state.get("photo_desc") or {})
            lines.append(
                f"图片存档：{len(paths)} 张 · 她记的描述 {desc_n} 条 · "
                f"画面细节 {len(self.vision)} 条"
                + ("" if self._vision_ready() else "（未配视觉 API）")
            )
        yield event.plain_result("\n".join(lines))

    # --------------------------------------------------------------- 导演模式

    def _director_id(self) -> str:
        return (self.conf.get("director_platform_id") or "").strip()

    @staticmethod
    def _umo_platform(umo: str) -> str:
        """UMO 第一段就是「机器人名称」，多 bot 靠它区分。"""
        return (umo or "").split(":", 1)[0]

    def _platform_of(self, event: AstrMessageEvent) -> str:
        return self._umo_platform(event.unified_msg_origin)

    def _director_guard(self, event: AstrMessageEvent) -> str | None:
        """校验这条指令来自控制台、且目标绑对了。返回 None 放行。"""
        did = self._director_id()
        if not did:
            return (
                "没配控制台。在插件配置里填「控制台机器人名称」——"
                "WebUI「平台配置」里另一个 bot 那一栏的第一项。"
            )
        if self._platform_of(event) != did:
            return "这条指令只能在控制台那个 bot 里发——在这儿发等于当着他的面喊话。"
        target = (self.state.get("director_target") or "").strip()
        if not target:
            return (
                "还没绑定目标会话。\n"
                "在这儿发：/link 角色机器人名称:FriendMessage:会话ID"
            )
        if self._umo_platform(target) == did:
            # 目标是控制台自己的话，消息会发回控制台、历史也写进控制台的会话，
            # 角色那边什么都没有，但看着像成功了
            return (
                f"投递目标绑到控制台自己了：\n{target}\n\n"
                "重新绑：/link 角色机器人名称:FriendMessage:会话ID"
            )
        return None

    async def _append_assistant(self, umo: str, text: str) -> bool:
        """把一条角色消息写进目标会话的对话历史。

        导演发出的话必须落进历史，否则她下一轮根本不知道自己说过这句，
        会接不上茬甚至自相矛盾。
        """
        cm = getattr(self.context, "conversation_manager", None)
        if cm is None:
            return False
        try:
            cid = await cm.get_curr_conversation_id(umo)
            if not cid:
                logger.warning(
                    f"[tg_presence] 写历史失败：{umo} 还没有对话。"
                    "先在那个会话里正常聊一句，让 AstrBot 把对话建起来"
                )
                return False
            conv = await cm.get_conversation(umo, cid)
            if not conv:
                logger.warning(f"[tg_presence] 写历史失败：取不到对话 {cid}")
                return False
            history = json.loads(conv.history or "[]")
            if not isinstance(history, list):
                history = []
            body = text
            if self.conf.get("stamp_own_messages", True):
                body = f"{datetime.now(self._tz()).strftime(STAMP_FMT)} {text}"
            before = len(history)
            history.append({"role": "assistant", "content": body})
            await cm.update_conversation(umo, cid, history=history)
            logger.info(
                f"[tg_presence] 已写入对话历史 cid={cid} {before} -> {len(history)} 条"
            )
            return True
        except Exception as e:
            logger.error(f"[tg_presence] 写历史失败: {e}")
            return False

    async def _director_deliver(self, text: str) -> str:
        """以角色的身份把一段话发到目标会话，并记进她的历史。"""
        from astrbot.core.message.message_event_result import MessageChain

        target = (self.state.get("director_target") or "").strip()
        text = (text or "").strip()
        if not text:
            return "内容是空的，没发。"

        try:
            found = await self.context.send_message(
                target, MessageChain().message(text)
            )
        except Exception as e:
            logger.error(f"[tg_presence] 导演发送失败: {e}")
            return f"没发出去：{e}"
        if not found:
            return f"找不到目标平台 {target.split(':', 1)[0]}，那个 bot 还连着吗？"

        wrote = await self._append_assistant(target, text)
        head = f"已发到 {self._umo_platform(target)}：\n{text}"
        if wrote:
            return head
        return (
            head
            + "\n\n⚠️ 但没能写进对话历史，她之后不记得说过这句。"
            + "\n日志里搜「写历史失败」看原因。"
        )

    async def _director_generate(self, brief: str) -> str:
        """按导演提示，用角色的人格和历史生成一条主动消息。抛异常给调用方。"""
        target = (self.state.get("director_target") or "").strip()
        cm = self.context.conversation_manager
        cid = await cm.get_curr_conversation_id(target)
        conv = await cm.get_conversation(target, cid) if cid else None

        history = []
        if conv:
            try:
                history = json.loads(conv.history or "[]")
            except json.JSONDecodeError:
                history = []
        limit = max(2, int(self.conf.get("director_context_turns", 40) or 40))

        system_prompt = ""
        pm = getattr(self.context, "persona_manager", None)
        if pm is not None:
            try:
                p = None
                if conv and conv.persona_id:
                    p = pm.get_persona_v3_by_id(conv.persona_id)
                if p is None:
                    p = await pm.get_default_persona_v3(umo=target)
                system_prompt = getattr(p, "system_prompt", "") or ""
            except Exception as e:
                logger.warning(f"[tg_presence] 取人格失败，这次不带人格生成: {e}")
        if not system_prompt:
            logger.warning("[tg_presence] 没拿到人格，生成的话可能不像她")

        provider_id = await self.context.get_current_chat_provider_id(target)
        resp = await self.context.llm_generate(
            chat_provider_id=provider_id,
            system_prompt=system_prompt,
            contexts=history[-limit:] if isinstance(history, list) else [],
            prompt=(
                "【以下是导演提示，只有你能看到，对方完全不知道这段存在】\n"
                f"{brief}\n\n"
                "现在由你主动给他发一条消息。直接写你要发的原话，"
                "用你平时的语气和分段习惯。不要复述或引用这段提示，"
                "不要写旁白、解释、心理描写，也不要加引号。"
            ),
        )
        return (getattr(resp, "completion_text", "") or "").strip()

    @filter.command("whoami")
    async def cmd_whoami(self, event: AstrMessageEvent):
        """诊断：这个会话里你是谁、插件读到的管理员名单认不认你。不需要管理员权限。"""
        self._seal_command(event)
        sid = str(event.get_sender_id())
        umo = event.unified_msg_origin
        lines = [
            f"你的 ID：{sid}",
            f"当前身份：{event.role or '（普通用户）'}",
            f"机器人名称：{self._umo_platform(umo)}",
            f"会话 UMO：{umo}",
        ]

        # 这个会话实际路由到哪份配置文件 —— WebUI 打开的默认是 default，
        # 多配置文件时最容易改错地方，所以直接把文件名报出来
        conf_name, conf_path = "", ""
        try:
            info = self.context.astrbot_config_mgr.get_conf_info(umo)
            conf_name, conf_path = info.get("name", ""), info.get("path", "")
        except Exception as e:
            logger.debug(f"[tg_presence] 取配置文件信息失败: {e}")

        try:
            admins = self.context.get_config(umo=umo).get("admins_id", []) or []
        except Exception as e:
            lines.append(f"\n读配置失败：{e}")
            yield event.plain_result("\n".join(lines))
            return

        if conf_name:
            lines.append(f"\n这个会话用的配置文件：{conf_name}")
            if conf_path:
                lines.append(f"  文件：{conf_path}")
        lines.append(f"里面的 admins_id 共 {len(admins)} 项")

        # 逐字复刻 WakingCheckStage 的判定：str(sender_id) == admin_id
        exact = [a for a in admins if sid == a]
        loose = [a for a in admins if str(a).strip() == sid]

        if exact:
            lines.append("✅ 精确匹配成功，你在这份名单里")
            if event.role != "admin":
                lines.append(
                    "但身份仍不是 admin —— 名单是对的，问题在别处，把这段发出来我看。"
                )
        elif loose:
            bad = loose[0]
            lines.append(
                f"⚠️ 名单里有你的 ID，但存成了 {type(bad).__name__} 类型：{bad!r}\n"
                'AstrBot 比的是字符串，必须是带引号的 "' + sid + '"，'
                "不能是纯数字、也不能带空格。"
            )
        else:
            lines.append(
                f"❌ 你的 ID 不在这份名单里。\n"
                f"要改的是上面那份「{conf_name or '当前'}」，"
                "不是 WebUI 打开时默认显示的那份——多配置文件时这俩经常不是同一个。"
            )
        yield event.plain_result("\n".join(lines))

    async def _peek_conversation(self, umo: str) -> tuple[bool, int]:
        """看一眼目标会话有没有对话、有多少条。用来当场识破 UMO 填错。"""
        try:
            cm = self.context.conversation_manager
            cid = await cm.get_curr_conversation_id(umo)
            if not cid:
                return False, 0
            conv = await cm.get_conversation(umo, cid)
            if not conv:
                return False, 0
            history = json.loads(conv.history or "[]")
            return True, len(history) if isinstance(history, list) else 0
        except Exception as e:
            logger.debug(f"[tg_presence] 探查会话失败 {umo}: {e}")
            return False, 0

    @filter.command("link")
    async def cmd_link(self, event: AstrMessageEvent, target: str = ""):
        """在控制台里绑定投递目标。用法：/link 目标UMO，或 /link show 查看当前绑定。"""
        self._seal_command(event)
        if self.conf.get("admin_only_commands", True) and event.role != "admin":
            yield event.plain_result("只有管理员能用这个指令。发 /whoami 看是哪儿没对上。")
            return

        here = self._platform_of(event)
        did = self._director_id()
        cur = (self.state.get("director_target") or "").strip()
        arg = (target or "").strip()

        if not arg or arg.lower() in ("show", "status"):
            lines = [
                f"投递目标：{cur or '（未绑定）'}",
                f"控制台：  {did or '（未配置）'}",
                f"这个会话：{event.unified_msg_origin}",
            ]
            if cur:
                ok, n = await self._peek_conversation(cur)
                lines.append(
                    f"目标会话：{'有对话，历史 ' + str(n) + ' 条' if ok else '⚠️ 查不到对话'}"
                )
            lines += [
                "",
                # 别用尖括号占位：Telegram 按 HTML 解析，<UMO> 会被当成标签整段吃掉
                "绑定：/link 目标UMO",
                "  例：/link AstrLover:FriendMessage:8338355157",
                "  UMO = 机器人名称:消息类型:会话ID",
                "  私聊是 FriendMessage，群聊是 GroupMessage",
            ]
            yield event.plain_result("\n".join(lines))
            return

        # 绑定只在控制台做 —— 在角色那边发指令会在你俩的聊天记录里留痕，
        # 那正是导演模式要避免的事
        if not did:
            yield event.plain_result(
                "先在插件配置里填「控制台机器人名称」，再来绑定。"
            )
            return
        if here != did:
            yield event.plain_result(
                "这条指令只能在控制台那个 bot 里发。\n"
                "在角色那边发会在你俩的聊天记录里留下一条与剧情无关的消息。"
            )
            return

        try:
            from astrbot.core.platform.astr_message_event import MessageSesion

            MessageSesion.from_str(arg)  # 只做格式校验
        except Exception:
            yield event.plain_result(
                f"UMO 格式不对：{arg}\n\n"
                "应该是三段，冒号分隔：\n"
                "  机器人名称:消息类型:会话ID\n"
                "  例：AstrLover:FriendMessage:8338355157\n"
                "私聊填 FriendMessage，群聊填 GroupMessage。"
            )
            return

        if self._umo_platform(arg) == did:
            yield event.plain_result(
                f"这是控制台自己（{did}），绑它没意义。\n"
                "第一段要填角色那个 bot 的机器人名称。"
            )
            return

        ok, n = await self._peek_conversation(arg)
        self.state["director_target"] = arg
        self._save_state()

        msg = [f"已绑定：{arg}"]
        if ok:
            msg.append(f"目标会话有对话，当前历史 {n} 条 ✅")
        else:
            msg.append(
                "⚠️ 但查不到这个会话的对话记录。\n"
                "要么 UMO 填错了，要么那个会话还没聊过——"
                "没有对话的话，/say 发得出去但写不进历史。"
            )
        msg += [
            "",
            "接下来：",
            "  /say 你要她说的原话",
            "  /act 给她的方向，她自己组织语言",
        ]
        yield event.plain_result("\n".join(msg))

    @filter.command("say")
    async def cmd_say(self, event: AstrMessageEvent, *, text: str = ""):
        """在控制台里用：让角色原样说一句话。用法：/say 内容"""
        self._seal_command(event)
        if self.conf.get("admin_only_commands", True) and event.role != "admin":
            yield event.plain_result("只有管理员能用这个指令。发 /whoami 看是哪儿没对上。")
            return
        if err := self._director_guard(event):
            yield event.plain_result(err)
            return
        yield event.plain_result(await self._director_deliver(text))

    @filter.command("act")
    async def cmd_act(self, event: AstrMessageEvent, *, brief: str = ""):
        """在控制台里用：给个方向，让角色自己组织语言发出去。用法：/act 跟他说你今天加班到很晚"""
        self._seal_command(event)
        if self.conf.get("admin_only_commands", True) and event.role != "admin":
            yield event.plain_result("只有管理员能用这个指令。发 /whoami 看是哪儿没对上。")
            return
        if err := self._director_guard(event):
            yield event.plain_result(err)
            return
        brief = (brief or "").strip()
        if not brief:
            yield event.plain_result("给个方向，比如：/act 跟他说你今天加班到很晚，有点累")
            return

        yield event.plain_result("让她想想…")
        try:
            text = await self._director_generate(brief)
        except Exception as e:
            logger.error(f"[tg_presence] 导演生成失败: {e}")
            yield event.plain_result(f"生成失败：{e}")
            return
        if not text:
            yield event.plain_result("她没说出话来（模型返回空），换个提示试试。")
            return
        yield event.plain_result(await self._director_deliver(text))

    @filter.command("gallery")
    async def cmd_gallery(
        self, event: AstrMessageEvent, action: str = "", *, rest: str = ""
    ):
        """管理相册索引。用法：/gallery [scan|index N|search 词|audit|redo|retry]"""
        self._seal_command(event)
        if self.conf.get("admin_only_commands", True) and event.role != "admin":
            yield event.plain_result("只有管理员能用这个指令。发 /whoami 看是哪儿没对上。")
            return

        action = (action or "").strip().lower()
        stat = self.gallery_stat()

        if not action:
            root = self._gallery_root()
            lines = [
                f"相册目录：{root or '（未配置或路径无效）'}",
                f"已登记：{stat['total']} 张 · {stat['folders']} 个分类",
                f"已索引：{stat['indexed']} 张 · 待索引：{stat['pending']} 张",
            ]
            if stat["stuck"]:
                lines.append(f"失败跳过：{stat['stuck']} 张（/gallery retry 重来）")
            if stat["sent"]:
                lines.append(f"累计发出：{stat['sent']} 次")
            if not stat["total"]:
                lines.append("\n先 /gallery scan 扫一遍目录。")
            elif stat["pending"]:
                lines.append("\n用 /gallery index 50 开始建索引，可以分多次跑。")
            yield event.plain_result("\n".join(lines))
            return

        if action == "scan":
            if not self._gallery_root():
                yield event.plain_result("没配相册目录，或路径不存在。填「相册目录」那一项。")
                return
            yield event.plain_result("开始扫描，上万张图可能要几十秒…")
            added, total = await asyncio.to_thread(self.gallery_scan)
            yield event.plain_result(
                f"扫完了。新增 {added} 张，库里共 {total} 张。\n"
                + ("接着 /gallery index 50 建索引。" if added else "没有新文件。")
            )
            return

        if action == "retry":
            self.db().execute("UPDATE photos SET fails = 0 WHERE descr IS NULL")
            self.db().commit()
            yield event.plain_result("失败计数已清零，/gallery index 可以重跑那些图了。")
            return

        if action == "audit":
            db = self.db()
            rows = db.execute(
                "SELECT COALESCE(tag_state,'未校验') s, COUNT(*) c FROM photos "
                "WHERE descr IS NOT NULL GROUP BY s ORDER BY c DESC"
            ).fetchall()
            if not rows:
                yield event.plain_result("还没有已索引的图。")
                return
            total = sum(r["c"] for r in rows)
            lines = [f"已索引 {total} 张，标签质量："]
            for r in rows:
                lines.append(f"  {r['s']:6} {r['c']:>5} 张 ({r['c']*100//total}%)")

            bad = db.execute(
                "SELECT id, tag_state, tag_issues FROM photos "
                "WHERE tag_state IS NOT NULL AND tag_state <> 'ok' "
                "ORDER BY id LIMIT 5"
            ).fetchall()
            if bad:
                lines.append("\n举例：")
                for r in bad:
                    lines.append(f"  g{r['id']} [{r['tag_state']}] {(r['tag_issues'] or '')[:70]}")
            miss = db.execute(
                "SELECT COUNT(*) c FROM photos WHERE tag_state IN ('缺失','段数不齐')"
            ).fetchone()["c"]
            if miss:
                lines.append(
                    f"\n{miss} 张标签缺失或不齐，/gallery redo 可以把它们排队重跑。"
                )
            lines.append("\n注：非法值不影响关键词检索（描述全文照样能搜到），")
            lines.append("只有要按项精确筛选时才需要在意。")
            yield event.plain_result("\n".join(lines))
            return

        if action == "redo":
            db = self.db()
            n = db.execute(
                "UPDATE photos SET descr = NULL, fails = 0 "
                "WHERE tag_state IN ('缺失','段数不齐')"
            ).rowcount
            db.commit()
            yield event.plain_result(
                f"已把 {n} 张标签有结构问题的图退回待索引，/gallery index 重跑。"
                if n
                else "没有需要重跑的图。"
            )
            return

        if action == "search":
            rows = self.gallery_search(rest, limit=10)
            if not rows:
                yield event.plain_result("没找到。")
                return
            yield event.plain_result(
                "\n".join(
                    f"g{r['id']} · [{r['folder'] or '根目录'}] {(r['descr'] or '')[:60]}"
                    for r in rows
                )
            )
            return

        if action == "index":
            if not self._vision_ready():
                yield event.plain_result("视觉 API 没配全，/vision 看缺哪项。")
                return
            batch = max(1, min(int(rest.strip()), 200)) if rest.strip().isdigit() else 20
            rows = self.db().execute(
                "SELECT id, path FROM photos WHERE descr IS NULL AND fails < ? "
                "ORDER BY id LIMIT ?",
                (VISION_MAX_FAILS, batch),
            ).fetchall()
            if not rows:
                yield event.plain_result(
                    f"没有待索引的图。已索引 {stat['indexed']} 张。"
                    + (f"\n有 {stat['stuck']} 张失败跳过，/gallery retry 重来。" if stat["stuck"] else "")
                )
                return

            yield event.plain_result(
                f"开始索引 {len(rows)} 张（待索引共 {stat['pending']} 张），"
                f"并发 {self.conf.get('vision_concurrency', 2)}，跑完再报。"
            )
            jobs = []
            for r in rows:
                p = self._photo_file(r)
                if p:
                    jobs.append(self._gallery_describe(r["id"], str(p)))
                else:
                    self.db().execute(
                        "UPDATE photos SET fails = ? WHERE id = ?",
                        (VISION_MAX_FAILS, r["id"]),
                    )
            self.db().commit()

            results = await asyncio.gather(*jobs, return_exceptions=True)
            ok = sum(1 for x in results if x is True)
            after = self.gallery_stat()
            yield event.plain_result(
                f"完成 {ok}/{len(rows)} 张。已索引 {after['indexed']} / {after['total']}，"
                f"还剩 {after['pending']} 张。"
                + ("\n再发一次 /gallery index 继续。" if after["pending"] else "\n全部索引完毕。")
            )
            return

        yield event.plain_result(
            "用法：/gallery [scan|index N|search 词|audit|redo|retry]\n"
            "  audit 看标签质量分布，redo 把结构坏的排队重跑"
        )

    @filter.command("vision")
    async def cmd_vision(self, event: AstrMessageEvent, arg: str = ""):
        """给还没有细节记录的存量图片补做视觉解析。用法：/vision [张数|retry|test]"""
        self._seal_command(event)
        if self.conf.get("admin_only_commands", True) and event.role != "admin":
            yield event.plain_result("只有管理员能用这个指令。发 /whoami 看是哪儿没对上。")
            return

        cfg = self._vision_conf()
        if not cfg:
            missing = [
                label
                for key, label in (
                    ("vision_base_url", "接口地址"),
                    ("vision_api_key", "API Key"),
                    ("vision_model", "模型 ID"),
                )
                if not (self.conf.get(key) or "").strip()
            ]
            yield event.plain_result(
                f"视觉 API 还没配全，缺：{'、'.join(missing)}。\n"
                "在插件配置的「独立视觉 API」几项里填。"
            )
            return

        arg = arg.strip().lower()
        paths_all = self.state.get("photo_paths") or {}

        if arg == "test":
            # 拿一张真图跑一次完整请求。配置错了这里能立刻看出是哪一步错
            sample = next(
                (p for p in reversed(list(paths_all.values())) if Path(p).exists()),
                None,
            )
            if not sample:
                yield event.plain_result(
                    "还没存过任何图片，没法测。先在聊天里发一张图再来。"
                )
                return
            yield event.plain_result(
                f"格式 {cfg['fmt']} · 模型 {cfg['model']} · "
                f"{'流式' if cfg['stream'] else '非流式'}\n{self._vision_url(cfg)}"
            )
            probe = "__test__"
            self.vision.pop(probe, None)
            ok = await self._vision_describe(probe, sample)
            if ok:
                got = self.vision.pop(probe, "")
                self._save_vision()
                yield event.plain_result(f"通了。返回 {len(got)} 字：\n{got[:300]}")
            else:
                (self.state.get("vision_fail") or {}).pop(probe, None)
                self._save_state()
                yield event.plain_result(
                    "没通。日志里搜 `视觉解析 #__test__ 失败` 看具体原因：\n"
                    "401/403 是 Key 错或格式选错（三家鉴权头不一样），\n"
                    "404 多半是接口地址或模型 ID 错，400 看返回的报错正文。"
                )
            return

        if arg == "retry":
            self.state["vision_fail"] = {}
            self._save_state()
        batch = max(1, min(int(arg), 50)) if arg.isdigit() else 10

        paths = self.state.get("photo_paths") or {}
        fails = self.state.get("vision_fail") or {}
        pending = [
            pid
            for pid, p in paths.items()
            if pid not in self.vision
            and fails.get(pid, 0) < VISION_MAX_FAILS
            and Path(p).exists()
        ]
        if not pending:
            stuck = sum(1 for pid in paths if fails.get(pid, 0) >= VISION_MAX_FAILS)
            msg = f"没有待解析的图片。已有细节记录 {len(self.vision)} 条。"
            if stuck:
                msg += f"\n另有 {stuck} 张失败满 {VISION_MAX_FAILS} 次被跳过，/vision retry 可重来。"
            yield event.plain_result(msg)
            return

        # 新图优先——越近的越可能被提起
        pending.sort(key=lambda p: int(p) if p.isdigit() else 0, reverse=True)
        todo = pending[:batch]
        yield event.plain_result(f"待解析 {len(pending)} 张，这次做 {len(todo)} 张。")

        results = await asyncio.gather(
            *(self._vision_describe(pid, paths[pid]) for pid in todo),
            return_exceptions=True,
        )
        ok = sum(1 for r in results if r is True)
        left = len(pending) - ok
        yield event.plain_result(
            f"完成 {ok}/{len(todo)} 张。"
            + (f"\n还剩 {left} 张，再发一次 /vision 继续。" if left > 0 else "")
        )
