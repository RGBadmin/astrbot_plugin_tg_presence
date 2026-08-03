import asyncio
import base64
import binascii
import hashlib
import inspect
import json
import math
import mimetypes
import random
import re
import shutil
import sqlite3
import struct
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


def _build_vocab() -> frozenset:
    """拿标签候选值凑一份中文分词词典。

    中文不写空格。人说「红底细高跟」，而库里是「红底」和「细高跟」两个
    分开的词，整串 LIKE 必然落空——这类词组恰恰是检索里最常用的说法。
    标签候选值本来就是这个领域最常用词的集合，拿来当词典比引一个通用
    分词库更贴题，还不用多一个依赖。

    「无」「空」「无法判断」这些占位词要剔掉：它们在库里遍地都是，
    切出来只会让每张图都命中一次，纯噪声。
    """
    stop = {"无", "空", "有", "没有", "未知", "其它", "其他", "无法判断", "不可见"}
    vocab = set()

    def put(s: str) -> None:
        s = s.strip()
        if len(s) >= 2 and s not in stop:
            vocab.add(s)

    for _name, cand in FIELDS:
        for v in cand.split("|"):
            for one in v.replace("，", ",").split(","):
                put(one)
                # 「室内-酒店」这类复合值要把两截也收进来：
                # 人嘴上说的是「酒店」，不会说「室内-酒店」
                if "-" in one:
                    for part in one.split("-"):
                        put(part)
    for k in ALIAS:
        put(k)
    return frozenset(vocab)


TAG_VOCAB = _build_vocab()
# 词典切不动的部分退回二元组滑窗。噪声片段（「色情」「趣内」）匹配不上
# 就是不加分，不会误召回，只是把分数摊薄一点
GRAM_MIN_LEN = 4

AVATAR_EXTS = {".jpg", ".jpeg"}  # Telegram 头像接口只收 JPEG
PHOTO_EXTS = {".jpg", ".jpeg", ".png", ".webp", ".gif"}
# 博主目录里会躺一个这个后缀的文件，用来标出"这一级的目录名就是博主名"
ARCHIVE_EXT = ".archive"
MEDIA_GROUP_MAX = 10  # Telegram 一组媒体最多 10 张
CAPTION_MAX = 1024  # 图片 caption 上限；纯文字消息上限是 4096
SIGNATURE_MAX = 120  # setMyShortDescription 的上限

# 角色自己消息的时间戳格式，形如 [08-01 14:30]
STAMP_FMT = "[%m-%d %H:%M]"
STAMP_RE = re.compile(r"^\[\d{2}-\d{2} \d{2}:\d{2}\]")
# 她会照着上下文里的戳自己也写一个——历史里每条自己的消息都以它开头，
# 这就是一份天然的 few-shot 示范。而且她写的时间是猜的，跟真实时钟对不上。
# 发出去之前按行首剥掉：打戳是插件的事，轮不到她自己动手
OWN_STAMP_RE = re.compile(r"^[ \t]*\[\d{2}-\d{2} \d{2}:\d{2}\][ \t]*", re.M)

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

# 视觉解析连续失败这么多次就不再自动重试，避免坏图无限撞 API。
# 只有「这张图自己的问题」才累加——上游故障不算，见 _gallery_describe
VISION_MAX_FAILS = 3
VISION_TIMEOUT = 120  # 秒。图片请求比纯文本慢，给宽裕些
VISION_FORMATS = ("openai", "anthropic", "gemini")

# 上游临时故障，等一会儿重试有意义：限流、网关抽风、后端没起来。
# 中转商的 auth 池空了也走 503，跟真限流一样属于「等等再来」
RETRY_STATUS = frozenset({408, 409, 425, 429, 500, 502, 503, 504, 509, 520, 521, 522, 524, 529})
# 请求本身就不对，重试一万次还是错：key 错、模型名错、图太大、请求体非法。
# 这类必须立刻中止整批，否则跑一整夜醒来发现一张没成
FATAL_STATUS = frozenset({400, 401, 403, 404, 405, 413, 414, 422})

TRIP_STREAK = 8              # 连续失败这么多次就熔断，全局歇一轮

# Gemini 不传这个的话，成人向图片会被安全策略拦掉——而且是 HTTP 200 空回，
# 从状态码完全看不出来。flash 尤其严，几乎全军覆没
GEMINI_HARM_CATEGORIES = (
    "HARM_CATEGORY_HARASSMENT",
    "HARM_CATEGORY_HATE_SPEECH",
    "HARM_CATEGORY_SEXUALLY_EXPLICIT",
    "HARM_CATEGORY_DANGEROUS_CONTENT",
)

# 模型嘴上拒绝时照样是 HTTP 200 + 有正文，不检测就会把「我无法满足这个请求」
# 当描述存进库，还跟着转成向量，把检索一起带歪。比直接失败难查得多
REFUSAL_MARKS = (
    "我无法", "我不能", "无法满足", "无法提供", "无法生成", "无法描述",
    "不能生成", "不能提供", "不能处理", "不便描述", "很抱歉", "抱歉，",
    "我被设定", "作为一个ai", "作为 ai", "违反", "不适当", "不合适的请求",
    "i can't", "i cannot", "i won't", "i'm unable", "i am unable",
    "i'm sorry", "i am sorry", "as an ai", "unable to comply",
    "can't assist", "cannot assist", "against my",
)
# 拒答都很短。长描述里偶然出现上面某个词也不该被误判，所以拿长度兜底
REFUSAL_MAX_CHARS = 400

# 结束标记允许的形近字符。要求模型输出十个「·」，但它未必挑得准同一个码位，
# ・•‧∙⋅ 这几个看着一样的都放行。不含英文句点——那个在正文里出现得太自然
END_MARK_CHARS = "·・•‧∙⋅"

# 思维链漏进正文的特征。Gemini 爱写 **Defining the Structure** 这种英文小标题，
# 提示词是中文时正常描述绝不会长这样
THINKING_MARKS = (
    "i'm now", "i am now", "i've ", "i'll ", "i need to", "let me ",
    "my primary task", "first, i", "i'm focusing", "i'm analyzing",
    "i'm grappling", "i'm considering", "i have re-assessed",
)

# 一轮最多请求几条图片描述。要多了模型容易敷衍，或写到一半被 max_tokens 截断
NOTES_PER_TURN = 5

GALLERY_SCHEMA = """
CREATE TABLE IF NOT EXISTS photos (
    id      INTEGER PRIMARY KEY AUTOINCREMENT,  -- 就是 gN 里的那个 N
    path    TEXT    NOT NULL UNIQUE,   -- 相对图库根目录；来源非图库时存绝对路径
    folder  TEXT    NOT NULL DEFAULT '',        -- 顶层子目录名，一个博主一个
    source  TEXT    NOT NULL DEFAULT 'gallery', -- gallery / moment，标明打哪来的
    descr   TEXT,                      -- 视觉 API 的描述；NULL = 还没索引
    fails   INTEGER NOT NULL DEFAULT 0,-- 索引失败次数，满 3 次不再自动重试
    sent    INTEGER NOT NULL DEFAULT 0,-- 发出去过几次，重排时用来避开老发的那几张
    last_sent REAL,                    -- 上次发出的时刻，「最近发过的那张」靠它
    added   REAL    NOT NULL,          -- 扫进库的时间，file_time 缺失时顶上
    file_time REAL,                    -- 这张图自己的时间：推特文件名解出的发推
                                       -- 时刻，解不出才用文件 mtime
    vec       BLOB,                    -- 全文向量，float32 且已归一化
    vec_env   BLOB,                    -- 环境段（第一层 + 第五层）
    vec_body  BLOB,                    -- 身体段（第二层 + 第三层）
    vec_act   BLOB,                    -- 动作段（第四层 + 第六层 + 关键词行）
    tag_state  TEXT,                   -- ok / 无标签 / 段数不齐 / 有问题
    tag_issues TEXT                    -- 上面那个的具体说明，给 /gallery audit 看
);
CREATE INDEX IF NOT EXISTS idx_folder  ON photos(folder);
CREATE INDEX IF NOT EXISTS idx_pending ON photos(fails) WHERE descr IS NULL;
CREATE INDEX IF NOT EXISTS idx_sent    ON photos(last_sent);
"""
ANTHROPIC_VERSION = "2023-06-01"

# 导演链路的提示词。全部可以在配置里覆盖，这儿是留空时的默认值。
# 「不要调用任何工具」那句是必须的：她手上有 update_signature、send_photo
# 这些工具，一看到「改签名」「发照片」就会去调，而这条路没给她工具，
# tool_call 无处可去，回来就是一片空白
DEFAULT_DIRECTOR_HEAD = "【以下是导演提示，只有你能看到，对方完全不知道这段存在】"
DEFAULT_DIRECTOR_ACT = (
    "现在由你主动给他发一条消息。直接写你要发的原话，用你平时的语气和分段习惯。"
)
DEFAULT_DIRECTOR_TAIL = (
    "这一轮你只负责把内容想出来、用纯文本写下来。"
    "不要调用任何工具，不要执行任何操作——写完自然有人去落实。\n"
    "不要复述或引用这段提示，不要写旁白、解释、心理描写，也不要加引号。"
    "不要在开头写 [月-日 时:分] 这样的时间戳——"
    "你在历史里看到的那些是系统加的，不是你写的。"
)
DEFAULT_DIRECTOR_RETRY = (
    "注意：这一轮禁止调用工具、禁止执行任何操作。"
    "你要做的只有一件事——把内容用纯文本写出来，写完就停。"
    "哪怕你觉得应该去执行，也先写出来给我看。"
)
DEFAULT_IMP_SIGNATURE = (
    "你在想换一句新的个性签名。签名是别人点开你资料时看到的那一行，"
    "所有人都看得见。现在只是想，还没到动手改的时候。\n\n"
    "把你想好的那句签名写出来就行，一行，不超过 {max} 个字，只写签名本身。"
)
DEFAULT_IMP_MOMENT = (
    "你在想往自己的频道发一条动态。那是发给所有人看的，不是私聊。"
    "可以是此刻的心情、刚做完的事、看到的东西，也可以没有由头。"
    "现在只是想内容，还没到发出去的时候。\n\n"
    "把动态正文写出来就行，一两句话，符合你平时发动态的语气。"
)
DEFAULT_IMP_AVATAR = (
    "你在想换个头像，正在挑用哪一类的照片。可选的有：{cats}。"
    "现在只是挑，还没到换的时候。\n\n"
    "回一个类别名就行，从上面那些里选，不要解释，不要加标点。"
)
DEFAULT_IMP_PHOTO = (
    "你在想给他发一张自己的照片，正在回忆要挑什么样的——"
    "什么场景、穿什么、什么姿态、露到什么程度。"
    "现在只是想，还没到发的时候，也不用去翻相册。\n\n"
    "第一行写这张照片的关键词，几个短语用逗号隔开，"
    "例如：酒店,黑丝,细高跟,M腿。\n"
    "第二行写你想配的一句话，不想配就留空。\n"
    "只输出这两行。"
)

# 分段向量。整段描述只转一个向量的话，三千多字里九成是身体细节，
# 环境那两百字会被彻底稀释——「黑色反光桌面，大片水渍」这种信息在
# 全文向量里几乎看不见，搜「桌上喷水」全凭运气。按层切开各转一个，
# 检索时取最大相似度，环境词就能直接撞上环境段。
# 值是这一段取哪几层；None 表示整篇。第六层往后会连标签行一起带上，
# 那正好——标签是特征清单，跟动作状态放一起不违和。
VEC_SEGS: dict[str, tuple[int, ...] | None] = {
    "vec": None,           # 全文，也是向后兼容的那一路
    "vec_env": (1, 5),     # 环境与背景 + 物品道具
    "vec_body": (2, 3),    # 人物整体 + 身体细节
    "vec_act": (4, 6),     # 互动动作 + 体液痕迹 + 标签行
}
# 必须锚在行首。正文里「背景中的杂物见第一层」这种交叉引用很常见，
# 不锚定的话它会被当成层标题，把真正的第一层内容整段吃掉
LAYER_RE = re.compile(r"^[\s*·・-]*第\s*([一二三四五六])\s*层[^\n]*", re.M)
LAYER_NUM = {"一": 1, "二": 2, "三": 3, "四": 4, "五": 5, "六": 6}

# 推特下载的媒体文件名就是推文 ID，同一条推文的多张图带 -1 -2 -3 后缀。
# 这个 ID 是 snowflake：高 42 位是毫秒时间戳，能还原出发推时刻。
# 比文件 mtime 可靠得多——mtime 是下载时间，网页上传一次全变成同一天
# 至少 17 位：snowflake 从 2010-11 启用时就已经是 17 位了，
# 位数放宽到 15 的话，随便一串 15 位数字都会被解析成 2010 年的推文
TWEET_ID_RE = re.compile(r"^(\d{17,20})(?:[-_ ]\d{1,2})?$")
TWITTER_EPOCH_MS = 1288834974657  # 2010-11-04，snowflake 的起点

# 插件自带控制台支持的指令 -> handler 名。
# 只收不需要平台 client 的那些：/photo /moment /avatar /signature 得借
# 角色那个 bot 的身份去调 Telegram（发图、改头像、改签名），控制台拿不到
# 它的 client，那四条继续在角色的会话里发
CONSOLE_ROUTES = {
    "gallery": "cmd_gallery",
    "vision": "cmd_vision",
    "presence": "cmd_presence",
    "proactive": "cmd_proactive",
    "umo": "cmd_umo",
    "link": "cmd_link",
    "say": "cmd_say",
    "act": "cmd_act",
    "photo": "cmd_photo",
    "moment": "cmd_moment",
    "avatar": "cmd_avatar",
    "signature": "cmd_signature",
    "whoami": "cmd_whoami",
}
# 这几条得以角色的身份去调 Telegram（发图、发频道、换头像、改签名），
# 在控制台执行时要借用目标会话那个 bot 的 client
CONSOLE_AS_TARGET = {"photo", "moment", "avatar", "signature"}
# 注册到 Telegram 的指令菜单，输入 / 就能看见。顺序即菜单顺序，
# 按「先绑谁、再让她说什么、最后管相册」排
CONSOLE_MENU = [
    ("umo", "列出所有会话，挑一个绑"),
    ("link", "绑定目标会话 · /link UMO"),
    ("say", "让她原样说一句 · /say 内容"),
    ("act", "给个方向，她自己组织语言 · /act 方向"),
    ("photo", "以她的身份发张照片 · /photo g123 [附言]"),
    ("proactive", "主动消息状态 · /proactive now 立即发"),
    ("moment", "让她发条动态到频道 · /moment [内容]"),
    ("avatar", "给她换个头像 · /avatar [分类]"),
    ("signature", "改她的签名 · /signature 内容"),
    ("gallery", "相册 · index auto / search 词 / show / embed"),
    ("vision", "视觉 API 配置诊断"),
    ("presence", "插件状态：动态、冷却、图片存档"),
    ("whoami", "这个会话里你是谁"),
]
# 九宫格的逐格描述。挑图时它们没有判别力——十张图开头都是「左上：白色墙面」
GRID_RE = re.compile(r"^(左上|中上|右上|左中|正中|右中|左下|中下|右下)\s*[：:]")
# 描述一变，所有分段向量都得作废，不能只清主向量
VEC_NULLS = ", ".join(f"{c} = NULL" for c in VEC_SEGS)


class ConsoleEvent:
    """给插件自带控制台用的假 event。

    handler 都是按 AstrMessageEvent 写的，为了不把十几个 handler 改成
    双入口，这里补一个最小实现：接住 plain_result、报出发送者身份。
    role 直接给 admin —— 能走到这儿说明已经过了白名单，控制台本来就是
    你一个人的。

    发照片、换头像这类要以角色身份调 Telegram 的指令，构造时把目标会话
    的 umo 和它那个 bot 的 client 传进来，_client() 和 _chat_id() 就都
    对得上了——它们看的正是这两样。
    """

    def __init__(self, uid: str, chat_id, umo: str = "", client=None):
        self._console_umo = f"console:FriendMessage:{chat_id}"
        self.unified_msg_origin = umo or self._console_umo
        self.client = client
        self.role = "admin"
        self.replies: list[str] = []
        self._uid = str(uid)
        self._as_target = bool(umo)

    def plain_result(self, text: str) -> str:
        if text:
            self.replies.append(text)
        return text

    def get_sender_id(self) -> str:
        return self._uid

    def get_platform_name(self) -> str:
        # 借角色身份执行时要报 telegram，否则 _client() 直接返回 None
        return "telegram" if self._as_target else "console"

    def should_call_llm(self, _flag: bool) -> None:
        """控制台不经过 AstrBot 管线，没有"要不要丢给 LLM"这回事。"""

    def get_result(self):
        return None


class VisionError(Exception):
    """视觉解析失败，消息直接进失败日志。

    分三类，决定了失败之后怎么办：
    · retryable —— 上游的锅（限流、网关 503、超时、安全策略随机拒答）。
      退避重试；重试耗尽也**不算这张图的失败次数**，否则上游挂一夜
      就能把整个图库标记成「坏图」。
    · fatal —— 配置的锅（key 错、模型名错）。立刻中止整批并报错，
      不然会拿着错配置空跑一整夜。
    · 都不是 —— 这张图自己的问题（读不出来、格式不认）。计入 fails，
      满 VISION_MAX_FAILS 次后不再自动重试。
    """

    def __init__(self, msg: str, *, retryable: bool = False, fatal: bool = False):
        super().__init__(msg)
        self.retryable = retryable
        self.fatal = fatal


@register(
    "astrbot_plugin_tg_presence",
    "chine",
    "让角色自己发动态到频道、换头像、改签名、对消息点表情，并把图片记成可检索的两层文字",
    "0.21.0",
)
class TgPresence(Star):
    def __init__(self, context: Context, config: AstrBotConfig):
        super().__init__(context)
        self.conf = self._flatten_conf(config)
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
        # {列名: (ids, numpy矩阵)}，第一次语义检索时构建，写入新向量后清空重建
        self._vec_cache: dict[str, tuple[list[int], object]] = {}
        # 上游熔断：连续失败到阈值就全局停一会儿，冷却时长随连续熔断次数翻倍
        self._cool_until: float = 0.0
        self._fail_streak: int = 0
        self._trip_level: int = 0
        # /gallery index auto 的后台任务，一次只允许有一个
        self._index_task: asyncio.Task | None = None
        self._index_note: str = ""
        # 主动消息的倒计时循环。懒启动——__init__ 时还不一定有事件循环
        self._proactive_task: asyncio.Task | None = None
        # 插件自带控制台的长轮询
        self._console_task: asyncio.Task | None = None

    @staticmethod
    def _walk_conf(node, out: dict) -> dict:
        """深度优先把嵌套配置收进一层。插件没有 dict 类型的配置项，
        所以见到 dict 一律当分组递归。"""
        for k, v in node.items():
            if isinstance(v, dict):
                TgPresence._walk_conf(v, out)
            else:
                out.setdefault(k, v)
        return out

    @staticmethod
    def _schema_defaults() -> dict:
        """从 _conf_schema.json 读出每项的默认值，用来判断某项有没有被改过。"""
        out: dict = {}

        def walk(node: dict) -> None:
            for k, v in node.items():
                if not isinstance(v, dict):
                    continue
                if v.get("type") == "object" and isinstance(v.get("items"), dict):
                    walk(v["items"])
                elif "default" in v:
                    out[k] = v["default"]

        try:
            raw = (Path(__file__).parent / "_conf_schema.json").read_text(encoding="utf-8")
            walk(json.loads(raw))
        except (OSError, ValueError) as e:
            logger.warning(f"[tg_presence] 读不到配置模板，旧配置迁移跳过：{e}")
        return out

    @staticmethod
    def _flatten_conf(config) -> dict:
        """把分组后的配置压平成一层。

        _conf_schema.json 里配置项是按功能分组嵌套的，那纯粹是给配置页看的——
        六十多项平铺一列谁也找不着东西。但代码里一律按扁平 key 读：
        分组是排版，不该让上百处读取点跟着改名。

        麻烦在升级：旧版本的配置是扁平存的，AstrBot 会把那些键留在顶层，
        而新 schema 生成的分组内是默认值。不能简单地"非空者胜"——
        并发数默认就是 2，你调成 6 存在顶层，一样非空，谁赢全看遍历顺序。

        判据是 schema 里的 default：分组内还等于默认值，说明你没在新页面
        动过它，那就沿用旧值；分组内已经不是默认值了，说明你刚在新页面
        填过，那当然以新的为准。
        """
        flat = TgPresence._walk_conf(config, {})
        stale = {
            k: v
            for k, v in config.items()
            if not isinstance(v, dict) and k in flat and v != flat[k]
        }
        if not stale:
            return flat
        defaults = TgPresence._schema_defaults()
        kept = [
            k for k, v in stale.items() if k in defaults and flat[k] == defaults[k]
        ]
        for k in kept:
            flat[k] = stale[k]
        if kept:
            logger.info(
                f"[tg_presence] 沿用旧版配置 {len(kept)} 项："
                + "、".join(kept[:6])
                + ("…" if len(kept) > 6 else "")
                + "。在配置页保存一次即可清掉这些遗留键。"
            )
        return flat

    async def initialize(self):
        """AstrBot 装载插件后调用。控制台得在这儿起——它不该等到你
        先跟角色说一句话才上线。"""
        self._ensure_console()

    async def terminate(self):
        """插件卸载或热重载时收尾，别把数据库句柄漏掉。"""
        for task in (self._index_task, self._proactive_task, self._console_task):
            if task and not task.done():
                task.cancel()  # 后台任务跟着插件一起走
        self._index_task = self._proactive_task = self._console_task = None
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
            cols = [("tag_state", "TEXT"), ("tag_issues", "TEXT"), ("file_time", "REAL")]
            cols += [(c, "BLOB") for c in VEC_SEGS]
            for col, typ in cols:
                if col not in have:
                    self._db.execute(f"ALTER TABLE photos ADD COLUMN {col} {typ}")
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

    @staticmethod
    def _folder_of(rel: Path, marked: set[str]) -> str:
        """定这张图归哪个分类。

        博主目录里放着一个 .archive 文件，那一级的目录名就是博主名。
        从图片往上找，遇到的第一个带标记的目录就是它的归属——
        博主目录下再分子目录（按年份、按合集）也归得对。

        没有标记的地方退回「文件名之外的整段路径」：aiimages/ 这种
        一层结构直接得到 aiimages，而 twitter/某人/ 会得到
        twitter/某人，两级都还能被模糊匹配搜到，不至于丢信息。
        """
        cur = rel.parent
        while cur != Path("."):
            if cur.as_posix() in marked:
                return cur.name
            cur = cur.parent
        return rel.parent.as_posix() if rel.parent != Path(".") else ""

    def _time_from_name(self, path: Path) -> float | None:
        """从推特媒体文件名解出发推时间。解不出返回 None。

        推特下载的文件名就是推文 ID，同一条推文的多张图带 -1 -2 -3。
        这个 ID 是 snowflake：右移 22 位再加上 2010-11-04 那个起点，
        就是发推的毫秒时间戳。

        为什么不用文件的 mtime——网页上传不传时间戳，几千张图传完
        全变成上传那一刻，时间维度直接失效。而文件名里的这个时间是
        图片内容自带的，跟怎么传、传几次都没关系。

        范围校验挡住误判：一串正好十几位的数字未必是推文 ID，
        但它解出来的时间落在 2010 年之前或者未来，那就一定不是。
        """
        if not self.conf.get("scan_time_from_name", True):
            return None
        m = TWEET_ID_RE.match(path.stem.strip())
        if not m:
            return None
        ts = ((int(m.group(1)) >> 22) + TWITTER_EPOCH_MS) / 1000
        return ts if TWITTER_EPOCH_MS / 1000 < ts < time.time() + 86400 else None

    def gallery_scan(self) -> tuple[int, int]:
        """扫描图库目录，把新文件登记进库。返回 (新增, 总数)。

        只登记路径，不调视觉 API —— 那一步交给 /gallery index 慢慢跑。
        """
        root = self._gallery_root()
        if not root:
            return 0, 0

        # 这个方法通过 asyncio.to_thread 跑在工作线程里——扫几万个文件要几十秒，
        # 不能占着事件循环。但 SQLite 连接不许跨线程用，所以开一条本线程自己的，
        # 用完就关。建表由主线程的 self.db() 负责，这里只管读写。
        db = sqlite3.connect(self.db_path)
        db.row_factory = sqlite3.Row
        try:
            return self._scan_into(db, root)
        finally:
            db.close()

    def _scan_into(self, db: sqlite3.Connection, root: Path) -> tuple[int, int]:
        before = db.execute("SELECT COUNT(*) c FROM photos").fetchone()["c"]

        # UPSERT 而不是 INSERT OR IGNORE：已登记的行也要刷新 file_time，
        # 否则给老库补这一列时永远填不上
        # folder 也要跟着刷新：目录改过名、或者分类规则变了（比如从只取顶层
        # 改成存完整路径），重扫一次就能就地修正，不用清库重来
        SQL = (
            "INSERT INTO photos(path, folder, source, added, file_time) "
            "VALUES (?,?,?,?,?) "
            "ON CONFLICT(path) DO UPDATE SET "
            "file_time = excluded.file_time, folder = excluded.folder"
        )
        # 先过一遍找出博主目录：那里面躺着一个 .archive 文件。
        # 靠层级猜是不行的——图库可能是 twitter/博主名/ 两层，
        # 也可能是 aiimages/ 一层，博主目录下还可能再分子目录
        files = list(root.rglob("*"))
        marked = {
            p.parent.relative_to(root).as_posix()
            for p in files
            if p.suffix.lower() == ARCHIVE_EXT and p.is_file()
        }
        if marked:
            logger.info(f"[tg_presence] 扫到 {len(marked)} 个带 .archive 标记的目录")

        rows = []
        for p in files:
            if not p.is_file() or p.suffix.lower() not in PHOTO_EXTS:
                continue
            rel = p.relative_to(root)
            folder = self._folder_of(rel, marked)
            # 文件名能解出发推时间就用它，那是这张图真正的时间；
            # 解不出再退回 mtime
            when = self._time_from_name(p)
            if when is None:
                try:
                    when = p.stat().st_mtime
                except OSError:
                    when = None
            rows.append((rel.as_posix(), folder, "gallery", time.time(), when))
            if len(rows) >= 500:
                db.executemany(SQL, rows)
                db.commit()
                rows.clear()
        if rows:
            db.executemany(SQL, rows)
        db.commit()
        total = db.execute("SELECT COUNT(*) c FROM photos").fetchone()["c"]
        return total - before, total

    @staticmethod
    def _split_query(keywords: str, cap: int = 16) -> list[str]:
        """把检索词切成能真正匹配上的片段。

        先按空格和标点切，再对每个中文长词做一次词典正向最大匹配——
        人说「红色情趣内衣」，库里写的是「红色蕾丝连体情趣内衣」，
        整串匹配不到，切成「红色」「情趣内衣」就都中了。

        原词也保留并排在最前：它要是真能整串命中，那是最强的信号，
        不该因为拆开而丢掉。
        """
        raw = [
            w
            for w in re.split(r"[\s,，、;；/]+", (keywords or "").strip())
            if w
        ]
        out: list[str] = []
        for w in raw:
            cjk_long = len(w) >= 3 and re.search(r"[一-鿿]", w)
            pieces = TgPresence._seg(w) if cjk_long else []
            # 整串原词保留——真能命中的话那是最强信号。但十来个字的整句
            # 不可能逐字出现在描述里，留着只是白占一个 LIKE 位置
            if (len(w) <= 8 or not pieces) and w not in out:
                out.append(w)
            for piece in pieces:
                if piece not in out:
                    out.append(piece)
        return out[:cap]

    @staticmethod
    def _seg(word: str) -> list[str]:
        """正向最大匹配切词，词典啃不动的残段退回二元组滑窗。

        标签词典只覆盖 44 项候选值，而人搜的词一大半来自描述正文——
        「酒店」「百叶窗」「路灯」「枕头」这些一个都不在候选值里。
        所以残段不能丢，得按二元组补上，否则「酒店里穿灰丝」里的
        「酒店」就凭空消失了。

        词典词排在前面：它们更可靠，截断时该优先保住。二元组噪声
        （「店里」「里穿」）匹配不上就是不加分，不会误召回。
        """
        solid, fuzzy, buf, i, n = [], [], [], 0, len(word)

        def flush() -> None:
            s = "".join(buf)
            buf.clear()
            if len(s) >= 2:
                fuzzy.extend(s[k : k + 2] for k in range(len(s) - 1))

        while i < n:
            for j in range(min(n, i + 6), i + 1, -1):
                if word[i:j] in TAG_VOCAB:
                    flush()
                    solid.append(word[i:j])
                    i = j
                    break
            else:
                buf.append(word[i])
                i += 1
        flush()
        # 一个词典词都没切出来的短词，外面已经把整串加过了，不用再拆
        if not solid and n < GRAM_MIN_LEN:
            return []
        return solid + fuzzy

    def _df(self, words: list[str], folder: str = "") -> tuple[int, list[int]]:
        """一次全表扫描算出每个词的文档频率。返回 (总数, 各词的 df)。"""
        if not words:
            return 0, []
        sums = ", ".join(["SUM(descr LIKE ?)"] * len(words))
        sql = f"SELECT COUNT(*) n, {sums} FROM photos WHERE descr IS NOT NULL"
        args: list = [f"%{w}%" for w in words]
        if folder.strip():
            sql += " AND folder LIKE ?"
            args.append(f"%{folder.strip()}%")
        try:
            row = self.db().execute(sql, args).fetchone()
        except sqlite3.Error as e:
            logger.warning(f"[tg_presence] 词频统计失败：{e}")
            return 0, [0] * len(words)
        return (row[0] or 0), [(row[i + 1] or 0) for i in range(len(words))]

    def _rescue_dead(self, words: list[str], folder: str = "") -> list[str]:
        """一个都匹配不上的词，降级成单字再试。

        人说「车上」，库里写的是「汽车座椅」——两个字不连着出现，
        整词 df 为 0，IDF 给它再高的权重也是零贡献。拆成单字，
        「车」就能命中了。

        单字噪声大，三道闸拦着：

        · 只有整词 df 为 0 才拆，能整词命中的不动。
        · 已命中词的组成字一律不要。否则搜「红色情趣内衣」时，整串落空
          被拆成红/色/情/趣/内/衣，而「情趣」「内衣」本来就已经命中了——
          同一个语义被算五遍，分数虚高到满分，别的图全被压死。
        · 拆出来的字超过六成图都有就丢掉。真漏进来一两个也不致命：
          IDF 会把它压到最低权重，而且它命中所有图，对排序只是常数项。
        """
        total, dfs = self._df(words, folder)
        dead = [w for w, df in zip(words, dfs) if df == 0 and len(w) > 1]
        if not dead or not total:
            return words
        alive = [w for w, df in zip(words, dfs) if df > 0]
        chars = list(
            dict.fromkeys(
                c
                for w in dead
                for c in w
                if c.strip() and not any(c in a for a in alive)
            )
        )
        if not chars:
            return alive or words
        _, cdfs = self._df(chars, folder)
        good = [c for c, df in zip(chars, cdfs) if 0 < df <= total * 0.6]
        return (alive + good)[:20] or words

    def _idf(self, words: list[str], folder: str = "") -> tuple[list[float], float]:
        """给每个词算权重：库里越常见的词越不值钱。

        只数命中几个词是不行的。一个博主的图张张都是「黑丝」「细高跟」，
        搜「黑丝车上细高跟」时每张都命中这两个，词面分全都一样，排序
        等于没排。真正能区分的是「车」——只有三张有，命中它几乎就
        锁定目标了，可它的分量和「黑丝」一模一样。

        所以按 IDF 加权：df 越大权重越低。加常数 1 是保底，免得所有词
        都是共性词时总权重归零除不了。
        """
        if not words:
            return [], 1.0
        total, dfs = self._df(words, folder)
        total = total or 1
        weights = [math.log((total + 1) / (df + 1)) + 1 for df in dfs]
        return weights, sum(weights) or 1.0

    def gallery_search(
        self, keywords: str = "", folder: str = "", limit: int = 8
    ) -> list[sqlite3.Row]:
        """按关键词和分类找图，按 IDF 加权的命中分排序。

        不用 AND 取交集：一句「酒店里穿灰丝踩红底细高跟」拆出六七个词，
        只要一个词跟描述里的用词对不上（说「足底」而档案里写「脚底」），
        交集就是空，整句话什么都搜不到。改成打分——漏词只降排名，
        不至于让图消失。

        分数已按总权重归一化到 0~1，调用方直接用，不用再除词数。
        """
        words = self._split_query(keywords)
        args: list = []
        if words:
            words = self._rescue_dead(words, folder)
            weights, total_w = self._idf(words, folder)
            # SQLite 里布尔就是 0/1，乘上各自的权重再求和
            expr = " + ".join(["(descr LIKE ?) * ?"] * len(words))
            for w, wt in zip(words, weights):
                args += [f"%{w}%", wt]
            score = f"({expr}) / {total_w:.6f}"
        else:
            score = "0"

        sql = f"SELECT *, ({score}) AS score FROM photos WHERE descr IS NOT NULL"
        if folder.strip():
            sql += " AND folder LIKE ?"
            args.append(f"%{folder.strip()}%")
        # 只按命中数排，同分用 id 兜底——不能有 RANDOM()：
        # 同一段词每次搜出来的候选必须是同一批，否则"上次那张"永远漂移。
        # 发送历史和时间的偏好交给后面的权重重排，那里是可控的确定性调整
        sql += " ORDER BY score DESC, id ASC LIMIT ?"
        args.append(max(1, min(limit, 200)))

        try:
            rows = self.db().execute(sql, args).fetchall()
        except sqlite3.Error as e:
            logger.warning(f"[tg_presence] 图库检索失败: {e}")
            return []
        # 一个词都没中的没意义（没给关键词时例外，那是随手翻）
        return [r for r in rows if not words or r["score"] > 0]

    # ------------------------------------------------------------ 语义向量

    def _embed_conf(self) -> dict | None:
        """向量接口配置。没填模型就是不启用。"""
        model = (self.conf.get("embed_model") or "").strip()
        if not model:
            return None
        vis = self._vision_conf() or {}
        base = (self.conf.get("embed_base_url") or "").strip().rstrip("/")
        key = (self.conf.get("embed_api_key") or "").strip()
        if not base:
            # 复用视觉的地址，但要把它补过的 /chat/completions 去掉
            base = (self.conf.get("vision_base_url") or "").strip().rstrip("/")
            base = base.removesuffix("/chat/completions").rstrip("/")
        if not key:
            key = vis.get("key", "")
        if not (base and key):
            return None
        if not base.endswith("/embeddings"):
            base += "/embeddings"
        return {
            "url": base,
            "key": key,
            "model": model,
            "dim": max(64, int(self.conf.get("embed_dim", 1024) or 1024)),
        }

    async def _embed(self, texts: list[str]) -> list[list[float]] | None:
        """一批文本转向量。只走 OpenAI 兼容的 /embeddings。"""
        cfg = self._embed_conf()
        if not cfg or not texts:
            return None
        payload = {"model": cfg["model"], "input": texts}
        # 支持指定维度的模型才认这个字段，不支持的会忽略
        if cfg["dim"]:
            payload["dimensions"] = cfg["dim"]
        headers = {
            "Authorization": f"Bearer {cfg['key']}",
            "Content-Type": "application/json",
        }
        try:
            timeout = aiohttp.ClientTimeout(total=VISION_TIMEOUT)
            async with aiohttp.ClientSession(timeout=timeout) as sess:
                async with sess.post(cfg["url"], json=payload, headers=headers) as r:
                    body = await r.text()
                    if r.status != 200:
                        # 有些服务不认 dimensions，去掉重试一次
                        if "dimensions" in payload and r.status == 400:
                            payload.pop("dimensions")
                            async with sess.post(
                                cfg["url"], json=payload, headers=headers
                            ) as r2:
                                body = await r2.text()
                                if r2.status != 200:
                                    raise VisionError(
                                        f"HTTP {r2.status} {body[:200]}",
                                        retryable=r2.status in RETRY_STATUS,
                                        fatal=r2.status in FATAL_STATUS,
                                    )
                        else:
                            raise VisionError(
                                f"HTTP {r.status} {body[:200]}",
                                retryable=r.status in RETRY_STATUS,
                                fatal=r.status in FATAL_STATUS,
                            )
                    data = json.loads(body)
            items = sorted(data["data"], key=lambda x: x.get("index", 0))
            return [it["embedding"] for it in items]
        except VisionError:
            raise
        except asyncio.TimeoutError:
            raise VisionError(f"超时（{VISION_TIMEOUT} 秒）", retryable=True) from None
        except Exception as e:
            raise VisionError(f"{type(e).__name__}: {e}", retryable=True) from e

    async def _embed_retry(self, texts: list[str]) -> list[list[float]] | None:
        """带退避的转向量。

        向量接口的限流比视觉接口容易撞得多：一张图要转四段，请求数直接
        翻四倍，而且这类接口往往按文本条数而不是按请求数计配额。
        没有重试的话撞一次 429 就整批丢掉，跑到一半全废。

        等待固定六十秒——限流配额按分钟计窗口，等满一分钟就跨过去了，
        指数翻倍只是白等。
        """
        tries = max(1, int(self.conf.get("embed_retries", 5) or 5))
        last: VisionError | None = None
        for attempt in range(1, tries + 1):
            try:
                return await self._embed(texts)
            except VisionError as e:
                if e.fatal or not e.retryable or attempt >= tries:
                    raise
                last = e
                await asyncio.sleep(self._retry_wait("embed_retry_wait", 60))
        raise last  # 循环只在重试耗尽时跳出

    def _embed_text(self, descr: str) -> str:
        """裁出送去转向量的文本。超长时必须保住结尾的标签行。

        描述九百来字加标签三百多字，对 2048 token 上限的模型（如
        gemini-embedding-001）正好压线。粗暴地截前 N 个字符会把标签整个切掉，
        而那一行恰恰是口语词最密集的地方——「黑丝」「细高跟」「M腿」全在那儿，
        丢了等于把语义检索最该抓住的东西扔了。
        """
        descr = descr or ""
        limit = max(200, int(self.conf.get("embed_max_chars", 1800) or 1800))
        if len(descr) <= limit:
            return descr
        lines = descr.rstrip().splitlines()
        tail = lines[-1].strip() if lines and "---" in lines[-1] else ""
        if tail and len(tail) < limit - 100:
            return descr[: limit - len(tail) - 1].rstrip() + "\n" + tail
        return descr[:limit]

    @staticmethod
    def _vec_pack(vec: list[float]) -> bytes:
        """归一化后存 float32。预归一化之后检索时点积即余弦，省一次开方。"""
        import math

        n = math.sqrt(sum(v * v for v in vec)) or 1.0
        return struct.pack(f"<{len(vec)}f", *[v / n for v in vec])

    def _photo_brief(self, descr: str) -> str:
        """给桃桃挑图时看的摘要。

        原来直接截前 70 字，而描述开头恰好是九宫格的「左上：白色墙面，
        窗户一角」——最没有判别力的那一格。她看十张，十张开头都长一样，
        等于让她闭着眼睛选。

        抽三样她真正需要的：场景一句、人物整体（穿着姿态镜头）、标签行
        （信息密度最高的特征清单）。切不出层就退回原来的截断。
        """
        layers = self._desc_layers(descr)
        if not layers:
            return " ".join((descr or "").split())[:120]

        bits = []
        # 第一层里九宫格之后那段才是场景总结，逐格描述对挑图没用
        env = [
            ln.strip()
            for ln in layers.get(1, "").splitlines()
            if ln.strip() and not GRID_RE.match(ln.strip())
        ]
        if env:
            bits.append(" ".join(env)[:56])
        if body := " ".join(layers.get(2, "").split()):
            bits.append(body[:76])
        # 末尾若有关键词行就用它，没有就退回第四层——描述里最能说清
        # 「这张在干什么」的一段。两种提示词版本都能给出有用的摘要
        if tag := self._tag_line(descr):
            bits.append(tag[:130])
        elif act := " ".join(layers.get(4, "").split()):
            bits.append(act[:96])
        return " ｜ ".join(bits) or " ".join((descr or "").split())[:120]

    @staticmethod
    def _tag_line(descr: str) -> str:
        """摘出末尾那行标签。取分隔符最多的一行，和 audit_tags 同一口径。"""
        line, best = "", 1
        for raw in (descr or "").splitlines():
            if (n := raw.count("---")) > best:
                best, line = n, raw.strip()
        return line

    @staticmethod
    def _desc_layers(descr: str) -> dict[int, str]:
        """按六层标题切开，返回 {层号: 内容}。切不出来返回空。"""
        if not descr:
            return {}
        marks = [m for m in LAYER_RE.finditer(descr) if m.group(1) in LAYER_NUM]
        if len(marks) < 4:  # 六层里连四层都找不到，格式对不上，别硬切
            return {}
        layers: dict[int, str] = {}
        for i, m in enumerate(marks):
            end = marks[i + 1].start() if i + 1 < len(marks) else len(descr)
            # 同一层出现两次就以头一次为准，别让后面的把内容盖掉
            layers.setdefault(LAYER_NUM[m.group(1)], descr[m.end() : end].strip())
        return layers

    @staticmethod
    def _desc_segments(descr: str) -> dict[str, str]:
        """按六层标题把描述切成几段，各自要转一个向量。

        切不出层标题（提示词换过、模型没照写）就返回空，那种情况只存
        全文向量，行为跟以前一样。
        """
        layers = TgPresence._desc_layers(descr)
        if not layers:
            return {}
        out: dict[str, str] = {}
        for col, nums in VEC_SEGS.items():
            if nums is None:
                continue
            txt = "\n".join(x for x in (layers.get(n, "") for n in nums) if x).strip()
            if txt:
                out[col] = txt
        return out

    def _load_matrix(self, col: str = "vec"):
        """把某一段的全库向量读进内存。第一次检索时构建，之后复用。

        一万张 × 四段 × 1024 维 float32 约 160 MB。每次检索都从 SQLite
        读一遍显然不行，而这个量级又完全不值得上向量数据库，常驻内存最省事。
        """
        if col in self._vec_cache:
            return self._vec_cache[col]
        try:
            import numpy as np
        except ImportError:
            logger.warning("[tg_presence] 没装 numpy，语义检索不可用")
            self._vec_cache[col] = ([], None)
            return self._vec_cache[col]

        rows = self.db().execute(
            f"SELECT id, {col} v FROM photos WHERE {col} IS NOT NULL ORDER BY id"
        ).fetchall()
        if not rows:
            self._vec_cache[col] = ([], None)
            return self._vec_cache[col]

        ids = [int(r["id"]) for r in rows]
        dim = len(rows[0]["v"]) // 4
        mat = np.frombuffer(b"".join(r["v"] for r in rows), dtype="<f4")
        try:
            mat = mat.reshape(len(ids), dim)
        except ValueError:
            logger.error("[tg_presence] 向量维度不一致，可能换过模型；请 /gallery embed redo")
            self._vec_cache[col] = ([], None)
            return self._vec_cache[col]
        logger.info(
            f"[tg_presence] 载入 {col} {len(ids)} 条 {dim} 维，{mat.nbytes/1048576:.0f} MB"
        )
        self._vec_cache[col] = (ids, mat)
        return self._vec_cache[col]

    async def _vector_search(self, query: str, limit: int) -> dict[int, float]:
        """全库语义检索，返回 {图片id: 余弦相似度}。不可用时返回空。

        每一段各比一次，同一张图取最高的那段。搜「桌上喷水」时环境段
        会强命中，而它在全文向量里早被三千字身体细节压没了。
        """
        if not query.strip() or not self._embed_conf():
            return {}
        try:
            import numpy as np

            got = await self._embed([query])
            if not got:
                return {}
            q = np.asarray(got[0], dtype="<f4")
            q /= np.linalg.norm(q) or 1.0

            best: dict[int, float] = {}
            for col in VEC_SEGS:
                ids, mat = self._load_matrix(col)
                if mat is None or not ids:
                    continue
                if q.shape[0] != mat.shape[1]:
                    logger.warning(
                        f"[tg_presence] 查询向量 {q.shape[0]} 维与 {col} 的 "
                        f"{mat.shape[1]} 维对不上，跳过这一段"
                    )
                    continue
                sims = mat @ q
                n = min(limit, len(ids))
                for i in np.argpartition(-sims, n - 1)[:n]:
                    pid, s = ids[i], float(sims[i])
                    if s > best.get(pid, -2.0):
                        best[pid] = s
            if len(best) <= limit:
                return best
            top = sorted(best.items(), key=lambda kv: -kv[1])[:limit]
            return dict(top)
        except VisionError as e:
            logger.warning(f"[tg_presence] 语义检索失败，退回纯关键词：{e}")
            return {}
        except Exception as e:
            logger.warning(f"[tg_presence] 语义检索出错：{e}")
            return {}

    async def _recall(
        self, keywords: str, want: str, folder: str, pool: int
    ) -> list[sqlite3.Row]:
        """关键词召回 ∪ 语义召回，合并出候选池并算出统一的匹配度。

        用并集而不是加权合并两条通路：加权要调系数，而且一方的分数会污染
        另一方——关键词精确命中的图不该因为语义分低就被挤出候选。并集则是
        两边各自的头部都一定进池，谁都不漏，反正后面还有分层重排收窄。

        进池之后再算统一的匹配度：关键词命中率和语义相似度按 vector_weight
        加权。这一步是在「匹配度」这个维度内部合成，不影响时间/发送条件
        压在它上面的分层结构。
        """
        kw_rows = self.gallery_search(keywords or want, folder, limit=pool)

        vw = float(self.conf.get("vector_weight", 0.4) or 0)
        query = " ".join(x for x in (want.strip(), keywords.strip()) if x)
        vec_hits = await self._vector_search(query, pool) if vw > 0 else {}

        by_id = {int(r["id"]): dict(r) for r in kw_rows}
        # 语义召回里那些关键词没捞到的，补进池子
        missing = [i for i in vec_hits if i not in by_id]
        if missing:
            marks = ",".join("?" * len(missing))
            extra = self.db().execute(
                f"SELECT *, 0 AS score FROM photos WHERE id IN ({marks})", missing
            ).fetchall()
            for r in extra:
                if folder.strip() and folder.strip() not in (r["folder"] or ""):
                    continue
                by_id[int(r["id"])] = dict(r)

        for pid, row in by_id.items():
            # gallery_search 已按 IDF 总权重归一化过，这儿直接用
            kw = min(1.0, max(0.0, float(row.get("score") or 0)))
            sim = vec_hits.get(pid)
            # 留痕给 /gallery search 看：这张是词面命中的，还是语义捞回来的
            row["kw_score"], row["sim_score"] = kw, sim
            # 只有真启用了向量、且这张图在语义 top 里，才把两者混起来
            row["score"] = kw * (1 - vw) + sim * vw if sim is not None and vw > 0 else kw
        merged = sorted(
            by_id.values(), key=lambda r: (-float(r["score"]), int(r["id"]))
        )[:pool]
        if vec_hits:
            logger.debug(
                f"[tg_presence] 召回 关键词{len(kw_rows)} ∪ 语义{len(vec_hits)} "
                f"-> {len(merged)} 张"
            )
        return merged

    def _month_range(self, around: str) -> tuple[float, float] | None:
        """把 YYYY-MM / MM / YYYY-MM-DD 解析成那个月的起止时间戳。

        时间条件按「月」而不是按天算：人说的是"三月那会儿的"，
        不是"3月1号那天的"。
        """
        s = (around or "").strip()
        if not s:
            return None
        tz = self._tz()
        this_year = datetime.now(tz).year
        for fmt, has_year in (("%Y-%m-%d", True), ("%Y-%m", True), ("%m", False)):
            try:
                d = datetime.strptime(s, fmt)
            except ValueError:
                continue
            y, mo = (d.year if has_year else this_year), d.month
            start = datetime(y, mo, 1, tzinfo=tz)
            end = datetime(y + (mo == 12), mo % 12 + 1, 1, tzinfo=tz)
            return start.timestamp(), end.timestamp()
        return None

    def _rerank(
        self, rows: list[sqlite3.Row], prefer_sent: str = "", around: str = ""
    ) -> list[sqlite3.Row]:
        """对粗筛结果重排。纯计算，不调模型。

        分层而不是加权：「上个月发过的那张」意思是在那批里挑匹配度最高的，
        不是让时间给匹配度加点分——加权会让一张匹配度稍高但时间根本不对的
        图挤上来，那不是人想要的。所以满足时间条件的整体排前面，组内再按
        匹配度。不满足的仍然保留在后面兜底，避免条件太严时一张都返回不了。

        排序键全是确定值，同一段词每次算出来的顺序完全一致。
        """
        if not rows:
            return rows

        now = time.time()
        window = max(1, int(self.conf.get("sent_window_days", 30) or 30)) * 86400.0
        rng = self._month_range(around)
        pref = (prefer_sent or "").strip().lower()
        want_recent = pref in ("recent", "发过", "上次")
        ignore_sent = pref in ("any", "不限")
        # 他明说的条件要压过默认偏好：只说了"三月那会儿的"时，三月的图
        # 必须全部排在前面，不能因为某张更新、恰好又没发过就被顶上来
        told_pref = bool(pref) and not ignore_sent

        def key(r: sqlite3.Row):
            # 图片自身的时间优先用文件修改时间；老库还没回填就退回入库时间
            ft = float(r["file_time"] or r["added"] or 0)
            last = float(r["last_sent"] or 0)
            fresh = (not last) or (now - last > window)

            told, default = 0, 0   # 他明说的 / 默认偏好
            if rng and rng[0] <= ft < rng[1]:
                told += 1
            if not ignore_sent and (want_recent != fresh):
                # recent 要窗口内发过的，fresh 要没发过或早就过了窗口的
                if told_pref:
                    told += 1
                else:
                    default += 1

            # 明说的条件 > 默认偏好 > 匹配度 > 新的优先 > id 兜底
            return (-told, -default, -float(r["score"] or 0), -ft, int(r["id"]))

        return sorted(rows, key=key)

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

        by_image = (self.conf.get("picker_mode") or "text").strip().lower() == "image"
        if by_image:
            # 看图选比看描述准 —— 描述再细也是二手信息，漏写的东西就永远找不回来。
            # 代价是贵：一张图 1500~4800 token，比一段描述贵好几倍，所以候选数另设上限
            cap = max(2, int(self.conf.get("picker_image_max", 6) or 6))
            rows = rows[:cap]
            images, kept = [], []
            for r in rows:
                p = self._photo_file(r)
                img = self._read_image(str(p)) if p else None
                if img:
                    images.append(img)
                    kept.append(r)
            if not images:
                logger.warning("[tg_presence] 候选图都读不出来，退回粗筛结果")
                return rows[:top]
            rows = kept
            prompt = (
                f"用户想找的画面：\n{want}\n\n"
                f"上面 {len(images)} 张图按 [1]~[{len(images)}] 编号。"
                f"挑出与描述最吻合的，按吻合程度从高到低排序，最多 {top} 个。"
                "明显不符的不要列。只输出编号，例如：3,1,2"
            )
            payload = self._multi_image_payload(cfg, images, prompt)
        else:
            blocks = [f"[{i}] {(r['descr'] or '')[:900]}" for i, r in enumerate(rows, 1)]
            prompt = (
                f"用户想找的画面：\n{want}\n\n"
                f"下面是 {len(rows)} 张候选图片的描述：\n\n"
                + "\n\n".join(blocks)
                + f"\n\n把与用户描述最吻合的挑出来，按吻合程度从高到低排序，"
                f"最多 {top} 个。明显不符的不要列。\n"
                "只输出编号，例如：3,7,1"
            )
            payload = self._text_payload(cfg, prompt)

        try:
            raw = await self._api_post(cfg, payload)
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
        logger.info(
            f"[tg_presence] {'看图' if by_image else '看描述'}精排 "
            f"{len(rows)} -> {len(picked)} 张"
        )
        return picked[:top]

    def gallery_stat(self) -> dict:
        db = self.db()
        # 别名一律加双引号：indexed 是 SQLite 保留字（INDEXED BY），
        # 裸着写会被当成子句开头，直接语法错误
        row = db.execute(
            'SELECT COUNT(*) AS "total",'
            ' SUM(descr IS NOT NULL) AS "indexed",'
            ' SUM(descr IS NULL AND fails < ?) AS "pending",'
            ' SUM(descr IS NULL AND fails >= ?) AS "stuck",'
            ' SUM(sent) AS "sent"'
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

    def _platform_client(self, umo: str):
        """按 UMO 第一段找到那个平台实例的底层 client。

        控制台是插件自己的 bot，手上没有角色那个 bot 的 client——
        而发照片、发频道动态、换头像、改签名都得以角色的身份去调
        Telegram。适配器把 ExtBot 挂在自己的 client 属性上，
        从平台管理器按 meta().id 找到实例就能拿到。
        """
        name = self._umo_platform(umo)
        pm = getattr(self.context, "platform_manager", None)
        if not name or pm is None:
            return None
        try:
            for inst in pm.get_insts() or []:
                meta = inst.meta()
                if getattr(meta, "id", None) != name:
                    continue
                if getattr(meta, "name", "") != "telegram":
                    logger.warning(f"[tg_presence] {name} 不是 telegram 平台，用不了")
                    return None
                return getattr(inst, "client", None)
        except Exception as e:
            logger.warning(f"[tg_presence] 找平台实例 {name} 失败：{e}")
        return None

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
            "safety": (self.conf.get("gemini_safety") or "BLOCK_NONE").strip(),
            "think": (self.conf.get("gemini_thinking_budget") or "").strip(),
            "system": (self.conf.get("vision_system_prompt") or "").strip()
            or DEFAULT_VISION_SYSTEM,
            "prompt": (self.conf.get("vision_prompt") or "").strip()
            or DEFAULT_VISION_PROMPT,
        }

    # ----------------------------------------------- 三种接口格式的请求与解析

    @staticmethod
    def _gemini_safety(cfg: dict) -> list | None:
        """Gemini 的安全阈值。返回 None 表示不传这个字段，用官方默认。

        默认阈值会把成人向图片整片拦掉，而且拦得很安静——HTTP 200、
        candidates 空着、状态码看不出任何异常。这个字段是 Gemini 这条
        链路能不能用的分水岭，不是调优项。

        BLOCK_NONE 是通用写法；OFF 更彻底但只有较新的模型认，老模型收到
        会 400。填「默认」就完全不传。
        """
        level = (cfg.get("safety") or "").strip()
        if not level or level in ("默认", "default", "DEFAULT"):
            return None
        return [{"category": c, "threshold": level} for c in GEMINI_HARM_CATEGORIES]

    @staticmethod
    def _gemini_gen_config(cfg: dict) -> dict:
        """Gemini 的 generationConfig。关键在 thinkingConfig。

        2.5 系列的思考 token 跟正文**共用** maxOutputTokens。放任不管的话，
        模型会先在思维链里把整篇描述打一遍草稿，等轮到正式输出时配额已经
        见底——结果就是草稿和正文双双被截断，两截还会被拼进同一条记录。
        限住思考预算，配额才留得给真正要存的那段。

        不填就完全不传这个字段：老模型（1.5 及更早）不认识它，收到会 400。
        """
        gc: dict = {"maxOutputTokens": cfg["max_tokens"]}
        raw = str(cfg.get("think") or "").strip()
        if not raw:
            return gc
        try:
            budget = int(raw)
        except ValueError:
            logger.warning(f"[tg_presence] 思考预算「{raw}」不是整数，已忽略")
            return gc
        # includeThoughts 一并关掉：思维链不是描述，拿回来也只会被丢弃
        gc["thinkingConfig"] = {"thinkingBudget": budget, "includeThoughts": False}
        return gc

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
                "generationConfig": TgPresence._gemini_gen_config(cfg),
            }
            if safety := TgPresence._gemini_safety(cfg):
                body["safetySettings"] = safety
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
        # 只要 text，丢掉推理模型的 thinking 块——那是思考过程不是描述。
        # 两家标记方式不同：Anthropic 用 type="thinking"，靠下面那个 type 判断
        # 排掉；Gemini 的 part 压根没有 type 字段，只在思考块上挂 thought=true，
        # 不单独认这个标记就会把整段思维链当描述收下来
        bits = [
            t.strip()
            for b in blocks
            if isinstance(b, dict)
            and b.get("type", "text") == "text"
            and not b.get("thought")
            and isinstance(t := b.get("text"), str)
            and t.strip()
        ]
        if len(bits) > 1:
            # 正常一次生成只有一段正文。出现多段说明模型把草稿也吐出来了，
            # 或者网关合并了多个候选——拼起来就是两篇描述首尾相接的怪东西
            logger.info(
                f"[tg_presence] 响应含 {len(bits)} 段正文，已拼接："
                + " | ".join(f"{len(b)} 字" for b in bits)
            )
        return " ".join(bits)

    def _cut_at_end_mark(self, text: str) -> tuple[str, bool]:
        """按结束标记裁掉尾巴。返回 (正文, 模型有没有写完)。

        标记干两件事，第二件才是重点：
        · 切掉标记之后的东西——模型偶尔把草稿和正文一起吐出来，
          两篇描述首尾相接存进同一条记录
        · 没有标记就说明没写完。被截断的描述看上去跟正常的一模一样，
          只是尾巴秃了一截，不靠这个信号根本发现不了——而秃掉的恰恰
          是最末尾的标签行，检索最依赖的那部分

        没配标记就退化成「一律当写完了」，不影响不用这套提示词的人。
        """
        mark = (self.conf.get("vision_end_mark") or "").strip()
        if not mark:
            return text, True
        i = text.find(mark)
        if i < 0 and len(set(mark)) == 1 and mark[0] in END_MARK_CHARS:
            # 标记是同一个点号重复 N 次时放宽：允许模型换成形近的另一个点号
            m = re.search(f"[{re.escape(END_MARK_CHARS)}]{{{len(mark)},}}", text)
            if m:
                i = m.start()
        return (text[:i].rstrip(), True) if i >= 0 else (text, False)

    def _junk_reason(self, text: str) -> str:
        """判断这段回复能不能当描述用。返回不能用的原因，能用则空串。

        三种垃圾都是 HTTP 200 正常返回的，不拦就会直接进库：
        · 模型嘴上拒绝——「我无法满足这个请求」被当成图片描述存下来
        · 思维链漏进正文——中转网关不打 thought 标记时，_resp_text 拦不住
        · 短得不可能是详细描述——模型敷衍了事

        存进去比失败严重得多：这些文本会跟着转成向量，把语义检索一起带偏，
        而且日志里什么都看不出来，只表现为「搜出来的图莫名其妙」。
        """
        t = (text or "").strip()
        if not t:
            return ""  # 空回有专门的处理路径，不在这儿判
        low = t.lower()

        head = low[:600]
        # 英文粗体小标题开头，配上中文提示词，只可能是思维链
        if re.match(r"^\*\*[a-z]", low) or any(p in head for p in THINKING_MARKS):
            return "像是思维链漏进了正文"

        if len(t) <= REFUSAL_MAX_CHARS:
            for p in REFUSAL_MARKS:
                if p in low:
                    return f"像是拒答，命中「{p}」"

        floor = int(self.conf.get("vision_min_chars", 0) or 0)
        if floor:
            # 下限不能高过截断上限，否则会自相矛盾：解析时按原文判定为合格，
            # 存进库的却是截断后的短文本，回头 /gallery clean 又把它判成脏数据
            cap = max(100, int(self.conf.get("vision_max_chars", 600) or 600))
            floor = min(floor, cap)
            if len(t) < floor:
                return f"只有 {len(t)} 字，不到下限 {floor}"
        return ""

    @staticmethod
    def _refusal_reason(fmt: str, data: dict) -> str:
        """空回的时候把「为什么空」挖出来。

        Gemini 拦内容时返回的是 HTTP 200，正文里 candidates 要么空着、
        要么只剩一个 finishReason。不把这些挖出来，日志里就只有一句
        「返回内容为空」，根本分不清是安全策略、是配额、还是模型抽风。

        PROHIBITED_CONTENT 要单独认出来——safetySettings 对它无效，
        再怎么重试都不会过，得换模型。
        """
        if fmt != "gemini":
            return ""
        bits = []
        if br := (data.get("promptFeedback") or {}).get("blockReason"):
            bits.append(f"blockReason={br}")
        cands = data.get("candidates") or []
        if not cands:
            bits.append("没有 candidates")
        elif isinstance(cands[0], dict):
            if fr := cands[0].get("finishReason"):
                bits.append(f"finishReason={fr}")
            hit = [
                (r.get("category") or "").replace("HARM_CATEGORY_", "")
                for r in (cands[0].get("safetyRatings") or [])
                if isinstance(r, dict)
                and (r.get("blocked") or r.get("probability") in ("HIGH", "MEDIUM"))
            ]
            if hit:
                bits.append("命中 " + "、".join(hit))
        return "；".join(bits)

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
                    p["text"]
                    for p in parts
                    if isinstance(p.get("text"), str) and not p.get("thought")
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
    def _multi_image_payload(
        cfg: dict, images: list[tuple[str, str]], prompt: str
    ) -> dict:
        """多图请求体。每张图前插一个 [N] 文本标记，模型才知道哪张是哪张。"""
        fmt = cfg["fmt"]
        if fmt == "anthropic":
            content: list = []
            for i, (mime, b64) in enumerate(images, 1):
                content.append({"type": "text", "text": f"[{i}]"})
                content.append(
                    {
                        "type": "image",
                        "source": {"type": "base64", "media_type": mime, "data": b64},
                    }
                )
            content.append({"type": "text", "text": prompt})
            body = {
                "model": cfg["model"],
                "max_tokens": cfg["max_tokens"],
                "system": cfg["system"],
                "messages": [{"role": "user", "content": content}],
            }
        elif fmt == "gemini":
            parts: list = []
            for i, (mime, b64) in enumerate(images, 1):
                parts.append({"text": f"[{i}]"})
                parts.append({"inline_data": {"mime_type": mime, "data": b64}})
            parts.append({"text": prompt})
            body = {
                "system_instruction": {"parts": [{"text": cfg["system"]}]},
                "contents": [{"role": "user", "parts": parts}],
                "generationConfig": TgPresence._gemini_gen_config(cfg),
            }
            if safety := TgPresence._gemini_safety(cfg):
                body["safetySettings"] = safety
        else:
            content = []
            for i, (mime, b64) in enumerate(images, 1):
                content.append({"type": "text", "text": f"[{i}]"})
                content.append(
                    {
                        "type": "image_url",
                        "image_url": {"url": f"data:{mime};base64,{b64}"},
                    }
                )
            content.append({"type": "text", "text": prompt})
            body = {
                "model": cfg["model"],
                "max_tokens": cfg["max_tokens"],
                "messages": [
                    {"role": "system", "content": cfg["system"]},
                    {"role": "user", "content": content},
                ],
            }
        if cfg["stream"] and fmt != "gemini":
            body["stream"] = True
        for k, v in (cfg["extra"] or {}).items():
            if isinstance(v, dict) and isinstance(body.get(k), dict):
                body[k].update(v)
            else:
                body[k] = v
        return body

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
                "generationConfig": TgPresence._gemini_gen_config(cfg),
            }
            if safety := TgPresence._gemini_safety(cfg):
                body["safetySettings"] = safety
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
                        raise VisionError(
                            f"HTTP {r.status} {body[:300]}",
                            retryable=r.status in RETRY_STATUS,
                            fatal=r.status in FATAL_STATUS,
                        )
                    if not cfg["stream"]:
                        data = json.loads(await r.text())
                        text = self._resp_text(fmt, data)
                        if not text:
                            # 200 却没正文，基本都是内容被拦。原因藏在正文里
                            why = self._refusal_reason(fmt, data)
                            raise VisionError(
                                "HTTP 200 但没有正文" + (f"：{why}" if why else ""),
                                retryable=True,
                            )
                        return text

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
            raise VisionError(f"超时（{VISION_TIMEOUT} 秒）", retryable=True) from None
        except (aiohttp.ClientError, json.JSONDecodeError, ValueError) as e:
            # 连接被掐、网关吐了半截 JSON——都是传输层的临时问题，值得再来一次
            raise VisionError(f"{type(e).__name__}: {e}", retryable=True) from e

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
            raise VisionError("视觉 API 没配全", fatal=True)
        image = self._read_image(path)
        if not image:
            raise VisionError("图片读不出来")  # 这张图自己的问题，该记账

        tries = max(1, int(self.conf.get("vision_retries", 4) or 4))
        cap = max(100, int(self.conf.get("vision_max_chars", 600) or 600))
        last: VisionError | None = None

        for attempt in range(1, tries + 1):
            try:
                async with self._gate():
                    if skip_check and skip_check():
                        return None
                    await self._wait_cooldown()
                    text = await self._vision_post(cfg, *image)
                if not text:
                    # 流式路径拿不到响应体，给不出具体原因；非流式的在
                    # _api_post 里已经带着 finishReason 抛出来了
                    raise VisionError(
                        "返回内容为空，可能是模型拒答或触发了内容过滤", retryable=True
                    )
                # 先按结束标记裁，再判内容——裁掉的可能正是拼在后面的另一篇
                text, whole = self._cut_at_end_mark(text)
                if not whole:
                    raise VisionError(
                        f"没写结束标记，输出多半被截断（收到 {len(text)} 字）"
                        f"，检查最大输出长度和思考预算",
                        retryable=True,
                    )
                if why := self._junk_reason(text):
                    # 重试是有意义的：拒答带随机性，同一张图换一次采样常常就过了
                    raise VisionError(f"返回的不是描述（{why}）：{text[:80]}", retryable=True)
                self._note_upstream_ok()
                return text[:cap]
            except VisionError as e:
                if e.fatal or not e.retryable:
                    raise
                last = e
                self._note_upstream_fail()
                if attempt >= tries:
                    break
                await asyncio.sleep(self._retry_wait("vision_retry_wait", 10))

        raise last  # 循环只在重试耗尽时跳出，last 必定有值

    def _retry_wait(self, key: str, default: int) -> float:
        """重试前等多久。固定值，不做指数退避。

        指数退避是给「不知道上游什么时候好」准备的。这儿两条链路的
        恢复窗口都是已知的：视觉侧有一组账号轮换，等十秒足够换一个；
        向量侧的限流按分钟计窗口，等六十秒正好跨过去。
        既然知道该等多久，翻倍只会白等。
        """
        return max(0.0, float(self.conf.get(key, default) or default))

    async def _wait_cooldown(self) -> None:
        """熔断期内原地等着。分段睡，好让 stop 能及时打断。"""
        while (gap := self._cool_until - time.time()) > 0:
            await asyncio.sleep(min(gap, 3))

    def _note_upstream_ok(self) -> None:
        self._fail_streak = 0

    def _note_upstream_fail(self) -> None:
        """连续失败到一定程度就全局歇一轮，别对着挂掉的上游猛捶。"""
        self._fail_streak += 1
        if self._fail_streak < TRIP_STREAK or time.time() < self._cool_until:
            return
        cool = self._retry_wait("vision_retry_wait", 10) * 3
        self._cool_until = time.time() + cool
        self._fail_streak = 0
        logger.warning(
            f"[tg_presence] 上游连续失败 {TRIP_STREAK} 次，全局暂停 {cool:.0f} 秒"
        )

    async def _vision_describe(self, pid: str, path: str) -> bool:
        """给上下文里的一张图做视觉解析，存进 vision.json。"""
        if pid in self.vision:
            return True
        try:
            text = await self._vision_of(path, lambda: pid in self.vision)
        except VisionError as e:
            if e.retryable and not e.fatal:
                # 同上：上游抖动不该让这张图被永久放弃，下一轮还能再来
                logger.warning(f"[tg_presence] 视觉解析 #{pid} 上游未恢复，本轮跳过：{e}")
                return False
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

    def audit_tags(self, descr: str) -> tuple[str, list[str]]:
        """校验描述末尾的标签行。返回 (归类, 问题列表)。

        归类：ok / 无标签 / 段数不齐 / 有问题

        提示词早期要求固定 44 项、按位置对齐，那时候校验的是「段数够不够」。
        后来改成自由列举关键词——检索的两路都不看词在第几个位置，固定格子
        除了增加模型负担没有别的作用，而约束越多遵守率越低（编号那条就是
        活例子）。所以现在只校验数量下限：关键词太少说明模型没好好列，
        那一行是检索命中率的主要来源。

        「段数不齐」这个归类名保留着，redo 和历史数据都认它。

        值校验（仅 tag_strict 开启）留给还在用固定候选集的场景，自由用词
        时会把几乎每张都标成「有问题」，纯噪声，默认关。

        只诊断不改数据——非法值往往仍是有意义的词（模型写"项圈"而候选集
        里只有"皮革项圈"），删了反而丢信息，留着还能被 substring 命中。
        """
        strict = bool(self.conf.get("tag_strict", False)) and bool(FIELDS)
        want = (
            len(FIELDS) if strict and FIELDS else int(self.conf.get("tag_min_words", 0) or 0)
        )
        if want <= 0:
            # 提示词把 44 项化进了自然语言，末尾不再有关键词行，
            # 这时候整个标签校验都不适用——全判 ok，别让 redo 把全库捞去重跑
            return "ok", []
        # 取分隔符最多的那一行。三点考虑：
        # · 不要求「1.」开头——模型基本不照做，硬卡这条会让校验对新格式全盲
        # · 不取最后一行——结束标记、模型自己补的备注都可能跟在后面
        # · 要求至少两个 ---，免得正文里偶然出现的一个破折号被当成标签行
        line, best = "", 1
        for raw in (descr or "").splitlines():
            if (n := raw.count("---")) > best:
                best, line = n, raw.strip()
        if not line:
            return "无标签", []

        segs = [s.strip() for s in line.split("---") if s.strip()]
        issues = []
        for pos, seg in enumerate(segs, 1):
            m = re.match(r"^(\d+)\.(.*)$", seg, re.S)
            i, val = (int(m.group(1)), m.group(2)) if m else (pos, seg)
            if not strict or not 1 <= i <= len(FIELDS):
                continue
            name, cand = FIELDS[i - 1]
            allowed = set(cand.split("|"))
            for one in val.split(","):
                one = ALIAS.get(one.strip(), one.strip())
                if not one or one in allowed:
                    continue
                owners = OWNER.get(one)
                if owners:
                    who = "、".join(f"{o}.{FIELDS[o - 1][0]}" for o in owners[:3])
                    issues.append(f"{i}.{name}「{one}」是 {who} 的值")
                else:
                    issues.append(f"{i}.{name}「{one}」不在候选集")

        # 严格模式要求逐项对齐，看总数；自由用词只看够不够多
        short = len(segs) != want if strict and FIELDS else len(segs) < want
        if short:
            issues.insert(
                0,
                f"只有 {len(segs)} 段，应该是 {want} 段"
                if strict and FIELDS
                else f"只有 {len(segs)} 个关键词，少于下限 {want}",
            )
            return "段数不齐", issues
        return ("有问题" if issues else "ok"), issues

    @staticmethod
    def _dur(sec: float) -> str:
        m, s = divmod(int(sec), 60)
        h, m = divmod(m, 60)
        if h:
            return f"{h} 小时 {m} 分"
        return f"{m} 分 {s} 秒" if m else f"{s} 秒"

    async def _index_batch(self, batch: int) -> tuple[int, int]:
        """跑一批待索引的图，返回 (成功数, 这批取到几张)。

        取到 0 张就是全库索引完了。fatal 异常往外抛，让调用方中止整批。
        """
        db = self.db()
        rows = db.execute(
            "SELECT id, path FROM photos WHERE descr IS NULL AND fails < ? "
            "ORDER BY id LIMIT ?",
            (VISION_MAX_FAILS, batch),
        ).fetchall()
        if not rows:
            return 0, 0

        jobs = []
        for r in rows:
            if p := self._photo_file(r):
                jobs.append(self._gallery_describe(r["id"], str(p)))
            else:
                # 文件没了，直接顶满失败数，不然每轮都会把它捞出来重试
                db.execute(
                    "UPDATE photos SET fails = ? WHERE id = ?",
                    (VISION_MAX_FAILS, r["id"]),
                )
        db.commit()

        results = await asyncio.gather(*jobs, return_exceptions=True)
        for x in results:
            if isinstance(x, VisionError) and x.fatal:
                raise x
        return sum(1 for x in results if x is True), len(rows)

    async def _index_loop(self, umo: str) -> None:
        """后台把待索引的图全部跑完，一条指令跑到底。

        设计成能扛住上游长时间抽风：一批全挂不会立刻放弃，而是拉长间隔
        守着，最多守到 max_dry 轮才收工。上游恢复了自动接上，进度全在库里，
        随时停随时续。
        """
        from astrbot.core.message.message_event_result import MessageChain

        batch = max(1, min(int(self.conf.get("index_auto_batch", 30) or 30), 200))
        gap = max(60, int(self.conf.get("index_report_gap", 600) or 600))
        max_dry = max(1, int(self.conf.get("index_max_dry", 12) or 12))
        started = last_report = time.time()
        done = dry = 0

        async def say(text: str) -> None:
            try:
                await self.context.send_message(umo, MessageChain().message(text))
            except Exception as e:  # 回报失败不能连累索引本身
                logger.warning(f"[tg_presence] 索引进度回报失败：{e}")

        try:
            while True:
                try:
                    ok, n = await self._index_batch(batch)
                except VisionError as e:
                    await say(f"❌ 配置有问题，索引停了：{e}\n改完发 /gallery index auto 重开。")
                    return

                if n == 0:
                    st = self.gallery_stat()
                    await say(
                        f"✅ 索引跑完了，用时 {self._dur(time.time() - started)}。\n"
                        f"本次新增 {done} 张，全库已索引 {st['indexed']}/{st['total']}。"
                        + (
                            f"\n有 {st['stuck']} 张失败跳过，/gallery retry 可以重来。"
                            if st["stuck"]
                            else ""
                        )
                        + "\n接着跑 /gallery embed 转向量。"
                    )
                    return

                done += ok
                if ok:
                    dry = 0
                else:
                    dry += 1
                    if dry >= max_dry:
                        st = self.gallery_stat()
                        await say(
                            f"⏸ 连着 {dry} 批一张都没成，上游看来是长时间挂了，先收工。\n"
                            f"本次完成 {done} 张，还剩 {st['pending']} 张。\n"
                            f"日志看下原因，恢复后 /gallery index auto 接着跑，进度不丢。"
                        )
                        return
                    # 越挂越久就等越久，上限 15 分钟。守着比放弃划算——
                    # 中转商的 auth 池通常几分钟到半小时就补上了
                    wait = min(60 * 2 ** min(dry, 4), 900)
                    if dry == 1 or dry % 3 == 0:
                        await say(
                            f"⚠️ 上游连续失败（第 {dry} 轮），{wait // 60} 分钟后再试。\n"
                            f"本次已完成 {done} 张。/gallery index stop 可以停。"
                        )
                    await asyncio.sleep(wait)
                    continue

                if time.time() - last_report >= gap:
                    st = self.gallery_stat()
                    await say(
                        f"索引中：本次 {done} 张，全库 {st['indexed']}/{st['total']}，"
                        f"还剩 {st['pending']} 张，已跑 {self._dur(time.time() - started)}。"
                    )
                    last_report = time.time()
        except asyncio.CancelledError:
            # 这里不再 await 发消息——任务已被取消，await 会立刻再抛一次。
            # 停止的回执由 /gallery index stop 那边直接回给用户
            logger.info(f"[tg_presence] 后台索引已取消，本次完成 {done} 张")
            raise
        finally:
            self._index_task = None

    async def _gallery_describe(self, row_id: int, path: str) -> bool:
        """给图库里的一张图做视觉解析，存进索引库。"""
        db = self.db()
        try:
            text = await self._vision_of(path)
        except VisionError as e:
            if e.fatal:
                raise  # 配置错，交给上层中止整批
            if e.retryable:
                # 重试都用完了上游还是不行。这不是图片的问题，绝不能记账——
                # 否则上游挂一夜就足以把整个图库标成「坏图」，还得手动 retry
                logger.warning(f"[tg_presence] 图库 g{row_id} 上游未恢复，本轮跳过：{e}")
                return False
            db.execute("UPDATE photos SET fails = fails + 1 WHERE id = ?", (row_id,))
            db.commit()
            logger.warning(f"[tg_presence] 图库 g{row_id} 索引失败：{e}")
            return False

        verdict, issues = self.audit_tags(text)
        db.execute(
            # 向量必须一起作废：描述换了，旧向量就不再代表这张图了。
            # 不清的话 embed 那边「descr 有、vec 空」的条件选不中它，
            # 新描述会一直配着旧向量，检索错得毫无痕迹
            f"UPDATE photos SET descr = ?, {VEC_NULLS}, fails = 0, tag_state = ?, "
            "tag_issues = ? WHERE id = ?",
            (text, verdict, "; ".join(issues[:8]), row_id),
        )
        db.commit()
        if verdict not in ("ok", "无标签"):
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
        text = getattr(resp, "completion_text", None)
        if not isinstance(text, str) or not text:
            return

        out = text
        if self.conf.get("describe_images", True) and "<img_note" in out:
            if found := self._harvest_notes(out):
                logger.info(f"[tg_presence] 收到 {found} 条图片描述")
            out = IMG_NOTE_RE.sub("", out)
        # 她模仿上下文自己写的时间戳，剥掉——真正的戳由 _stamp_own 事后打，
        # 用的是真实时钟，她猜的那个多半是错的
        if OWN_STAMP_RE.search(out):
            logger.info("[tg_presence] 剥掉她自己写的时间戳")
            out = OWN_STAMP_RE.sub("", out)
        if (out := out.strip()) != text:
            resp.completion_text = out

    @filter.on_decorating_result()
    async def strip_notes_before_send(self, event: AstrMessageEvent):
        """发送前最后一道闸：确保 <img_note> 不会漏进聊天窗口。

        上一步已经剥过一次，但文本抵达发送阶段的路径不止一条（其它插件改写、
        分段回复重组等），这里照最终要发的内容再兜一次底。
        正常情况下这里什么都匹配不到 —— 一旦日志里出现，说明上一步漏了。
        """
        result = event.get_result()
        chain = getattr(result, "chain", None)
        if not chain:
            return

        notes_on = bool(self.conf.get("describe_images", True))
        keep, found, stamps = [], 0, 0
        for comp in chain:
            text = getattr(comp, "text", None)
            if not isinstance(text, str) or not text:
                keep.append(comp)
                continue
            out = text
            if notes_on and "<img_note" in out:
                found += self._harvest_notes(out)
                out = IMG_NOTE_RE.sub("", out)
            if OWN_STAMP_RE.search(out):
                stamps += 1
                out = OWN_STAMP_RE.sub("", out)
            if out == text:
                keep.append(comp)
                continue
            comp.text = out.strip()
            # 整条只有描述标记时剥完是空的，别把空消息发出去
            if comp.text:
                keep.append(comp)

        if found:
            logger.warning(f"[tg_presence] 发送前兜底剥掉 {found} 条图片描述")
        if stamps:
            logger.warning(f"[tg_presence] 发送前兜底剥掉 {stamps} 处她自写的时间戳")
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
        folder: str = "", prefer_sent: str = "", around: str = "", **_extra
    ):
        """在你自己的相册里翻，找一张想发给他的照片。想给他看点什么、或者他描述了某个画面让你找的时候用。返回一批候选，你自己挑一张，再用 send_photo 发出去。

        Args:
            keywords(string): 检索词，空格分隔，例如「酒店 灰丝 细高跟 M腿」。词尽量多给几个，命中越多排得越前，个别词没对上也不影响
            want(string): 可选，把想找的画面用一句话原样描述出来
            folder(string): 可选，限定某个相册分类
            prefer_sent(string): 他要的是最近发过的那张就填 recent，要没发过的新图就填 fresh，听不出来就留空（默认 fresh，免得老发同一张）
            around(string): 他提到某个月份就填，格式 YYYY-MM 或 MM，例如「三月那会儿的」填 03。那个月的图会整体排到前面。没提就留空
        """
        pool = max(10, int(self.conf.get("rank_pool", 60) or 60))
        rows = await self._recall(keywords, want, folder, pool)
        if not rows:
            stat = self.gallery_stat()
            if not stat["indexed"]:
                return "相册还没建好索引，现在挑不了。"
            return "没找到合适的。换几个词再翻翻，或者把想找的画面整句说出来。"

        # 召回之后按固定逻辑重排。纯计算，同一段词每次结果都一样
        ranked = self._rerank(rows, prefer_sent, around)
        top = max(1, int(self.conf.get("rank_return", 10) or 10))
        picked, by_model = ranked[:top], False

        # 只有填了 want 且显式开了 picker 才额外过一遍模型
        if want.strip() and self.conf.get("picker_enable", False) and len(picked) > 1:
            picked = await self._pick_best(want.strip(), picked, top=top)
            by_model = True

        lines = []
        for r in picked:
            tag = f"[{r['folder']}] " if r["folder"] else ""
            seen = f"发过{r['sent']}次" if r["sent"] else "没发过"
            lines.append(f"g{r['id']} · {tag}{seen}\n  {self._photo_brief(r['descr'])}")
        return (
            f"从 {len(rows)} 张候选里挑出这 {len(picked)} 张"
            + ("（模型逐张比对过）" if by_model else "")
            + "，越靠前越合适：\n"
            + "\n".join(lines)
            + "\n\n看不够就用 inspect_photo 加编号调出整篇描述再定。"
            + "\n挑好一张，用 send_photo 加编号发出去。"
        )

    @filter.llm_tool(name="inspect_photo")
    async def inspect_photo(self, event: AstrMessageEvent, photo_id: str = "", **_extra):
        """调出相册里某张照片的完整描述。browse_gallery 给的是摘要，拿不准哪张更合适、或者想确认某个细节在不在画面里的时候用这个细看。

        Args:
            photo_id(string): 相册编号，browse_gallery 列出来的那个 g123
        """
        raw = (photo_id or "").strip().lstrip("gG")
        if not raw.isdigit():
            return "编号得是 browse_gallery 给的那种 g123。"
        row = self.db().execute(
            "SELECT id, folder, descr, sent, last_sent FROM photos WHERE id = ?",
            (int(raw),),
        ).fetchone()
        if not row or not row["descr"]:
            return f"g{raw} 找不到，或者它还没建索引。"
        when = ""
        if row["last_sent"]:
            when = "，上次发是 " + datetime.fromtimestamp(
                row["last_sent"], self._tz()
            ).strftime("%m-%d")
        return (
            f"g{row['id']}"
            + (f"（{row['folder']}）" if row["folder"] else "")
            + f"，发过 {row['sent']} 次{when}：\n{row['descr']}"
        )

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
        self, event: AstrMessageEvent, photo_id: str, caption: str = ""
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

        note = ""
        if row is not None:
            self.db().execute(
                "UPDATE photos SET sent = sent + 1, last_sent = ? WHERE id = ?",
                (time.time(), row["id"]),
            )
            self.db().commit()
            # 让她自己也记住这张。不登记的话她发完就忘：下一句你说
            # 「刚那张真好看」她接不上，过两轮还可能把同一张再发一遍
            if pid := self._remember_sent(path, row["descr"] or "", f"g{row['id']}"):
                note = f" 在你们的对话里它是 #{pid}"

        # 记进她自己的历史，否则下一轮她不知道刚发过什么。
        # 用摘要不用原文：原文开头是"第一层：环境与背景"那套层标题，
        # 对她回忆自己发了什么毫无帮助，还占地方
        pid = pid if row is not None else raw.lstrip("#")
        raw_descr = (row["descr"] if row is not None else self.vision.get(pid, "")) or ""
        brief = self._photo_brief(raw_descr) if raw_descr else ""
        await self._log_action(
            event,
            f"我给他发了张照片。[图片 #{pid}]"
            + (f" 画面是：{brief}" if brief else "")
            + (f"\n我配的话：{caption.strip()}" if caption.strip() else ""),
        )
        logger.info(f"[tg_presence] 已发送照片 {raw} -> {path.name}")
        return f"照片发出去了（{raw}）。{note}"

    def _remember_sent(self, path: Path, descr: str, key: str) -> str | None:
        """把她刚发出去的图登记进图片记忆，跟对方发来的图一视同仁。

        图库里的图已经有现成的描述，直接搬过来当画面细节用，不用再花一次
        视觉 API。key 用 g123 这样的稳定串，同一张重发时编号不会变。
        """
        try:
            index = self.state.setdefault("photo_index", {})
            if key not in index:
                index[key] = str(len(index) + 1)
            pid = index[key]
            self.state.setdefault("photo_paths", {})[pid] = str(path)
            self._save_state()
            if descr and pid not in self.vision:
                self.vision[pid] = descr
                self._save_vision()
            return pid
        except (OSError, ValueError) as e:
            logger.warning(f"[tg_presence] 登记已发照片失败：{e}")
            return None

    @filter.command("photo")
    async def cmd_photo(self, event: AstrMessageEvent, photo_id: str = "", *, caption: str = ""):
        """手动发一张照片。用法：/photo g123 [附言]"""
        self._seal_command(event)
        if self.conf.get("admin_only_commands", True) and event.role != "admin":
            yield event.plain_result("只有管理员能用这个指令。发 /whoami 看是哪儿没对上。")
            return
        if not photo_id:
            yield event.plain_result("让她自己挑…")
            picked, said = await self._improvise_photo()
            if not picked:
                yield event.plain_result(said or "她没挑出来。直接指定：/photo g123 [附言]")
                return
            photo_id, caption = picked, (caption or said)
            yield event.plain_result(f"她挑了 {picked}" + (f"，配文：{said}" if said else ""))
        yield event.plain_result(
            await self._do_send_photo(event, photo_id, caption)
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
        photos = self._moment_photos(moment)
        if photos:
            # 只报"配图 N 张"的话，她知道发过图却不知道发的是什么，
            # 对方提起"你那张桌上的照片"就接不上。把描述一并带出来
            desc = [d for d in (self._photo_descr(p) for p in photos) if d]
            bits.append(
                f"配图 {len(photos)} 张"
                + ("：" + "；".join(d[:60] for d in desc[:3]) if desc else "")
            )
        if moment.get("quiet"):
            bits.append("当时没跟他提")
        return {"role": "assistant", "content": " · ".join(bits), "_no_save": True}

    def _photo_descr(self, path: str) -> str:
        """按文件路径找它的画面描述。图库里索引过的直接有，没有就返回空。"""
        if not path:
            return ""
        try:
            p = Path(path)
            key = str(p)
            if root := self._gallery_root():
                try:
                    key = p.resolve().relative_to(root.resolve()).as_posix()
                except (ValueError, OSError):
                    pass
            row = self.db().execute(
                "SELECT descr FROM photos WHERE path = ? OR path = ?", (key, str(p))
            ).fetchone()
            return self._photo_brief(row["descr"]) if row and row["descr"] else ""
        except sqlite3.Error as e:
            logger.debug(f"[tg_presence] 查配图描述失败 {path}: {e}")
            return ""

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
            yield event.plain_result("让她自己想…")
            text, err = await self._improvise(
                self._prompt_of("improvise_moment", DEFAULT_IMP_MOMENT)
            )
            if not text:
                yield event.plain_result(f"没想出来：{err}\n直接给内容也行：/moment 正文")
                return
            yield event.plain_result(f"她想发：\n{text}")
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
        await self._log_action(
            event,
            "我换了头像"
            + (f"，从「{category}」里挑的" if category else "")
            + f"（{pic.name}）。头像换了没有通知，他不点开我资料是看不到的。",
        )
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
        if not category:
            cats = self._list_categories(self.conf.get("avatar_dir") or "")
            if cats:
                yield event.plain_result("让她自己挑…")
                pick, err = await self._improvise(
                    self._prompt_of(
                        "improvise_avatar", DEFAULT_IMP_AVATAR, cats="、".join(cats)
                    )
                )
                # 她可能连着说一句话，只认里面出现的那个类别名
                hit = next((c for c in cats if c and c in (pick or "")), "")
                if hit:
                    category = hit
                    yield event.plain_result(f"她挑了：{hit}")
                elif err:
                    yield event.plain_result(f"她没挑成：{err}\n随机来一张")
                else:
                    yield event.plain_result(f"她没挑出来（回的是「{pick[:20]}」），随机来一张")
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

        await self._log_action(
            event,
            f"我把个性签名改成了：{text.strip()}"
            + ("（没打算跟他提）" if quiet else ""),
        )
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
            yield event.plain_result("让她自己想…")
            text, err = await self._improvise(
                self._prompt_of(
                    "improvise_signature", DEFAULT_IMP_SIGNATURE, max=SIGNATURE_MAX // 2
                )
            )
            if not text:
                yield event.plain_result(f"没想出来：{err}\n直接给内容也行：/signature 新签名")
                return
            yield event.plain_result(f"她想改成：\n{text}")
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
        here = self._platform_of(event)
        # 插件自带的控制台天生就是"另一头"，不用再对机器人名称
        if here != "console":
            did = self._director_id()
            if not did:
                return (
                    "没配控制台。两种办法：在插件配置里填「控制台 Bot Token」"
                    "用插件自带的控制台，或者填「控制台机器人名称」"
                    "沿用 AstrBot 里接入的另一个 bot。"
                )
            if here != did:
                return "这条指令只能在控制台里发——在这儿发等于当着他的面喊话。"
        target = (self.state.get("director_target") or "").strip()
        if not target:
            return (
                "还没绑定目标会话。\n"
                "在这儿发：/link 角色机器人名称:FriendMessage:会话ID"
            )
        if self._umo_platform(target) in ("console", self._director_id() or "\0"):
            # 目标绑到控制台自己的话，消息会发回控制台、历史也写进控制台的会话，
            # 角色那边什么都没有，但看着像成功了
            return (
                f"投递目标绑到控制台自己了：\n{target}\n\n"
                "重新绑：/link 角色机器人名称:FriendMessage:会话ID"
            )
        return None

    async def _log_action(self, event, text: str) -> None:
        """把她刚做的事记进她自己的对话历史。

        发照片、换头像、改签名这些动作，做完之后在她那边不留任何痕迹——
        下一轮她既不知道自己发过什么，也不知道头像换成了哪张，
        你提起时她只能装。从控制台执行时尤其明显：连工具回执都没有。

        动态不走这儿：它有 inject_moments 按时间线注回上下文，
        再写一条历史就成了同一件事说两遍。
        """
        umo = (getattr(event, "unified_msg_origin", "") or "").strip()
        if not umo or self._umo_platform(umo) == "console":
            return
        try:
            await self._append_assistant(umo, text)
        except Exception as e:
            logger.warning(f"[tg_presence] 记录动作失败：{e}")

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

    @staticmethod
    def _persona_prompt(p) -> str:
        """从人格对象里取出正文。

        字段名有两套：AstrBot 内部的 Persona 用 system_prompt，而
        persona_manager 对外给的 v3 形态用 prompt——
        get_v3_persona_data 里明摆着写的 {"prompt": persona.system_prompt}。
        而且 v3 可能是 dict 也可能是对象，dict 用 getattr 取永远是空。
        两套字段名、两种容器都认，才不会白白丢掉人格。
        """
        if not p:
            return ""
        if isinstance(p, dict):
            return str(p.get("prompt") or p.get("system_prompt") or "").strip()
        for attr in ("prompt", "system_prompt"):
            if v := getattr(p, attr, None):
                return str(v).strip()
        return ""

    async def _persona_of(self, umo: str, conv=None) -> str:
        """解析这个会话最终生效的人格正文。取不到返回空串。"""
        pm = getattr(self.context, "persona_manager", None)
        if pm is None:
            return ""
        pid = getattr(conv, "persona_id", None) if conv else None

        # 优先走官方的解析入口：它还会考虑会话级强制人格（/persona 设的那个），
        # 那是 conversation.persona_id 看不到的一层
        if resolve := getattr(pm, "resolve_selected_persona", None):
            try:
                cfg = self.context.astrbot_config_mgr.get_conf(umo)
                _, persona, _, _ = await resolve(
                    umo=umo,
                    conversation_persona_id=pid,
                    platform_name=self._umo_platform(umo),
                    provider_settings=(cfg or {}).get("provider_settings", {}),
                )
                if text := self._persona_prompt(persona):
                    logger.debug(f"[tg_presence] 人格来自 resolve，{len(text)} 字")
                    return text
            except Exception as e:
                logger.debug(f"[tg_presence] resolve_selected_persona 用不了：{e}")

        try:
            p = pm.get_persona_v3_by_id(pid) if pid else None
            if p is None:
                p = await pm.get_default_persona_v3(umo=umo)
            text = self._persona_prompt(p)
            if text:
                name = p.get("name") if isinstance(p, dict) else getattr(p, "name", "?")
                logger.debug(f"[tg_presence] 人格「{name}」{len(text)} 字")
            return text
        except Exception as e:
            logger.warning(f"[tg_presence] 取人格失败，这次不带人格生成：{e}")
            return ""

    async def _improvise(self, prompt: str) -> tuple[str, str]:
        """让她自己想内容。返回 (内容, 没成的原因)。

        指令后面留空时走这条路：与其让人再想一遍措辞，不如让她自己拿主意
        ——反正内容本来就该是她的。

        原因必须带出来。吞掉异常只回一句"模型返回空"，会把配置错、
        没绑会话、模型拒答这三种完全不同的毛病显示成同一句话，
        人就只能去翻日志。
        """
        if not (self.state.get("director_target") or "").strip():
            return "", "还没绑定目标会话，取不到她的人格和历史。先 /umo 看看有哪些，再 /link 绑一个"
        try:
            now = datetime.now(self._tz()).strftime("%m-%d %H:%M")
            # instruct 传空串：要求已经写在 prompt 里了，别再叠一句"发条消息给他"
            text = await self._director_generate(f"现在是 {now}。{prompt}", "")
        except Exception as e:
            logger.error(f"[tg_presence] 即兴生成失败：{e}", exc_info=True)
            return "", f"{type(e).__name__}: {e}"
        if not text:
            return "", "模型返回了空内容（可能是拒答，或者上下文里有它处理不了的东西）"
        return text, ""

    async def _improvise_photo(self) -> tuple[str, str]:
        """让她自己从相册里挑一张，顺带写句配文。返回 (gN, 配文)。

        分两步：先让她说想发什么样的（几个短语），拿这些词去检索，
        取排最前的那张。不直接把候选列表塞给她——那要先检索一遍才有
        候选，而检索本身就需要她先说出想要什么。
        """
        if not self.gallery_stat()["indexed"]:
            return "", "相册还没建索引，挑不了。先 /gallery index auto。"
        raw, err = await self._improvise(
            self._prompt_of("improvise_photo", DEFAULT_IMP_PHOTO)
        )
        if not raw:
            return "", f"没想出来：{err}"
        parts = [x.strip() for x in raw.splitlines() if x.strip()]
        words = parts[0].replace("，", ",").replace(",", " ") if parts else ""
        caption = parts[1] if len(parts) > 1 else ""
        if not words:
            return "", "她没说清想发什么样的。"

        pool = max(10, int(self.conf.get("rank_pool", 60) or 60))
        rows = await self._recall(words, "", "", pool)
        if not rows:
            return "", f"她想找「{parts[0][:30]}」，但库里没有对得上的。"
        # 默认偏好没发过的，免得老发同一张
        best = self._rerank(rows, "fresh")[0]
        return f"g{best['id']}", caption

    def _prompt_of(self, key: str, default: str, **fmt) -> str:
        """取一段可配置的提示词，填好占位符。

        留空是"用默认"而不是"不要"——AstrBot 的配置里没配和填空串是
        同一个值，分不开。真想去掉某一段就填「无」，那是显式的关掉。
        """
        tpl = (self.conf.get(key) or "").strip()
        if tpl in ("无", "-", "none", "None", "NONE"):
            return ""
        tpl = tpl or default
        if not fmt:
            return tpl
        try:
            return tpl.format(**fmt)
        except (KeyError, IndexError, ValueError) as e:
            # 占位符写错不该让整条指令瘫掉，原样用还能跑
            logger.warning(f"[tg_presence] 提示词「{key}」的占位符有问题（{e}），按原文用")
            return tpl

    async def _director_generate(self, brief: str, instruct: str | None = None) -> str:
        """按导演提示，用角色的人格和历史生成一段文本。抛异常给调用方。

        instruct 决定生成什么：None 用配置里那句默认的（/act 走这条），
        空串表示 brief 里已经把要求写全了（四条留空指令走这条）。
        人格和历史是共用的——不管让她做什么，都得是她来做。
        """
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

        system_prompt = await self._persona_of(target, conv)
        if not system_prompt:
            logger.warning(
                "[tg_presence] 没拿到人格，这次只靠历史模仿语气——"
                "人格里的硬设定（背景、行为准则、禁忌）都不会生效"
            )

        provider_id = await self.context.get_current_chat_provider_id(target)
        ctx = history[-limit:] if isinstance(history, list) else []
        # instruct 传 None 表示"用默认那句"（/act 走这条），
        # 传空串表示 brief 里已经把要求写全了（四条留空指令走这条）
        act = self._prompt_of("director_act", DEFAULT_DIRECTOR_ACT) if instruct is None else instruct
        head = self._prompt_of("director_head", DEFAULT_DIRECTOR_HEAD)
        head = head + "\n" if head else ""
        tail = self._prompt_of("director_tail", DEFAULT_DIRECTOR_TAIL)
        tail = "\n" + tail if tail else ""

        async def call(prompt: str) -> str:
            resp = await self.context.llm_generate(
                chat_provider_id=provider_id,
                system_prompt=system_prompt,
                contexts=ctx,
                prompt=prompt,
            )
            got = (getattr(resp, "completion_text", "") or "").strip()
            if got:
                return got

            # 返空时把整个响应对象摊开记下来。这种失败不抛异常、
            # 日志里一片空白，不留证据只能靠猜。thinking 模型尤其要看
            # reasoning_content——正文空而思考满，说明配额全烧在思考上了
            try:
                dump = {
                    k: (v if isinstance(v, (int, float, bool, type(None))) else str(v))
                    for k, v in vars(resp).items()
                }
            except Exception:  # dataclass 用了 __slots__ 之类
                dump = {
                    k: str(getattr(resp, k, None))
                    for k in (
                        "_completion_text", "reasoning_content", "role",
                        "tools_call_name", "raw_completion", "usage", "id",
                    )
                }
            reason = str(dump.get("reasoning_content") or "")
            logger.warning(
                f"[tg_presence] 导演生成返回空。provider={provider_id} "
                f"人格 {len(system_prompt)} 字 · 历史 {len(ctx)} 条 · "
                f"提示 {len(prompt)} 字"
                + (f" · 思考 {len(reason)} 字" if reason else " · 思考也是空的")
            )
            for k, v in dump.items():
                if v not in (None, "", "[]", "{}", "None"):
                    logger.warning(f"[tg_presence]   {k} = {str(v)[:600]}")
            return ""

        body = f"{brief}\n\n{act}" if act else brief
        text = await call(head + body + tail)
        if not text:
            # 还是空，多半还是奔着调工具去了。把话说死再来一次
            logger.info("[tg_presence] 返空，改用更硬的措辞重试一次")
            retry = self._prompt_of("director_retry", DEFAULT_DIRECTOR_RETRY)
            text = await call(f"{body}\n\n{retry}" if retry else body)

        # 她还是会写时间戳的话在这儿剥掉。导演这条路不经过 AstrBot 管线，
        # on_llm_response / on_decorating_result 那两道闸都够不着
        if OWN_STAMP_RE.search(text):
            logger.info("[tg_presence] 剥掉她在导演回复里自写的时间戳")
            text = OWN_STAMP_RE.sub("", text).strip()
        return text

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

    async def _peek_conv_obj(self, umo: str):
        """取目标会话的 conversation 对象，用来读它绑的人格。取不到返回 None。"""
        cm = getattr(self.context, "conversation_manager", None)
        if cm is None:
            return None
        try:
            cid = await cm.get_curr_conversation_id(umo)
            return await cm.get_conversation(umo, cid) if cid else None
        except Exception as e:
            logger.debug(f"[tg_presence] 取对话对象失败 {umo}: {e}")
            return None

    @filter.command("umo")
    async def cmd_umo(self, event: AstrMessageEvent, arg: str = ""):
        """列出所有会话的 UMO，用来挑一个 /link 绑上。用法：/umo [关键词]"""
        self._seal_command(event)
        if self.conf.get("admin_only_commands", True) and event.role != "admin":
            yield event.plain_result("只有管理员能用这个指令。发 /whoami 看是哪儿没对上。")
            return

        cm = getattr(self.context, "conversation_manager", None)
        if cm is None or not hasattr(cm, "get_filtered_conversations"):
            yield event.plain_result(
                "这个 AstrBot 版本列不出会话清单。\n"
                "手动拼：机器人名称:FriendMessage:会话ID\n"
                "机器人名称看 WebUI「平台配置」第一项，会话ID 在那个会话里发 /whoami 看。"
            )
            return

        kw = (arg or "").strip()
        try:
            convs, total = await cm.get_filtered_conversations(
                page=1, page_size=60, search_query=kw, include_history=False
            )
        except Exception as e:
            logger.error(f"[tg_presence] 列会话失败：{e}")
            yield event.plain_result(f"列不出来：{e}")
            return
        if not convs:
            yield event.plain_result(
                f"没有{'匹配「' + kw + '」的' if kw else ''}会话。"
                + ("\n换个词，或者直接 /umo 看全部。" if kw else "\n先在角色那边正常聊一句，对话才会建起来。")
            )
            return

        cur = (self.state.get("director_target") or "").strip()
        did = self._director_id()
        tz = self._tz()
        # 同一个会话可能有多个对话（AstrBot 支持一个会话开多轮），
        # 这里只关心 UMO，按会话归并，取最近活跃的那条
        seen: dict[str, dict] = {}
        skipped = 0
        for c in convs:
            umo = getattr(c, "user_id", "") or ""
            if not umo:
                continue
            # 控制台自己的会话不列——绑它没意义，只会挤占列表
            if self._umo_platform(umo) in ("console", did or "\0"):
                skipped += 1
                continue
            ts = int(getattr(c, "updated_at", 0) or 0)
            got = seen.setdefault(umo, {"ts": 0, "n": 0, "title": ""})
            got["n"] += 1
            if ts >= got["ts"]:
                got["ts"] = ts
                got["title"] = (getattr(c, "title", "") or "").strip()

        rows = sorted(seen.items(), key=lambda kv: -kv[1]["ts"])
        if not rows:
            yield event.plain_result(
                "除了控制台自己，没有别的会话。\n"
                "先在角色那边正常聊一句，对话建起来才能绑。"
            )
            return

        lines = [f"共 {len(rows)} 个会话："]
        for umo, info in rows[:25]:
            mark = "  ← 当前绑定" if umo == cur else ""
            when = (
                datetime.fromtimestamp(info["ts"], tz).strftime("%m-%d %H:%M")
                if info["ts"]
                else "时间未知"
            )
            lines.append(f"\n{umo}{mark}")
            detail = f"  {when}"
            if info["n"] > 1:
                detail += f" · {info['n']} 个对话"
            if info["title"]:
                detail += f" · {info['title'][:18]}"
            lines.append(detail)
        if len(rows) > 25:
            lines.append(f"\n…还有 {len(rows) - 25} 个，用 /umo 关键词 缩小范围")
        lines.append("\n绑定：/link 上面任意一个 UMO")
        yield event.plain_result("\n".join(lines))

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
                # 人格取不到时，/act 和主动消息只能靠历史模仿语气，
                # 人格里的硬设定一条都不生效——这事不报出来根本发现不了
                persona = await self._persona_of(cur, await self._peek_conv_obj(cur))
                lines.append(
                    f"人格：    {'读到 ' + str(len(persona)) + ' 字' if persona else '⚠️ 没读到，/act 会不像她'}"
                )
            lines += [
                "",
                "/umo          列出所有会话，从里面挑一个",
                # 别用尖括号占位：Telegram 按 HTML 解析，<UMO> 会被当成标签整段吃掉
                "/link 目标UMO  绑上它",
                "",
                "多个角色就靠这两条来回切：绑谁，/say 和 /act 就发给谁。",
            ]
            yield event.plain_result("\n".join(lines))
            return

        # 绑定只在控制台做 —— 在角色那边发指令会在你俩的聊天记录里留痕，
        # 那正是导演模式要避免的事。插件自带的控制台天生就是"另一头"
        if here != "console":
            if not did:
                yield event.plain_result(
                    "先配一个控制台再来绑定。两种办法：\n"
                    "  填「控制台 Bot Token」用插件自带的（推荐，不占 AstrBot 通道）\n"
                    "  或填「控制台机器人名称」，沿用 AstrBot 里接入的另一个 bot"
                )
                return
            if here != did:
                yield event.plain_result(
                    "这条指令只能在控制台里发。\n"
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

        if self._umo_platform(arg) in ("console", did or "\0"):
            yield event.plain_result(
                f"这是控制台自己（{self._umo_platform(arg)}），绑它没意义——"
                "消息会发回控制台，角色那边什么都收不到。\n"
                "第一段要填角色那个 bot 的机器人名称，/umo 能列出来。"
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

    # ------------------------------------------------------- 插件自带的控制台

    def _console_admins(self) -> set[str]:
        raw = (self.conf.get("console_admins") or "").replace("，", ",")
        return {x.strip() for x in raw.split(",") if x.strip()}

    async def _tg_api(self, method: str, timeout: int = 15, **params):
        """直接打 Telegram Bot API。控制台不经过 AstrBot 的平台系统。"""
        token = (self.conf.get("console_token") or "").strip()
        if not token:
            return None
        url = f"https://api.telegram.org/bot{token}/{method}"
        try:
            async with aiohttp.ClientSession(
                timeout=aiohttp.ClientTimeout(total=timeout)
            ) as sess:
                async with sess.post(url, json=params) as r:
                    data = await r.json()
            if not data.get("ok"):
                logger.warning(f"[tg_presence] 控制台 {method} 失败：{data.get('description')}")
                return None
            return data.get("result")
        except asyncio.TimeoutError:
            return None
        except Exception as e:
            logger.warning(f"[tg_presence] 控制台 {method} 出错：{e}")
            return None

    async def _console_say(self, chat_id, text: str) -> None:
        """回消息。超过 Telegram 单条上限就切开发。"""
        for i in range(0, len(text), 3800):
            await self._tg_api("sendMessage", chat_id=chat_id, text=text[i : i + 3800])

    @staticmethod
    def _bind_args(func, rest: str) -> tuple[list, dict]:
        """按 handler 的签名把参数切出来，规则跟 AstrBot 那套对齐。

        位置参数一个词一个，keyword-only（写在 * 之后的那个）吃掉剩下的
        全部文本——所以 /gallery index auto 会切成 action='index'、rest='auto'，
        而 /act 后面整句话都进 brief。
        """
        args: list = []
        kwargs: dict = {}
        remain = (rest or "").strip()
        for name, p in inspect.signature(func).parameters.items():
            if name in ("self", "event"):
                continue
            if p.kind is p.KEYWORD_ONLY:
                kwargs[name] = remain
                remain = ""
            elif p.kind is p.VAR_KEYWORD:
                continue
            elif remain:
                head, _, remain = remain.partition(" ")
                args.append(head)
                remain = remain.strip()
            # 位置参数没东西可填就跳过它用默认值，但不能就此收手——
            # /gallery 不带参数时，后面那个 keyword-only 的 rest 还等着赋值
        return args, kwargs

    async def _console_run(self, chat_id, uid: str, text: str) -> None:
        """把控制台收到的一行指令交给对应的 handler，回复原样转发回去。"""
        name, _, rest = text[1:].partition(" ")
        name = name.split("@", 1)[0].strip().lower()  # /gallery@mybot 也认
        handler = CONSOLE_ROUTES.get(name)
        if handler is None:
            await self._console_say(
                chat_id,
                f"没有 /{name} 这个指令。\n可用：" + "、".join(f"/{k}" for k in CONSOLE_ROUTES),
            )
            return

        func = getattr(self, handler)
        if name in CONSOLE_AS_TARGET:
            target = (self.state.get("director_target") or "").strip()
            if not target:
                await self._console_say(
                    chat_id,
                    f"/{name} 要以角色的身份执行，得先知道是哪个角色。\n"
                    "/umo 看有哪些会话，/link 绑一个。",
                )
                return
            client = self._platform_client(target)
            if client is None:
                await self._console_say(
                    chat_id,
                    f"找不到 {self._umo_platform(target)} 这个 bot 的连接。\n"
                    "它在 AstrBot 平台配置里还开着吗？只有 telegram 平台支持这条指令。",
                )
                return
            ev = ConsoleEvent(uid, chat_id, umo=target, client=client)
        else:
            ev = ConsoleEvent(uid, chat_id)
        try:
            args, kwargs = self._bind_args(func, rest)
            async for _ in func(ev, *args, **kwargs):
                # handler 是 async generator，每 yield 一次就回一条
                while ev.replies:
                    await self._console_say(chat_id, ev.replies.pop(0))
        except Exception as e:
            logger.error(f"[tg_presence] 控制台执行 /{name} 出错：{e}", exc_info=True)
            await self._console_say(chat_id, f"执行 /{name} 出错：{e}")
            return
        while ev.replies:
            await self._console_say(chat_id, ev.replies.pop(0))

    async def _console_loop(self) -> None:
        """长轮询收指令。跟 AstrBot 的平台系统完全无关，不会跟它抢 getUpdates。"""
        offset = 0
        # 起来先把积压的旧消息丢掉，免得重启后把几小时前的指令重跑一遍
        if backlog := await self._tg_api("getUpdates", timeout=10, offset=-1, limit=1):
            offset = backlog[-1]["update_id"] + 1
        me = await self._tg_api("getMe", timeout=10)
        # 注册指令菜单，输入 / 就有提示，不用记
        ok = await self._tg_api(
            "setMyCommands",
            timeout=10,
            commands=[{"command": c, "description": d} for c, d in CONSOLE_MENU],
        )
        logger.info(
            f"[tg_presence] 控制台已上线：@{(me or {}).get('username', '?')}，"
            f"管理员 {len(self._console_admins())} 人"
            + ("，指令菜单已注册" if ok else "")
        )
        while True:
            try:
                updates = await self._tg_api(
                    "getUpdates", timeout=40, offset=offset, limit=20, allowed_updates=["message"]
                )
                if not updates:
                    await asyncio.sleep(3)
                    continue
                for u in updates:
                    offset = max(offset, u.get("update_id", 0) + 1)
                    msg = u.get("message") or {}
                    text = (msg.get("text") or "").strip()
                    if not text.startswith("/"):
                        continue
                    uid = str((msg.get("from") or {}).get("id", ""))
                    chat = (msg.get("chat") or {}).get("id")
                    admins = self._console_admins()
                    if not admins:
                        logger.warning(
                            f"[tg_presence] 控制台没配管理员，忽略来自 ID {uid} 的消息。"
                            "在「控制台管理员 ID」里填上你自己的 ID 才会响应"
                        )
                        continue
                    if uid not in admins:
                        logger.warning(f"[tg_presence] 控制台收到非管理员消息，来自 ID {uid}")
                        continue
                    await self._console_run(chat, uid, text)
            except asyncio.CancelledError:
                raise
            except Exception as e:
                logger.error(f"[tg_presence] 控制台轮询出错：{e}")
                await asyncio.sleep(10)

    def _ensure_console(self) -> None:
        """懒启动控制台。没填 token 就不起。"""
        if not (self.conf.get("console_token") or "").strip():
            return
        if self._console_task and not self._console_task.done():
            return
        try:
            self._console_task = asyncio.create_task(self._console_loop())
        except RuntimeError:
            pass

    # --------------------------------------------------------------- 主动消息

    def _next_gap(self) -> float:
        """摇一个新的倒计时。

        随机而不是固定周期——固定的话几天就被看出来了，随机才像
        「想起你」而不是「定时任务」。
        """
        lo = float(self.conf.get("proactive_min_hours", 4) or 4)
        hi = float(self.conf.get("proactive_max_hours", 14) or 14)
        if hi < lo:
            lo, hi = hi, lo
        return max(60.0, random.uniform(lo, hi) * 3600)

    def _touch_proactive(self, umo: str) -> None:
        """他一说话就重排倒计时，未回复计数清零。"""
        st = self.state.setdefault("proactive", {})
        now = time.time()
        st.update({"last_user": now, "unanswered": 0, "due": now + self._next_gap(), "umo": umo})
        self._save_state()

    def _in_quiet(self) -> bool:
        """现在是不是静默时段。支持跨零点，如 23:30-08:30。"""
        raw = (self.conf.get("proactive_quiet") or "").strip()
        if "-" not in raw:
            return False
        try:
            a, b = (x.strip() for x in raw.split("-", 1))
            ah, am = (int(x) for x in a.split(":"))
            bh, bm = (int(x) for x in b.split(":"))
        except ValueError:
            logger.warning(f"[tg_presence] 静默时段「{raw}」格式不对，按不静默处理")
            return False
        now = datetime.now(self._tz())
        cur, start, end = now.hour * 60 + now.minute, ah * 60 + am, bh * 60 + bm
        return start <= cur < end if start <= end else (cur >= start or cur < end)

    @staticmethod
    def _human_gap(sec: float) -> str:
        h = sec / 3600
        if h < 1:
            return f"{int(sec // 60)} 分钟"
        return f"{h:.0f} 小时" if h < 48 else f"{h / 24:.1f} 天"

    def _proactive_brief(self) -> str:
        """把提示词模板填上时间和未回复次数。"""
        st = self.state.get("proactive") or {}
        tz, now = self._tz(), time.time()
        last = st.get("last_user")
        tpl = (self.conf.get("proactive_prompt") or "").strip() or (
            "你跟他上一次说话是 {last}（距今 {gap}），现在是 {now}。你现在要主动联系他。"
            "回复必须完全符合你的人格设定，是继续之前的话题、开始新话题，"
            "还是说说你今天遇到的事，由你自己决定。"
        )
        n = int(st.get("unanswered", 0) or 0)
        brief = tpl.format(
            last=datetime.fromtimestamp(last, tz).strftime("%m-%d %H:%M") if last else "不记得了",
            now=datetime.now(tz).strftime("%m-%d %H:%M"),
            gap=self._human_gap(now - last) if last else "很久",
            n=n,
        )
        if n:
            # 连着没等到回音，得让她自己知道，否则会写得像什么都没发生过
            brief += (
                f"\n注意：你已经连着主动找过他 {n} 次，他一次都没回。"
                "这一条要体现出你察觉到了，别装作前面没发生过。"
            )
        return brief

    async def _proactive_fire(self) -> str:
        """生成并发出一条主动消息。返回结果说明，给指令回显用。"""
        st = self.state.setdefault("proactive", {})
        try:
            text = await self._director_generate(self._proactive_brief())
        except Exception as e:
            logger.error(f"[tg_presence] 主动消息生成失败：{e}", exc_info=True)
            st["due"] = time.time() + 1800  # 半小时后再试，别把这次倒计时白扔
            self._save_state()
            return f"生成失败：{type(e).__name__}: {e}"
        if not text:
            st["due"] = time.time() + 1800
            self._save_state()
            return "模型返回空，没发。"

        out = await self._director_deliver(text)
        st["unanswered"] = int(st.get("unanswered", 0) or 0) + 1
        st["due"] = time.time() + self._next_gap()
        st["last_fire"] = time.time()
        self._save_state()
        logger.info(f"[tg_presence] 主动消息已发（第 {st['unanswered']} 次未获回复）：{text[:40]}")
        return out

    async def _proactive_loop(self) -> None:
        """倒计时到点就让她开口。一分钟查一次——倒计时是小时级的，够用。"""
        while True:
            await asyncio.sleep(60)
            try:
                if not self.conf.get("proactive_enable", False):
                    continue
                st = self.state.get("proactive") or {}
                due = st.get("due")
                if not due or time.time() < due:
                    continue
                if self._in_quiet():
                    continue  # 不取消，等出了静默时段立刻发
                cap = int(self.conf.get("proactive_max_unanswered", 3) or 0)
                if cap > 0 and int(st.get("unanswered", 0) or 0) >= cap:
                    continue  # 停下来等他，他一回复就清零
                if not (self.state.get("director_target") or "").strip():
                    logger.warning("[tg_presence] 主动消息到点了，但还没 /link 绑定目标会话")
                    st["due"] = time.time() + 3600
                    self._save_state()
                    continue
                await self._proactive_fire()
            except asyncio.CancelledError:
                raise
            except Exception as e:
                logger.error(f"[tg_presence] 主动消息循环出错：{e}")

    def _ensure_proactive(self) -> None:
        """懒启动倒计时循环。__init__ 时不一定有事件循环，这里才有。"""
        if self._proactive_task and not self._proactive_task.done():
            return
        try:
            self._proactive_task = asyncio.create_task(self._proactive_loop())
        except RuntimeError:
            pass

    @filter.on_llm_request(priority=-95)
    async def note_user_activity(self, event: AstrMessageEvent, req: ProviderRequest):
        """他一开口就重排倒计时。控制台那边的指令不算互动。"""
        umo = event.unified_msg_origin
        if self._umo_platform(umo) == self._director_id():
            return
        self._ensure_proactive()
        self._ensure_console()  # initialize 没被调到时的兜底
        if self.conf.get("proactive_enable", False):
            self._touch_proactive(umo)

    @filter.command("proactive")
    async def cmd_proactive(self, event: AstrMessageEvent, arg: str = ""):
        """看主动消息的倒计时状态。用法：/proactive [now]"""
        self._seal_command(event)
        if self.conf.get("admin_only_commands", True) and event.role != "admin":
            yield event.plain_result("只有管理员能用这个指令。发 /whoami 看是哪儿没对上。")
            return

        st = self.state.get("proactive") or {}
        on = bool(self.conf.get("proactive_enable", False))
        tz, now = self._tz(), time.time()

        if arg.strip().lower() in ("now", "试试", "立刻"):
            if err := self._director_guard(event):
                yield event.plain_result(err)
                return
            yield event.plain_result("让她想想…")
            yield event.plain_result(await self._proactive_fire())
            return

        lines = [f"主动消息：{'开' if on else '关'}"]
        if last := st.get("last_user"):
            lines.append(
                f"他上次说话：{datetime.fromtimestamp(last, tz).strftime('%m-%d %H:%M')}"
                f"（{self._human_gap(now - last)}前）"
            )
        if due := st.get("due"):
            left = due - now
            lines.append(
                f"下次开口：{datetime.fromtimestamp(due, tz).strftime('%m-%d %H:%M')}"
                + (f"（还有 {self._human_gap(left)}）" if left > 0 else "（已到点）")
            )
        else:
            lines.append("下次开口：还没排（等他先说一句话）")
        n = int(st.get("unanswered", 0) or 0)
        cap = int(self.conf.get("proactive_max_unanswered", 3) or 0)
        if n:
            lines.append(f"连续未获回复：{n} 次" + (f"，满 {cap} 次就停" if cap else ""))
        if self._in_quiet():
            lines.append(f"⏸ 正在静默时段（{self.conf.get('proactive_quiet')}），到点也不发")
        if not (self.state.get("director_target") or "").strip():
            lines.append("⚠️ 还没绑定目标会话，发不出去。先在控制台 /link")
        lines.append(f"间隔范围：{self.conf.get('proactive_min_hours', 4)}"
                     f"~{self.conf.get('proactive_max_hours', 14)} 小时随机")
        lines.append("\n/proactive now 立刻让她发一条（不等倒计时）")
        yield event.plain_result("\n".join(lines))

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
            logger.error(f"[tg_presence] 导演生成失败: {e}", exc_info=True)
            yield event.plain_result(f"生成失败：{type(e).__name__}: {e}")
            return
        if not text:
            yield event.plain_result(
                "她没说出话来——模型返回了空内容。\n"
                "可能是拒答，也可能是上下文里有它处理不了的东西。"
                "换个提示试试，或者 /link show 看人格读到没有。"
            )
            return
        yield event.plain_result(await self._director_deliver(text))

    @filter.command("gallery")
    async def cmd_gallery(
        self, event: AstrMessageEvent, action: str = "", *, rest: str = ""
    ):
        """管理相册索引。用法：/gallery [scan|index N|search 词|embed N|audit|redo|retry]"""
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
            if self._embed_conf():
                segs = ", ".join(f"SUM({c} IS NOT NULL)" for c in VEC_SEGS)
                v = self.db().execute(
                    f"SELECT SUM(descr IS NOT NULL AND vec IS NULL) b, {segs} FROM photos"
                ).fetchone()
                got = " / ".join(
                    f"{c.removeprefix('vec_') if c != 'vec' else '全文'} {v[i + 1] or 0}"
                    for i, c in enumerate(VEC_SEGS)
                )
                lines.append(f"语义向量：{got} · 待转 {v['b'] or 0} 张")
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

        if action == "embed":
            db = self.db()
            if not self._embed_conf():
                yield event.plain_result(
                    "没配向量模型。填「向量模型 ID」那一项，地址和 Key 留空会复用视觉 API 的。\n"
                    "注意 Anthropic 不提供向量服务，视觉用 anthropic 格式的话要单独填地址。"
                )
                return
            arg = rest.strip().lower()
            if arg == "test":
                # 光看「有没有报错」不够：内容策略更常见的表现不是拒绝，
                # 而是照常返回向量、但对敏感内容的区分度塌掉。
                # 拿三段文本探一下——两段同类不同细节，一段完全无关。
                probes = [
                    "卧室床上仰躺，穿黑色丝袜，双腿M型大开，小阴唇外翻蝴蝶形，"
                    "阴道口微张有透明淫水，阴蒂从包皮露出",
                    "浴室里站着，白色丝袜半脱到膝盖，背对镜头翘臀，"
                    "肛门闭合周围干净，没有插入物",
                    "厨房灶台前系着围裙切西红柿，砧板上有青菜，窗外是白天",
                ]
                try:
                    vs = await self._embed(probes)
                except VisionError as e:
                    yield event.plain_result(
                        f"调不通：{e}\n"
                        "401 是 Key 错，404 多半是地址或模型 ID 错。\n"
                        "Gemini 要填 https://generativelanguage.googleapis.com/v1beta/openai"
                    )
                    return
                if not vs or len(vs) != 3:
                    yield event.plain_result(f"返回条数不对（{len(vs or [])}/3），接口有问题。")
                    return

                def cos(a, b):
                    import math
                    d = sum(x * y for x, y in zip(a, b))
                    na = math.sqrt(sum(x * x for x in a)) or 1
                    nb = math.sqrt(sum(x * x for x in b)) or 1
                    return d / (na * nb)

                s12, s13 = cos(vs[0], vs[1]), cos(vs[0], vs[2])
                gap = s12 - s13
                lines = [
                    f"通了。维度 {len(vs[0])}，配置写的 {self._embed_conf()['dim']}"
                    + ("  ⚠️ 对不上，按实际维度改配置" if len(vs[0]) != self._embed_conf()["dim"] else ""),
                    "",
                    f"两段露骨描述之间   相似度 {s12:.3f}",
                    f"露骨 vs 厨房做饭   相似度 {s13:.3f}",
                    f"区分度             {gap:.3f}",
                ]
                if len(set(len(v) for v in vs)) > 1:
                    lines.append("\n❌ 三条维度不一致，接口异常。")
                elif gap < 0.05:
                    lines.append(
                        "\n❌ 区分度几乎为零——露骨内容和做饭被编码得差不多。\n"
                        "这个模型对这类文本没有有效表示，检索会一直不准。换一个。"
                    )
                elif gap < 0.15:
                    lines.append(
                        "\n⚠️ 区分度偏低，语义检索效果会打折。可以先跑 200 条看看实际效果。"
                    )
                else:
                    lines.append("\n✅ 区分度正常，可以放量。")
                yield event.plain_result("\n".join(lines))
                return

            if arg == "redo":
                sets = ", ".join(f"{c} = NULL" for c in VEC_SEGS)
                n = db.execute(f"UPDATE photos SET {sets}").rowcount
                db.commit()
                self._vec_cache.clear()
                yield event.plain_result(
                    f"已清空 {n} 条向量的全部分段（换了模型或维度就该这样）。"
                    f"再发 /gallery embed 重建。"
                )
                return

            todo = max(1, min(int(arg), 20000)) if arg.isdigit() else 1000
            rows = db.execute(
                "SELECT id, descr FROM photos "
                "WHERE descr IS NOT NULL AND vec IS NULL ORDER BY id LIMIT ?",
                (todo,),
            ).fetchall()
            left_before = db.execute(
                "SELECT COUNT(*) c FROM photos WHERE descr IS NOT NULL AND vec IS NULL"
            ).fetchone()["c"]
            if not rows:
                done = db.execute(
                    "SELECT COUNT(*) c FROM photos WHERE vec IS NOT NULL"
                ).fetchone()["c"]
                yield event.plain_result(f"没有待转向量的图。已有 {done} 条向量。")
                return

            # 一张图要转好几段，按「文本条数」分批而不是按图片张数，
            # 否则批大小填 32 实际会一次发一百多条上去
            jobs: list[tuple[int, str, str]] = []
            for r in rows:
                jobs.append((r["id"], "vec", self._embed_text(r["descr"])))
                for col, txt in self._desc_segments(r["descr"]).items():
                    jobs.append((r["id"], col, self._embed_text(txt)))
            seg_n = len(jobs) - len(rows)

            batch = max(1, min(int(self.conf.get("embed_batch", 32) or 32), 256))
            yield event.plain_result(
                f"待转 {left_before} 张，这次做 {len(rows)} 张。\n"
                f"分段后共 {len(jobs)} 条文本（全文 {len(rows)} + 分段 {seg_n}），每批 {batch}。"
                + ("\n⚠ 一段都没切出来，检查描述里的层标题" if not seg_n else "")
            )
            ok = fail = dry = 0
            err = ""
            for i in range(0, len(jobs), batch):
                chunk = jobs[i : i + batch]
                try:
                    vecs = await self._embed_retry([t for _, _, t in chunk])
                except VisionError as e:
                    fail += len(chunk)
                    err = err or str(e)
                    logger.warning(f"[tg_presence] 转向量失败：{e}")
                    if e.fatal:
                        break
                    dry += 1
                    if dry >= 3:  # 连着三批都挂，别再空转
                        break
                    continue
                dry = 0
                if not vecs or len(vecs) != len(chunk):
                    fail += len(chunk)
                    err = err or "接口返回的条数和送进去的对不上"
                    continue
                # 同一批里可能混着不同的列，按列分组写回
                by_col: dict[str, list] = {}
                for (rid, col, _), v in zip(chunk, vecs):
                    by_col.setdefault(col, []).append((self._vec_pack(v), rid))
                for col, pairs in by_col.items():
                    db.executemany(
                        f"UPDATE photos SET {col} = ? WHERE id = ?", pairs
                    )
                db.commit()
                ok += len(chunk)
            self._vec_cache.clear()  # 有新向量，下次检索重建内存矩阵
            left = db.execute(
                "SELECT COUNT(*) c FROM photos WHERE descr IS NOT NULL AND vec IS NULL"
            ).fetchone()["c"]
            msg = [
                f"完成 {ok} 条文本" + (f"，失败 {fail} 条" if fail else "")
                + f"。还剩 {left} 张图"
                + ("，再发一次 /gallery embed 继续。" if left else "，全部转完。")
            ]
            if err:
                msg.append(f"\n最后的错误：{err[:160]}")
                if "429" in err:
                    msg.append(
                        "撞限流了。一张图要转四段，请求数是原来的四倍，"
                        "而这类接口常按文本条数算配额。\n"
                        "等一两分钟再发一次就行，进度不会丢；"
                        "老撞就把「向量批大小」调小到 8~16。"
                    )
                elif "401" in err or "403" in err or "404" in err:
                    msg.append("这是配置问题，重试没用。检查向量接口的地址、密钥、模型名。")
            yield event.plain_result("\n".join(msg))
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
                "SELECT COUNT(*) c FROM photos WHERE tag_state = '段数不齐'"
            ).fetchone()["c"]
            none_n = db.execute(
                "SELECT COUNT(*) c FROM photos WHERE tag_state = '无标签'"
            ).fetchone()["c"]
            if miss or none_n:
                lines.append(
                    f"\n{miss + none_n} 张关键词不合格，/gallery redo 排队重跑。"
                )
            lines.append(
                f"\n注：关键词行是检索命中率的主要来源，少于 "
                f"{max(2, int(self.conf.get('tag_min_words', 12) or 12))} 个就算不合格。"
            )
            lines.append("词在第几个位置不影响检索，「有问题」不用重跑。")
            yield event.plain_result("\n".join(lines))
            return

        if action == "clean":
            db = self.db()
            rows = db.execute(
                "SELECT id, path, descr FROM photos WHERE descr IS NOT NULL"
            ).fetchall()
            bad = [
                (r["id"], r["path"], why)
                for r in rows
                if (why := self._junk_reason(r["descr"]))
            ]
            if not bad:
                yield event.plain_result(
                    f"扫了 {len(rows)} 条描述，没发现拒答、思维链或过短的。"
                )
                return

            def kind(why: str) -> str:
                if why.startswith("像是思维链"):
                    return "思维链漏进正文"
                return "模型拒答" if why.startswith("像是拒答") else "描述过短"

            if rest.strip().lower() not in ("go", "确认"):
                tally: dict[str, int] = {}
                for _, _, why in bad:
                    tally[kind(why)] = tally.get(kind(why), 0) + 1
                lines = [f"扫了 {len(rows)} 条，{len(bad)} 条不能当描述用："]
                lines += [
                    f"  {k} × {v}"
                    for k, v in sorted(tally.items(), key=lambda x: -x[1])
                ]
                lines.append("\n举例：")
                lines += [f"  g{i} {Path(p).name} — {why}" for i, p, why in bad[:5]]
                lines.append("\n这些会污染向量检索。确认清掉重跑：/gallery clean go")
                yield event.plain_result("\n".join(lines))
                return

            db.executemany(
                f"UPDATE photos SET descr = NULL, {VEC_NULLS}, tag_state = NULL, "
                "tag_issues = NULL, fails = 0 WHERE id = ?",
                [(i,) for i, _, _ in bad],
            )
            db.commit()
            self._vec_cache.clear()
            yield event.plain_result(
                f"清掉 {len(bad)} 条，已退回待索引。\n"
                f"先确认视觉配置改好了（Gemini 记得设安全阈值），再 /gallery index auto 重跑。"
            )
            return

        if action == "redo":
            db = self.db()
            n = db.execute(
                f"UPDATE photos SET descr = NULL, {VEC_NULLS}, tag_state = NULL, "
                "tag_issues = NULL, fails = 0 "
                "WHERE tag_state IN ('段数不齐', '无标签')"
            ).rowcount
            db.commit()
            self._vec_cache.clear()
            yield event.plain_result(
                f"已把 {n} 张标签有结构问题的图退回待索引，/gallery index 重跑。"
                if n
                else "没有需要重跑的图。"
            )
            return

        if action == "show":
            db = self.db()
            key = rest.strip().lstrip("gG")
            cols = (
                "id, path, folder, descr, tag_state, tag_issues, sent, last_sent, "
                "file_time, vec IS NOT NULL AS has_vec"
            )
            if key.isdigit():
                row = db.execute(
                    f"SELECT {cols} FROM photos WHERE id = ?", (int(key),)
                ).fetchone()
            else:
                # 随机抽，用来肉眼验描述质量——同一条看第二遍没什么意义
                row = db.execute(
                    f"SELECT {cols} FROM photos WHERE descr IS NOT NULL "
                    "ORDER BY RANDOM() LIMIT 1"
                ).fetchone()
            if not row:
                yield event.plain_result(
                    "没这张图。" if key else "库里还没有已索引的图。"
                )
                return
            if not row["descr"]:
                yield event.plain_result(f"g{row['id']} 还没索引。")
                return

            descr = row["descr"]
            when = (
                datetime.fromtimestamp(row["file_time"], self._tz()).strftime("%Y-%m-%d")
                if row["file_time"]
                else "未知"
            )
            head = (
                f"g{row['id']} · [{row['folder'] or '根目录'}] {Path(row['path']).name}\n"
                f"{len(descr)} 字 · 标签 {row['tag_state'] or '未校验'} · "
                f"向量 {'有' if row['has_vec'] else '无'} · "
                f"文件日期 {when} · 发过 {row['sent']} 次\n"
                + (f"标签问题：{row['tag_issues']}\n" if row["tag_issues"] else "")
                + "─" * 18
                + "\n"
            )
            # Telegram 单条上限 4096，描述本身就三四千字，必须分条发
            text = head + descr
            for i in range(0, len(text), 3500):
                yield event.plain_result(text[i : i + 3500])
            return

        if action == "search":
            if not rest.strip():
                yield event.plain_result("要搜什么？例如 /gallery search 红色情趣内衣")
                return
            # 走 _recall 而不是 gallery_search——那才是桃桃调 browse_gallery 时
            # 实际走的路径。只测关键词那条路的话，向量有没有生效根本看不出来
            pool = max(10, int(self.conf.get("rank_pool", 60) or 60))
            rows = await self._recall(rest, "", "", pool)
            # 显示实际参与匹配的词表：整词落空被拆成单字的话，这里和
            # 原始切词不一样，不显示出来就会对着「桌上」猜半天
            raw_words = self._split_query(rest)
            words = self._rescue_dead(raw_words)
            if not rows:
                yield event.plain_result(
                    "没找到。\n切词：" + " / ".join(raw_words)
                    + ("\n实际用：" + " / ".join(words) if words != raw_words else "")
                )
                return

            vw = float(self.conf.get("vector_weight", 0.4) or 0)
            n_kw = sum(1 for r in rows if (r.get("kw_score") or 0) > 0)
            n_vec = sum(1 for r in rows if r.get("sim_score") is not None)
            head = ["切词：" + " / ".join(raw_words)]
            if words != raw_words:
                dropped = [w for w in raw_words if w not in words]
                head.append(
                    "实际用：" + " / ".join(words)
                    + (f"（{'、'.join(dropped)} 一张都没匹配上，已拆成单字）" if dropped else "")
                )
            head.append(f"候选 {len(rows)} 张（词面命中 {n_kw} · 语义召回 {n_vec}）")
            if vw <= 0:
                head.append("⚠ 语义权重是 0，向量路没启用")
            elif not n_vec:
                head.append("⚠ 语义一张都没召回，/gallery embed 转过向量没有？")
            head.append("─" * 18)

            lines = []
            for r in rows[:10]:
                kw, sim = r.get("kw_score") or 0, r.get("sim_score")
                mark = "词+义" if kw > 0 and sim is not None else ("义" if sim is not None else "词 ")
                detail = f"词{kw:.2f}" + (f" 义{sim:.2f}" if sim is not None else "")
                # 到底哪几个词中了——不列出来就分不清「桌上」真命中了，
                # 还是只是单字「桌」蹭到了「桌面」
                hit = [w for w in words if w in (r["descr"] or "")]
                # 描述本身是多行的，不压平的话十条结果会散成几十行糊在一起
                snippet = " ".join((r["descr"] or "").split())[:44]
                lines.append(
                    f"g{r['id']} {r['score']:.3f} [{mark}] {detail}"
                    + (f" ⟨{' '.join(hit)}⟩" if hit else "")
                    + f"\n   {snippet}"
                )
            yield event.plain_result("\n".join(head + lines))
            return

        if action == "index":
            if not self._vision_ready():
                yield event.plain_result("视觉 API 没配全，/vision 看缺哪项。")
                return
            arg = rest.strip().lower()
            running = bool(self._index_task and not self._index_task.done())

            if arg == "stop":
                if not running:
                    yield event.plain_result("没有在跑的后台索引。")
                    return
                self._index_task.cancel()
                self._index_task = None
                yield event.plain_result(
                    "已停。进度都在库里，/gallery index auto 可以接着跑。"
                )
                return

            if running:
                yield event.plain_result(
                    "后台索引正在跑，/gallery 看进度，/gallery index stop 停掉。"
                )
                return

            if arg == "auto":
                if not stat["pending"]:
                    yield event.plain_result(
                        f"没有待索引的图。已索引 {stat['indexed']} 张。"
                        + (
                            f"\n有 {stat['stuck']} 张失败跳过，/gallery retry 重来。"
                            if stat["stuck"]
                            else ""
                        )
                    )
                    return
                self._index_task = asyncio.create_task(
                    self._index_loop(event.unified_msg_origin)
                )
                yield event.plain_result(
                    f"后台开跑，待索引 {stat['pending']} 张，"
                    f"并发 {self.conf.get('vision_concurrency', 2)}。\n"
                    f"跑完会告诉你，中途每隔一阵报一次进度。\n"
                    f"上游要是挂了会自动等它恢复，不会把图标成坏图。\n"
                    f"/gallery index stop 随时停，进度不丢。"
                )
                return

            batch = max(1, min(int(arg), 200)) if arg.isdigit() else 20
            if not stat["pending"]:
                yield event.plain_result(
                    f"没有待索引的图。已索引 {stat['indexed']} 张。"
                    + (f"\n有 {stat['stuck']} 张失败跳过，/gallery retry 重来。" if stat["stuck"] else "")
                )
                return

            yield event.plain_result(
                f"开始索引 {min(batch, stat['pending'])} 张（待索引共 {stat['pending']} 张），"
                f"并发 {self.conf.get('vision_concurrency', 2)}，跑完再报。"
            )
            try:
                ok, n = await self._index_batch(batch)
            except VisionError as e:
                yield event.plain_result(f"配置有问题，已中止：{e}")
                return
            after = self.gallery_stat()
            yield event.plain_result(
                f"完成 {ok}/{n} 张。已索引 {after['indexed']} / {after['total']}，"
                f"还剩 {after['pending']} 张。"
                + (
                    "\n量大的话用 /gallery index auto，一条指令跑到底。"
                    if after["pending"]
                    else "\n全部索引完毕。"
                )
            )
            return

        yield event.plain_result(
            "用法：/gallery [scan|index N|index auto|index stop|search 词|show [gN]|"
            "embed N|audit|clean|redo|retry]\n"
            "  index auto 后台跑到全部完成，show 看某张的完整描述（不带参数随机抽），\n"
            "  embed 把描述转成语义向量，clean 揪出拒答和思维链，\n"
            "  audit 看标签质量，redo 重跑结构坏的"
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
