"""AI 음악 필터링 & 유튜브 플레이리스트 생성기 v2.4

- BYOK: 사용자의 YouTube Data API v3 키를 OS 자격 증명 저장소(keyring)에 저장
- 로컬 SQLite 캐시(검색어는 해시로만 저장)
- 규칙 기반 AI 의심 점수 (참고용, 오탐/미탐 가능)
"""
import csv
import hashlib
import html
import os
import queue
import re
import sqlite3
import threading
import webbrowser
from contextlib import contextmanager
from datetime import datetime, timedelta
from tkinter import filedialog, messagebox
from urllib.parse import urlencode, urlparse

import customtkinter as ctk
import keyring
import requests
from keyring.errors import KeyringError, PasswordDeleteError
from platformdirs import user_data_dir

# ============================== 설정 상수 ==============================
SERVICE_NAME = "ai_music_filter_app"
KEY_USERNAME = "youtube_user"
APP_VERSION = "v2.4"

MAX_DAILY_SEARCHES = 10      # 앱 자체 안전 한도 (search.list 1회 = 100 unit, 기본 일일 10,000 unit)
MAX_RESULTS = 15             # 검색 1회당 결과 수 (쇼츠 제외 후에도 충분히 남도록 여유)
VIDEO_TTL_DAYS = 30          # 영상 캐시 보관 기간 (API 약관상 장기 저장 제한 대비)
QUERY_TTL_DAYS = 7           # 검색어 -> 결과 목록 캐시 보관 기간
RULE_VERSION = 4             # 판별 규칙을 바꾸면 올려서 옛 캐시를 무효화
PLAYLIST_LIMIT = 50          # watch_videos 방식의 영상 수 상한(비공식, 변경 가능)
REQUEST_TIMEOUT = (5, 10)    # (연결, 읽기) 초
SEARCH_URL = "https://www.googleapis.com/youtube/v3/search"
VIDEOS_URL = "https://www.googleapis.com/youtube/v3/videos"
SHORTS_MAX_SECONDS = 60      # 이 길이 이하는 쇼츠로 간주해 제외 (videos.list 의 실제 재생시간 기준)
# search.list 의 videoDuration: None | "short"(4분 미만) | "medium"(4~20분) | "long"(20분 초과)
# 주의: "medium" 은 4분 미만의 일반 곡까지 사라지므로 기본값은 None. 쇼츠는 재생시간으로 거른다.
SEARCH_VIDEO_DURATION = None

DEFAULT_TEXT_COLOR = ("gray10", "gray90")

API_KEY_PATTERN = re.compile(r"^[A-Za-z0-9_\-]{30,60}$")
VIDEO_ID_PATTERN = re.compile(r"^[A-Za-z0-9_\-]{11}$")
CONTROL_CHARS = re.compile(r"[\x00-\x1f\x7f]")

# 단어 경계(\b)를 써서 'audio'(udio 포함), 'most/cost'(ost 포함) 같은 오탐을 막는다.
AI_PATTERNS = [
    (re.compile(r"\b(suno|udio)\b"), 30, "AI 플랫폼 흔적"),
    # 유튜브 라벨/고지 문구 포함. 'ai' 앞 (?<![a-z]) 로 email 등 오탐 방지 (한글 조사 앞에선 \b 가 안 먹음)
    (re.compile(r"\bai[- ]generated\b|\b(generated|made|created) (with|by|using) ai\b|인공지능 음악"
                r"|(?<![a-z])ai 생성|(?<![a-z])ai로 (제작|생성|창작)|(?<![a-z])ai 기술을 활용"
                r"|(?<![a-z])ai를 활용하여|인공지능(으로|을 활용)"),
     100, "AI 생성 명시/라벨 문구"),
    (re.compile(r"\bai (music|bgm|cover|song)\b"), 15, "AI 음악 키워드"),
]
AI_CONTEXT_PATTERN = re.compile(r"(?<![a-z])ai(?![a-z])|인공지능")
# 부정 표현("not AI generated", "AI 아님")은 매칭 전에 제거. 반복 횟수를 제한해 정규식 부하를 막는다.
NEGATION_PATTERN = re.compile(
    r"\b(?:not|no|non|never|without)[ -]{1,3}(?:(?:made|created|generated)[ -]{1,3})?"
    r"(?:(?:with|by|using)[ -]{1,3})?(?:an?[ -]{1,3})?ai\b(?:[ -]{1,3}generated)?"
    r"|\bai[ -]free\b|ai 아님|ai를 사용하지 않|인공지능을 사용하지 않")
SHORTS_TAG_PATTERN = re.compile(r"#shorts?\b")
ISO_DURATION_PATTERN = re.compile(r"^P(?:(\d+)D)?(?:T(?:(\d+)H)?(?:(\d+)M)?(?:(\d+)S)?)?$")
OFFICIAL_WORK_PATTERN = re.compile(r"\b(ost|soundtrack|theme song)\b")


# ============================== 순수 함수 ==============================
def clean_text(value, limit=200):
    """외부 입력 정제: HTML 엔티티 해제, 제어문자 제거, 길이 제한."""
    text = html.unescape(str(value or ""))
    text = CONTROL_CHARS.sub(" ", text).strip()
    return text[:limit]


def csv_safe(value):
    """엑셀 수식 주입 방지: =,+,-,@ 로 시작하는 셀 앞에 ' 를 붙인다."""
    text = str(value)
    if text and text[0] in ("=", "+", "-", "@", "\t", "\r"):
        return "'" + text
    return text


def parse_iso_duration(value):
    """ISO 8601 재생시간(PT3M20S)을 초로 변환. 해석 실패/라이브(P0D)는 0."""
    m = ISO_DURATION_PATTERN.match(value or "")
    if not m:
        return 0
    days, hours, minutes, seconds = (int(x or 0) for x in m.groups())
    return days * 86400 + hours * 3600 + minutes * 60 + seconds


def quota_date_key():
    """Google 할당량은 태평양시 자정에 초기화되므로 같은 기준으로 날짜를 센다."""
    try:
        from zoneinfo import ZoneInfo
        now = datetime.now(ZoneInfo("America/Los_Angeles"))
    except Exception:  # Windows에 tzdata가 없으면 로컬 날짜로 대체
        now = datetime.now()
    return now.strftime("%Y-%m-%d")


def query_hash(query):
    """검색어 원문을 DB에 남기지 않기 위해 정규화 후 SHA-256 해시만 저장."""
    normalized = " ".join(query.lower().split())
    return hashlib.sha256(normalized.encode("utf-8")).hexdigest()


def evaluate_ai_score(snippet, synthetic=False):
    """규칙 기반 판별. 반환: (점수 0~100, 상태, 근거). 참고용이며 확정 판정이 아님.
    synthetic=True 는 videos.list 의 status.containsSyntheticMedia(유튜브 '변경/합성 콘텐츠' 라벨)."""
    if synthetic:
        return 100, "제외", "🚨 유튜브 공식 'AI/합성 콘텐츠' 라벨(status.containsSyntheticMedia)"
    title = snippet.get("title", "")
    description = snippet.get("description", "")
    channel = snippet.get("channelTitle", "")
    text = f"{title} {description}".lower()[:2000]  # 입력 길이 상한(정규식 부하 방어)
    text = NEGATION_PATTERN.sub(" ", text)

    score = 0
    reasons = []
    is_official = False

    for pattern, points, label in AI_PATTERNS:
        if pattern.search(text):
            score += points
            reasons.append(f"{label}(+{points})")

    # '새롭게 생성되었습니다' 는 일반 문구일 수 있어 AI/인공지능 언급이 함께 있을 때만 인정
    if "새롭게 생성되었습니다" in text and AI_CONTEXT_PATTERN.search(text):
        score += 100
        reasons.append("AI 라벨 문구(+100)")

    channel_lower = channel.lower()
    if "vevo" in channel_lower or "official artist" in channel_lower or channel.endswith(" - Topic"):
        score -= 25
        reasons.append("공식 유통망/Topic 출처(-25)")
        is_official = True

    if OFFICIAL_WORK_PATTERN.search(text):
        score -= 35
        reasons.append("공식 사운드트랙 추정(-35)")
        is_official = True

    published = snippet.get("publishedAt", "")
    if published:
        try:
            pub_date = datetime.strptime(published[:10], "%Y-%m-%d")
            if datetime.now() - pub_date > timedelta(days=5 * 365):
                score -= 20
                reasons.append("5년 이상 전 업로드(-20)")
        except ValueError:
            pass

    score = max(0, min(score, 100))
    detail = ", ".join(reasons) if reasons else "특이사항 없음"

    if score >= 50 and is_official:
        return score, "보류", f"⚠️ 판정 충돌(AI 흔적 + 공식 출처): {detail}"
    if score >= 75:
        return score, "제외", f"🚨 AI 생성 강력 의심: {detail}"
    if score >= 50:
        return score, "제외", f"❌ AI 의심 높음: {detail}"
    if score >= 25:
        return score, "보류", f"❓ 판정 불확실: {detail}"
    return score, "유지", f"💚 인간 제작 음원 추정: {detail}"


def is_safe_youtube_url(url):
    """https 이고 호스트가 정확히 youtube.com / www.youtube.com 일 때만 허용."""
    try:
        parsed = urlparse(url)
    except ValueError:
        return False
    return parsed.scheme == "https" and parsed.hostname in ("www.youtube.com", "youtube.com")


def build_playlist_url(video_ids):
    """영상 ID 형식을 검증한 뒤 우회 재생 URL 생성. 실패 시 None.
    (watch_videos 는 비공식 기능이라 동작이 바뀌거나 막힐 수 있음)"""
    ids = [v for v in video_ids if VIDEO_ID_PATTERN.match(v)]
    if not ids:
        return None
    url = "https://www.youtube.com/watch_videos?" + urlencode({"video_ids": ",".join(ids)}, safe=",")
    return url if is_safe_youtube_url(url) else None


INSECURE_BACKEND_HINTS = ("plaintext", "fail", "null")


def keyring_backend_status():
    """(사용 가능 여부, 안내문). 보안 저장소가 없거나 평문 저장 백엔드뿐이면 키 저장을 막는다."""
    try:
        kr = keyring.get_keyring()
        backends = getattr(kr, "backends", None)  # ChainerBackend 는 실제 후보 목록을 가짐
        candidates = list(backends) if backends is not None else [kr]
    except Exception:
        return False, "OS 보안 저장소를 찾지 못했습니다."
    for backend in candidates:
        ident = f"{type(backend).__module__}.{type(backend).__name__}".lower()
        if not any(hint in ident for hint in INSECURE_BACKEND_HINTS):
            return True, ""
    return False, ("사용 가능한 OS 보안 저장소가 없어 키를 저장할 수 없습니다. "
                   "(Linux는 GNOME Keyring/KWallet 등이 필요합니다)")


# ============================== 앱 ==============================
class App(ctk.CTk):
    def __init__(self):
        super().__init__()
        self.title(f"AI 음악 필터링 & 플레이리스트 생성기 {APP_VERSION}")
        self.geometry("900x700")

        # 사용자 데이터 폴더 (실행 폴더와 분리, 가능한 OS에서 본인만 접근하도록 권한 제한)
        self.db_dir = user_data_dir(SERVICE_NAME, "Developer")
        os.makedirs(self.db_dir, mode=0o700, exist_ok=True)
        if os.name == "posix":  # makedirs 의 mode 는 이미 존재하는 폴더에는 적용되지 않으므로 명시 적용
            try:
                os.chmod(self.db_dir, 0o700)
            except OSError:
                pass
        self.db_path = os.path.join(self.db_dir, "cache.db")

        self.is_searching = False
        self.current_videos = []
        self.result_queue = queue.Queue()  # 워커 스레드 -> UI 스레드 전달용

        # --- UI ---
        ctk.CTkLabel(self, text=f"AI 음악 필터링 및 유튜브 플레이리스트 생성기 {APP_VERSION}",
                     font=("Arial", 18, "bold")).pack(pady=10)

        self.key_frame = ctk.CTkFrame(self)
        self.key_frame.pack(pady=5, fill="x", padx=20)
        self.key_entry = ctk.CTkEntry(self.key_frame, width=540, show="*",
                                      placeholder_text="YouTube Data API v3 Key 입력")
        self.key_entry.grid(row=0, column=0, padx=10, pady=10)
        ctk.CTkButton(self.key_frame, text="키 보안 저장", width=100,
                      command=self.save_api_key).grid(row=0, column=1, padx=5, pady=10)
        ctk.CTkButton(self.key_frame, text="키 삭제", width=80, fg_color="red",
                      hover_color="darkred", command=self.delete_api_key).grid(row=0, column=2, padx=5, pady=10)

        self.search_frame = ctk.CTkFrame(self)
        self.search_frame.pack(pady=5, fill="x", padx=20)
        self.search_entry = ctk.CTkEntry(
            self.search_frame, width=480,
            placeholder_text=f"음악이나 아티스트명 (일일 {MAX_DAILY_SEARCHES}회 제한)")
        self.search_entry.grid(row=0, column=0, padx=10, pady=10)
        self.search_entry.bind("<Return>", lambda _e: self.execute_youtube_search())
        self.search_btn = ctk.CTkButton(self.search_frame, text="유튜브 검색", width=110,
                                        command=self.execute_youtube_search)
        self.search_btn.grid(row=0, column=1, padx=5, pady=10)
        self.quota_label = ctk.CTkLabel(self.search_frame, text="", font=("Arial", 12, "bold"))
        self.quota_label.grid(row=0, column=2, padx=10, pady=10)

        self.scroll_frame = ctk.CTkScrollableFrame(
            self, width=840, height=360,
            label_text="[곡 검토]  판별은 참고용입니다  (0~24 유지 | 25~49 보류 | 50+ 제외 후보)")
        self.scroll_frame.pack(pady=10, padx=20, fill="both", expand=True)

        self.build_frame = ctk.CTkFrame(self, fg_color="transparent")
        self.build_frame.pack(pady=10, fill="x", padx=20)
        ctk.CTkButton(self.build_frame, text="🔗 '유지' 곡 재생목록 열기", fg_color="green",
                      hover_color="darkgreen", command=self.open_playlist).grid(row=0, column=0, padx=8)
        ctk.CTkButton(self.build_frame, text="📥 CSV 내보내기",
                      command=self.export_to_csv).grid(row=0, column=1, padx=8)
        ctk.CTkButton(self.build_frame, text="📋 ID 목록 복사",
                      command=self.copy_ids_to_clipboard).grid(row=0, column=2, padx=8)
        ctk.CTkButton(self.build_frame, text="🗑 캐시 삭제", fg_color="gray40",
                      command=self.clear_cache).grid(row=0, column=3, padx=8)

        self.status_label = ctk.CTkLabel(self, text="초기화 중...", text_color="gray", font=("Arial", 11))
        self.status_label.pack(pady=5)

        self.keyring_ok, self.keyring_msg = keyring_backend_status()
        self.init_database()
        self.refresh_key_state()
        self.update_quota_display()

    # ------------------------- 공통 유틸 -------------------------
    def update_status(self, text, color="gray"):
        self.status_label.configure(text=text, text_color=color)

    @contextmanager
    def db(self):
        """연결을 항상 닫고, 성공 시 커밋/실패 시 롤백."""
        conn = sqlite3.connect(self.db_path, timeout=10)
        try:
            yield conn
            conn.commit()
        except Exception:
            conn.rollback()
            raise
        finally:
            conn.close()

    def set_busy(self, busy):
        self.is_searching = busy
        self.search_btn.configure(state="disabled" if busy else "normal")

    # ------------------------- DB -------------------------
    def init_database(self):
        try:
            with self.db() as conn:
                # 구버전(컬럼 부족) 캐시는 재생성 가능한 데이터이므로 폐기
                cols = {row[1] for row in conn.execute("PRAGMA table_info(video_cache)")}
                if cols and not {"status", "rule_version"}.issubset(cols):
                    conn.execute("DROP TABLE video_cache")
                conn.execute("""
                    CREATE TABLE IF NOT EXISTS video_cache (
                        video_id TEXT PRIMARY KEY,
                        title TEXT,
                        channel_name TEXT,
                        ai_score INTEGER,
                        status TEXT,
                        reason TEXT,
                        rule_version INTEGER,
                        saved_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                    )""")
                conn.execute("""
                    CREATE TABLE IF NOT EXISTS query_cache (
                        query_hash TEXT PRIMARY KEY,
                        video_ids TEXT,
                        saved_at TIMESTAMP DEFAULT CURRENT_TIMESTAMP
                    )""")
                conn.execute("""
                    CREATE TABLE IF NOT EXISTS api_quota_counter (
                        date_key TEXT PRIMARY KEY,
                        search_count INTEGER DEFAULT 0
                    )""")
                # 만료 데이터 정리
                conn.execute("DELETE FROM video_cache WHERE saved_at <= datetime('now', ?)",
                             (f"-{VIDEO_TTL_DAYS} days",))
                conn.execute("DELETE FROM query_cache WHERE saved_at <= datetime('now', ?)",
                             (f"-{QUERY_TTL_DAYS} days",))
            if os.name == "posix":
                try:
                    os.chmod(self.db_path, 0o600)
                except OSError:
                    pass
            self.update_status("[시스템] 로컬 DB 준비 완료.", "green")
        except sqlite3.Error as e:
            self.update_status(f"[DB 오류] 초기화 실패: {type(e).__name__}", "red")

    def get_today_search_count(self):
        try:
            with self.db() as conn:
                row = conn.execute("SELECT search_count FROM api_quota_counter WHERE date_key = ?",
                                   (quota_date_key(),)).fetchone()
            return row[0] if row else 0
        except sqlite3.Error:
            return MAX_DAILY_SEARCHES  # 확인 불가 시 안전하게 막는다

    def increment_search_count(self):
        today = quota_date_key()
        with self.db() as conn:
            conn.execute("INSERT OR IGNORE INTO api_quota_counter (date_key, search_count) VALUES (?, 0)", (today,))
            conn.execute("UPDATE api_quota_counter SET search_count = search_count + 1 WHERE date_key = ?", (today,))
        self.update_quota_display()

    def update_quota_display(self):
        count = self.get_today_search_count()
        self.quota_label.configure(text=f"오늘 사용: {count}/{MAX_DAILY_SEARCHES}회",
                                   text_color="red" if count >= MAX_DAILY_SEARCHES else DEFAULT_TEXT_COLOR)

    def clear_cache(self):
        if not messagebox.askyesno("캐시 삭제", "저장된 검색 결과 캐시를 모두 삭제할까요?\n(오늘 사용 횟수는 초기화되지 않습니다)"):
            return
        try:
            with self.db() as conn:
                conn.execute("DELETE FROM video_cache")
                conn.execute("DELETE FROM query_cache")
            self.update_status("캐시를 삭제했습니다.", "green")
        except sqlite3.Error as e:
            self.update_status(f"[DB 오류] 캐시 삭제 실패: {type(e).__name__}", "red")

    # ------------------------- API 키 (keyring) -------------------------
    def get_api_key(self):
        if not self.keyring_ok:
            return None
        try:
            return keyring.get_password(SERVICE_NAME, KEY_USERNAME)
        except KeyringError:
            return None

    def refresh_key_state(self):
        """키 값을 화면에 다시 채우지 않고 저장 여부만 표시한다."""
        if not self.keyring_ok:
            self.key_entry.configure(placeholder_text="보안 저장소 없음 - 키 저장 불가")
            self.update_status(self.keyring_msg, "red")
        elif self.get_api_key():
            self.key_entry.configure(placeholder_text="✔ 키가 안전하게 저장되어 있습니다 (변경하려면 새 키 입력)")
        else:
            self.key_entry.configure(placeholder_text="YouTube Data API v3 Key 입력")

    def save_api_key(self):
        if not self.keyring_ok:
            self.update_status(self.keyring_msg, "red")
            return
        api_key = self.key_entry.get().strip()
        if not api_key:
            self.update_status("API 키를 입력하세요.", "orange")
            return
        if not API_KEY_PATTERN.match(api_key):
            self.update_status("키 형식이 올바르지 않습니다. 공백 없이 복사했는지 확인하세요.", "orange")
            return
        try:
            keyring.set_password(SERVICE_NAME, KEY_USERNAME, api_key)
        except KeyringError:
            self.update_status("OS 보안 저장소에 저장하지 못했습니다.", "red")
            return
        self.key_entry.delete(0, "end")  # 화면/메모리의 입력값 제거
        self.refresh_key_state()
        self.update_status("API 키를 OS 보안 저장소에 저장했습니다.", "green")

    def delete_api_key(self):
        if not messagebox.askyesno("키 삭제", "저장된 API 키를 삭제할까요?"):
            return
        try:
            keyring.delete_password(SERVICE_NAME, KEY_USERNAME)
            self.update_status("저장된 키를 삭제했습니다.", "green")
        except PasswordDeleteError:
            self.update_status("삭제할 키가 없습니다.", "orange")
        except KeyringError:
            self.update_status("OS 보안 저장소 접근에 실패했습니다.", "red")
        self.key_entry.delete(0, "end")
        self.refresh_key_state()

    # ------------------------- 검색 -------------------------
    def execute_youtube_search(self):
        if self.is_searching:
            return
        query = clean_text(self.search_entry.get(), 100)
        if not query:
            self.update_status("검색어를 입력해 주세요.", "orange")
            return

        # 1) 캐시 우선 (API 호출/할당량 소모 없음)
        qh = query_hash(query)
        try:
            cached = self.load_query_cache(qh)
        except sqlite3.Error:
            cached = None
        if cached:
            self.show_results(cached)
            self.update_status("캐시에서 불러왔습니다. (API 호출 없음)", "green")
            return

        # 2) 사전 차단: 키 / 일일 한도
        api_key = self.get_api_key()
        if not api_key:
            self.update_status("[경고] 먼저 YouTube API 키를 저장해 주세요.", "orange")
            return
        if self.get_today_search_count() >= MAX_DAILY_SEARCHES:
            self.update_status(f"[한도 초과] 오늘 {MAX_DAILY_SEARCHES}회를 모두 사용했습니다.", "red")
            return

        # 3) 네트워크 요청은 별도 스레드 (UI 멈춤 방지)
        self.set_busy(True)
        self.update_status("유튜브 검색 중...")
        threading.Thread(target=self._search_worker, args=(api_key, query, qh), daemon=True).start()
        self.after(100, self._poll_result)

    def _search_worker(self, api_key, query, qh):
        params = {
            "part": "snippet",
            "q": query,
            "maxResults": MAX_RESULTS,
            "type": "video",
            "videoCategoryId": "10",
        }
        if SEARCH_VIDEO_DURATION:
            params["videoDuration"] = SEARCH_VIDEO_DURATION
        # 키는 URL 쿼리가 아니라 헤더로 전달 -> 예외 메시지/로그에 URL로 노출되지 않음
        headers = {"x-goog-api-key": api_key}
        try:
            resp = requests.get(SEARCH_URL, params=params, headers=headers, timeout=REQUEST_TIMEOUT)
            if resp.status_code == 200:
                data = resp.json()
                details = self._fetch_video_details(headers, data)
                self.result_queue.put(("ok", data, qh, details))
            else:
                self.result_queue.put(("http_error", resp.status_code, self._error_reason(resp)))
        except requests.exceptions.Timeout:
            self.result_queue.put(("net_error", "응답 시간 초과"))
        except requests.exceptions.RequestException as e:
            self.result_queue.put(("net_error", type(e).__name__))  # 원문 메시지는 노출하지 않음
        except ValueError:
            self.result_queue.put(("net_error", "응답 해석 실패"))

    @staticmethod
    def _fetch_video_details(headers, data):
        """videos.list(1 unit)로 실제 재생시간과 유튜브 AI/합성 라벨을 조회. 실패 시 None."""
        ids = []
        for item in data.get("items", []):
            vid = (item.get("id") or {}).get("videoId", "")
            if VIDEO_ID_PATTERN.match(str(vid)):
                ids.append(vid)
        if not ids:
            return {}
        try:
            resp = requests.get(VIDEOS_URL, headers=headers, timeout=REQUEST_TIMEOUT,
                                params={"part": "contentDetails,status", "id": ",".join(ids)})
            if resp.status_code != 200:
                return None
            details = {}
            for it in resp.json().get("items", []):
                details[it.get("id")] = {
                    "duration": parse_iso_duration((it.get("contentDetails") or {}).get("duration", "")),
                    "synthetic": bool((it.get("status") or {}).get("containsSyntheticMedia", False)),
                }
            return details
        except (requests.exceptions.RequestException, ValueError):
            return None

    @staticmethod
    def _error_reason(resp):
        try:
            reason = resp.json()["error"]["errors"][0]["reason"]
            return re.sub(r"[^A-Za-z0-9_]", "", str(reason))[:40]
        except (ValueError, KeyError, IndexError, TypeError):
            return ""

    def _poll_result(self):
        try:
            msg = self.result_queue.get_nowait()
        except queue.Empty:
            self.after(100, self._poll_result)
            return

        self.set_busy(False)
        kind = msg[0]
        if kind == "ok":
            try:
                self.increment_search_count()
                videos, shorts = self.process_api_response(msg[1], msg[2], msg[3])
            except sqlite3.Error as e:
                self.update_status(f"[DB 오류] {type(e).__name__}", "red")
                return
            note = f" (쇼츠 {shorts}개 제외)" if shorts else ""
            if videos:
                self.show_results(videos)
                if msg[3] is None:
                    self.update_status("공식 AI 라벨·길이 확인에 실패해 제목/설명 규칙으로만 판별했습니다."
                                       f"(캐시 미저장){note}", "orange")
                else:
                    self.update_status(f"검색 및 판별 완료. 결과는 참고용입니다.{note}", "green")
            else:
                self.update_status(f"표시할 결과가 없습니다.{note}", "orange")
        elif kind == "http_error":
            code, reason = msg[1], msg[2]
            hints = {
                400: "요청 오류: API 키가 올바른지 확인하세요.",
                403: "접근 거부/할당량 초과: 키 제한 설정과 YouTube Data API 활성화 여부를 확인하세요.",
                429: "요청이 너무 많습니다. 잠시 후 다시 시도하세요.",
            }
            hint = hints.get(code, "서버 오류가 발생했습니다.")
            suffix = f" ({reason})" if reason else ""
            self.update_status(f"[API 오류 {code}] {hint}{suffix}", "red")  # 재시도하지 않음
        else:
            self.update_status(f"[통신 장애] {msg[1]}", "red")

    def process_api_response(self, data, qh, details):
        """반환: (표시할 영상 목록, 제외한 쇼츠 수). details 가 None 이면 캐시에 저장하지 않는다."""
        videos = []
        shorts = 0
        with self.db() as conn:
            for item in data.get("items", []):
                vid = (item.get("id") or {}).get("videoId", "")
                if not VIDEO_ID_PATTERN.match(str(vid)):
                    continue
                snippet = item.get("snippet") or {}
                title = clean_text(snippet.get("title"))
                channel = clean_text(snippet.get("channelTitle"), 100)
                description = clean_text(snippet.get("description"), 1000)
                info = (details or {}).get(vid) or {}

                # 쇼츠 제외: 실제 재생시간(<= 60초) 또는 #shorts 태그
                duration = info.get("duration", 0)
                if (0 < duration <= SHORTS_MAX_SECONDS) or SHORTS_TAG_PATTERN.search(f"{title} {description}".lower()):
                    shorts += 1
                    continue

                score, status, reason = evaluate_ai_score(
                    {"title": title, "description": description, "channelTitle": channel,
                     "publishedAt": snippet.get("publishedAt", "")},
                    synthetic=info.get("synthetic", False))
                if details is not None:
                    conn.execute(
                        "INSERT OR REPLACE INTO video_cache "
                        "(video_id, title, channel_name, ai_score, status, reason, rule_version) "
                        "VALUES (?, ?, ?, ?, ?, ?, ?)",
                        (vid, title, channel, score, status, reason, RULE_VERSION))
                videos.append({"id": vid, "title": title, "channel": channel,
                               "score": score, "status": status, "reason": reason})
            if videos and details is not None:
                conn.execute("INSERT OR REPLACE INTO query_cache (query_hash, video_ids) VALUES (?, ?)",
                             (qh, ",".join(v["id"] for v in videos)))
        return videos, shorts

    def load_query_cache(self, qh):
        """검색어 캐시가 유효하고 모든 영상 캐시가 살아 있을 때만 반환, 아니면 None."""
        with self.db() as conn:
            row = conn.execute("SELECT video_ids FROM query_cache WHERE query_hash = ? "
                               "AND saved_at > datetime('now', ?)",
                               (qh, f"-{QUERY_TTL_DAYS} days")).fetchone()
            if not row:
                return None
            videos = []
            for vid in row[0].split(","):
                r = conn.execute(
                    "SELECT title, channel_name, ai_score, status, reason FROM video_cache "
                    "WHERE video_id = ? AND rule_version = ? AND saved_at > datetime('now', ?)",
                    (vid, RULE_VERSION, f"-{VIDEO_TTL_DAYS} days")).fetchone()
                if not r:
                    return None
                videos.append({"id": vid, "title": r[0], "channel": r[1],
                               "score": r[2], "status": r[3], "reason": f"[캐시] {r[4]}"})
            return videos

    # ------------------------- 결과 표시 -------------------------
    def show_results(self, videos):
        for widget in self.scroll_frame.winfo_children():
            widget.destroy()
        self.current_videos = []
        for index, v in enumerate(videos):
            v = dict(v, status_var=ctk.StringVar(value=v["status"]))
            self.current_videos.append(v)
            self.render_video_row(index, v)

    def render_video_row(self, index, v):
        row = ctk.CTkFrame(self.scroll_frame)
        row.pack(fill="x", pady=5, padx=5)
        row.grid_columnconfigure(0, weight=1)

        title = v["title"] if len(v["title"]) <= 45 else v["title"][:45] + "..."
        ctk.CTkLabel(row, text=f"{index + 1}. {title}\n   └ {v['channel']} | 의심지수: {v['score']}점",
                     anchor="w", justify="left", font=("Arial", 12)).grid(row=0, column=0, padx=10, pady=5, sticky="w")

        radios = ctk.CTkFrame(row, fg_color="transparent")
        radios.grid(row=0, column=1, padx=10, sticky="e")
        ctk.CTkRadioButton(radios, text="유지", value="유지", variable=v["status_var"], width=60
                           ).grid(row=0, column=0, padx=2)
        ctk.CTkRadioButton(radios, text="보류", value="보류", variable=v["status_var"], width=60,
                           fg_color="orange").grid(row=0, column=1, padx=2)
        ctk.CTkRadioButton(radios, text="제외", value="제외", variable=v["status_var"], width=60,
                           fg_color="red").grid(row=0, column=2, padx=2)

        ctk.CTkLabel(row, text=f"   근거: {v['reason']}", font=("Arial", 11), text_color="gray",
                     wraplength=780, justify="left").grid(row=1, column=0, columnspan=2, padx=10, pady=2, sticky="w")

    # ------------------------- 출력 기능 -------------------------
    def kept_ids(self):
        return [v["id"] for v in self.current_videos if v["status_var"].get() == "유지"]

    def open_playlist(self):
        ids = self.kept_ids()
        if not ids:
            self.update_status("[알림] '유지'로 선택된 곡이 없습니다.", "orange")
            return
        truncated = len(ids) > PLAYLIST_LIMIT
        url = build_playlist_url(ids[:PLAYLIST_LIMIT])
        if not url:
            self.update_status("[보안 차단] 유효한 유튜브 주소를 만들 수 없어 중단했습니다.", "red")
            return
        try:
            webbrowser.open(url)
        except webbrowser.Error:
            self.update_status("브라우저를 열지 못했습니다. 'ID 목록 복사' 또는 CSV를 이용하세요.", "red")
            return
        note = f" (상위 {PLAYLIST_LIMIT}곡만 포함)" if truncated else ""
        self.update_status("브라우저에서 재생목록을 열었습니다. 열리지 않으면 'ID 목록 복사'/CSV를 "
                           f"이용하세요.{note}", "green")

    def export_to_csv(self):
        if not self.current_videos:
            self.update_status("내보낼 결과가 없습니다.", "orange")
            return
        path = filedialog.asksaveasfilename(defaultextension=".csv", initialfile="filtered_music_report.csv",
                                            filetypes=[("CSV 파일", "*.csv")])
        if not path:
            return
        try:
            with open(path, "w", encoding="utf-8-sig", newline="") as f:
                writer = csv.writer(f)
                writer.writerow(["영상ID", "곡 제목", "채널명", "AI의심점수", "유저최종선택", "근거"])
                for v in self.current_videos:
                    writer.writerow([v["id"], csv_safe(v["title"]), csv_safe(v["channel"]),
                                     v["score"], v["status_var"].get(), csv_safe(v["reason"])])
            self.update_status(f"CSV 저장 완료: {path}", "green")
        except OSError as e:
            self.update_status(f"CSV 저장 실패: {type(e).__name__}", "red")

    def copy_ids_to_clipboard(self):
        ids = self.kept_ids()
        if not ids:
            self.update_status("복사할 '유지' 곡이 없습니다.", "orange")
            return
        self.clipboard_clear()
        self.clipboard_append(",".join(ids))
        self.update_status("'유지' 곡의 영상 ID를 클립보드에 복사했습니다.", "green")


if __name__ == "__main__":
    app = App()
    app.mainloop()