#!/usr/bin/env python3
"""Informal mathematical reasoning via external LLMs (OpenAI / Gemini / OpenRouter / CZ).

No dependencies beyond Python 3.10+ stdlib.

Environment variables:
    OPENAI_API_KEY      Required for --provider openai
    GEMINI_API_KEY      Required for --provider gemini
    OPENROUTER_API_KEY  Required for --provider openrouter
    CZ_API_KEY          Required for --provider cz

Usage:
    python3 archon-informal-agent.py "Prove that ..."        # default: cz + gemini-3.1-pro-preview-thinking
    python3 archon-informal-agent.py --model gpt-5.5-xhigh "Prove that ..."
    python3 archon-informal-agent.py --provider openai "Prove that ..."
    python3 archon-informal-agent.py --provider gemini --think "Prove that ..."
    python3 archon-informal-agent.py --provider openrouter "Prove that ..."
    python3 archon-informal-agent.py --provider openrouter --model deepseek/deepseek-r1 "..."

OpenRouter (https://openrouter.ai) provides access to 200+ models through a single
API key. Set OPENROUTER_API_KEY and use any model ID from their catalog, e.g.:
    --provider openrouter --model google/gemini-3.1-pro-preview   (default)
    --provider openrouter --model deepseek/deepseek-r1
    --provider openrouter --model anthropic/claude-sonnet-4

CZ (https://apicz.boyuerichdata.com) is an OpenAI-compatible relay fronting
GPT / Claude / Gemini / DeepSeek / MiniMax. Reasoning text (CoT) is captured
when the model supports it: GPT models via /v1/responses (reasoning.summary),
Claude/Gemini *-thinking variants via /v1/chat/completions (reasoning_content).

By default, stdout receives only the final answer. Each call appends one
JSON line to <workspace>/.claude/informal_log.jsonl containing the raw
upstream API response verbatim plus {ts, provider, model, prompt}. Query
with `jq`, e.g.
  jq -r 'select(.provider=="cz") | .prompt' .claude/informal_log.jsonl
Use --include-cot to also stream [Thinking] blocks to stdout, or --no-log
to suppress the log file.
"""

import argparse
import json
import os
import pathlib
import re
import sys
import threading
import time
import urllib.error
import urllib.request
from datetime import datetime, timezone

DEFAULTS = {
    "openai": "gpt-5.4",
    "gemini": "gemini-3.1-pro-preview",
    "openrouter": "google/gemini-3.1-pro-preview",
    "cz": "gemini-3.1-pro-preview-thinking",
}
DEFAULT_PROVIDER = "cz"

CZ_BASE_URL = "https://apicz.boyuerichdata.com/v1"

SYSTEM_PROMPT = (
    "You are an expert mathematician. Given a mathematical statement or problem, "
    "provide a clear, detailed informal proof or solution. "
    "Focus on mathematical reasoning and intuition. "
    "Structure your response with clear logical steps."
)

TIMEOUT = 300
RETRY_MAX = 5
RETRY_DELAY = 30.0  # seconds between attempts
RETRYABLE_HTTP = {429, 500, 502, 503, 504}


def _require_key(name: str) -> str:
    val = os.environ.get(name, "")
    if not val:
        sys.exit(f"Error: {name} not set")
    return val


def _retry_notice(reason: str, attempt: int) -> None:
    sys.stderr.write(
        f"\n[informal_agent] {reason}; retry {attempt}/{RETRY_MAX} in {RETRY_DELAY:.0f}s\n"
    )
    sys.stderr.flush()


def _post(url: str, headers: dict, body: dict) -> dict:
    req = urllib.request.Request(
        url,
        data=json.dumps(body).encode(),
        headers={"Content-Type": "application/json", **headers},
    )
    # initial attempt + RETRY_MAX retries on transient failures
    for attempt in range(RETRY_MAX + 1):
        try:
            with urllib.request.urlopen(req, timeout=TIMEOUT) as resp:
                return json.loads(resp.read().decode())
        except urllib.error.HTTPError as e:
            if e.code in RETRYABLE_HTTP and attempt < RETRY_MAX:
                _retry_notice(f"HTTP {e.code}", attempt + 1)
                time.sleep(RETRY_DELAY)
                continue
            detail = e.read().decode() if e.fp else ""
            sys.exit(f"API error {e.code}: {detail}")
        except (urllib.error.URLError, TimeoutError) as e:
            if attempt < RETRY_MAX:
                reason = getattr(e, "reason", e)
                _retry_notice(f"network: {reason}", attempt + 1)
                time.sleep(RETRY_DELAY)
                continue
            sys.exit(f"Network error after {RETRY_MAX} retries: {e}")


def call_gemini(prompt: str, model: str, think: bool) -> tuple[str, dict]:
    key = _require_key("GEMINI_API_KEY")
    url = f"https://generativelanguage.googleapis.com/v1beta/models/{model}:generateContent"
    gen_config: dict = {}
    if think:
        gen_config["thinkingConfig"] = {"thinkingLevel": "high", "includeThoughts": True}
    else:
        gen_config["temperature"] = 0.3

    data = _post(url, {"x-goog-api-key": key}, {
        "system_instruction": {"parts": [{"text": SYSTEM_PROMPT}]},
        "contents": [{"parts": [{"text": prompt}]}],
        "generationConfig": gen_config,
    })

    parts = data["candidates"][0]["content"]["parts"]
    out = []
    for p in parts:
        if p.get("thought"):
            out.append(f"[Thinking]\n{p['text']}\n[/Thinking]")
        else:
            out.append(p["text"])
    return "\n\n".join(out), data


def _openai_base() -> str:
    return os.environ.get("OPENAI_BASE_URL", "https://api.openai.com/v1").rstrip("/")


def call_openai(prompt: str, model: str, think: bool) -> tuple[str, dict]:
    key = _require_key("OPENAI_API_KEY")
    auth = {"Authorization": f"Bearer {key}"}
    base = _openai_base()

    if model.startswith("o") and "api.openai.com" in base:
        return _openai_responses(prompt, model, auth, base, think)
    return _openai_chat(prompt, model, auth, base)


def _openai_responses(prompt: str, model: str, auth: dict, base: str, think: bool) -> tuple[str, dict]:
    data = _post(f"{base}/responses", auth, {
        "model": model,
        "input": [
            {"role": "developer", "content": SYSTEM_PROMPT},
            {"role": "user", "content": prompt},
        ],
        "reasoning": {"effort": "high" if think else "medium"},
    })
    out = []
    for item in data.get("output", []):
        if item.get("type") == "reasoning":
            for s in item.get("summary", []):
                out.append(f"[Thinking]\n{s.get('text', '')}\n[/Thinking]")
        elif item.get("type") == "message":
            for c in item.get("content", []):
                if c.get("type") == "output_text":
                    out.append(c["text"])
    text = "\n\n".join(out) if out else json.dumps(data, indent=2)
    return text, data


def _openai_chat(prompt: str, model: str, auth: dict, base: str) -> tuple[str, dict]:
    data = _post(f"{base}/chat/completions", auth, {
        "model": model,
        "messages": [
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": prompt},
        ],
    })
    return data["choices"][0]["message"]["content"], data


def call_openrouter(prompt: str, model: str, think: bool) -> tuple[str, dict]:
    key = _require_key("OPENROUTER_API_KEY")
    auth = {"Authorization": f"Bearer {key}"}
    data = _post("https://openrouter.ai/api/v1/chat/completions", auth, {
        "model": model,
        "messages": [
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": prompt},
        ],
    })
    return data["choices"][0]["message"]["content"], data


def call_cz(prompt: str, model: str, think: bool) -> tuple[str, dict]:
    key = _require_key("CZ_API_KEY")
    auth = {"Authorization": f"Bearer {key}"}
    if model.startswith(("gpt-", "o1", "o3", "o4")):
        return _cz_responses(prompt, model, auth)
    return _cz_chat(prompt, model, auth)


def _cz_responses(prompt: str, model: str, auth: dict) -> tuple[str, dict]:
    data = _post(f"{CZ_BASE_URL}/responses", auth, {
        "model": model,
        "input": [
            {"role": "developer", "content": SYSTEM_PROMPT},
            {"role": "user", "content": prompt},
        ],
        "reasoning": {"summary": "auto"},
    })
    out = []
    for item in data.get("output", []):
        if item.get("type") == "reasoning":
            for s in item.get("summary", []):
                out.append(f"[Thinking]\n{s.get('text', '')}\n[/Thinking]")
        elif item.get("type") == "message":
            for c in item.get("content", []):
                if c.get("type") == "output_text":
                    out.append(c["text"])
    text = "\n\n".join(out) if out else json.dumps(data, indent=2)
    return text, data


def _cz_chat(prompt: str, model: str, auth: dict) -> tuple[str, dict]:
    data = _post(f"{CZ_BASE_URL}/chat/completions", auth, {
        "model": model,
        "messages": [
            {"role": "system", "content": SYSTEM_PROMPT},
            {"role": "user", "content": prompt},
        ],
    })
    msg = data["choices"][0]["message"]
    parts = []
    if msg.get("reasoning_content"):
        parts.append(f"[Thinking]\n{msg['reasoning_content']}\n[/Thinking]")
    parts.append(msg.get("content", ""))
    return "\n\n".join(parts), data


class _Heartbeat:
    """Stderr 'still-alive' indicator. Context manager: emits a label, ticks a dot
    every `interval` seconds while the body runs, prints elapsed time on exit."""

    def __init__(self, label: str, interval: float = 5.0):
        self.label = label
        self.interval = interval
        self._stop = threading.Event()
        self._thread: threading.Thread | None = None
        self._t0: float = 0.0

    def __enter__(self):
        self._t0 = time.monotonic()
        sys.stderr.write(f"[informal_agent] {self.label} ")
        sys.stderr.flush()
        self._thread = threading.Thread(target=self._tick, daemon=True)
        self._thread.start()
        return self

    def __exit__(self, exc_type, exc, tb):
        self._stop.set()
        if self._thread is not None:
            self._thread.join(timeout=1.0)
        elapsed = time.monotonic() - self._t0
        tag = "failed" if exc_type is not None else "done"
        sys.stderr.write(f" {tag} in {elapsed:.1f}s\n")
        sys.stderr.flush()

    def _tick(self):
        while not self._stop.wait(self.interval):
            sys.stderr.write(".")
            sys.stderr.flush()


_THINKING_RE = re.compile(r"\[Thinking\]\n(.*?)\n\[/Thinking\]", re.DOTALL)


def split_cot(raw: str) -> tuple[str, str]:
    """Separate [Thinking]...[/Thinking] blocks from the final answer.
    Returns (cot, answer). cot is empty when the model didn't emit thinking."""
    cot_blocks = _THINKING_RE.findall(raw)
    answer = _THINKING_RE.sub("", raw).strip()
    answer = re.sub(r"\n{3,}", "\n\n", answer)
    return "\n\n---\n\n".join(b.strip() for b in cot_blocks), answer


def _log_path() -> pathlib.Path:
    # script lives at <workspace>/.claude/tools/archon-informal-agent.py
    # jsonl log lands at <workspace>/.claude/informal_log.jsonl
    return pathlib.Path(__file__).resolve().parent.parent / "informal_log.jsonl"


def append_log(provider: str, model: str, prompt: str, response: dict) -> pathlib.Path:
    """Append one JSON object per call to the workspace-local jsonl log.
    Stores the raw API response verbatim plus call metadata — no extra parsing."""
    path = _log_path()
    path.parent.mkdir(parents=True, exist_ok=True)
    record = {
        "ts": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "provider": provider,
        "model": model,
        "prompt": prompt,
        "response": response,
    }
    with path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(record, ensure_ascii=False) + "\n")
    return path


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("prompt")
    p.add_argument("--provider", choices=["openai", "gemini", "openrouter", "cz"], default=DEFAULT_PROVIDER)
    p.add_argument("--model", default=None)
    p.add_argument("--think", action="store_true")
    p.add_argument("--include-cot", action="store_true",
                   help="Also emit [Thinking] blocks to stdout (default: only final answer; CoT goes to log file only).")
    p.add_argument("--no-log", action="store_true",
                   help="Skip writing the log file (CoT will be lost).")
    args = p.parse_args()

    model = args.model or DEFAULTS[args.provider]
    fn = {
        "gemini": call_gemini,
        "openai": call_openai,
        "openrouter": call_openrouter,
        "cz": call_cz,
    }[args.provider]
    with _Heartbeat(f"calling {args.provider}/{model}"):
        raw, response = fn(args.prompt, model, args.think)
    _, answer = split_cot(raw)

    if not args.no_log:
        path = append_log(args.provider, model, args.prompt, response)
        print(f"(log: {path})", file=sys.stderr)

    print(raw if args.include_cot else answer)


if __name__ == "__main__":
    main()
