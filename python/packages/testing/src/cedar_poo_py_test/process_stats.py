"""Parse OS time utility observations with explicit units and precision."""
from decimal import Decimal
import re


def _number(text: str) -> int:
    return int(Decimal(text) * 1_000_000_000)


def _field(pattern: str, text: str) -> str:
    matches = re.findall(pattern, text, re.MULTILINE)
    if not matches:
        raise ValueError("native process OS time observation unavailable")
    return matches[-1]


def parse_stats(text: str, system: str) -> dict:
    if system == "Darwin":
        rss = _field(r"^\s*(\d+)\s+maximum resident set size\s*$", text)
        times = re.findall(r"^\s*([0-9.]+)\s+real\s+([0-9.]+)\s+user\s+([0-9.]+)\s+sys\s*$", text, re.MULTILINE)
        if not times:
            raise ValueError("native process OS CPU/wall observation unavailable")
        wall, user, kernel = times[-1]
        peak = int(rss)
    elif system == "Linux":
        rss = _field(r"^\s*Maximum resident set size \(kbytes\):\s*(\d+)\s*$", text)
        user = _field(r"^\s*User time \(seconds\):\s*([0-9.]+)\s*$", text)
        kernel = _field(r"^\s*System time \(seconds\):\s*([0-9.]+)\s*$", text)
        elapsed = _field(r"^\s*Elapsed \(wall clock\) time \(h:mm:ss or m:ss\):\s*([0-9:.]+)\s*$", text)
        parts = elapsed.split(":")
        wall = parts[-1]
        for index, part in enumerate(reversed(parts[:-1]), 1):
            wall = str(Decimal(wall) + Decimal(part) * (60 ** index))
        peak = int(rss) * 1024
    else:
        raise ValueError(f"unsupported native observation platform: {system}")
    precision = 10 ** max(0, 9 - len(wall.partition(".")[2]))
    return {"peak_rss_bytes": peak, "os_elapsed_ns": _number(wall),
            "user_cpu_ns": _number(user), "system_cpu_ns": _number(kernel),
            "os_elapsed_resolution_ns": precision,
            "os_time_scope": "OS time command accounting including waited-for children; rounded at reported precision"}
