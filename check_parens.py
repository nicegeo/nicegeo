#!/usr/bin/env python3
from __future__ import annotations

import argparse
import sys
from dataclasses import dataclass
from pathlib import Path


OPEN_TO_CLOSE = {"(": ")", "[": "]", "{": "}"}
CLOSE_TO_OPEN = {v: k for k, v in OPEN_TO_CLOSE.items()}


@dataclass
class Delim:
    ch: str
    line: int
    col: int


def check_text(text: str) -> tuple[bool, str]:
    stack: list[Delim] = []
    line = 1
    col = 0
    i = 0
    n = len(text)
    comment_depth = 0
    in_string = False

    while i < n:
        ch = text[i]
        col += 1

        if ch == "\n":
            line += 1
            col = 0
            i += 1
            continue

        nxt = text[i + 1] if i + 1 < n else ""

        if not in_string and ch == "(" and nxt == "*":
            comment_depth += 1
            i += 2
            col += 1
            continue

        if comment_depth > 0:
            if ch == "*" and nxt == ")":
                comment_depth -= 1
                i += 2
                col += 1
            else:
                i += 1
            continue

        if ch == '"':
            escaped = i > 0 and text[i - 1] == "\\"
            if not escaped:
                in_string = not in_string
            i += 1
            continue

        if in_string:
            i += 1
            continue

        if ch in OPEN_TO_CLOSE:
            stack.append(Delim(ch, line, col))
        elif ch in CLOSE_TO_OPEN:
            if not stack:
                return False, f"unmatched closer {ch!r} at {line}:{col}"
            top = stack.pop()
            expected = OPEN_TO_CLOSE[top.ch]
            if ch != expected:
                return (
                    False,
                    f"mismatched closer {ch!r} at {line}:{col}; "
                    f"expected {expected!r} for opener {top.ch!r} at {top.line}:{top.col}",
                )

        i += 1

    if comment_depth > 0:
        return False, "unterminated block comment"
    if in_string:
        return False, "unterminated string literal"
    if stack:
        tail = ", ".join(f"{d.ch}@{d.line}:{d.col}" for d in stack[-8:])
        return False, f"unclosed delimiters remain: {tail}"
    return True, "balanced"


def main() -> int:
    parser = argparse.ArgumentParser(description="Check delimiter balance in a file.")
    parser.add_argument("path", nargs="?", default="proof.ncg")
    args = parser.parse_args()

    path = Path(args.path)
    text = path.read_text(encoding="utf-8")
    ok, message = check_text(text)
    print(f"{path}: {message}")
    return 0 if ok else 1


if __name__ == "__main__":
    sys.exit(main())
