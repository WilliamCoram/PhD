#!/usr/bin/env python3
"""mark.py <ID> <status> [progress text] — set a ticket's status and add/append a Progress line."""
import sys, re, pathlib
p = pathlib.Path("/Users/nkw24xru/Desktop/Lean/PhD/.mathlib-quality/tauceti-pfa-layer2/tickets.md")
tid, status = sys.argv[1], sys.argv[2]
prog = sys.argv[3] if len(sys.argv) > 3 else None
s = p.read_text()
i = s.index(f"### [{tid}]")
j = s.index("- **Status**: ", i)
k = s.index(" · ", j)
s = s[:j] + f"- **Status**: {status}" + s[k:]
if prog:
    eol = s.index("\n", j)
    nxt = s[eol+1:eol+1+16]
    if nxt.startswith("- **Progress**: "):
        eol2 = s.index("\n", eol+1)
        s = s[:eol2] + f" · {prog}" + s[eol2:]
    else:
        s = s[:eol+1] + f"- **Progress**: {prog}\n" + s[eol+1:]
p.write_text(s)
print(tid, "->", status)
