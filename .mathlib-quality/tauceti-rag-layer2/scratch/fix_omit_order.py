#!/usr/bin/env python3
"""Move `omit … in` / `include … in` / `variable … in` lines that sit between a docstring and its
declaration to before the docstring (Lean requires the modifier before the doc comment)."""
import re, sys
for p in sys.argv[1:]:
    s = open(p).read()
    pat = re.compile(r"(/--(?:(?!-/).)*?-/\n)((?:(?:omit|include|variable) [^\n]* in\n)+)", re.S)
    s2 = pat.sub(lambda m: m.group(2) + m.group(1), s)
    if s2 != s:
        open(p, 'w').write(s2)
        print('fixed', p)
