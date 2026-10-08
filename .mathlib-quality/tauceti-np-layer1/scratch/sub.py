#!/usr/bin/env python3
"""Exact-substring replacement: python3 sub.py FILE PAIRS.py, where PAIRS.py defines a list P of
(old, new) pairs. Each `old` must occur exactly once."""
import sys, runpy
path, pairs = sys.argv[1], runpy.run_path(sys.argv[2])['P']
s = open(path).read()
for old, new in pairs:
    n = s.count(old)
    if n != 1:
        raise SystemExit(f'{n} occurrences of:\n{old}')
    s = s.replace(old, new)
open(path, 'w').write(s)
print('ok', len(pairs), 'replacements in', path)
