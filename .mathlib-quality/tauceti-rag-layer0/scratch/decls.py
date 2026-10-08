#!/usr/bin/env python3
"""Print declaration statements (without proofs) of Lean files."""
import re, sys
KW = re.compile(r'^(@\[[^\]]*\]\s*)?(private |protected |noncomputable |nonrec )*(theorem|lemma|def|abbrev|instance|structure|class|inductive)\b')
def stmts(path):
    lines = open(path).read().split('\n')
    out = []
    i = 0
    n = len(lines)
    while i < n:
        l = lines[i]
        if KW.match(l):
            buf = [l]
            j = i
            # collect until a line containing ':=' or ' where' at end, or blank line
            while not (re.search(r':=\s*(by)?\s*$', lines[j]) or re.search(r':=', lines[j]) or lines[j].rstrip().endswith(' where') or lines[j].strip() == '' ) and j + 1 < n and j - i < 14:
                j += 1
                buf.append(lines[j])
            txt = '\n'.join(buf)
            txt = re.sub(r':=.*$', '', txt, flags=re.S).rstrip()
            out.append((i + 1, txt))
            i = j + 1
        else:
            i += 1
    return out
for p in sys.argv[1:]:
    print('=' * 20, p)
    for ln, t in stmts(p):
        print(f'{ln}: {t}')
