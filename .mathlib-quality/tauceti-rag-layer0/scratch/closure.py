#!/usr/bin/env python3
import re, sys, os
def imports(mod):
    path = mod.replace('.', '/') + '.lean'
    if not os.path.exists(path): return []
    out = []
    for l in open(path):
        m = re.match(r'^(public )?import\s+(\S+)', l)
        if m: out.append(m.group(2))
    return out
def closure(roots):
    seen = {}
    stack = list(roots)
    while stack:
        m = stack.pop()
        if m in seen: continue
        imps = imports(m)
        seen[m] = imps
        for i in imps:
            if i.startswith('PhD.'): stack.append(i)
    return seen
roots = sys.argv[1:]
c = closure(roots)
tot = 0
for m in sorted(c):
    p = m.replace('.', '/') + '.lean'
    n = sum(1 for _ in open(p))
    tot += n
    ml = [i for i in c[m] if not i.startswith('PhD.')]
    pl = [i.replace('PhD.Main.ForMathlib.', '~') for i in c[m] if i.startswith('PhD.')]
    print(f'{n:5d} {m.replace("PhD.Main.ForMathlib.", "~")}\n        PhD: {pl}\n        Mathlib: {ml}')
print('files', len(c), 'lines', tot)
