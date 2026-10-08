#!/usr/bin/env python3
"""Greedy import pruning: for each (file, import) reported REDUNDANT by prune_imports.py, remove it
from the real file if the file still compiles (via `lake env lean` on a scratch copy) with every
earlier accepted removal applied. Usage: prune_greedy.py LOG SCRATCHDIR."""
import os, re, subprocess, sys
D = 'PhD/TauCeti/Code/NewtonPolygons/AddVal/'
log, out = sys.argv[1], sys.argv[2]
cands = {}
for l in open(log):
    m = re.match(r'^(\w+): (import \S+) -> REDUNDANT', l.strip())
    if m:
        cands.setdefault(m.group(1), []).append(m.group(2))
for f, imps in cands.items():
    path = D + f + '.lean'
    lines = open(path).read().split('\n')
    for imp in imps:
        trial = [l for l in lines if l != imp]
        p = os.path.join(out, f'greedy_{f}.lean')
        open(p, 'w').write('\n'.join(trial))
        r = subprocess.run(['lake', 'env', 'lean', p], capture_output=True, text=True)
        ok = r.returncode == 0 and 'error' not in r.stdout
        if ok:
            lines = trial
        print(f'{f}: {imp} -> {"REMOVED" if ok else "kept"}', flush=True)
        os.remove(p)
    open(path, 'w').write('\n'.join(lines))
    b = subprocess.run(['lake', 'build', 'PhD.TauCeti.Code.NewtonPolygons.AddVal.' + f],
                       capture_output=True, text=True)
    print(f'{f}: rebuilt -> {"ok" if b.returncode == 0 else "FAILED"}', flush=True)
print('greedy done', flush=True)
