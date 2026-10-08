#!/usr/bin/env python3
"""For each AddVal file and each `import Mathlib.*` line, try compiling the file without that line
(copy in the scratchpad, `lake env lean`). Prints the imports whose removal still compiles cleanly."""
import os, subprocess, sys
D = 'PhD/TauCeti/Code/NewtonPolygons/AddVal/'
OUT = sys.argv[1]
files = ['NegLog', 'RatLog', 'Basic', 'RankOne', 'Commensurable', 'Discrete', 'Normed', 'Padic',
         'LaurentSeries', 'Extension', 'PadicComplex', 'Examples']
for f in files:
    lines = open(D + f + '.lean').read().split('\n')
    for i, l in enumerate(lines):
        if not l.startswith('import Mathlib'):
            continue
        trial = lines[:i] + lines[i + 1:]
        p = os.path.join(OUT, f'{f}_{i}.lean')
        open(p, 'w').write('\n'.join(trial))
        r = subprocess.run(['lake', 'env', 'lean', p], capture_output=True, text=True)
        ok = r.returncode == 0 and 'error' not in r.stdout
        print(f'{f}: {l} -> {"REDUNDANT" if ok else "needed"}', flush=True)
        os.remove(p)
