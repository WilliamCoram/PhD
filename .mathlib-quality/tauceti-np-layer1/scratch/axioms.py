#!/usr/bin/env python3
"""python3 axioms.py File.lean [File2.lean ...] — print axioms of every declaration of the skeleton listed in
fullnames.json for the given AddVal files (plus private-free names), via `lake env lean`."""
import json, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
D = 'PhD/TauCeti/Code/NewtonPolygons/AddVal/'
names = json.load(open(os.path.join(HERE, 'fullnames.json')))
files = [D + f for f in sys.argv[1:]]
mods = sorted({'PhD.TauCeti.Code.NewtonPolygons.AddVal.' + f[:-5] for f in sys.argv[1:]})
sel = [n for f, l, n in names if f in files]
src = ''.join(f'import {m}\n' for m in mods) + ''.join(f'#print axioms {n}\n' for n in sel)
p = os.path.join(HERE, 'axioms_check.lean'); open(p, 'w').write(src)
out = subprocess.run(['lake', 'env', 'lean', p], capture_output=True, text=True).stdout
bad = [l for l in out.split('\n') if 'sorryAx' in l or 'error' in l]
std = {'propext', 'Classical.choice', 'Quot.sound'}
import re
nonstd = []
for blk in out.split("'")[1::2]:
    pass
for line in out.split('\n'):
    m = re.search(r"depends on axioms: \[(.*)\]", line)
    if m:
        ax = {a.strip() for a in m.group(1).split(',') if a.strip()}
        if not ax <= std: nonstd.append(line)
print(len(sel), 'declarations checked;', 'non-standard:', len(nonstd), '| sorry/error lines:', len(bad))
for l in nonstd + bad: print('  ', l[:200])
