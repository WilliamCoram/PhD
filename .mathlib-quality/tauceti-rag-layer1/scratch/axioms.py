#!/usr/bin/env python3
"""Usage: axioms.py <Module> <name> [<name> ...] — print the axioms of each declaration.
Writes scratch/axioms_check.lean and runs it with `lake env lean`."""
import subprocess, sys, os
mod, names = sys.argv[1], sys.argv[2:]
here = os.path.dirname(os.path.abspath(__file__))
f = os.path.join(here, 'axioms_check.lean')
with open(f, 'w') as h:
    h.write(f'import {mod}\n\n')
    for n in names:
        h.write(f'#print axioms {n}\n')
b = subprocess.run([os.path.expanduser('~/.elan/bin/lake'), 'build', mod], capture_output=True, text=True)
if b.returncode != 0:
    print('BUILD FAILED'); print((b.stdout + b.stderr)[-3000:]); sys.exit(1)
r = subprocess.run([os.path.expanduser('~/.elan/bin/lake'), 'env', 'lean', f], capture_output=True, text=True)
out = r.stdout + r.stderr
bad = []
for block in out.split("'")[1::2] if False else []:
    pass
print(out.strip())
std = {'propext', 'Classical.choice', 'Quot.sound'}
import re
for m in re.finditer(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out):
    ax = {a.strip() for a in m.group(2).split(',') if a.strip()}
    if not ax <= std:
        bad.append((m.group(1), ax - std))
for m in re.finditer(r"'([^']+)' does not depend on any axioms", out):
    pass
print('NONSTANDARD:', bad if bad else 'none')
