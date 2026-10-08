#!/usr/bin/env python3
"""Compute the fully qualified name of every open declaration (from sorries.json), by tracking
`namespace`/`section`/`end` in each file, and emit a Lean file of `#check @name` commands."""
import json, re, os
HERE = os.path.dirname(os.path.abspath(__file__))
S = json.load(open(os.path.join(HERE, 'sorries.json')))
files = sorted({o['file'] for o in S})
ctx = {}
for f in files:
    lines = open(f).read().split('\n')
    stack = []  # (kind, name)
    ns_at = {}
    for i, l in enumerate(lines):
        m = re.match(r'^namespace\s+(\S+)', l)
        if m:
            stack.append(('ns', m.group(1)))
        m2 = re.match(r'^section(\s+(\S+))?', l)
        if m2:
            stack.append(('sec', m2.group(2) or ''))
        m3 = re.match(r'^end(\s+(\S+))?\s*$', l)
        if m3 and stack:
            stack.pop()
        ns_at[i + 1] = '.'.join(n for k, n in stack if k == 'ns')
    ctx[f] = ns_at
out = ['import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Examples', 'set_option pp.proofs.withType false', '']
names = []
for o in S:
    nm = o['name']
    if nm == '(anonymous)':
        continue
    ns = ctx[o['file']][o['line']]
    if nm.startswith('_root_.'):
        full = nm[len('_root_.'):]
    elif ns:
        full = ns + '.' + nm
    else:
        full = nm
    names.append((o['file'], o['line'], full))
    out.append(f'#check @{full}')
open(os.path.join(HERE, 'signatures.lean'), 'w').write('\n'.join(out) + '\n')
json.dump(names, open(os.path.join(HERE, 'fullnames.json'), 'w'), indent=1)
print(len(names), 'names')
