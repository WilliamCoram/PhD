#!/usr/bin/env python3
"""Fully qualified names of the skeleton's sorry'd declarations (namespace tracking), and a Lean file
`#check`ing each of them. Run from the repo root after sorries.py."""
import json, re, os
HERE = os.path.dirname(os.path.abspath(__file__))
S = json.load(open(os.path.join(HERE, 'sorries.json')))
byfile = {}
for o in S: byfile.setdefault(o['file'], []).append(o)
names = []
for f, decls in byfile.items():
    lines = open(f).read().split('\n')
    stack = []; ns_at = {}
    for i, l in enumerate(lines):
        m = re.match(r'^namespace\s+([\w.\']+)', l)
        if m: stack.append(m.group(1))
        m2 = re.match(r'^end\s+([\w.\']+)', l)
        if m2 and stack and stack[-1] == m2.group(1): stack.pop()
        ns_at[i + 1] = '.'.join(stack)
    for o in decls:
        if o['name'] == '(anonymous)': continue
        block = lines[o['line'] - 1]
        if 'private ' in block: continue
        ns = ns_at[o['line']]
        names.append((o['file'], o['line'], (ns + '.' if ns else '') + o['name']))
json.dump(names, open(os.path.join(HERE, 'fullnames.json'), 'w'), indent=1, ensure_ascii=False)
with open(os.path.join(HERE, 'signatures.lean'), 'w') as g:
    g.write('import PhD.TauCeti.Code.NewtonPolygons.AddVal.Examples\nset_option pp.proofs false\nset_option linter.style.setOption false\n')
    for f, ln, n in names:
        g.write(f'-- {f}:{ln}\n#check @{n}\n')
print(len(names), 'names')
