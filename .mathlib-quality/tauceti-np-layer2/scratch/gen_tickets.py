#!/usr/bin/env python3
"""Generate ../tickets.md from tickets_data_a.py + tickets_data_b.py and the skeleton. Statements are
copied verbatim from the Lean files (through sorries.json, refreshed by sorries.py); non-`sorry`
definitions a ticket introduces are copied from the source by name (`defs=[(file, name)]`). Run from
the repository root:

    python3 .mathlib-quality/tauceti-np-layer2/scratch/sorries.py > /dev/null
    python3 .mathlib-quality/tauceti-np-layer2/scratch/gen_tickets.py
"""
import json, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import tickets_data_a as da
import tickets_data_b as db

ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
D = 'PhD/TauCeti/Code/NewtonPolygons/Coeff/'
def fullpath(f):
    return D + f

S = json.load(open(os.path.join(HERE, 'sorries.json')))
by = {}
for o in S:
    by.setdefault((o['file'], o['name']), []).append(o)

def lines_of(f):
    return open(os.path.join(ROOT, f), encoding='utf-8').read().split('\n')

def block_from(lines, i):
    out = []
    while i < len(lines) and lines[i].strip() != '':
        out.append(lines[i]); i += 1
    return '\n'.join(out)

def prefix(lines, i0):
    """`omit … in` / `include … in` / `variable … in` lines that govern the declaration at index i0."""
    i = i0 - 1
    pre = []
    in_doc = False
    while i >= 0:
        l = lines[i]
        if in_doc:
            if l.lstrip().startswith('/--'):
                in_doc = False
            i -= 1; continue
        if l.rstrip().endswith('-/'):
            in_doc = not l.lstrip().startswith('/--')
            i -= 1; continue
        if l.startswith('@['):
            i -= 1; continue
        if (l.startswith('omit ') or l.startswith('include ') or l.startswith('variable ')) and l.rstrip().endswith(' in'):
            pre.insert(0, l); i -= 1; continue
        break
    return ''.join(x + '\n' for x in pre)

used = set()
def statement(key):
    f, name = fullpath(key[0]), key[1]
    occ = key[2] if len(key) > 2 else 0
    lst = by.get((f, name))
    if not lst:
        raise SystemExit(f'no open declaration {name} in {f}')
    if len(lst) > 1 and len(key) < 3:
        raise SystemExit(f'ambiguous {name} in {f}: give an occurrence index')
    o = lst[occ]
    used.add((o['file'], o['line']))
    lines = lines_of(o['file'])
    if o['kind'] in ('def', 'instance', 'abbrev', 'structure') or o['sorries'] > 1 or o['statement'].rstrip().endswith(' where'):
        return prefix(lines, o['line'] - 1) + block_from(lines, o['line'] - 1)
    return prefix(lines, o['line'] - 1) + o['statement'] + ' := by sorry'

def defblock(key):
    f, name = fullpath(key[0]), key[1]
    lines = lines_of(f)
    pat = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|abbrev|structure|instance)\s+' + re.escape(name) + r'\b')
    for i, l in enumerate(lines):
        if pat.match(l):
            return prefix(lines, i) + block_from(lines, i)
    raise SystemExit(f'no definition {name} in {f}')

T = da.T + db.T
CLEAN, ALL, ORDER, FINAL = db.CLEAN, db.ALL, db.ORDER, db.FINAL
TK = {x['id']: x for x in T}
missing_order = (set(TK) | set(CLEAN) | set(ALL) | {'CLEANUP-FINAL'}) ^ set(ORDER)
assert not missing_order, f'order list mismatch: {sorted(missing_order)}'

out = []
w = out.append
w(open(os.path.join(HERE, 'tickets_header.md')).read().rstrip('\n'))
w('')
w('---')
w('')
w('## Tickets')
w('')
for tid in ORDER:
    if tid in TK:
        x = TK[tid]
        ms = f" · **Milestone**: {x['milestone']}" if x.get('milestone') else ''
        w(f"### [{tid}] {x['title']}")
        w(f"- **Status**: open · **File**: `{x['file']}` · **Depends on**: {x['deps']} · **Parallel**: {x['par']} · **Type**: {x['typ']}{ms}")
        w(f"- **Leaves**: {x['leaves']}")
        w('')
        w('#### Statement')
        w('```lean')
        parts = []
        for k in x.get('defs', []):
            parts.append(defblock(k))
        if x.get('statement_override'):
            parts.append(x['statement_override'])
        else:
            for k in x['decls']:
                parts.append(statement(k))
        w('\n\n'.join(parts))
        w('```')
        w('#### Proof sketch')
        w(x['sketch'].rstrip('\n'))
        w('#### Mathlib lemmas needed')
        w(x['mathlib'].rstrip('\n'))
        w('#### Sources')
        w(x['sources'].rstrip('\n'))
        w('#### Generality decision')
        w(x['gen'].rstrip('\n'))
        w('')
    elif tid in CLEAN:
        f, deps, kind = CLEAN[tid]
        w(f"### [{tid}] Run /cleanup on `{f}`")
        w(f"- **Status**: open · **File**: `{f}` · **Depends on**: {deps} · **Parallel**: no · **Type**: cleanup")
        if kind == 'mid':
            w("- Per-file cadence (after the third proof ticket on the file since the last cleanup). Inline as the main agent; `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.Coeff.<Module>`; lines ≤ 100 characters; no deprecated names; readable arithmetic (explicit `ring` identities + `linarith` over opaque `nlinarith`); do not touch declarations that are still `sorry`.")
        else:
            w("- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names; `omit` unused section instances; `@[simp]` only where `simpNF` accepts it.")
        w('')
    elif tid in ALL:
        deps, ms, files = ALL[tid]
        w(f"### [{tid}] Run /cleanup-all before milestone {ms}")
        w(f"- **Status**: open · **Depends on**: {deps} · **Parallel**: no · **Type**: cleanup")
        w(f"- Sweep before the milestone: {files} Every finished module builds without warnings, `runLinter` is clean, `#print axioms` is standard on the declarations the milestone uses. Do not touch declarations that are still `sorry`.")
        w('')
    else:
        w("### [CLEANUP-FINAL] Run /cleanup-all on the whole layer")
        w(f"- **Status**: open · **Depends on**: {FINAL['deps']} · **Parallel**: no · **Type**: cleanup")
        w(f"- {FINAL['text']}")
        w('')

allopen = {(o['file'], o['line']) for o in S}
missing = allopen - used
if missing:
    raise SystemExit('open declarations without a ticket: ' + ', '.join(sorted(f"{f}:{l}" for f, l in missing)))
open(os.path.join(HERE, '..', 'tickets.md'), 'w').write('\n'.join(out).rstrip('\n') + '\n')
nproof = len(TK); nclean = len(CLEAN); nall = len(ALL)
print('tickets:', len(ORDER), '| proof tickets:', nproof, '| per-file cleanups:', nclean, '| cleanup-all:', nall,
      '| declarations covered:', len(used), 'of', len(allopen))
