#!/usr/bin/env python3
"""Generate ../tickets.md from tickets_data.py and the skeleton. Statements are copied verbatim from the
Lean files (through sorries.json, refreshed by sorries.py). Run from the repository root:

    python3 .mathlib-quality/tauceti-rag-layer1/scratch/sorries.py > /dev/null
    python3 .mathlib-quality/tauceti-rag-layer1/scratch/gen_tickets.py
"""
import json, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import tickets_data as d

ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
CODE = 'PhD/TauCeti/Code/'
RAG = CODE + 'RigidAnalyticGeometry/'
def fullpath(f):
    return CODE + f if f.startswith('PadicFunctionalAnalysis/') else RAG + f

S = json.load(open(os.path.join(HERE, 'sorries.json')))
by = {}
for o in S:
    by.setdefault((o['file'], o['name']), []).append(o)

def block(o):
    """Full text of a definition whose fields are sorry'd (up to the next blank line)."""
    lines = open(os.path.join(ROOT, o['file'])).read().split('\n')
    i = o['line'] - 1
    out = []
    while i < len(lines) and lines[i].strip() != '':
        out.append(lines[i]); i += 1
    return '\n'.join(out)

def prefix(o):
    """`omit … in` / `include … in` lines that govern the declaration (they change its hypotheses)."""
    lines = open(os.path.join(ROOT, o['file'])).read().split('\n')
    i = o['line'] - 2
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
        if (l.startswith('omit ') or l.startswith('include ')) and l.rstrip().endswith(' in'):
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
    if o['kind'] in ('def', 'instance', 'abbrev') or o['sorries'] > 1 or o['statement'].rstrip().endswith(' where'):
        return prefix(o) + block(o)
    return prefix(o) + o['statement'] + ' := by sorry'

PAR = {}

CLEAN = {
 'CLEANUP-1': (d.ALG, 'T001', 'final'),
 'CLEANUP-2': (d.EV, 'T003', 'final'),
 'CLEANUP-3': (d.PB, 'T004', 'final'),
 'CLEANUP-4': (d.NQ, 'T006', 'final'),
 'CLEANUP-5': (d.SUM, 'T009', 'mid'), 'CLEANUP-6': (d.SUM, 'T010', 'final'),
 'CLEANUP-7': (d.BAS, 'T013', 'final'),
 'CLEANUP-8': (d.EXT, 'T016', 'mid'), 'CLEANUP-9': (d.EXT, 'T019', 'mid'), 'CLEANUP-10': (d.EXT, 'T020', 'final'),
 'CLEANUP-11': (d.NOE, 'T023', 'final'),
 'CLEANUP-12': (d.BCO, 'T026', 'final'),
 'CLEANUP-13': (d.NTH, 'T029', 'mid'), 'CLEANUP-14': (d.NTH, 'T032', 'mid'), 'CLEANUP-15': (d.NTH, 'T035', 'final'),
 'CLEANUP-16': (d.ACO, 'T038', 'mid'), 'CLEANUP-17': (d.ACO, 'T041', 'final'),
 'CLEANUP-18': (d.TEN, 'T044', 'mid'), 'CLEANUP-19': (d.TEN, 'T048', 'final'),
 'CLEANUP-20': (d.FRA, 'T051', 'mid'), 'CLEANUP-21': (d.FRA, 'T054', 'final'),
 'CLEANUP-22': (d.BCH, 'T057', 'final'),
 'CLEANUP-23': (d.POL, 'T060', 'final'),
 'CLEANUP-24': (d.EXA, 'T063', 'final'),
}
ALL = {
 'CLEANUP-ALL-1': ('CLEANUP-1, CLEANUP-2', 'M1 (T004)',
   '`Restricted/Algebra.lean` and `TateAlgebra/Eval.lean` (the Layer 0 files generalised in place); afterwards `lake build PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Examples` must be sorry-free again except for `PowerBounded.lean`.'),
 'CLEANUP-ALL-2': ('CLEANUP-4, CLEANUP-7, CLEANUP-13', 'M2 (T030)',
   '`NormedQuotient.lean`, `Affinoid/Basic.lean`, `Affinoid/Noether.lean` (so far).'),
 'CLEANUP-ALL-3': ('CLEANUP-10, CLEANUP-11, CLEANUP-12, CLEANUP-15, T036', 'M3 (T037)',
   '`Affinoid/Extend.lean`, `BanachAlgebra/{Noetherian, Continuity}.lean`, `Affinoid/Noether.lean`, `Affinoid/Continuity.lean` (so far).'),
 'CLEANUP-ALL-4': ('CLEANUP-6, CLEANUP-17, CLEANUP-18, T046', 'M4 (T047)',
   '`Restricted/Sum.lean`, `Affinoid/Continuity.lean`, `Affinoid/Tensor.lean` (so far). It is also the mid-file cleanup of `Affinoid/Tensor.lean` (three proof tickets since CLEANUP-18).'),
 'CLEANUP-ALL-5': ('CLEANUP-20, T052', 'M5 (T053)',
   '`Affinoid/Fractions.lean` (so far) and every module it imports that changed since CLEANUP-ALL-4.'),
}
ORDER = """T001 CLEANUP-1 T002 T003 CLEANUP-2 CLEANUP-ALL-1 T004 CLEANUP-3
T005 T006 CLEANUP-4
T007 T008 T009 CLEANUP-5 T010 CLEANUP-6
T011 T012 T013 CLEANUP-7
T014 T015 T016 CLEANUP-8 T017 T018 T019 CLEANUP-9 T020 CLEANUP-10
T021 T022 T023 CLEANUP-11
T024 T025 T026 CLEANUP-12
T027 T028 T029 CLEANUP-13 CLEANUP-ALL-2 T030 T031 T032 CLEANUP-14 T033 T034 T035 CLEANUP-15
T036 CLEANUP-ALL-3 T037 T038 CLEANUP-16 T039 T040 T041 CLEANUP-17
T042 T043 T044 CLEANUP-18 T045 T046 CLEANUP-ALL-4 T047 T048 CLEANUP-19
T049 T050 T051 CLEANUP-20 T052 CLEANUP-ALL-5 T053 T054 CLEANUP-21
T055 T056 T057 CLEANUP-22
T058 T059 T060 CLEANUP-23
T061 T062 T063 CLEANUP-24
T064 CLEANUP-FINAL""".split()

TK = {x['id']: x for x in d.T}
assert set(ORDER) == set(TK) | set(CLEAN) | set(ALL) | {'CLEANUP-FINAL'}, 'order list incomplete'

def short(f):
    return f

out = []
w = out.append
ndecl = sum(len(x['decls']) for x in d.T)
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
        w(f"- **Status**: open · **File**: `{short(x['file'])}` · **Depends on**: {x['deps']} · **Parallel**: {PAR.get(tid, x['par'])} · **Type**: {x['typ']}{ms}")
        w(f"- **Leaves**: {x['leaves']}")
        w('')
        w('#### Statement')
        w('```lean')
        if x.get('statement_override'):
            w(x['statement_override'])
        else:
            w('\n'.join(statement(k) for k in x['decls']))
        w('```')
        w('#### Proof sketch')
        w(x['sketch'])
        w('#### Mathlib lemmas needed')
        w(x['mathlib'])
        w('#### Sources')
        w(x['sources'])
        w('#### Generality decision')
        w(x['gen'])
        w('')
    elif tid in CLEAN:
        f, deps, kind = CLEAN[tid]
        w(f"### [{tid}] Run /cleanup on `{f}`")
        w(f"- **Status**: open · **File**: `{f}` · **Depends on**: {deps} · **Parallel**: no · **Type**: cleanup")
        if kind == 'mid':
            w("- Per-file cadence (after the third proof ticket on the file). Inline as the main agent; `lake exe runLinter` on the module; lines ≤ 100 characters; no deprecated names; do not touch declarations that are still `sorry`.")
        else:
            w("- Final cleanup of the file (after its last proof ticket). Inline as the main agent; `lake exe runLinter` on the module; prune imports by hand (the build confirms each removal — there is no `lake exe shake` here); the module docstring lists the final declaration names.")
        w('')
    elif tid in ALL:
        deps, ms, files = ALL[tid]
        w(f"### [{tid}] Run /cleanup-all before milestone {ms}")
        w(f"- **Status**: open · **Depends on**: {deps} · **Parallel**: no · **Type**: cleanup")
        w(f"- Sweep before the milestone: {files} Every finished module builds without warnings, `runLinter` is clean, `#print axioms` is standard on the declarations the milestone uses. Do not touch declarations that are still `sorry`.")
        w('')
    else:
        w("### [CLEANUP-FINAL] Run /cleanup-all on the whole layer")
        w("- **Status**: open · **Depends on**: T064 · **Parallel**: no · **Type**: cleanup")
        w("- Final sweep of the sixteen files of this board (`NormedQuotient.lean`, `Restricted/{Algebra, Sum}.lean`, `TateAlgebra/Eval.lean`, `Affinoid/*.lean`, `BanachAlgebra/*.lean`, `PadicFunctionalAnalysis/PowerBounded.lean`): naming, docstrings, import minimality by hand, module docstrings list the final declaration names, `runLinter` clean on every module, `lake build PhD.TauCeti` passes, `#print axioms` standard on the five milestones. Then update the Status line of this file, the roadmap README's Layer 1 status note, and the memory entry of the board.")
        w('')

# every open declaration must be covered exactly once
allopen = {(o['file'], o['line']) for o in S}
missing = allopen - used
if missing:
    raise SystemExit('open declarations without a ticket: ' + ', '.join(sorted(f"{f}:{l}" for f, l in missing)))
open(os.path.join(HERE, '..', 'tickets.md'), 'w').write('\n'.join(out).rstrip('\n') + '\n')
print('tickets:', len(ORDER), '| proof tickets:', len(TK), '| declarations covered:', len(used), 'of', len(allopen))
