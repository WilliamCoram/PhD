#!/usr/bin/env python3
"""Generate ../tickets.md from tickets_data.py and the skeleton. Statements are copied verbatim from the
Lean files (through sorries.json, refreshed by sorries.py). Run from the repository root:

    python3 .mathlib-quality/tauceti-rag-layer0/scratch/sorries.py > /dev/null
    python3 .mathlib-quality/tauceti-rag-layer0/scratch/gen_tickets.py
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
    if o['sorries'] > 1 or o['statement'].rstrip().endswith(' where'):
        return prefix(o) + block(o)
    return prefix(o) + o['statement'] + ' := by sorry'

PAR = {'T002': 'no (same file as T001)', 'T017': 'no (same file as T013–T016)',
       'T063': 'no (same file as T062)', 'T066': 'no (same file as T062–T065)',
       'T074': 'no (same file as T071–T073)', 'T058': 'no'}

CLEAN = {
 'CLEANUP-1': (d.B, 'T003', 'mid'), 'CLEANUP-2': (d.B, 'T005', 'final'),
 'CLEANUP-3': (d.RED, 'T008', 'mid'), 'CLEANUP-4': (d.RED, 'T011', 'mid'), 'CLEANUP-5': (d.RED, 'T012', 'final'),
 'CLEANUP-6': (d.EV, 'T015', 'mid'), 'CLEANUP-7': (d.EV, 'T017, T018', 'final'),
 'CLEANUP-8': (d.EVR, 'T021', 'final'), 'CLEANUP-9': (d.SUP, 'T023, T024', 'final'),
 'CLEANUP-10': (d.MM, 'T028', 'final'),
 'CLEANUP-11': (d.DIST, 'T031', 'mid'), 'CLEANUP-12': (d.DIST, 'T034', 'final'),
 'CLEANUP-13': (d.FIN, 'T037', 'final'),
 'CLEANUP-14': (d.CH, 'T040', 'mid'), 'CLEANUP-15': (d.CH, 'T043', 'final'),
 'CLEANUP-16': (d.RU, 'T046', 'mid'), 'CLEANUP-17': (d.RU, 'T048', 'final'),
 'CLEANUP-18': (d.TRU, 'T050', 'final'),
 'CLEANUP-19': (d.BALD, 'T053', 'mid'), 'CLEANUP-20': (d.BALD, 'T054', 'final'),
 'CLEANUP-21': (d.ON, 'T057', 'final'),
 'CLEANUP-22': (d.LIFT, 'T060', 'mid'), 'CLEANUP-23': (d.LIFT, 'T061', 'final'),
 'CLEANUP-24': (d.SC, 'T064', 'mid'), 'CLEANUP-25': (d.SC, 'T067', 'mid'), 'CLEANUP-26': (d.SC, 'T070', 'final'),
 'CLEANUP-27': (d.WS, 'T073', 'mid'), 'CLEANUP-28': (d.WS, 'T075', 'final'),
 'CLEANUP-29': (d.JAP, 'T076', 'final'), 'CLEANUP-30': (d.ST, 'T077', 'final'),
 'CLEANUP-31': (d.EX, 'T080', 'final'),
}
ALL = {
 'CLEANUP-ALL-1': ('T027, CLEANUP-2, CLEANUP-5, CLEANUP-7, CLEANUP-8, CLEANUP-9', 'M1 (T028)',
   '`TateAlgebra/{Basic, Reduction, Eval, EvalReduction, MaxModulus}.lean` and `SupSeminorm.lean`. It is also the mid-file cleanup of `MaxModulus.lean` (three proof tickets done).'),
 'CLEANUP-ALL-2': ('T049, CLEANUP-12, CLEANUP-13, CLEANUP-15, CLEANUP-17', 'M2 (T050)',
   '`TateAlgebra/{Distinguished, Finiteness, Chart, Rueckert}.lean` and `Rueckert.lean`.'),
 'CLEANUP-ALL-3': ('T069, CLEANUP-20, CLEANUP-21, CLEANUP-23', 'M3 (T070)',
   '`Bald.lean`, `PadicFunctionalAnalysis/Orthonormal.lean`, `OrthonormalLift.lean`, `TateAlgebra/StrictlyClosed.lean`.'),
 'CLEANUP-ALL-4': ('CLEANUP-18, CLEANUP-28, CLEANUP-29', 'M4 (T077)',
   '`WeaklyStable.lean`, `Japanese.lean`, `TateAlgebra/Stable.lean`, and the instances of `TateAlgebra/Rueckert.lean` that M4 consumes.'),
}
ORDER = """T001 T002 T003 CLEANUP-1 T004 T005 CLEANUP-2
T006 T007 T008 CLEANUP-3 T009 T010 T011 CLEANUP-4 T012 CLEANUP-5
T013 T014 T015 CLEANUP-6 T016 T017 T018 CLEANUP-7
T019 T020 T021 CLEANUP-8
T022 T023 T024 CLEANUP-9
T025 T026 T027 CLEANUP-ALL-1 T028 CLEANUP-10
T029 T030 T031 CLEANUP-11 T032 T033 T034 CLEANUP-12
T035 T036 T037 CLEANUP-13
T038 T039 T040 CLEANUP-14 T041 T042 T043 CLEANUP-15
T044 T045 T046 CLEANUP-16 T047 T048 CLEANUP-17
T049 CLEANUP-ALL-2 T050 CLEANUP-18
T051 T052 T053 CLEANUP-19 T054 CLEANUP-20
T055 T056 T057 CLEANUP-21
T058 T059 T060 CLEANUP-22 T061 CLEANUP-23
T062 T063 T064 CLEANUP-24 T065 T066 T067 CLEANUP-25 T068 T069 CLEANUP-ALL-3 T070 CLEANUP-26
T071 T072 T073 CLEANUP-27 T074 T075 CLEANUP-28
T076 CLEANUP-29
CLEANUP-ALL-4 T077 CLEANUP-30
T078 T079 T080 CLEANUP-31
T081 CLEANUP-FINAL""".split()

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
        w("- **Status**: open · **Depends on**: T081 · **Parallel**: no · **Type**: cleanup")
        w("- Final sweep of `PhD/TauCeti/Code/RigidAnalyticGeometry/` (skeleton files and the ported floor) and of `PadicFunctionalAnalysis/Orthonormal.lean`: naming, docstrings, import minimality by hand, module docstrings list the final declaration names, `runLinter` clean on every module, `lake build PhD.TauCeti` passes. Then update the Status line of this file, the roadmap README's provenance, and the memory entry of the board.")
        w('')

# every open declaration must be covered exactly once
allopen = {(o['file'], o['line']) for o in S}
missing = allopen - used
if missing:
    raise SystemExit('open declarations without a ticket: ' + ', '.join(sorted(f"{f}:{l}" for f, l in missing)))
open(os.path.join(HERE, '..', 'tickets.md'), 'w').write('\n'.join(out).rstrip('\n') + '\n')
print('tickets:', len(ORDER), '| proof tickets:', len(TK), '| declarations covered:', len(used), 'of', len(allopen))
