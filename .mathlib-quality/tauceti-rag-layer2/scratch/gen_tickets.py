#!/usr/bin/env python3
"""Generate ../tickets.md from tickets_data.py and the skeleton. Statements are copied verbatim from the
Lean files (through sorries.json, refreshed by sorries.py). Run from the repository root:

    python3 .mathlib-quality/tauceti-rag-layer2/scratch/sorries.py > /dev/null
    python3 .mathlib-quality/tauceti-rag-layer2/scratch/gen_tickets.py
"""
import json, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import tickets_data as d

ROOT = os.path.abspath(os.path.join(HERE, '..', '..', '..'))
CODE = 'PhD/TauCeti/Code/'
RAG = CODE + 'RigidAnalyticGeometry/'
def fullpath(f):
    if f.startswith('PhD/'):
        return f
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
 'CLEANUP-1': (d.SEM, 'T003', 'mid'), 'CLEANUP-2': (d.SEM, 'T007', 'final'),
 'CLEANUP-3': (d.SPV, 'T010', 'mid'), 'CLEANUP-4': (d.SPV, 'T011', 'final'),
 'CLEANUP-5': (d.INT, 'T014', 'mid'), 'CLEANUP-6': (d.INT, 'T017', 'mid'), 'CLEANUP-7': (d.INT, 'T020', 'mid'),
 'CLEANUP-8': (d.INT, 'T022', 'final'),
 'CLEANUP-9': (d.BAN, 'T025', 'mid'), 'CLEANUP-10': (d.BAN, 'T027', 'final'),
 'CLEANUP-11': (d.MOD, 'T030', 'final'),
 'CLEANUP-12': (d.BFA, 'T033', 'mid'), 'CLEANUP-13': (d.BFA, 'T036', 'mid'), 'CLEANUP-14': (d.BFA, 'T037', 'final'),
 'CLEANUP-15': (d.ASUP, 'T040', 'mid'), 'CLEANUP-16': (d.ASUP, 'T043', 'mid'), 'CLEANUP-17': (d.ASUP, 'T046', 'final'),
 'CLEANUP-18': (d.APB, 'T049', 'mid'), 'CLEANUP-19': (d.APB, 'T052', 'final'),
 'CLEANUP-20': (d.RED, 'T055', 'final'),
 'CLEANUP-21': (d.AFA, 'T059', 'final'),
 'CLEANUP-22': (d.RF, 'T062', 'mid'), 'CLEANUP-23': (d.RF, 'T064', 'final'),
 'CLEANUP-24': (d.EX, 'T067', 'mid'), 'CLEANUP-25': (d.EX, 'T069', 'final'),
}
ALL = {
 'CLEANUP-ALL-1': ('CLEANUP-2, CLEANUP-4, CLEANUP-6, T018', 'M1 (T019)',
   '`SupSeminorm/{Seminorm, SpectralValue, Integral}.lean` (so far).'),
 'CLEANUP-ALL-2': ('CLEANUP-8, CLEANUP-10, CLEANUP-15, T041', 'M2 (T042)',
   '`SupSeminorm/{Integral, Banach}.lean`, `Affinoid/SupSeminorm.lean` (so far).'),
 'CLEANUP-ALL-3': ('CLEANUP-17, CLEANUP-18, T049', 'M3 (T050)',
   '`Affinoid/{SupSeminorm, PowerBounded}.lean` (so far) and every module they import that changed since CLEANUP-ALL-2.'),
 'CLEANUP-ALL-4': ('CLEANUP-11, CLEANUP-14, CLEANUP-19, CLEANUP-20, T057', 'M4 (T058)',
   '`BanachAlgebra/Module.lean`, `SupSeminorm/FunctionAlgebra.lean`, `Affinoid/{PowerBounded, Reduction, FunctionAlgebra}.lean` (so far).'),
 'CLEANUP-ALL-5': ('CLEANUP-21, CLEANUP-22, T063', 'M5 (T064)',
   '`Affinoid/{FunctionAlgebra, ReductionFunctor}.lean` (so far).'),
}
ORDER = """T001 T002 T003 CLEANUP-1 T004 T005 T006 T007 CLEANUP-2
T008 T009 T010 CLEANUP-3 T011 CLEANUP-4
T012 T013 T014 CLEANUP-5 T015 T016 T017 CLEANUP-6 T018 CLEANUP-ALL-1 T019 T020 CLEANUP-7 T021 T022 CLEANUP-8
T023 T024 T025 CLEANUP-9 T026 T027 CLEANUP-10
T028 T029 T030 CLEANUP-11
T031 T032 T033 CLEANUP-12 T034 T035 T036 CLEANUP-13 T037 CLEANUP-14
T038 T039 T040 CLEANUP-15 T041 CLEANUP-ALL-2 T042 T043 CLEANUP-16 T044 T045 T046 CLEANUP-17
T047 T048 T049 CLEANUP-18 CLEANUP-ALL-3 T050 T051 T052 CLEANUP-19
T053 T054 T055 CLEANUP-20
T056 T057 CLEANUP-ALL-4 T058 T059 CLEANUP-21
T060 T061 T062 CLEANUP-22 T063 CLEANUP-ALL-5 T064 CLEANUP-23
T065 T066 T067 CLEANUP-24 T068 T069 CLEANUP-25
T070 CLEANUP-FINAL""".split()

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
        w("- **Status**: open · **Depends on**: T070 · **Parallel**: no · **Type**: cleanup")
        w("- Final sweep of the twelve files of this board (`SupSeminorm/{Seminorm, SpectralValue, Integral, Banach, FunctionAlgebra}.lean`, `BanachAlgebra/Module.lean`, `Affinoid/{SupSeminorm, PowerBounded, Reduction, FunctionAlgebra, ReductionFunctor, SupExamples}.lean`): naming, docstrings, import minimality by hand, module docstrings list the final declaration names, `runLinter` clean on every module, `lake build PhD.TauCeti` passes, `#print axioms` standard on the five milestones. Then update the Status line of this file, the roadmap README's Layer 2 status note, and the memory entry of the board.")
        w('')

# every open declaration must be covered exactly once
allopen = {(o['file'], o['line']) for o in S}
missing = allopen - used
if missing:
    raise SystemExit('open declarations without a ticket: ' + ', '.join(sorted(f"{f}:{l}" for f, l in missing)))
open(os.path.join(HERE, '..', 'tickets.md'), 'w').write('\n'.join(out).rstrip('\n') + '\n')
print('tickets:', len(ORDER), '| proof tickets:', len(TK), '| declarations covered:', len(used), 'of', len(allopen))
