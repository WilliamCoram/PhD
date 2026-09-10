# Development Plan — `lwx-atkinlehner` (the H1 reduction)

**BOARD PATH: `.mathlib-quality/lwx-atkinlehner/`.**  The default `.mathlib-quality/` board is the
completed NewtonPolygons project — never touch it.  Every `/beastmode` run for this project must
name this board path explicitly.

Planned 2026-09-06.

## Goal

Reduce [LWX, Prop 3.22] — the Atkin–Lehner slope symmetry, hypothesis **H1** of the Step I / Step III
development — to a **single operator identity**, and prove everything else.

Milestone (`PhD/LWX/AtkinLehner.lean`):

```lean
theorem roots_charpoly_atkinLehner {A B A' P Q : Matrix ι ι K} {c : K} (hc : c ≠ 0)
    (hAB : A * B = c • (1 : Matrix ι ι K)) (hQP : Q * P = 1) (hA' : A' = P * B * Q) :
    A'.charpoly.roots = A.charpoly.roots.map (fun x => c / x)
```

Read at the classical space with `A` the matrix of `U_p` at nebentypus `ψ`, `A'` the matrix of
`U_p` at `ψ⁻¹`, `B` the matrix of `U'_p` at `ψ`, and `c = p^{k+1}`, this **is** Prop 3.22.  The
conjugation data `(P, Q)` is supplied by the Atkin–Lehner element, whose properties this board
proves; `hAB` is the hypothesis.

## Jacquet–Langlands dependencies (standing requirement)

Per the standing rule, this board must state where the classical results it touches use
Jacquet–Langlands and how we avoid it.  **The per-result audit is
`.mathlib-quality/lwx-stepone/JL-AUDIT.md`; read it before working any ticket.**  In summary:

- **[LWX, Prop 3.22] — the result this board reduces — is proved in the source by Jacquet–Langlands**
  plus a classification of the local component as a principal series (`lwx.txt:1773–1789`, quoted
  verbatim in `decomposition.md`).  That route is ruled out for this development.
- **How we avoid it: we do not prove Prop 3.22.** We prove a reduction of it.  The board discharges
  the Atkin–Lehner element's properties and the linear algebra, and carries the operator identity
  `U_p ∘ U'_p = p^{k+1}` as an explicit hypothesis in every downstream statement.
- **The avoidance is not yet a concrete method.**  The expected route to the identity is a local
  double-coset expansion in which the non-central terms are traces from level `p^{m−1}` and vanish
  by character orthogonality at conductor exactly `p^m`.  **No source stating this in the
  quaternionic setting was found.**  Per the `/develop` quote-or-delete rule it is therefore **not
  ticketed**; it is the intended `/expert-review` question.
- Two further Jacquet–Langlands uses in the wider chain (Buzzard 2004 Prop 4's second half, and
  Buzzard's Theorem 2) are **not** relevant to this board: the audit shows they are removed by
  assuming H1, which is exactly what this board does.

## References

- **[LWX]** Liu–Wan–Xiao, *The eigencurve over the boundary of weight space*, arXiv:1412.2584v4.
  Text at `.mathlib-quality/tate-riesz/references/lwx.txt`.  Prop 3.22 at `lwx.txt:1763–1789`;
  its consumption in Step I at `lwx.txt:1807–1846`; in Step III at `lwx.txt:2053–2058`.
- **`../lwx-stepone/JL-AUDIT.md`** — the Jacquet–Langlands audit and the plan of record for the
  surrounding Step I / Step III development.
- **`../lwx-stepone/FINDINGS.md`** — the evidence trail, including which references were searched
  for a Jacquet–Langlands-free proof and came up empty.

## Mathlib inventory

| Concept | Mathlib status | Our action |
|---|---|---|
| `Matrix.charpolyRev = det (1 − X·M)` | `LinearAlgebra/Matrix/Charpoly/Coeff.lean:292` | USE |
| Sylvester `det(1−XAB) = det(1−XBA)` | project: `PhD/TateFredholm/Charpoly.lean:47`, sorry-free | USE |
| `charpoly` under unit conjugation | `Charpoly/Basic.lean:280` (`charpoly_units_conj`) | USE, with a `Q * P = 1` wrapper |
| `det (c • A) = c^n · det A` | `Determinant/Basic.lean:272` | USE |
| roots of `charpoly` = eigenvalues with multiplicity | `Charpoly/Eigs.lean` | USE |
| root pairing under `A * B = c • 1` | not in mathlib | DEFINE (`CharpolyPairing.lean`) |
| Atkin–Lehner element, Iwahori normalisation | not in mathlib, not in project | DEFINE (`AtkinLehner.lean`) |
| Iwahori subgroup `Iw_{p^m}` | project has `LWX.Mh` (`HaloWeightH.lean:54`) but it is **not** conjugation-stable | DEFINE a sibling `LWX.Iw` |

Why `Mh` cannot be reused: it requires only `‖g 1 1‖ = 1` (`d` a unit), whereas conjugation by `w`
swaps `a` and `d`, so the conjugate needs `‖g 0 0‖ = 1` too.  `LWX.Iw` asks for `‖det‖ = 1`, which
gives both.  Recorded so nobody "simplifies" `Iw` back to `Mh`.

## File structure

- `PhD/TateFredholm/CharpolyPairing.lean` — the algebraic half: determinants, characteristic
  polynomials and root multisets under a scalar factorisation `A * B = c • 1`.  Purely algebraic,
  no `p`-adics, no analysis imports; a plausible future mathlib contribution.
- `PhD/LWX/AtkinLehner.lean` — the `p`-adic half: the Atkin–Lehner element, its conjugation action,
  the Iwahori subgroup and its normalisation, and the three forms of the reduction.

Both files are **new**.  No file on this board is owned by any other board: `lwx-seam-m` and
`tate-riesz` are both complete, and neither ever owned these paths.

## Dependency graph

```
W1 ─┬─► W3 ─┐
    └─► W4 ─┴─► W11 ─┐                    (Atkin–Lehner element normalises Iw)
W2                   │
W5, W6, W7           │   (diagonal swap ⇒ nebentypus inverts)
W8                   │   (U_p ↦ U'_p)
W9 ──► W10 ──────────┘

A1 ─┬─► A5 ─► A6 ─┐
    └─► R1        │
A2                │
A3 ───────────────┼─► R2  (MILESTONE)  ─► R3
A4 ───────────────┘
```

The two halves are independent until `R1`/`R2`, so the board has real parallel capacity; see the
ticket board's `Parallel` fields.

## Generality decisions

1. **The algebraic half is stated over `CommRing` wherever possible.**  `det_mul_det_of_mul_eq_smul`,
   the conjugation lemmas and the functional equation need no field, no invertibility and no
   `Nontrivial`.  Only the root statements need `Field` + `IsAlgClosed`, and only the slope statement
   needs `NormedField`.  An earlier draft put the determinant form in the algebraically-closed
   section; the adversarial pass caught it and it was moved.
2. **Conjugation hypotheses are one-sided (`Q * P = 1`).**  For square matrices this implies the
   other side, so callers prove strictly less.
3. **Conjugation is expressed multiplicatively**, `w * conj γ = γ * w`, so **no matrix inverse
   appears anywhere on this board**.  Matrix inverses in Lean carry junk-value side conditions;
   avoiding them removes a whole class of proof obligations.
4. **The reduction is stated for abstract matrices, not for the classical space.**  That space does
   not exist in Lean yet — it is built by the theta layer on the companion board — so tying the
   reduction to it now would make this board depend on that one and destroy the parallelism that is
   the reason for splitting the work.  The seam is deliberately deferred.
5. **Root multisets, not sorted slope indices.**  Equivalent to [LWX]'s indexing, needs no sorting,
   and serves both consumers directly: `Multiset.sum` gives Step I's slope total, `Multiset.count`
   gives Step III's per-slope multiplicities.

## Out of scope (recorded so nobody re-litigates)

- The operator identity `U_p ∘ U'_p = p^{k+1}` — the hypothesis; see the audit.
- Instantiating the reduction at the genuine classical space; needs the companion board's theta
  layer.
- Nebentypus bookkeeping beyond the exact identity `a·d = det + b·c`.  Reducing modulo `p^m` would
  pull in `PadicInt.toZModPow` for no gain at this stage.
- Recovering [LWX]'s sorted indexing from the multiset form — a pure `Multiset.sort` exercise with
  no mathematical content.
- `p = 2`.  Nothing on this board needs `p` odd, but nothing claims it either; the level is `p^m`
  throughout.

## Planning-pass notes

The adversarial pass changed two statements before any ticket was written:

- `atkinLehnerConj_mem_Iw` carried a hypothesis `m ≠ 0` copied from `norm_apply_zero_zero_of_mem_Iw`.
  Re-deriving the four entry bounds shows none of them uses it; the hypothesis was removed.
  (`m ≠ 0` **is** genuinely needed for `norm_apply_zero_zero_of_mem_Iw`: at `m = 0` the matrix
  `(0,1;1,0)` has unit determinant and `‖a‖ = 0`.)
- `det_mul_det_atkinLehner` was drafted inside the `[Field K] [IsAlgClosed K]` section although its
  proof needs neither; it now lives in its own `CommRing` section.

No ChatGPT second opinion was obtained: the `chatgpt-math` MCP server failed to connect this
session.
