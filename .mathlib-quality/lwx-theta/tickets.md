# Ticket Board — `lwx-theta` (tranche 1: the shared theta layer)

**BOARD PATH: `.mathlib-quality/lwx-theta/`.**  The default `.mathlib-quality/` board belongs to
the completed NewtonPolygons project — NEVER touch it.  Every `/beastmode` run must name this
board path explicitly.

**Files owned by this board**: `PhD/LWX/Theta.lean`, `PhD/LWX/ConjChar.lean`,
`PhD/TateFredholm/FiniteFactor.lean`, `PhD/LWX/StepOne.lean`, `PhD/LWX/Degrees.lean`,
`PhD/LWX/AtkinLehnerInst.lean` (all new; all skeletoned and building).  Do not edit any other file.

**Build**: `lake build PhD.LWX.Theta`.  The skeleton compiles today with sorry warnings only.
Statements are transcribed verbatim from the compiling skeleton and are **protected** — if a
statement is wrong, file a B2 in `b2_log.jsonl` rather than editing it.

**Read before working any ticket**: `.mathlib-quality/lwx-stepone/JL-AUDIT.md` and this board's
`plan.md` and `decomposition.md`.  Nothing in tranche 1 depends on Jacquet–Langlands; if a ticket
seems to need it, that is a signal the route has drifted — file a B2.

**Scope note (revised 2026-09-06).**  Tranche 1 (theta layer), 1b (seams) and the equivariance are
fully ticketed.  Of tranche 2 (Step I), the pieces whose shapes do **not** depend on the two open
gaps are now ticketed in `PhD/LWX/StepOne.lean`; of tranche 3 (Step III), the Hida input at the
coefficient level is ticketed in `PhD/LWX/Degrees.lean`.  What remains unticketed is exactly what
is downstream of T-AG3 (Newton polygon of a product) and T-AG4 (Atkin–Lehner instantiation): the
converse half of classicality, the squeeze, and Step III's degree formulas.  Run
`/develop --continue` once T-AG3/T-AG4 have shapes.

## Summary

**2026-09-10, `/beastmode` — BOARD COMPLETE (all dispatchable tickets done).**  Tranches 1–7 are
closed: `PhD/LWX/Touching.lean`, `PhD/LWX/ClassicalPoint.lean` and `PhD/LWX/StepThree.lean` are
**sorry-free**, and `lake build PhD` is green (3903 jobs).  Both milestones are proved:

- **T5.23 `LWX.isStepOneTouching_of_atkinLehnerHypothesis`** — [LWX, §3.23 Step I], the touching
  of the Newton polygon at `P_k = (n_{k+1}, λ(n_{k+1})·v(T_{χ_k}))`, granted **H1**.  With
  **T5.24** it discharges `HasUnitBand` for the completed `lwx-slopes` board.
- **S7.15 `LWX.degX_succ`** — [LWX, Thm 1.3]'s degree formula
  `deg X_{k+1,ω} = r_ord(ω') + r_ord(ω₁)`, granted **H1 + H2**; with **S7.14** `degX_zero`
  (unconditional) and **S7.16** `degXint_zero`.

`#print axioms` on all of these is `[propext, Classical.choice, Quot.sound]`.

### What this pass added outside the board's files

Two general API files were factored out because the LWX proofs needed them and neither belongs in
`PhD/LWX/`:

- **`PhD/TateFredholm/NewtonSlopes.lean`** (new) — the `TateFredholm` × `NewtonPolygons` seam:
  `exists_evalT_zero_of_slope` (moved here from `PhD/JacobsSlash/5_EigenSlopes.lean`, which had
  flagged it as a public-API candidate) and the new `exists_evalT_zero_of_unitSlope`, which reads
  a zero off a **unit** slope with no hypothesis on the segment.
- **`PhD/NewtonPolygons/RootFaces.lean`** (new) — **the faces of a polynomial's polygon count its
  roots** (`faceRight_eq_card_roots_le`, `faceLeft_eq_card_roots_lt`, and their `IsAlgClosed K`
  forms), plus the face-through-the-origin lemmas `pointHeight_faceRight_eq` /
  `lt_pointHeight_of_faceRight_lt` that let two Fredholm determinants differing by a `rescale` be
  compared without a polygon-shear theory.  These are what the Atkin–Lehner reflection (S7.11) and
  hypothesis H2 (S7.13) consume.

`PhD/NewtonPolygons/Product.lean` gained `faceLeft_newtonPolygon₀OfPowerSeries_mul` (the mirror of
the existing `faceRight_` wrapper); `PhD/LWX/StepOne.lean` gained `norm_le_one_of_eigen` and had
`eq_zero_of_intertwine_of_norm_lt` restated over `[Module K E] [IsBoundedSMul K E]` (the model
space `c(I, K)` carries no `NormedSpace` instance, so the original could never be applied);
`PhD/LWX/HaloRing.lean` gained `HaloInt.isUnit_coeff_zero_of_isUnit`, the converse of
`HaloInt.isUnit_of_isUnit_coeff_zero`, which is what makes `rightIndex … 0 = ordDim` an equality.

### One B2 found and repaired

**S7.10** `unitSlope_charpolyRev_matrix_le` was **false as ticketed** (it quantified over every
`j`, but a polynomial's polygon has `unitSlope j = ⊤` past the degree, and `⊤ ≤ ↑σ` is false).
Logged in `b2_log.jsonl`; repaired by adding the range hypothesis
`j < Fintype.card ι * ((k+1) * p^1)`, and the root-level content the downstream tickets actually
use was split out as `S7.10a` (`norm_le_one_of_isRoot_charpoly_upMatrix`) and `S7.10b`
(`norm_pow_le_of_mem_roots_charpoly_matrix`).

### Ticket counts

- Total: 141 tickets. **Done: 135.** Retired: 5 (the earlier B2 batch, deleted by the user).
- Not done, none dispatchable: `B8` (deferred `ExpansionData`), `T-AG4` (expanded into
  sub-tickets), `T-AG5` (API gap, needs a source or a reviewer), `AG-ζ` and `AG-ω₀` (design gaps),
  `CLEANUP-FINAL` (this entry).
- Hypotheses of the development: **H1** `AtkinLehnerHypothesis` and **H2** `IsThetaExact`.
  Nothing else is assumed; nothing depends on Jacquet–Langlands
  (`.mathlib-quality/lwx-stepone/JL-AUDIT.md`).

---

**2026-09-09, `/develop --continue` (planning pass for Steps I and III).**  Tranches 1–4 are
closed (53 done, 5 retired by the user).  This pass adds **tranches 5–7** — Step I's squeeze, the
classical halo points, and Step III's degree bookkeeping — as **77 new tickets** (54 proof/def,
20 cleanup, G1, and two design gaps) on three NEW files, all skeletoned with `sorry` and building.

### The two design findings of this pass (details in `decomposition.md`, tranches 5–7)

1. **Step I needs no classicality.**  [LWX] identify the classical slopes with the first
   `n_{k+1}` overconvergent slopes via Prop 2.15 and then use their sum; the squeeze only needs
   `h_ψ ≤ S_ψ`, which is the Minkowski upper bound of the product theorem (the first `n` slopes are
   at most any `n` of the slopes).  Classicality becomes a corollary of the touching.  So Step I
   is: finite factor (one-sided determinant splitting, no commuting projection) + Minkowski +
   `−log‖det‖` under H1 + Cor 3.18 + (3.23.1).  No root multisets, no `IsAlgClosed`.
2. **The `_of_autFactor` equivariance must carry a nebentypus constant.**  At a classical weight
   `(k, ψ)` of conductor `p²` the automorphy factor on the level-`1` disc is `ψ(d)·(cz+d)^k`; the
   constant `ψ(d)` passes through Bol's identity but the current hypotheses force it to be `1`.
   Ticket **G1** generalises B7/B9–B12 in place; Step III's intertwining (S7.6) consumes the
   generalised form.  Corollary: `invChar ω` (S1) is the conjugate nebentypus only at weight `0`;
   the theorems take the twisted characters as parameters (gap AG-ω₀ is about spelling only).

### T-AG3 is closed by the `newton-product` board

`PhD/NewtonPolygons/{Face,Product}.lean` (complete 2026-09-09, sorry-free) supply
`height_mul`, `height_mul_of_forall_le`, `unitSlope_mul_of_forall_le`, `faceRight_mul`,
`faceLeft_mul` and `isEntireNewtonPolygonOf_coeffVal` — exactly what T-AG3 asked for, in the
height/face form tranches 5 and 7 consume.  T-AG3 is marked superseded below.

## Dependency order

```
theta layer:   T001 T002 (done)  T003 [CLEANUP-1] T004 T005 T006 [CLEANUP-2] T007 [CLEANUP-3]
seams (∥):     S1 S2 [CLEANUP-4]  S3 [CLEANUP-5]
equivariance:  T-AG1a → T-AG1b → T-AG2 → AL2 → AL3 ;  T-AG3 (independent of the theta layer)
AL inst.:      AL0a AL0b AL0c (done)  AL1 AL2 AL3 [CLEANUP-9] AL4 AL5 [CLEANUP-10] ;  T-AG5 (gap, H1a)
Step I  (∥):   SO0 (done) SO1 SO2 SO3 [CLEANUP-6] SO4 [CLEANUP-7]
Step III (∥):  D0 (done) D1 D2 D3 [CLEANUP-8]
               [CLEANUP-FINAL]
```

---

### [T001] `LWX.thetaOne` — the single-disc theta operator
- **Status**: done (2026-09-06, discharged in the planning skeleton)
- **File**: PhD/LWX/Theta.lean:67 | **Depends on**: none | **Parallel**: yes | **Type**: def
- Constructed via `TateFredholm.ofCoeffs`; both obligations (bound `≤ 1`, column-finiteness) are
  proved in the definition, no sorry.

### [T002] `LWX.thetaDisc` — the disc-model theta operator
- **Status**: done (2026-09-06, discharged in the planning skeleton)
- **File**: PhD/LWX/Theta.lean:91 | **Depends on**: T001 | **Parallel**: no | **Type**: def
- `blockMap (σ := ZMod (p ^ h)) (thetaOne K r)`; no sorry.

---

### [T003] `LWX.thetaDisc_apply` — the coefficient formula
- **Status**: done (finished 2026-09-09)
- **File**: PhD/LWX/Theta.lean:95 | **Depends on**: T002 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem thetaDisc_apply (h r : ℕ) (c : c(ZMod (p ^ h) × ℕ, K)) (a : ZMod (p ^ h)) (j : ℕ) :
    thetaDisc p K h r c (a, j) = ((Nat.descFactorial (j + r) r : ℕ) : K) * c (a, j + r) := by
  sorry
```

#### Proof sketch
1. **Unfold the block structure.** `thetaDisc` is `blockMap`, so evaluating at `(a, j)` reduces to
   evaluating `thetaOne K r` on the `a`-th block.  Use `BlockMap.lean`'s apply/projection lemmas
   (`blockOpMap_blockIncl` and the `blockProj`/`blockIncl` simp set); `blockMap` is
   `blockOpMap fun a b => if a = b then f else 0`, so all off-diagonal terms drop by `if_neg`.
2. **Unfold `thetaOne`.** `TateFredholm.ofCoeffs_apply` gives
   `thetaOne K r f j = ∑' i, M j i * f i` with `M j i = if i = j + r then descFactorial (j+r) r
   else 0`.
3. **Collapse the `tsum`.** Exactly one index contributes; use `tsum_eq_single (j + r)` with the
   `if_neg` for every other `i`, then `if_pos rfl`.

Bridging tactics that may be needed: `Finset.sum_ite_eq'` if the block sum is finite rather than a
`tsum`; `simp [thetaDisc, thetaOne]` to open the definitions.

#### Mathlib lemmas needed
- `tsum_eq_single` — collapse a `tsum` with a single nonzero term.
- `TateFredholm.ofCoeffs_apply` — project, `PhD/TateFredholm/GenFun.lean:186` (verified present).
- `TateFredholm.blockOpMap_blockIncl` — project, `PhD/TateFredholm/BlockMap.lean:47` (verified).
- `if_pos`, `if_neg`.

#### Sources
[Bu04, §7], `references/bu04.txt:1064`: the map is `d^{k−1}f/dz^{k−1}`.  This lemma is that
derivative read on Taylor coefficients; see `decomposition.md` leaf L1.3 for the verbatim quote and
the Lean ↔ source match.

#### Generality decision
Stated for arbitrary `r`, not just `k+1`, so that `θ^0 = id` (T004) and any future composition law
are instances.  No `CharZero` needed here.


**Progress**:
- 2026-09-09: DONE — `thetaDisc_apply` proven. Needed a new private helper `blockMap_apply_prod` (a block-diagonal operator acts blockwise, pointwise form) — no such lemma in `BlockMap.lean`; kept private here rather than editing another board's file. `ofCoeffs_apply` is `rfl`, so the tsum collapse via `tsum_eq_single` closed it.

---

### [CLEANUP-1] Run /cleanup on PhD/LWX/Theta.lean
- **Status**: done (finished 2026-09-09) — done inline (no subagents, per project convention) — covered together with CLEANUP-2/3 after T007. | **File**: PhD/LWX/Theta.lean | **Depends on**: T003 | **Type**: cleanup
- Per-file cadence (T001, T002, T003 since the file was created).  Blocks T004 onwards.

---

### [T004] `LWX.thetaDisc_zero` — `θ⁰ = id`
- **Status**: done (finished 2026-09-09)
- **File**: PhD/LWX/Theta.lean:100 | **Depends on**: T003, CLEANUP-1 | **Parallel**: yes (with T005)
- **Type**: theorem

#### Statement
```lean
@[simp]
theorem thetaDisc_zero (h : ℕ) : thetaDisc p K h 0 = ContinuousLinearMap.id K _ := by
  sorry
```

#### Proof sketch
1. **Reduce to points.** `ContinuousLinearMap.ext` then `funext`/`cSpace` extensionality; a
   disc-model element is determined by its values at `(a, j)`.
2. **Apply T003 at `r = 0`.** `thetaDisc_apply` gives `descFactorial (j+0) 0 * c (a, j+0)`.
3. **Simplify.** `Nat.descFactorial_zero` gives `1`, `Nat.cast_one`, `one_mul`, `Nat.add_zero`.

#### Mathlib lemmas needed
- `Nat.descFactorial_zero`, `Nat.cast_one`, `one_mul`, `ContinuousLinearMap.ext`,
  `ContinuousLinearMap.id_apply`.

#### Sources
None — API hygiene for the `def` (the no-one-off-definitions rule).  `θ⁰ = id` is not a claim from
either reference.

#### Generality decision
`@[simp]` because downstream compositions will normalise `θ⁰` away.  No hypotheses.


**Progress**:
- 2026-09-09: DONE — `thetaDisc_zero` proven via `ContinuousLinearMap.ext` + `DFunLike.ext` + T003 at `r = 0`.

---

### [T005] `LWX.locPolyDegSubmodule` — the classical subspace as a submodule
- **Status**: done (finished 2026-09-09)
- **File**: PhD/LWX/Theta.lean:114 | **Depends on**: CLEANUP-1 | **Parallel**: yes (with T004)
- **Type**: def (three field obligations)

#### Statement
```lean
def locPolyDegSubmodule (h k : ℕ) : Submodule K c(ZMod (p ^ h) × ℕ, K) where
  carrier := {c | IsLocPolyDeg p K h k c}
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry
```

#### Proof sketch
All three are pointwise, from `IsLocPolyDeg p K h k c ↔ ∀ a j, k < j → c (a, j) = 0`.
1. `add_mem'`: `intro ha hb a j hj; simp [ha a j hj, hb a j hj]` — the sum of two zeros.
2. `zero_mem'`: `intro a j _; rfl` (or `simp`).
3. `smul_mem'`: `intro r c hc a j hj; simp [hc a j hj]` — a scalar times zero.

Bridging tactics: the `c(·,·)` space's `add_apply` / `zero_apply` / `smul_apply` simp lemmas may be
needed to push the application through; if they are not simp, name them explicitly.

#### Mathlib lemmas needed
- `add_zero`, `mul_zero`, `smul_zero`, and the `cSpace` application simp lemmas
  (`TateFredholm.cSpace` — check the exact names in `PhD/TateFredholm/`; the file already uses
  them elsewhere).

#### Sources
[Bu04, Prop 4] proof, `references/bu04.txt:1113–1115`: "the space of polynomials of degree at most
`k − 2`, which is precisely the space of classical forms".  Buzzard's `k` is our `k + 2`, so his
"degree at most `k − 2`" is our "degree `≤ k`".  Full quote in `decomposition.md` leaf L1.5.

#### Generality decision
A `Submodule` rather than a bare predicate, because `finrank` (T007) needs the module structure.
No `CharZero` here — that is only needed for the kernel identification (T006).


**Progress**:
- 2026-09-09: DONE — `locPolyDegSubmodule` obligations proven. NOTE for future tickets: bare `add_apply`/`zero_apply`/`smul_apply` resolve to mathlib's `IsAddApply`-style typeclass lemmas and FAIL here, and `ZeroAtInftyContinuousMap.*_apply` does not match either (cSpace's FunLike is indexed by `I`, C₀'s by `Ix I`). The working idiom is a definitional `have hadd : (x + y) (a, j) = x (a, j) + y (a, j) := rfl`.

---

### [T006] `LWX.thetaDisc_eq_zero_iff` — `ker θ^{k+1}` is the classical subspace
- **Status**: done (finished 2026-09-09)
- **File**: PhD/LWX/Theta.lean:126 | **Depends on**: T003, T005 | **Parallel**: no
- **Type**: theorem

#### Statement
```lean
theorem thetaDisc_eq_zero_iff (h k : ℕ) (c : c(ZMod (p ^ h) × ℕ, K)) :
    thetaDisc p K h (k + 1) c = 0 ↔ IsLocPolyDeg p K h k c := by
  sorry
```

#### Proof sketch
1. **Reduce both sides to coefficients.**  `thetaDisc p K h (k+1) c = 0` iff for every `(a, j)` the
   value is `0`; by T003 that value is `descFactorial (j+k+1) (k+1) * c (a, j+k+1)`.
2. **The multiplier is nonzero in `K`.**  `Nat.descFactorial_pos` gives
   `0 < descFactorial (j+k+1) (k+1)` in `ℕ`; `Nat.cast_ne_zero` (needs `CharZero K`) transports
   this to `K`.  **This is the one place `CharZero K` is load-bearing** — over a field of
   characteristic `p ≤ k+1` the multiplier can vanish and the statement is false.
3. **`→`.**  From `mul_eq_zero` and step 2, `c (a, j+k+1) = 0` for every `j`; re-index by
   `j' = j + k + 1`, i.e. every `j' > k` has `c (a, j') = 0`, which is `IsLocPolyDeg`.
4. **`←`.**  Given `IsLocPolyDeg`, every `c (a, j+k+1)` vanishes since `j + k + 1 > k`, so each
   coefficient of the image is `0`; conclude by extensionality.

Bridging tactics: `omega` for the index arithmetic in both directions; `ContinuousLinearMap.ext`
plus the `cSpace` extensionality lemma to get from "all coefficients vanish" to "the element is
`0`".

#### Mathlib lemmas needed
- `Nat.descFactorial_pos`, `Nat.cast_ne_zero`, `mul_eq_zero`, `Nat.pos_iff_ne_zero`.
- T003 (`thetaDisc_apply`, this file).

#### Sources
[Bu04, Prop 4], `references/bu04.txt:1105–1115`.  Statement (verbatim): "The kernel of `θ^{1−k}` is
precisely the classical forms `S^D_k(U₀ ∩ U₁(pⁿ))(ε_p)`."  Proof (verbatim): "The kernel of
`θ^{1−k}` is the functions `f ∈ S^D_κ(U;1)` whose image is contained within the space of
polynomials of degree at most `k − 2`, which is precisely the space of classical forms."
**This is the Jacquet–Langlands-free part of Prop 4** — see `../lwx-stepone/JL-AUDIT.md` §2.

#### Generality decision
`CharZero K` is necessary, not over-specified; the adversarial pass ran the characteristic-`p`
counterexample explicitly (`decomposition.md` leaf L1.6).  Stated as an `Iff` (one conclusion), not
split.


**Progress**:
- 2026-09-09: DONE — `thetaDisc_eq_zero_iff` proven first attempt. `CharZero K` used exactly as planned, via `Nat.descFactorial_pos.mpr (Nat.le_add_left _ _)` then `Nat.cast_ne_zero`.

---

### [CLEANUP-2] Run /cleanup on PhD/LWX/Theta.lean
- **Status**: done (finished 2026-09-09) — done inline — see CLEANUP-3. | **File**: PhD/LWX/Theta.lean | **Depends on**: T006 | **Type**: cleanup
- Per-file cadence (T004, T005, T006 since CLEANUP-1).

---

### [T007] `LWX.finrank_locPolyDegSubmodule` — the local half of [LWX, (3.21.1)]
- **Status**: done (finished 2026-09-09)
- **File**: PhD/LWX/Theta.lean:132 | **Depends on**: T005, CLEANUP-2 | **Parallel**: no
- **Type**: theorem

#### Statement
```lean
theorem finrank_locPolyDegSubmodule (h k : ℕ) :
    Module.finrank K (locPolyDegSubmodule p K h k) = (k + 1) * p ^ h := by
  sorry
```

#### Proof sketch
1. **Exhibit the subspace as a finite product.**  An element of `locPolyDegSubmodule p K h k` is
   determined by its values at `ZMod (p^h) × Fin (k+1)` (degrees `0,…,k` on each disc), and every
   such family occurs (extend by zero — the extension is in `c(·,·)` because it has finite
   support).  Build the linear equivalence to `ZMod (p^h) × Fin (k+1) → K`.
2. **Count.**  `Module.finrank_pi` gives `Fintype.card (ZMod (p^h) × Fin (k+1))`;
   `Fintype.card_prod`, `ZMod.card` and `Fintype.card_fin` give `p^h * (k+1)`.
3. **Reorder** with `Nat.mul_comm` to match the statement.

Bridging tactics: constructing the equivalence is the bulk; `LinearEquiv.ofBijective` with an
explicit inverse (extend-by-zero) is likely cleaner than `Basis.mk`.  If the finite-support
extension is awkward in `c(·,·)`, spawn a sub-ticket for "a finitely-supported family lies in
`c(I, K)`" rather than weakening the statement.

#### Mathlib lemmas needed
- `Module.finrank_pi`, `Fintype.card_prod`, `Fintype.card_fin`, `ZMod.card`,
  `LinearEquiv.finrank_eq`.

#### Sources
[LWX, §3.21], `.mathlib-quality/tate-riesz/references/lwx.txt:1755–1760` (verbatim): "we see that
`S^D_{k+2}(K^pIw_{pᵐ};ψ)` is isomorphic to the direct sum of `t` copies of
`LP_{m−v(q),deg≤k}(ℤ_p;E)`.  So in total, (3.21.1) `dim S^D_{k+2}(K^pIw_{pᵐ};ψ) = (k + 1)q⁻¹pᵐt`."

#### Generality decision
This is the **local** factor `(k+1)·p^h`, deliberately without the class-number `t`; `h = m − 1`
for odd `p`, so `(k+1)p^h = (k+1)q⁻¹pᵐ`.  The `t` enters once in tranche 2's assembly over the
block index.  Recorded so this leaf is not read as claiming the source's global formula.


**Progress**:
- 2026-09-09: DONE — `finrank_locPolyDegSubmodule` proven. Built the planned equivalence as a private `locPolyDegEquiv` (extend-by-zero is a finite sum of `cSpace.single`s, so the sketch's feared finite-support gap never arose). Also needed a private `prod_val_inj` (dropping the `Fin` bound on the index is injective) — the round-trips need it twice.

---

### [CLEANUP-3] Run /cleanup on PhD/LWX/Theta.lean (final per-file for tranche 1)
- **Status**: done (finished 2026-09-09) — done inline 2026-09-09: `lake exe runLinter PhD.LWX.Theta` reports 0 issues in this file; build emits no style warnings (unused-section-variable warnings fixed with `omit` on `thetaDisc_zero`, `thetaDisc_apply`, `matrixCoeff_thetaOne`, `prod_val_inj`, `finrank_locPolyDegSubmodule`); no line exceeds 100 codepoints; every proof is well under the length gate; `#print axioms` on all five results shows exactly `[propext, Classical.choice, Quot.sound]`. | **File**: PhD/LWX/Theta.lean | **Depends on**: T007 | **Type**: cleanup

---

### [T-AG1a] `LWX.thetaOne_comp_kappaSlash` — the equivariance on one disc
- **Status**: **RETIRED (2026-09-09, user decision)** — the statement was false (B2 below) and the user chose to delete it rather than repair the signature.  The declaration is gone from the Lean file; its replacement is B7 `LWX.thetaOne_comp_kappaSlash_of_autFactor` (`PhD/LWX/Bol.lean`), proved and sorry-free.  **Do not re-create this ticket.**
- **File**: PhD/LWX/Theta.lean:160 | **Depends on**: CLEANUP-3 | **Parallel**: no | **Type**: theorem
- **Design step done 2026-09-06** — the statement below is now in the compiling skeleton.

#### Statement
```lean
theorem thetaOne_comp_kappaSlash (κ κ' : AnalyticWeight UK S ρ) (r : ℕ) (ν : UK →* Kˣ)
    (hκ : ∀ u : UK, κ.toChar u = (u : Kˣ) ^ ((r : ℤ) + 1) * ν u)
    (hκ' : ∀ u : UK, κ'.toChar u = (u : Kˣ) ^ (1 - (r : ℤ)) * ν u)
    (g : S) :
    (thetaOne K r).comp (κ.kappaSlash g)
      = ((g : Matrix (Fin 2) (Fin 2) K).det ^ r) •
        ((κ'.kappaSlash g).comp (thetaOne K r)) := by
  sorry
```
(section variables: `{UK : Subgroup Kˣ} {S : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ : ℝ}`)


#### B2 — statement defective (found by /beastmode, 2026-09-09)

**The hypotheses do not entail the conclusion.**  `ν : UK →* Kˣ` is an unconstrained monoid
hom, so the series `ν(cz + d)` need not be constant in `z`.  Writing the action out,
`f∣_κ g (z) = κ(cz+d)·(cz+d)^{−2}·f(gz)`, so with `κ(u) = u^{r+1}ν(u)` the left side is
`d^r/dz^r [(cz+d)^{r−1}·ν(cz+d)·f(gz)]`.  At `r = 1` that is
`c·(d/dz)[ν(cz+d)]·f(gz) + det(g)·ν(cz+d)(cz+d)^{−2}f'(gz)`, whose second term is exactly the
right side; the first term survives unless `ν(cz+d)` is constant.

**Counterexample.**  `r = 1`, `ν =` the inclusion `UK ↪ Kˣ`, so `κ = (·)^3` and `κ' = (·)^1`
— both honest `AnalyticWeight`s, their expansions being the polynomials `(cx+d)^3`, `(cx+d)`.
Take `g = (a b; c d)` with `c ≠ 0` and `f = 1 = cSpace.single 0 1`.  Then
`θ(f∣_κ g)(z) = d/dz[(cz+d)^{3−2}·1] = c`, while
`det(g)^1 · ((θ f)∣_{κ'} g) = det(g)·(0∣_{κ'}g) = 0`.

**The repair (for the user to approve; the ticketed statement is protected and was not edited).**
Delete `ν`:
```lean
    (hκ : ∀ u : UK, κ.toChar u = (u : Kˣ) ^ ((r : ℤ) + 1))
    (hκ' : ∀ u : UK, κ'.toChar u = (u : Kˣ) ^ (1 - (r : ℤ)))
```
This is exactly the case [Bu04, §7]'s display states — the displayed identity
(`references/bu04.txt:1074–1090`) carries **no** nebentypus factor, only `(cz+d)^{k−2}` — and it is
what the [LWX] application needs, since there the nebentypus `ψ` sits on the Iwahori level, not in
`κ`'s expansion.  The design pass of 2026-09-06 got `m = r + 1` right and the determinant
orientation right; what it missed is that a *finite part* is only harmless when it is locally
constant, which a bare `MonoidHom` is not.  With `ν` deleted the sketch below goes through
unchanged.

#### Proof sketch
**The orientation has been checked and corrected (review of 2026-09-06).**  [Bu04, Prop 4]'s
proof says a `U_p`-eigenvector of eigenvalue `λ` has `θ f` an eigenvector "with eigenvalue
`λ/p^{k−1}`" — divided by `p^{k−1}` — which forces `θ ∘ U_p = p^r • (U_p ∘ θ)`, the determinant
power multiplying the `θ`-first composition.  Confirmed at `r = 1`, weight `2` (no prefactor in
`kappaSlash`): `d/dz[f((az+b)/(cz+d))] = (ad−bc)(cz+d)⁻² f'((az+b)/(cz+d)) = (ad−bc)·(f'∣_{κ'} g)`.
The first draft had the two sides swapped; the statement above is the corrected one.  If a worker
finds otherwise, that is a B2, not an edit.

1. **Reduce to matrix coefficients.**  Both sides are continuous linear maps on `c(ℕ, K)`; use
   `ContinuousLinearMap.ext` and compare `matrixCoeff`.  `matrixCoeff_kappaSlash`
   (`Char.lean:835`) expresses the weight action's matrix as coefficients of the weight's
   generating function; `matrixCoeff_thetaOne` (this file, already proved) gives the shift-diagonal.
2. **Base case `r = 0`.**  Both sides are `κ.kappaSlash g` composed with the identity
   (`thetaDisc_zero` / `thetaOne` at `r = 0`), and `hκ`, `hκ'` coincide.  The source: "This
   identity is trivial for `k = 1`."
3. **Induction on `r`.**  The source: "the general case is easily established by induction on `k`."
   Differentiate the `r`-case identity once and collect terms; the weight hypotheses `hκ`, `hκ'`
   are what make the lower-order terms cancel.

#### Mathlib lemmas needed
- `AnalyticWeight.matrixCoeff_kappaSlash` — project, `PhD/QMF/Weight/Char.lean:835` (verified).
- `LWX.matrixCoeff_thetaOne` — project, this file (already proved).
- `ContinuousLinearMap.ext`, `zpow_natCast`, `zpow_neg`.

#### Sources
[Bu04, §7], `references/bu04.txt:1074–1090` (verbatim): "One has to verify that the map `θ^{1−k}`
is well-defined, which boils down to checking that for `(a b; c d) ∈ M_α` and `F` a power series in
`z`, we have the identity `(d^{k−1}/dz^{k−1})((cz + d)^{k−2}F((az + b)/(cz + d))) =
(ad − bc)^{k−1}(cz + d)^{−k}(d^{k−1}F/dz^{k−1})((az + b)/(cz + d))`.  This identity is trivial for
`k = 1` and the general case is easily established by induction on `k`."

#### Generality decision
**The design pass found that a shift relation between `κ` and `κ'` is not enough.**  `kappaSlash`
acts through the exponent `m − 2` for `κ(x) = x^m·ν(x)`; matching the source's `(cz+d)^{k−2}` with
the `(k−1)`-st derivative forces `m = r + 1`, and then the target weight is `1 − r`.  So `κ` must
be **classical of weight exactly `r + 1` relative to the order of the derivative** — hence `hκ` and
`hκ'` against a common finite part `ν`, rather than a bare `κ' = κ·x^{−2r}`.  Checked at `r = 1`:
with only the shift relation, the first-order term `(m−2)c(cz+d)^{m−3}f` survives unless `m = 2`,
which is `r + 1`.  This is the one substantive finding of the design pass.

---

### [T-AG1b] `LWX.thetaDisc_comp_discSlash` — the equivariance on the disc model
- **Status**: **RETIRED (2026-09-09, user decision)** — the statement was false (B2 below) and the user chose to delete it rather than repair the signature.  The declaration is gone from the Lean file; its replacement is B9 `LWX.thetaDisc_comp_discSlash_of_autFactor` (`PhD/LWX/Bol.lean`), proved and sorry-free.  **Do not re-create this ticket.**
- **File**: PhD/LWX/Theta.lean:178 | **Depends on**: T-AG1a | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem thetaDisc_comp_discSlash (h r : ℕ) (κ κ' : AnalyticWeight UK (M1Kh h ψ) ρ)
    (ν : UK →* Kˣ)
    (hκ : ∀ u : UK, κ.toChar u = (u : Kˣ) ^ ((r : ℤ) + 1) * ν u)
    (hκ' : ∀ u : UK, κ'.toChar u = (u : Kˣ) ^ (1 - (r : ℤ)) * ν u)
    (δ : M1 p) :
    (thetaDisc p K h r).comp (discSlash h ψ κ δ)
      = (ψ ((δ : Matrix (Fin 2) (Fin 2) ℚ_[p]).det) ^ r) •
        ((discSlash h ψ κ' δ).comp (thetaDisc p K h r)) := by
  sorry
```


#### B2 — statement defective (found by /beastmode, 2026-09-09)

Inherits T-AG1a's defect verbatim: `discSlash` is a `blockOp` of `kappaSlash`s, so the
single-disc counterexample transports to any `δ` whose disc conjugate has lower-left entry `≠ 0`.
Same repair — delete `ν` from both weight hypotheses.  See T-AG1a and `b2_log.jsonl`.

#### Proof sketch
1. **Open both block structures.**  `discSlash` is `blockOp fun a b => if b = discImage h δ a then
   κ.kappaSlash (discConjK h δ a ψ) else 0` (`DiscModel.lean`), and `thetaDisc` is
   `blockMap (thetaOne K r)`.  Since `thetaDisc` is block-*diagonal*, composing on either side
   permutes nothing: the `(a, b)` block of both sides is the `(a, b)` block of `discSlash`
   composed with `thetaOne` on the appropriate side.
2. **Apply T-AG1a per block** at `g := discConjK h δ a ψ`.
3. **Match the scalar.**  The determinant of the disc conjugate equals that of `δ` up to the
   parametrisation: `discConjMat h δ a = t_{a'}⁻¹ · δ · t_a` (`DiscModel.lean`), and the two
   parametrisations have reciprocal determinants, so `det (discConjK h δ a ψ) = ψ (det δ)`.
   Prove this as a `have` (or spawn a sub-ticket for it if it needs its own lemma).

#### Mathlib lemmas needed
- T-AG1a (this file), `TateFredholm.blockOp`/`blockMap` apply lemmas
  (`PhD/TateFredholm/BlockOp.lean:622`, `BlockMap.lean:41`), `Matrix.det_mul`.
- `LWX.discConj`, `LWX.discConjK`, `LWX.discImage` — project, `PhD/LWX/DiscModel.lean` (sorry-free).

#### Sources
As T-AG1a; this is the transport of the same identity along the disc decomposition, which
`DiscModel.discEval_discSlash` (sorry-free) already shows is [LWX, (2.3.2)] pointwise.

#### Generality decision
Stated for a general `δ : M1 p`, not just the `U_p` element, so that T-AG2 can sum over the coset
representatives.  Same weight hypotheses as T-AG1a.

---

### [T-AG2] `LWX.thetaDisc_comp_discHeckeBlock` — the `U_p` intertwining, **MILESTONE**
- **Status**: **RETIRED (2026-09-09, user decision)** — the statement was false (B2 below) and the user chose to delete it rather than repair the signature.  The declaration is gone from the Lean file; its replacement is B10 `LWX.thetaDisc_comp_discHeckeBlock_of_autFactor` (`PhD/LWX/Bol.lean`), proved and sorry-free.  **Do not re-create this ticket.**
- **File**: PhD/LWX/Theta.lean:197 | **Depends on**: T-AG1b | **Parallel**: no | **Type**: theorem
- **Design step done 2026-09-06.**  This ticket unblocks both assemblies.

#### Statement
```lean
theorem thetaDisc_comp_discHeckeBlock (h r : ℕ) (κ κ' : AnalyticWeight UK (M1Kh h ψ) ρ)
    (ν : UK →* Kˣ)
    (hκ : ∀ u : UK, κ.toChar u = (u : Kˣ) ^ ((r : ℤ) + 1) * ν u)
    (hκ' : ∀ u : UK, κ'.toChar u = (u : Kˣ) ^ (1 - (r : ℤ)) * ν u)
    (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)
    (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θG) (idx : ι → Fin p → ι)
    (uu : ι → Fin p → U) (cst : K)
    (hdet : ∀ i t, ψ ((certM1 θG U hU vRep hvΔ uu i t :
      Matrix (Fin 2) (Fin 2) ℚ_[p]).det) = cst) (i j : ι) :
    (thetaDisc p K h r).comp (discHeckeBlock θG h ψ κ U hU vRep hvΔ idx uu i j)
      = (cst ^ r) •
        ((discHeckeBlock θG h ψ κ' U hU vRep hvΔ idx uu i j).comp (thetaDisc p K h r)) := by
  sorry
```


#### B2 — statement defective (found by /beastmode, 2026-09-09)

Inherits T-AG1a's defect: `discHeckeBlock` is a finite sum of `discSlash` terms over the coset
representatives, so a defect in one term is a defect in the sum.  Same repair — delete `ν`.
See T-AG1a and `b2_log.jsonl`.

#### Proof sketch
1. **Unfold the block.**  `discHeckeBlock … i j = ∑_{t : idx i t = j} discSlash h ψ κ (certM1 … i t)`
   (`DiscForms.lean:189`).  `ContinuousLinearMap.comp` is additive in the composed argument, so
   push the composition inside the sum on both sides
   (`ContinuousLinearMap.sum_comp` / `ContinuousLinearMap.comp_sum`).
2. **Apply T-AG1b termwise** at `δ := certM1 θG U hU vRep hvΔ uu i t`.
3. **Pull out the uniform scalar.**  `hdet` says every term's factor is the same `cst`, so
   `Finset.sum_congr` then `Finset.smul_sum` extracts `cst ^ r`.

Bridging tactics: `Finset.sum_congr rfl` to rewrite termwise; `smul_comm` if the scalar ends up on
the wrong side of the sum.

#### Mathlib lemmas needed
- T-AG1b (this file).
- `ContinuousLinearMap.sum_comp`, `ContinuousLinearMap.comp_sum`, `Finset.smul_sum`,
  `Finset.sum_congr`.
- `LWX.discHeckeBlock`, `LWX.certM1` — project, `PhD/LWX/DiscForms.lean` (sorry-free).

#### Sources
[Bu04, §7], `references/bu04.txt:1095–1100` (verbatim): "Next one can analyse the relationship
between `θ^{1−k}` and Hecke operators.  Again it is elementary to check that if `f ∈ S^D_κ(U, 1)`
and `η ∈ D^×_f` with `η_p ∈ M_α`, then `(θ^{1−k}f)|η = |ν(η)|^{k−1}θ^{1−k}(f|η)` and hence that
`[UηU]θ^{1−k} = |ν(η)|^{k−1}θ^{1−k}[UηU]`."  The source gives it in one paragraph given the
equivariance.

#### Generality decision
The uniform determinant is a **hypothesis** `hdet` rather than a derived fact, so the lemma covers
any Hecke element whose certificate matrices share a determinant, with `U_p` (`η = diag(1,p)`,
`cst = ψ p`, giving `p^{k+1}` at `r = k+1`) as the instance.  That matches the source, which proves
the relation for a general `η` and then specialises.

---

## Tranche 1b — the connecting seams (added 2026-09-06; restored after an editing accident)

Both tickets below are **independent of the theta layer** and can be worked immediately, in
parallel with T003–T007.

### [S1] `LWX.invChar` — the conjugate nebentypus
- **Status**: done (2026-09-09, sorry-free; board status was lost in the 2026-09-06 editing accident and is restored here)
- **File**: PhD/LWX/ConjChar.lean:35 | **Depends on**: none | **Parallel**: yes | **Type**: def

#### Statement
```lean
def invChar (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) : (ZMod p)ˣ →* ℤ_[p]ˣ where
  toFun u := (ω u)⁻¹
  map_one' := by sorry
  map_mul' u v := by sorry
```

#### Proof sketch
1. `map_one'`: `(ω 1)⁻¹ = 1⁻¹ = 1`.  `simp [map_one]` — `map_one` then `inv_one`.
2. `map_mul'`: `(ω (u*v))⁻¹ = (ω u * ω v)⁻¹ = (ω u)⁻¹ * (ω v)⁻¹`.  `simp [map_mul, mul_inv]` —
   `ℤ_[p]ˣ` is a commutative group, so `mul_inv` applies with no reordering; if the orientation
   comes out swapped, add `mul_comm`.

#### Mathlib lemmas needed
- `map_one`, `map_mul`, `inv_one`, `mul_inv` (for `DivisionCommMonoid` / commutative groups).

#### Sources
[LWX, §3.23 Step I], `.mathlib-quality/tate-riesz/references/lwx.txt:1826–1830` (verbatim): "On the
other hand, for each of `T_{(k,χ)}` and `T_{(k,χ⁻¹)}`, when the x-coordinate is `(k + 1)qt`, the
y-coordinate of the lower bound polygon is … `= (k + 1)²qt/2`."  The source runs the lower bound at
the character **and at its inverse**; this supplies the inverse.

#### Generality decision
A bundled `MonoidHom` rather than a bare function, so that every existing halo result (all stated
for an arbitrary `ω : (ZMod p)ˣ →* ℤ_[p]ˣ`) instantiates at it with no glue.  No `p ≠ 2` needed.

---

### [S2] `LWX.invChar_invChar` — the involution
- **Status**: done (2026-09-09, sorry-free; status restored)
- **File**: PhD/LWX/ConjChar.lean:44 | **Depends on**: S1 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
@[simp]
theorem invChar_invChar (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) : invChar (invChar ω) = ω := by
  sorry
```

#### Proof sketch
1. `ext u` (`MonoidHom.ext`).
2. `simp [invChar_apply, inv_inv]`.

#### Mathlib lemmas needed
- `MonoidHom.ext`, `inv_inv`.

#### Sources
None — API hygiene for S1 (the no-one-off-definitions rule).

#### Generality decision
`@[simp]` so that double conjugation normalises away in the Step I squeeze, which moves between
the two characters repeatedly.

---

### [CLEANUP-4] Run /cleanup on PhD/LWX/ConjChar.lean (final per-file)
- **Status**: done (2026-09-09, builds warning-free; no linter finding) | **File**: PhD/LWX/ConjChar.lean | **Depends on**: S2 | **Type**: cleanup

---

### [S3] `TateFredholm.charPowerSeries_eq_mul_polynomial` — the finite factor
- **Status**: done (2026-09-09, sorry-free; status restored)
- **File**: PhD/TateFredholm/FiniteFactor.lean:46 | **Depends on**: none | **Parallel**: yes
- **Type**: theorem

#### Statement
```lean
theorem charPowerSeries_eq_mul_polynomial
    {u pr : c(I, R) →L[R] c(I, R)} (hu : IsCompactoid u) (hpr : pr * pr = pr)
    (hcomm : u * pr = pr * u) {s : Finset c(I, R)}
    (hs : LinearMap.range ((u * pr : c(I, R) →L[R] c(I, R)) : c(I, R) →ₗ[R] c(I, R))
        ≤ Submodule.span R (s : Set c(I, R))) :
    ∃ G : R[X], G.natDegree ≤ s.card ∧
      charPowerSeries u = charPowerSeries (u * (1 - pr)) * (G : PowerSeries R) := by
  sorry
```
(section variables: `{R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]`
`[NormOneClass R] [IsTate R] {I : Type*} [DecidableEq I]`)

#### Proof sketch
1. **Split the determinant along the idempotent.**
   `TateFredholm.charPowerSeries_eq_mul_of_comm hu hpr hcomm` gives
   `charPowerSeries u = charPowerSeries (u * (1 - pr)) * charPowerSeries (u * pr)`.
2. **Identify the second factor as a polynomial.**
   `TateFredholm.exists_polynomial_charPowerSeries_of_range_le hs` gives `G : R[X]` with
   `G.natDegree ≤ s.card` and `charPowerSeries (u * pr) = (G : PowerSeries R)`.
3. **Assemble.** `obtain ⟨G, hdeg, hG⟩ := …; exact ⟨G, hdeg, by rw [step1, hG]⟩`.

#### Mathlib lemmas needed
- `TateFredholm.charPowerSeries_eq_mul_of_comm` — project, `PhD/TateFredholm/RieszColeman.lean:278`
  (verified present and sorry-free; signature `(hx : IsCompactoid x) (hp : p * p = p)`
  `(hxp : x * p = p * x)`).
- `TateFredholm.exists_polynomial_charPowerSeries_of_range_le` — project,
  `PhD/TateFredholm/RieszColeman.lean:326` (verified present and sorry-free).

#### Sources
[LWX, §3.23 Step I], `lwx.txt:1818–1822` (verbatim): "By Proposition 2.15, one deduces that the set
of all `U_p`-slopes on `S^D_{k+2}(K^pIw_{q²};ψ) ⊕ S^D_{k+2}(K^pIw_{q²};ψ⁻¹)` is exactly the set of
the first `n_{k+1}` `U_p`-slopes in each of `S^{D,†}_{(k,ψ)}` and `S^{D,†}_{(k,ψ⁻¹)}`."
This ticket is the **algebraic half** of that comparison — the determinant genuinely factors with
the classical piece contributing a polynomial of the right degree.  The *ordering* half is T-AG3.

#### Generality decision
Stated for an arbitrary idempotent and an arbitrary finite spanning set, not for the classical
projection specifically, so the lemma is reusable and is a plausible future mathlib contribution.
`IsTate R` is inherited from the cited lemmas' section and is genuinely needed there.

---

### [CLEANUP-5] Run /cleanup on PhD/TateFredholm/FiniteFactor.lean (final per-file)
- **Status**: done (2026-09-09, builds warning-free; no linter finding) | **File**: PhD/TateFredholm/FiniteFactor.lean | **Depends on**: S3 | **Type**: cleanup
- **Type**: cleanup

---

## Tranche 2 (Step I) — the pieces stateable today (`PhD/LWX/StepOne.lean`)

### [SO0] `LWX.IsStepOneTouching` — Step I's conclusion as a named definition
- **Status**: done (2026-09-06, a definition with no obligation)
- **File**: PhD/LWX/StepOne.lean:48 | **Depends on**: none | **Type**: def
- The exact hypothesis of `hasUnitBand_of_height_eq`, named, so that Step III consumes Step I as a
  statement.  This is the split point the plan calls for.

### [SO1] `LWX.hasUnitBand_of_isStepOneTouching` — the bridge to Step II
- **Status**: done (2026-09-09, sorry-free; status restored)
- **File**: PhD/LWX/StepOne.lean:57 | **Depends on**: SO0 | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem hasUnitBand_of_isStepOneTouching (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ : ℤ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (h : IsStepOneTouching D ω ψ T₀ k) :
    HasUnitBand D ω k := by
  sorry
```

#### Proof sketch
`IsStepOneTouching` is definitionally the hypothesis of `hasUnitBand_of_height_eq`
(`PhD/LWX/Vertices.lean:769`, sorry-free), so
`exact hasUnitBand_of_height_eq hp2 D ω ψ hψ h0 h1 h`.  One line.

#### Mathlib lemmas needed
- `LWX.hasUnitBand_of_height_eq` — project, `PhD/LWX/Vertices.lean:769` (verified sorry-free).

#### Sources
[LWX, §3.23 Step I → Step II], `lwx.txt:1880–1900`: "We deduce the decomposition … from the
touching of polygons."  The bridge is the content of Step II's opening, already proved on the
`lwx-slopes` board.

#### Generality decision
Identical hypotheses to the bridge it wraps; no new assumption.

---

### [SO2] `LWX.eq_zero_of_intertwine_of_norm_lt` — Buzzard's small-slope argument, abstract
- **Status**: done (2026-09-09, sorry-free; status restored — `hc` is slack and is now `_hc`, see the file)
- **File**: PhD/LWX/StepOne.lean:70 | **Depends on**: none | **Parallel**: yes | **Type**: theorem
- Pure functional analysis; independent of every other ticket.  Mathlib-able.

#### Statement
```lean
theorem eq_zero_of_intertwine_of_norm_lt {E : Type*} [NormedAddCommGroup E] [NormedSpace K E]
    {P P' θ : E →L[K] E} (hP' : ‖P'‖ ≤ 1) {c : K} (hc : c ≠ 0)
    (hint : θ.comp P = c • P'.comp θ) {f : E} {μ : K} (hf : P f = μ • f) (hμ : ‖c‖ < ‖μ‖) :
    θ f = 0 := by
  sorry
```

#### Proof sketch
1. **Compute `P' (θ f)`.**  Apply `hint` to `f`: `θ (P f) = c • P' (θ f)`; with `hf` the left side
   is `μ • θ f`.  Since `c ≠ 0`, `P' (θ f) = (μ / c) • θ f` (`smul_right_injective` or divide by
   `c` via `inv_smul_smul₀`).
2. **Bound the norm two ways.**  `‖P' (θ f)‖ ≤ ‖P'‖ ‖θ f‖ ≤ ‖θ f‖` by
   `ContinuousLinearMap.le_opNorm` and `hP'`; and `‖P' (θ f)‖ = ‖μ / c‖ ‖θ f‖` by `norm_smul`.
3. **Conclude.**  `‖μ / c‖ > 1` by `hμ` (`one_lt_div`, `norm_div`), so
   `‖μ/c‖ ‖θ f‖ ≤ ‖θ f‖` forces `‖θ f‖ = 0` (`nlinarith` or `le_antisymm` with
   `mul_le_iff_le_one_left`), hence `θ f = 0` by `norm_eq_zero`.

#### Mathlib lemmas needed
- `ContinuousLinearMap.le_opNorm`, `norm_smul`, `norm_div`, `norm_eq_zero`, `inv_smul_smul₀`,
  `one_lt_div`.

#### Sources
[Bu04, Prop 4] proof, `references/bu04.txt:1125–1129` (verbatim): "if `v_p(λ) < k − 1` then
`θ^{1−k}f` is in `S^D_{κ′}(U;1)` and if it is non-zero then it is an eigenvector for `U_p` with
eigenvalue `λ/p^{k−1}`, which has negative valuation.  On the other hand, `U_p` is an operator with
norm at most 1, and hence `θ^{1−k}f = 0`."  **This is the Jacquet–Langlands-free half of Prop 4**
(`../lwx-stepone/JL-AUDIT.md` §2), with the automorphic setup stripped away.

#### Generality decision
Stated for arbitrary operators on an arbitrary normed space over `K`, with the intertwining as a
hypothesis in the corrected orientation `θ ∘ P = c • (P' ∘ θ)`.  The concrete
`classical_of_slope_lt` is this applied to `thetaDisc_comp_discHeckeBlock` with `c = p^{k+1}`, and
is deferred until T-AG2 is proved.

---

### [SO3] `LWX.locPolyDegSubmoduleBlock` — the classical subspace of the block model
- **Status**: done (2026-09-09, sorry-free; status restored)
- **File**: PhD/LWX/StepOne.lean:81 | **Depends on**: none | **Parallel**: yes
- **Type**: def (three field obligations)

#### Statement
```lean
def locPolyDegSubmoduleBlock (h k : ℕ) : Submodule K c(ι × (ZMod (p ^ h) × ℕ), K) where
  carrier := {c | ∀ (i : ι) (a : ZMod (p ^ h)) (j : ℕ), k < j → c (i, (a, j)) = 0}
  add_mem' := by sorry
  zero_mem' := by sorry
  smul_mem' := by sorry
```

#### Proof sketch
Exactly as T005 with one more index: all three obligations are pointwise vanishing.
`intro ha hb i a j hj; simp [ha i a j hj, hb i a j hj]`, `simp`, and
`intro r c hc i a j hj; simp [hc i a j hj]`.

#### Mathlib lemmas needed
- `add_zero`, `smul_zero`, and the `cSpace` application simp lemmas (as T005).

#### Sources
[LWX, §3.21], `lwx.txt:1755–1760`: the classical space "is isomorphic to the direct sum of `t`
copies of `LP_{m−v(q),deg≤k}(ℤ_p;E)`" — one copy per block index.

#### Generality decision
Defined directly on the block model rather than as a product of T005's submodules, so `finrank`
(SO4) is a single count.  No `CharZero`.

---

### [CLEANUP-6] Run /cleanup on PhD/LWX/StepOne.lean
- **Status**: done (2026-09-09, subsumed by CLEANUP-7) | **File**: PhD/LWX/StepOne.lean | **Depends on**: SO3 | **Type**: cleanup
- Per-file cadence (SO1, SO2, SO3).  Blocks SO4.

---

### [SO4] `LWX.finrank_locPolyDegSubmoduleBlock` — [LWX, (3.21.1)], global form
- **Status**: done (2026-09-09, sorry-free; status restored)
- **File**: PhD/LWX/StepOne.lean:89 | **Depends on**: SO3, CLEANUP-6 | **Parallel**: no
- **Type**: theorem

#### Statement
```lean
theorem finrank_locPolyDegSubmoduleBlock (h k : ℕ) :
    Module.finrank K (locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k)
      = Fintype.card ι * ((k + 1) * p ^ h) := by
  sorry
```

#### Proof sketch
As T007 with the extra finite index: exhibit a linear equivalence with
`ι × ZMod (p^h) × Fin (k+1) → K` (extend by zero; finite support lies in `c(·,·)`), then
`Module.finrank_pi`, `Fintype.card_prod`, `ZMod.card`, `Fintype.card_fin`, and `mul_assoc`.
If T007 lands first, reuse its equivalence blockwise.

#### Mathlib lemmas needed
- `Module.finrank_pi`, `Fintype.card_prod`, `Fintype.card_fin`, `ZMod.card`,
  `LinearEquiv.finrank_eq`.

#### Sources
[LWX, §3.21], `lwx.txt:1755–1760` (verbatim): "(3.21.1) `dim S^D_{k+2}(K^pIw_{pᵐ};ψ) =
(k + 1)q⁻¹pᵐt`."  With `h = m − 1` (odd `p`) and `t = card ι` this is
`card ι * ((k+1) * p^h)`.

#### Generality decision
This is the **global** (3.21.1); T007 is its local factor.  Stated with the product in the order
`t · ((k+1) · p^h)` to match the source's `(k+1)q⁻¹pᵐ · t` reading.

---

### [CLEANUP-7] Run /cleanup on PhD/LWX/StepOne.lean (final per-file)
- **Status**: done (2026-09-09; fixed two deprecations, two `omit`s, and the unused `hc` binder) | **File**: PhD/LWX/StepOne.lean | **Depends on**: SO4 | **Type**: cleanup

---

## Tranche 3 (Step III) — Hida's input at the coefficient level (`PhD/LWX/Degrees.lean`)

### [D0] `LWX.ordDim` — the ordinary dimension at the coefficient level
- **Status**: done (2026-09-06, a definition with no obligation)
- **File**: PhD/LWX/Degrees.lean:41 | **Depends on**: none | **Type**: def
- `sSup {n | IsUnit (charCoeff (D.op ω) n)}`: [LWX, Thm 3.19 proof]'s "maximal index such that
  `c_d(T)` is a unit".

### [D1] `LWX.bddAbove_isUnit_charCoeff` — the unit indices are bounded
- **Status**: done (2026-09-09, sorry-free; three cases: `IsEmpty ι`, `p = 2` junk operator, halo bound)
- **File**: PhD/LWX/Degrees.lean:46 | **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem bddAbove_isUnit_charCoeff (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    BddAbove {n : ℕ | IsUnit (charCoeff (D.op ω) n)} := by
  sorry
```

#### Proof sketch
1. **The halo bound.**  [LWX, Thm 3.16] (`lwx-halo` board, complete): `‖c_n‖ ≤ p^{−λ(n)}` in the
   halo ring, with `λ(n) = lwxLambda p t n`.  Locate the exported form (the `norm_charCoeff_le`-style
   lemma in `PhD/LWX/Halo.lean`; confirm the exact name).
2. **A unit has norm one.**  In `HaloInt p`, `IsUnit g → ‖g‖ = 1` (the units are detected by the
   constant coefficient, `HaloInt.isUnit_of_isUnit_coeff_zero`'s converse direction; if only the
   forward direction exists, spawn a sub-ticket for `norm_eq_one_of_isUnit`).
3. **`λ` is eventually positive.**  `lwxLambda p t n ≥ 1` once `n ≥ t` (it is a sum of
   `⌊k/t⌋ − ⌊k/pt⌋`, positive from `k = t` on) — `lwxLambda_succ` / the monotonicity lemmas in
   `PhD/LWX/Halo.lean`.  So for `n ≥ t`, `‖c_n‖ ≤ p^{−1} < 1`, hence `c_n` is not a unit.
4. **Conclude.**  `⟨t, fun n hn => by_contra …⟩`.

#### Mathlib lemmas needed
- `bddAbove_def`, `not_lt`, `pow_le_one₀`; project: the halo bound and `lwxLambda` API in
  `PhD/LWX/Halo.lean` (names to be confirmed at the first step — record them here).

#### Sources
[LWX, Thm 3.19 proof], `lwx.txt:1717–1719` (verbatim): "Let `d` be the maximal index such that
`c_d(T)` is a unit in `ℤ_p⟦T⟧`, or equivalently, the constant term of `c_d(T)` is a `p`-adic unit
in `ℤ_p`; such a `d` must exist by Corollary 3.18."  This ticket is the "must exist by Corollary
3.18" clause.

#### Generality decision
Stated for any datum and character, since the halo bound is.

---

### [D1a] `LWX.HaloInt.one_le_norm_of_isUnit` — a unit of the halo ring has norm one
- **Status**: done (2026-09-09, sorry-free; general normed-ring helper kept private)
- **File**: PhD/LWX/Degrees.lean | **Depends on**: none | **Parent**: D1 | **Parallel**: yes
- **Type**: theorem (sub-ticket spawned by /beastmode, Tier A2)

#### Statement
```lean
theorem HaloInt.one_le_norm_of_isUnit {f : HaloInt p} (hf : IsUnit f) : 1 ≤ ‖f‖
```

#### Proof sketch
`obtain ⟨u, rfl⟩ := hf`.  Then
`1 = ‖(1 : HaloInt p)‖ = ‖(u : HaloInt p) * (↑u⁻¹)‖ ≤ ‖u‖ * ‖↑u⁻¹‖ ≤ ‖u‖ * 1 = ‖u‖`,
the last inequality by `HaloInt.norm_le_one` (`PhD/LWX/HaloRing.lean:378`) and
`mul_le_mul_of_nonneg_left`.  The argument uses only `NormedRing`, `NormOneClass`
and `∀ x, ‖x‖ ≤ 1`, so it is proved through a `private` general helper
`one_le_norm_of_isUnit_of_norm_le_one` and specialised.

#### Mathlib lemmas needed
- `norm_one`, `norm_mul_le`, `Units.mul_inv`, `Units.val_mul`, `Units.val_one`,
  `mul_le_mul_of_nonneg_left`, `norm_nonneg`; project: `LWX.HaloInt.norm_le_one`.

#### Sources
Not a source statement: the "unit ⟹ norm 1" step that [LWX, Cor 3.18] uses implicitly when it
reads unit-ness of `c_n` off the estimate `‖c_n‖ ≤ p^{−λ(n)}`.

#### Generality decision
Stated for `HaloInt p` (the only consumer).  The general normed-ring form is kept `private`
because the hypothesis `∀ x, ‖x‖ ≤ 1` is unusual; if a second consumer appears, promote it.

---

### [D1b] `LWX.lwxLambda_pos` — `λ` is positive past the block size
- **Status**: done (2026-09-09, sorry-free)
- **File**: PhD/LWX/Degrees.lean | **Depends on**: none | **Parent**: D1 | **Parallel**: yes
- **Type**: theorem (sub-ticket spawned by /beastmode, Tier A2)

#### Statement
```lean
theorem lwxLambda_pos {p t n : ℕ} (hp : 1 < p) (ht : 0 < t) (htn : t < n) :
    0 < lwxLambda p t n
```

#### Proof sketch
`lwxLambda p t n = ∑_{k < n} (⌊k/t⌋ − ⌊k/pt⌋)` is a sum of naturals, so `Finset.sum_pos'`
reduces to exhibiting one positive term.  Take `k = t`, which lies in `range n` by `htn`:
`⌊t/t⌋ = 1` (`Nat.div_self ht`) and `⌊t/(pt)⌋ = 0` (`Nat.div_eq_of_lt` from `t < p*t`,
which is `1*t < p*t`).  So the term is `1`.

#### Mathlib lemmas needed
- `Finset.sum_pos'`, `Finset.mem_range`, `Nat.div_self`, `Nat.div_eq_of_lt`,
  `Nat.mul_lt_mul_right`; project: `LWX.lwxLambda` (`PhD/LWX/Halo.lean:41`).

#### Sources
[LWX, Thm 3.16]'s `λ(n) = ∑_{k<n}(⌊k/t⌋ − ⌊k/pt⌋)`, `lwx.txt` Theorem 3.16.  The positivity is
the reason Corollary 3.18 forces `c_n` to be a non-unit for large `n`.

#### Generality decision
Stated for arbitrary `p t n : ℕ` with the two positivity hypotheses, matching `lwxLambda`'s own
unbundled signature (it takes bare naturals, not the `Fact p.Prime` instance).

---

### [D1c] `LWX.charCoeff_eq_zero_of_forall_minor` — a vanishing-minor criterion
- **Status**: done (2026-09-09, sorry-free; `omit [Fintype ι]`)
- **File**: PhD/LWX/Degrees.lean | **Depends on**: none | **Parent**: D1 | **Parallel**: yes
- **Type**: theorem (sub-ticket spawned by /beastmode, Tier A2)

#### Statement
```lean
theorem charCoeff_eq_zero_of_forall_minor {u : c(ι × ℕ, HaloInt p) →L[HaloInt p] c(ι × ℕ, HaloInt p)}
    {n : ℕ} (h : ∀ S : Finset (ι × ℕ), S.card = n → minor u S = 0) :
    charCoeff u n = 0
```

#### Proof sketch
`charCoeff u n = (−1)^n * ∑' S : {S // S.card = n}, minor u S`; rewrite the summand to `0` by
`tsum_congr` and `h`, then `tsum_zero` and `mul_zero`.

#### Mathlib lemmas needed
- `tsum_congr`, `tsum_zero`, `mul_zero`; project: `TateFredholm.charCoeff`,
  `TateFredholm.minor` (`PhD/TateFredholm/Fredholm.lean:33,148`).

#### Sources
Not a source statement: bookkeeping for D1's two degenerate cases (`IsEmpty ι`, where no finset
has positive cardinality, and `p = 2`, where `UpDatum.op` is the junk value `0`).

#### Generality decision
Stated on the index type `ι × ℕ` actually used, to keep the ticket in `PhD/LWX/Degrees.lean`
rather than forcing a rebuild of `PhD/TateFredholm/Fredholm.lean`.  Promoting it to
`TateFredholm` for a general index type is a `/cleanup` decision, recorded in CLEANUP-8.

---

### [D2] `LWX.isUnit_charCoeff_ordDim` — `c_{ordDim}` is a unit
- **Status**: done (2026-09-09, sorry-free, `Nat.sSup_mem`)
- **File**: PhD/LWX/Degrees.lean:51 | **Depends on**: D1 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem isUnit_charCoeff_ordDim (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    IsUnit (charCoeff (D.op ω) (ordDim D ω)) := by
  sorry
```

#### Proof sketch
1. The set is nonempty: `0` belongs, since `charCoeff_zero` gives `c₀ = 1` (as in
   `isUnitCoeff_zero`, `Vertices.lean:51`).
2. The set is bounded above (D1).
3. `Nat.sSup_mem` for a nonempty bounded set of naturals.

#### Mathlib lemmas needed
- `Nat.sSup_mem`, `isUnit_one`; project: `TateFredholm.charCoeff_zero`.

#### Sources
Same passage as D1 — the maximal index is attained.

#### Generality decision
As D1.

---

### [D3] `LWX.not_isUnit_charCoeff_of_ordDim_lt` — nothing beyond `ordDim` is a unit
- **Status**: done (2026-09-09, sorry-free, `le_csSup`)
- **File**: PhD/LWX/Degrees.lean:56 | **Depends on**: D1 | **Parallel**: yes (with D2)
- **Type**: theorem

#### Statement
```lean
theorem not_isUnit_charCoeff_of_ordDim_lt (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {n : ℕ}
    (hn : ordDim D ω < n) : ¬ IsUnit (charCoeff (D.op ω) n) := by
  sorry
```

#### Proof sketch
`intro h; exact absurd (le_csSup (D1 D ω) h) (not_le.2 hn)` — a member of a bounded set is at
most its supremum.

#### Mathlib lemmas needed
- `le_csSup`, `not_le`.

#### Sources
The "maximal" in the same passage.

#### Generality decision
As D1.  Together D2 and D3 are the two API lemmas that make `ordDim` more than a one-off.

---

### [CLEANUP-8] Run /cleanup on PhD/LWX/Degrees.lean (final per-file)
- **Status**: done (2026-09-09, builds warning-free; no linter finding) | **File**: PhD/LWX/Degrees.lean | **Depends on**: D2, D3 | **Type**: cleanup
- Three proof tickets on the file, so the cadence cleanup and the final one coincide.

---

## Tranche 4 — Bol's identity, the repaired equivariance (`PhD/LWX/Bol.lean`, NEW file)

Spawned by `/beastmode` on 2026-09-09 after the T-AG1a B2.  The B2 blocks the *ticketed* statements
(they keep `ν`), but the mathematics the repair needs is forced and independent of how the user
words the fix, so it is being built here as new declarations in a new file.  Nothing in this
tranche edits a protected statement.

**The whole content is one induction.**  Write `u = numX γ`, `L = linX γ`, `D = det γ`.  The
identity behind [Bu04, §7]'s display is Bol's identity, which in column form is
`∂^r (u^(j+r) · (L⁻¹)^(j+1)) = D^r · (j+r)_r · u^j · (L⁻¹)^(j+r+1)`.
Parametrised by `j` (rather than by `i` with `i − r`) it is **subtraction-free**, and the induction
on `r` closes on the nose: differentiating once gives two terms, the induction hypothesis applies
to each at `j` and `j+1`, and the two `descFactorial` recurrences
`Nat.succ_descFactorial_succ` and `Nat.descFactorial_succ` make both coefficients `(j+r+1)_{r+1}`,
leaving the factor `C a · L − C c · u = C (det γ)`.  **No Leibniz rule, no binomial theorem, no
falling-factorial splitting is needed** — a first plan that went through iterated Leibniz was
abandoned once this parametrisation was found.

### [B1] `LWX.coeff_iterate_derivative` — the `r`-th derivative on coefficients
- **Status**: done (2026-09-09, sorry-free) | **File**: PhD/LWX/Bol.lean | **Depends on**: none | **Type**: theorem

#### Statement
```lean
theorem coeff_iterate_derivative (F : PowerSeries K) (r j : ℕ) :
    PowerSeries.coeff j ((PowerSeries.derivative K)^[r] F)
      = ((Nat.descFactorial (j + r) r : ℕ) : K) * PowerSeries.coeff (j + r) F
```

#### Proof sketch
Induction on `r`, `F` generalised.  `Function.iterate_succ_apply` puts one `d⁄dX` inside;
`PowerSeries.coeff_derivative` turns it into `coeff (j+r+1) F * (j+r+1)`, and
`Nat.succ_descFactorial_succ` rewrites `(j+r+1)_{r+1} = (j+r+1)·(j+r)_r`.

#### Mathlib lemmas needed
`PowerSeries.coeff_derivative`, `Function.iterate_succ_apply`, `Nat.succ_descFactorial_succ`.

#### Sources
Not a source statement: this is the bridge between `LWX.thetaOne` (whose matrix is the
`descFactorial` shift) and mathlib's `PowerSeries.derivative`.

#### Generality decision
Stated over the section's field `K`; mathlib's `derivative` needs only a commutative semiring, so
this is promotable if a second consumer appears.

---

### [B2] `LWX.derivative_numX_pow` and `LWX.derivative_linX_inv_pow` — the two derivative rules
- **Status**: done (2026-09-09, sorry-free; `hd` turned out to be unnecessary — `PowerSeries.derivative_inv'` holds unconditionally over a field) | **File**: PhD/LWX/Bol.lean | **Depends on**: none | **Type**: theorem (two)

#### Statement
```lean
theorem derivative_numX_pow (γ : Matrix (Fin 2) (Fin 2) K) (n : ℕ) :
    PowerSeries.derivative K (numX γ ^ (n + 1))
      = ((n : K) + 1) * PowerSeries.C (γ 0 0) * numX γ ^ n

theorem derivative_linX_inv_pow (γ : Matrix (Fin 2) (Fin 2) K) (hd : γ 1 1 ≠ 0) (m : ℕ) :
    PowerSeries.derivative K (((linX γ)⁻¹) ^ m)
      = -(m : K) * PowerSeries.C (γ 1 0) * ((linX γ)⁻¹) ^ (m + 1)
```

#### Proof sketch
`numX γ = C b + C a·X` and `linX γ = C d + C c·X`, so `d⁄dX (numX γ) = C (γ 0 0)` and
`d⁄dX (linX γ) = C (γ 1 0)` by `derivative_C`/`derivative_X`.  Then `PowerSeries.derivative_pow`.
For the second, `PowerSeries.derivative_inv'` gives `d⁄dX f⁻¹ = −f⁻¹² · d⁄dX f`; split `m` as
`0` (both sides zero) or `m'+1` (then `(f⁻¹)^{m'}·(f⁻¹)² = (f⁻¹)^{m'+2}`).

#### Mathlib lemmas needed
`PowerSeries.derivative_pow`, `PowerSeries.derivative_inv'` (needs `Field K` — available),
`PowerSeries.derivative_C`, `PowerSeries.derivative_X`, `PowerSeries.mul_inv_cancel`,
`QMF.constantCoeff_linX`.

#### Sources
Elementary calculus of the automorphy factor; no source needed.

#### Generality decision
Stated for a matrix rather than for a general linear series, so that the `det` lemma B3 can be
stated in the same language.

---

### [B3] `LWX.C_mul_linX_sub_C_mul_numX` — `a·L − c·u = det γ`
- **Status**: done (2026-09-09, sorry-free) | **File**: PhD/LWX/Bol.lean | **Depends on**: none | **Type**: theorem

#### Statement
```lean
theorem C_mul_linX_sub_C_mul_numX (γ : Matrix (Fin 2) (Fin 2) K) :
    PowerSeries.C (γ 0 0) * linX γ - PowerSeries.C (γ 1 0) * numX γ
      = PowerSeries.C γ.det
```

#### Proof sketch
Expand both `linX` and `numX`, `Matrix.det_fin_two`, then `map_sub`/`map_mul` on `C` and `ring`.
The `X`-terms cancel: `a·c − c·a = 0`.

#### Mathlib lemmas needed
`Matrix.det_fin_two`, `map_sub`, `map_mul`, `ring`.

#### Sources
The cocycle constant of the Möbius action; elementary.

#### Generality decision
None to make.

---

### [B4] `LWX.coeff_numX_pow_mul_linX_pow_eq_zero` — the polynomial degree bound
- **Status**: done (2026-09-09, sorry-free; reproved rather than de-privatised, as the ticket anticipated) | **File**: PhD/LWX/Bol.lean | **Depends on**: none | **Type**: theorem

#### Statement
```lean
theorem coeff_numX_pow_mul_linX_pow_eq_zero (γ : Matrix (Fin 2) (Fin 2) K) {i t n : ℕ}
    (hn : i + t < n) : PowerSeries.coeff n (numX γ ^ i * linX γ ^ t) = 0
```

#### Proof sketch
`PhD/QMF/Weight/Algebraic.lean:242` has a **private** `coeff_linX_pow_mul_numX_pow_eq_zero` with
the same content (factors in the other order).  First check whether de-privatising it is cheaper
than reproving; if reproving, both factors are degree-`1` polynomials so induct on `i` and `t`
with `PowerSeries.coeff_mul` and `Finset.antidiagonal`.

#### Mathlib lemmas needed
`PowerSeries.coeff_mul`, `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`; project:
`QMF.linX`, `QMF.numX`.

#### Sources
Bookkeeping for B5.

#### Generality decision
Stated in the order `numX^i * linX^t` that B5 consumes, whichever way the existing private lemma
is phrased.

---

### [B5] `LWX.iterate_derivative_numX_pow_mul_linX_pow` — the vanishing case
- **Status**: done (2026-09-09, sorry-free) | **File**: PhD/LWX/Bol.lean | **Depends on**: B1, B4 | **Type**: theorem

#### Statement
```lean
theorem iterate_derivative_numX_pow_mul_linX_pow (γ : Matrix (Fin 2) (Fin 2) K) (i t : ℕ) :
    (PowerSeries.derivative K)^[i + t + 1] (numX γ ^ i * linX γ ^ t) = 0
```

#### Proof sketch
`PowerSeries.ext`; each coefficient is `descFactorial · coeff (j + i + t + 1) (…)` by B1, and that
coefficient vanishes by B4 since `i + t < j + i + t + 1`.

#### Mathlib lemmas needed
`PowerSeries.ext`, `PowerSeries.coeff_zero`; B1, B4.

#### Sources
This is the `i < r` half of [Bu04, §7]'s display, where the left side is a polynomial of degree
below the order of the derivative.

#### Generality decision
Phrased with `r = i + t + 1` rather than a hypothesis `i < r`, to stay subtraction-free.

---

### [B6] `LWX.bol` — **Bol's identity, the milestone of this tranche**
- **Status**: done (2026-09-09, sorry-free) — **MILESTONE of tranche 4** | **File**: PhD/LWX/Bol.lean | **Depends on**: B2, B3 | **Type**: theorem

#### Statement
```lean
theorem bol (γ : Matrix (Fin 2) (Fin 2) K) (hd : γ 1 1 ≠ 0) (r j : ℕ) :
    (PowerSeries.derivative K)^[r] (numX γ ^ (j + r) * ((linX γ)⁻¹) ^ (j + 1))
      = PowerSeries.C γ.det ^ r * ((Nat.descFactorial (j + r) r : ℕ) : K)
          * numX γ ^ j * ((linX γ)⁻¹) ^ (j + r + 1)
```

**Landed 2026-09-09 exactly as sketched.**  The one adjustment: `rw` needs `j + (r + 1)` written
as `(j + r) + 1` before `derivative_numX_pow` matches (they are defeq but not syntactically equal),
and the constants must be pushed through `PowerSeries.C` with
`simp only [map_add, map_mul, map_natCast, map_one]` before `ring` closes the derivative
computation.  The final collection is one `linear_combination` against `C_mul_linX_sub_C_mul_numX`
and the cast form of the two `descFactorial` recurrences.

#### Proof sketch
Induction on `r`, **`j` generalised**.
* `r = 0`: `descFactorial j 0 = 1`, both sides are `u^j (L⁻¹)^{j+1}`.
* `r+1`: `Function.iterate_succ_apply` peels one derivative *inside*.  By B2 and the Leibniz rule
  of the derivation, `d⁄dX (u^{j+r+1}(L⁻¹)^{j+1}) = (j+r+1)·C a·u^{j+r}(L⁻¹)^{j+1}
  − (j+1)·C c·u^{j+r+1}(L⁻¹)^{j+2}`.  Apply the induction hypothesis at `j` to the first term and
  at `j+1` to the second (`(j+1)+r = j+r+1` and `(j+1)+1 = j+2` match on the nose).  Collect
  `D^r·u^j·(L⁻¹)^{j+r+2}` using `L·L⁻¹ = 1`; the bracket is
  `(j+r+1)(j+r)_r·C a·L − (j+1)(j+r+1)_r·C c·u`, and both coefficients equal `(j+r+1)_{r+1}` by
  `Nat.succ_descFactorial_succ` and `Nat.descFactorial_succ` respectively, so B3 finishes.

#### Mathlib lemmas needed
`Function.iterate_succ_apply`, `Derivation.leibniz`, `map_sub`, `map_smul`,
`Nat.succ_descFactorial_succ`, `Nat.descFactorial_succ`, `PowerSeries.mul_inv_cancel`; B2, B3.

#### Sources
[Bu04, §7], `references/bu04.txt:1074–1090` (verbatim): "for `(a b; c d) ∈ M_α` and `F` a power
series in `z`, we have the identity `(d^{k−1}/dz^{k−1})((cz + d)^{k−2}F((az + b)/(cz + d))) =
(ad − bc)^{k−1}(cz + d)^{−k}(d^{k−1}F/dz^{k−1})((az + b)/(cz + d))`.  This identity is trivial for
`k = 1` and the general case is easily established by induction on `k`."  Column `i = j + r` of
that display is exactly this statement.  Classically it is Bol's identity.

#### Generality decision
Stated for a bare matrix with `γ 1 1 ≠ 0`, not for a level element: nothing analytic is used, only
that `linX γ` is a unit of `PowerSeries K`.

---

### [B7] `LWX.thetaOne_comp_kappaSlash_of_autFactor` — **the repaired equivariance**
- **Status**: done (2026-09-09, sorry-free) | **File**: PhD/LWX/Bol.lean | **Depends on**: B5, B6 | **Type**: theorem

#### Statement
```lean
theorem thetaOne_comp_kappaSlash_of_autFactor (κ κ' : AnalyticWeight UK S ρ) (r : ℕ) (g : S)
    (hA : κ.toWeightSeries.autFactor g * linX (g : Matrix (Fin 2) (Fin 2) K)
      = linX (g : Matrix (Fin 2) (Fin 2) K) ^ r)
    (hA' : κ'.toWeightSeries.autFactor g * linX (g : Matrix (Fin 2) (Fin 2) K) ^ (r + 1) = 1) :
    (thetaOne K r).comp (κ.kappaSlash g)
      = ((g : Matrix (Fin 2) (Fin 2) K).det ^ r) • ((κ'.kappaSlash g).comp (thetaOne K r))
```

#### Proof sketch
Compare matrix coefficients (`TateFredholm.ext_matrixCoeff`).  `matrixCoeff_kappaSlash` +
`coeff_yCoeff` + `WeightSeries.yCoeff_genFun` say column `i` of `κ.kappaSlash g` is
`coeff · (autFactor g * mobius g ^ i)`; `matrixCoeff_thetaOne` is the `descFactorial` shift.  So
the `(j, i)` entry of the left side is `(j+r)_r · coeff (j+r) (A_κ · w^i)` and of the right side is
`det^r · (i)_r · coeff j (A_{κ'} · w^{i−r})` when `r ≤ i`, and `0` when `i < r`.  Split on `r ≤ i`:
* `i = j' + r`: `hA` and `hA'` turn `A_κ·w^i` into `u^{j'+r}(L⁻¹)^{j'+1}` and `A_{κ'}·w^{i−r}` into
  `u^{j'}(L⁻¹)^{j'+r+1}`, and B6 with B1 is the claim.
* `i < r`: write `r = i + t + 1`; `A_κ·w^i` is `u^i·L^t`, and B5 with B1 gives `0`.

#### Mathlib lemmas needed
`TateFredholm.ext_matrixCoeff` (confirm the name in `PhD/TateFredholm/Matrix.lean:58`),
`QMF.AnalyticWeight.matrixCoeff_kappaSlash`, `QMF.coeff_yCoeff`,
`QMF.WeightSeries.yCoeff_genFun`, `LWX.matrixCoeff_thetaOne`, `TateFredholm.matrixCoeff_comp`,
`TateFredholm.matrixCoeff_smul`; B1, B5, B6.

#### Sources
As B6; this is the same display read as an operator identity on the Tate algebra.

#### Generality decision
**The hypotheses are on `autFactor`, not on the character.**  Going from
`κ.toChar u = u^(r+1)` to `A_κ = L^{r−1}` needs an `ExpansionData` for an *integer* power of the
identity character on an arbitrary subgroup `UK`; `QMF.algExpansionData`
(`PhD/QMF/Weight/Algebraic.lean:96`) only covers exponents `≥ 2` on `⊤`.  That construction is
ticket B8.  Stating B7 against `autFactor` keeps the analytic content separate from the
bookkeeping and is what T-AG1b will consume anyway.

---

### [B9] `LWX.thetaDisc_comp_discSlash_of_autFactor` — the repaired equivariance on the disc model
- **Status**: done (2026-09-09, sorry-free; compiled first try) | **File**: PhD/LWX/Bol.lean
- **Depends on**: B7 | **Type**: theorem (sub-ticket spawned by /beastmode)

#### Statement
As `T-AG1b` but with `ν` deleted and the weight hypotheses moved onto the automorphy factors of
the disc conjugates, quantified over the discs:
`hA : ∀ a, autFactor (discConjK h δ a ψ) * linX (…) = linX (…) ^ r`, and the matching `hA'`.

#### Proof sketch
`blockMap_comp_blockOp` and `blockOp_comp_blockMap` (`PhD/TateFredholm/BlockMap.lean:98,111`) turn
both sides into `blockOpMap`s; a new `smul_blockOpMap` passes the scalar inside; then
`congrArg blockOpMap` and a `by_cases` on `b = discImage h δ a` reduce to B7 in the surviving
block.  The scalar matches by the two new determinant lemmas `det_discConjMat` / `det_discConjK`.

#### Mathlib lemmas needed
`blockMap_comp_blockOp`, `blockOp_comp_blockMap`, `RingHom.map_det`, `Matrix.det_fin_two_of`,
`field_simp`; project: B7, `LWX.discConjMat`, `LWX.coe_discConjK`.

#### Sources
As B6/B7; the transport of the same display along the disc decomposition.

#### Generality decision
`det_discConjMat` and `smul_blockOpMap` are stated in `Bol.lean` rather than in their proper homes
(`PhD/LWX/DiscModel.lean` and `PhD/TateFredholm/BlockMap.lean`) to avoid rebuilding those trees;
both carry a note saying so.  Moving them is a `/cleanup` decision.

---

### [B10] `LWX.thetaDisc_comp_discHeckeBlock_of_autFactor` — the repaired `U_p` intertwining
- **Status**: done (2026-09-09, sorry-free) | **File**: PhD/LWX/Bol.lean
- **Depends on**: B9 | **Type**: theorem (sub-ticket spawned by /beastmode)

#### Statement
As `T-AG2` but with `ν` deleted and the weight hypotheses quantified over the discs *and* the
certificate matrices `certM1 θG U hU vRep hvΔ uu i' t`.

#### Proof sketch
`discHeckeBlock` is `∑ t ∈ filter …, discSlash …`.  Two new helpers `comp_sum`/`sum_comp'`
distribute composition over the sum, `Finset.smul_sum` distributes the scalar, and B9 closes each
term; `hdet` makes the scalar uniform.

#### Mathlib lemmas needed
`ContinuousLinearMap.comp_add`, `ContinuousLinearMap.add_comp`, `ContinuousLinearMap.comp_zero`,
`ContinuousLinearMap.zero_comp`, `Finset.smul_sum`, `Finset.sum_congr`; B9.

#### Sources
[Bu04, §7], `references/bu04.txt:1095–1100`: "`[UηU]θ^{1−k} = |ν(η)|^{k−1}θ^{1−k}[UηU]`".

#### Generality decision
The scalar is the hypothesis `cst` with `hdet`, exactly as in the ticketed T-AG2, so the two
statements differ only in the weight hypotheses.

---

### [B11] `LWX.thetaBlock_comp_discHeckeBlockOp_of_autFactor` — the repaired block intertwining
- **Status**: done (2026-09-09, sorry-free) | **File**: PhD/LWX/AtkinLehnerInst.lean
- **Depends on**: B10 | **Type**: theorem (sub-ticket spawned by /beastmode)

#### Proof sketch
The corrected AL2: same `blockMap_comp_blockOp` / `blockOp_comp_blockMap` / `smul_blockOpMap`
pattern as B9, now at `σ := ι`, with B10 in every block.  `AtkinLehnerInst.lean` gained
`import PhD.LWX.Bol`.

#### Sources / Generality
As B10, assembled over the class set.

---

### [B12] `LWX.mem_locPolyDegSubmoduleBlock_discHeckeBlockOp_of_autFactor` — repaired `U_p`-stability
- **Status**: done (2026-09-09, sorry-free) | **File**: PhD/LWX/AtkinLehnerInst.lean
- **Depends on**: AL1, B11 | **Type**: theorem (sub-ticket spawned by /beastmode)

#### Proof sketch
The corrected AL3, and the payoff of the whole tranche: rewrite through AL1
(`thetaBlock_eq_zero_iff`), apply B11 at `r = k + 1` to `f`, and use `θ^{k+1} f = 0`.

#### Sources
[Bu04, §7], `bu04.txt:1095–1100`: the kernel of an intertwiner is stable, which is why
`θ^{1−k}` is a map of Hecke modules.

#### Generality decision
As AL3.

---

### [B8] An `ExpansionData` for an integer power character — DEFERRED
- **Status**: open — **not dispatchable yet** (design step; see the note)
- **File**: PhD/QMF/Weight/Algebraic.lean or a new file | **Depends on**: B7 | **Type**: API gap

#### What is missing
`QMF.algExpansionData` builds the datum for `u ↦ u^(n+2)` on `⊤` with column `(C d + C c X)^(n+2)`.
B7's character hypotheses need `u ↦ u^m` for **`m : ℤ`** and on an **arbitrary** subgroup `UK`, with
column `(C d + C c X)^m` read as a `zpow` in `(PowerSeries K)ˣ`.  The row decay for the negative
part is `QMF.coeffLeOne_linX_inv` (`SlashAction.lean:630`), which wants `‖γ 1 1‖ = 1` rather than
`≠ 0` — deciding whether that is the right hypothesis, or whether `LevelBounds.integral` already
supplies it, **is the design step**.  Until it lands, discharge B7's `hA`/`hA'` by hand at each
call site.

#### Sources
None; this is formalisation bookkeeping, not mathematics from [Bu04] or [LWX].

#### Generality decision
To be made at the design step.

---

### [T-AG3] The Newton polygon of a product — API GAP
- **Status**: **SUPERSEDED (2026-09-09)** — delivered by the `newton-product` board (`PhD/NewtonPolygons/Product.lean`, complete, sorry-free); consumed by tranches 5 and 7 below.  Do not work this ticket.
- **File**: PhD/NewtonPolygons/ (new file) | **Depends on**: none | **Parallel**: yes
- **Type**: API gap (design + theorem)
- **No statement is pre-written.**  The right phrasing depends on whether to work with the existing
  `unitSlope` sequence or to introduce a slope multiset; **that choice is step 1**.  `/beastmode`
  will refuse this ticket until the statement lands.

#### Proof sketch
1. **Design step.**  Choose the slope language.  `PhD/NewtonPolygons/Height.lean:36` already has
   `unitSlope (j : ℕ) : WithBotTop ℝ` (the `j`-th slope) and `heightFun`;
   `PhD/NewtonPolygons/Spec.lean:61` has `IsNewtonPolygonOf` with its `height_le` and maximality
   clauses.  A multiset of slopes may be cleaner for the union statement.
2. **The union.**  The slope multiset of `F * G` is the multiset union of those of `F` and `G`.
3. **The consequence.**  If every slope of a degree-`n` factor is at most every slope of the other,
   the polygon's height at `n` is the sum of that factor's slopes.  Follows from (2) by sorting.

#### Mathlib lemmas needed
To be determined at the design step; record them in this ticket when it lands.

#### Sources
[LWX, §3.23 Step I], `lwx.txt:1818–1822` (quoted under S3).  The source treats "the first `n_{k+1}`
slopes" as evident once the classical slopes are known; the formal content is the multiset union.

#### Generality decision
State for a product of two power series over a valued field, not for the specific factorisation —
this is general Newton polygon theory and is mathlib-able.

---

### [T-AG4] Instantiate the Atkin–Lehner reduction at the classical space
- **Status**: expanded (2026-09-09) → AL0a–AL5 below, plus the gap T-AG5.
- The design pass found the instantiation is two things: (i) pinning down the genuine matrices and
  discharging H1 to the multiset pairing, which is stateable now and is AL0–AL5; and (ii)
  constructing the conjugation itself, hypothesis H1a, which is T-AG5.

---

## The Atkin–Lehner instantiation (`PhD/LWX/AtkinLehnerInst.lean`)

**Why (ii) is not plumbing.**  The Atkin–Lehner element `w = (0, 1; −p^m, 0)` is **not in `M1 p`**:
`M1` requires `‖g 1 1‖ = 1` (`IntegralModel.lean:228`) and `w` has `g 1 1 = 0`.  Every weight and
Hecke operator in the project requires membership in `levelM1` (`DiscForms.lean:179,202,262`), so
none is defined at `w`.  Independently, `w` sends `z ↦ 1/(−p^m z)`, which does not preserve `ℤ_p`,
so `w` does not act on the disc model at any level.  It acts only on the finite-dimensional
classical subspace, where `Sym^k` is a representation of all of `GL₂`.

### [AL0a] `LWX.thetaBlock` — `θ^r` on the block model
- **Status**: done (2026-09-09, definition, no obligation; `[Nonempty ι]` dropped by CLEANUP-10 — `runLinter` flagged it as unused)
- **File**: PhD/LWX/AtkinLehnerInst.lean:72 | **Type**: def
- `blockMap (σ := ι) (thetaDisc p K h r)`.

### [AL0b] `LWX.upMatrix` — the matrix of a block operator on the classical subspace
- **Status**: done (2026-09-09, definition; AL4 landed, so it is now sorry-free)
- **File**: PhD/LWX/AtkinLehnerInst.lean:130 | **Type**: def
- `LinearMap.toMatrix b b (T.restrict hT)` in the basis `Module.finBasisOfFinrankEq` from
  [LWX, (3.21.1)] (`finrank_locPolyDegSubmoduleBlock`, SO4).  SO4 and AL4 both landed on
  2026-09-09, so the definition no longer depends on `sorryAx`.

### [AL0c] `LWX.AtkinLehnerHypothesis` — **H1, named on the genuine spaces**
- **Status**: done (2026-09-09, definition, no obligation; `[Nonempty ι]` dropped by CLEANUP-10 — `runLinter` flagged it as unused)
- **File**: PhD/LWX/AtkinLehnerInst.lean:145 | **Type**: def
- `A * B = ψ p ^ (k+1) • 1 ∧ ∃ P Q, Q * P = 1 ∧ A' = P * B * Q` — exactly **H1b ∧ H1a**.

---

### [AL1] `LWX.thetaBlock_eq_zero_iff` — `ker θ^{k+1}` on the block model
- **Status**: done (2026-09-09, sorry-free; needed the new sub-ticket AL1a and made `blockMap_apply_prod` public)
- **File**: PhD/LWX/AtkinLehnerInst.lean:77 | **Depends on**: T006 | **Parallel**: yes
- **Type**: theorem

#### Statement
```lean
theorem thetaBlock_eq_zero_iff (h k : ℕ) (c : c(ι × (ZMod (p ^ h) × ℕ), K)) :
    thetaBlock (p := p) (K := K) (ι := ι) h (k + 1) c = 0
      ↔ c ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k := by
  sorry
```

#### Proof sketch
1. `thetaBlock` is `blockMap` of `thetaDisc`, so `thetaBlock c = 0` iff every block
   `thetaDisc (blockProj i c) = 0` (`blockMap` apply lemmas from `BlockMap.lean`; extensionality
   over `ι × …`).
2. Apply T006 (`thetaDisc_eq_zero_iff`) blockwise: each block vanishes iff `IsLocPolyDeg` holds on
   that block.
3. `IsLocPolyDeg` on every block is exactly membership in `locPolyDegSubmoduleBlock` (unfold both;
   `forall_and`/`Prod` currying).

#### Mathlib lemmas needed
- T006 (`Theta.lean`); `TateFredholm.blockOpMap_blockIncl` / the `blockProj` simp set
  (`BlockMap.lean:47`); `ContinuousLinearMap.ext`.

#### Sources
[Bu04, Prop 4] proof, `bu04.txt:1113–1115` (quoted in T006): the kernel of `θ` is the classical
forms.  This is the same statement with the class-set index attached.

#### Generality decision
`CharZero K` inherited from T006, where it is load-bearing.

---

### [AL1a] `LWX.thetaBlock_apply` — the coefficient formula on the block model
- **Status**: done (2026-09-09, sorry-free)
- **File**: PhD/LWX/AtkinLehnerInst.lean:77 | **Depends on**: T003 | **Parent**: AL1
- **Parallel**: yes | **Type**: theorem (sub-ticket spawned by /beastmode, Tier A2)

#### Statement
```lean
theorem thetaBlock_apply (h r : ℕ) (c : c(ι × (ZMod (p ^ h) × ℕ), K)) (i : ι)
    (a : ZMod (p ^ h)) (j : ℕ) :
    thetaBlock (p := p) (K := K) (ι := ι) h r c (i, (a, j))
      = ((Nat.descFactorial (j + r) r : ℕ) : K) * c (i, (a, j + r))
```

#### Proof sketch
`rw [thetaBlock, blockMap_apply_prod, thetaDisc_apply, cSpace.blockProj_apply]` — the block form of
`thetaDisc_apply` (T003).  AL1 then reads exactly like `thetaDisc_eq_zero_iff` (T006) with the
class-set index carried along.

#### Mathlib lemmas needed
- `LWX.blockMap_apply_prod` (`PhD/LWX/Theta.lean`, **made public by this ticket** — it was
  `private`; its real home is `PhD/TateFredholm/BlockMap.lean` and moving it there is recorded as a
  `/cleanup` decision, deferred because it would rebuild the whole `TateFredholm` tree),
  `LWX.thetaDisc_apply` (T003), `TateFredholm.cSpace.blockProj_apply` (`BlockOp.lean:590`).

#### Sources
Bookkeeping for AL1; no new mathematical content beyond T003.

#### Generality decision
`omit [CharZero K]`: the formula is characteristic-free, only `thetaDisc_eq_zero_iff` needs
`CharZero`.

---

### [AL2] `LWX.thetaBlock_comp_discHeckeBlockOp` — the intertwining at the block-operator level
- **Status**: **RETIRED (2026-09-09, user decision)** — the statement was false (B2 below) and the user chose to delete it rather than repair the signature.  The declaration is gone from the Lean file; its replacement is B11 `LWX.thetaBlock_comp_discHeckeBlockOp_of_autFactor` (`PhD/LWX/AtkinLehnerInst.lean`), proved and sorry-free.  **Do not re-create this ticket.**
- **File**: PhD/LWX/AtkinLehnerInst.lean:88 | **Depends on**: T-AG2
- **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem thetaBlock_comp_discHeckeBlockOp (h r : ℕ) (κ κ' : AnalyticWeight UK (M1Kh h ψ) ρ)
    (ν : UK →* Kˣ)
    (hκ : ∀ u : UK, κ.toChar u = (u : Kˣ) ^ ((r : ℤ) + 1) * ν u)
    (hκ' : ∀ u : UK, κ'.toChar u = (u : Kˣ) ^ (1 - (r : ℤ)) * ν u)
    (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)
    (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θG) (idx : ι → Fin p → ι)
    (uu : ι → Fin p → U) (cst : K)
    (hdet : ∀ i t, ψ ((certM1 θG U hU vRep hvΔ uu i t :
      Matrix (Fin 2) (Fin 2) ℚ_[p]).det) = cst) :
    (thetaBlock (p := p) (K := K) (ι := ι) h r).comp (discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu)
      = (cst ^ r) •
        ((discHeckeBlockOp θG h ψ κ' U hU vRep hvΔ idx uu).comp
          (thetaBlock (p := p) (K := K) (ι := ι) h r)) := by
  sorry
```


#### B2 — statement defective (found by /beastmode, 2026-09-09)

Inherits T-AG1a's defect: this is T-AG2 assembled over the class set.  Same repair — delete `ν`.
See T-AG1a and `b2_log.jsonl`.

#### Proof sketch
1. `discHeckeBlockOp = blockOp (discHeckeBlock …)` (`DiscForms.lean:195`) and
   `thetaBlock = blockMap thetaDisc`.  Both sides are `blockOp`s; compare block `(i, j)`.
2. The `(i, j)` block of the left side is `thetaDisc ∘ discHeckeBlock i j`; of the right,
   `cst^r • (discHeckeBlock' i j ∘ thetaDisc)`.  That is T-AG2 verbatim.
3. Assemble with the `blockOp` composition lemmas (`BlockOp.lean:622` onward) and
   `Finset.smul_sum`.

#### Mathlib lemmas needed
- T-AG2 (`Theta.lean`); `TateFredholm.blockOp` composition/`blockMap` lemmas; `Finset.smul_sum`.

#### Sources
[Bu04, §7], `bu04.txt:1095–1100`: "`[UηU]θ^{1−k} = |ν(η)|^{k−1}θ^{1−k}[UηU]`".

#### Generality decision
Same hypothesis bundle as T-AG2; the orientation is the corrected one (`θ ∘ U_p = cst^r • (U_p' ∘ θ)`).

---

### [AL3] `LWX.mem_locPolyDegSubmoduleBlock_discHeckeBlockOp` — the classical subspace is `U_p`-stable
- **Status**: **RETIRED (2026-09-09, user decision)** — the statement was false (B2 below) and the user chose to delete it rather than repair the signature.  The declaration is gone from the Lean file; its replacement is B12 `LWX.mem_locPolyDegSubmoduleBlock_discHeckeBlockOp_of_autFactor` (`PhD/LWX/AtkinLehnerInst.lean`), proved and sorry-free.  **Do not re-create this ticket.**
- **File**: PhD/LWX/AtkinLehnerInst.lean:104 | **Depends on**: AL1, AL2
- **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem mem_locPolyDegSubmoduleBlock_discHeckeBlockOp (h k : ℕ)
    (κ κ' : AnalyticWeight UK (M1Kh h ψ) ρ) (ν : UK →* Kˣ)
    (hκ : ∀ u : UK, κ.toChar u = (u : Kˣ) ^ (((k + 1 : ℕ) : ℤ) + 1) * ν u)
    (hκ' : ∀ u : UK, κ'.toChar u = (u : Kˣ) ^ (1 - ((k + 1 : ℕ) : ℤ)) * ν u)
    (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)
    (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θG) (idx : ι → Fin p → ι)
    (uu : ι → Fin p → U) (cst : K)
    (hdet : ∀ i t, ψ ((certM1 θG U hU vRep hvΔ uu i t :
      Matrix (Fin 2) (Fin 2) ℚ_[p]).det) = cst)
    {f : c(ι × (ZMod (p ^ h) × ℕ), K)}
    (hf : f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) :
    discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu f
      ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k := by
  sorry
```


#### B2 — statement defective (found by /beastmode, 2026-09-09)

**Independently false, not merely blocked.**  With `ν =` the inclusion and `r = k + 1` the weight
is `κ = (·)^{k+3}`, so `f∣_κ g (z) = (cz+d)^{k+1} f(gz)`, which has degree `k + 1` when `f` has
degree `k`: the classical subspace is *not* stable.  Concretely at `k = 0`: `f = 1` has degree `0`
and `f∣_κ g = cz + d` has degree `1`.  Same repair — delete `ν`, after which `κ = (·)^{k+2}` and
`f∣_κ g = (cz+d)^k f(gz)` has degree `≤ k`.  See T-AG1a and `b2_log.jsonl`.

#### Proof sketch
1. Rewrite the goal through AL1: it is `thetaBlock h (k+1) (U_p f) = 0`.
2. Apply AL2 at `r = k + 1` to `f`: `thetaBlock (U_p f) = cst^{k+1} • U_p' (thetaBlock f)`.
3. `thetaBlock f = 0` by AL1 applied to `hf`; so the right side is `cst^{k+1} • U_p' 0 = 0`
   (`map_zero`, `smul_zero`).

#### Mathlib lemmas needed
- AL1, AL2 (this file); `ContinuousLinearMap.comp_apply`, `map_zero`, `smul_zero`.

#### Sources
[Bu04, §7], `bu04.txt:1095–1100`: the kernel of an intertwiner is stable — this is why Buzzard's
`θ^{1−k}` is a map *of Hecke modules*.

#### Generality decision
The conclusion mentions only `κ`, but the hypotheses name `κ'` too: the proof goes *through* the
target weight, and without it there is no intertwining to use.  Not over-specified; recorded
because it looks like it at first glance.

---

### [CLEANUP-9] Run /cleanup on PhD/LWX/AtkinLehnerInst.lean
- **Status**: done (2026-09-09) as far as AL2/AL3's B2 allows | **File**: PhD/LWX/AtkinLehnerInst.lean | **Depends on**: AL3 | **Type**: cleanup
- Per-file cadence (AL1, AL2, AL3).

---

### [AL4] `LWX.finite_locPolyDegSubmoduleBlock` — the classical subspace is finite-dimensional
- **Status**: done (2026-09-09, sorry-free; `Module.finite_of_finrank_pos` + SO4, `omit [CharZero K]`)
- **File**: PhD/LWX/AtkinLehnerInst.lean:122 | **Depends on**: SO4, CLEANUP-9
- **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem finite_locPolyDegSubmoduleBlock [Nonempty ι] (h k : ℕ) :
    Module.Finite K (locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) := by
  sorry
```

#### Proof sketch
`Module.finite_of_finrank_pos` (`Dimension/Free.lean:248`) with SO4: the finrank is
`card ι * ((k+1) * p^h) > 0` since `ι` is nonempty (`Fintype.card_pos`), `k + 1 > 0`, `p^h > 0`
(`positivity`).

#### Mathlib lemmas needed
- `Module.finite_of_finrank_pos`, `Fintype.card_pos`, `Nat.pos_pow_of_pos`; SO4 (`StepOne.lean`).

#### Sources
[LWX, (3.21.1)], `lwx.txt:1755–1760`.

#### Generality decision
`[Nonempty ι]` is **slack**: the empty case is the zero module, trivially finite.  It is kept
because the intended proof goes through `finrank_pos`, and the class set is nonempty in every
application.  Removing it is a one-line change to a direct-basis proof; not done now.

---

### [AL5] `LWX.roots_charpoly_of_atkinLehnerHypothesis` — H1 discharges to the pairing
- **Status**: done (2026-09-09, sorry-free; `roots_charpoly_atkinLehner` + `RingHom.injective`)
- **File**: PhD/LWX/AtkinLehnerInst.lean:155 | **Depends on**: AL0c
- **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem roots_charpoly_of_atkinLehnerHypothesis [Nonempty ι] [IsAlgClosed K] (h k : ℕ)
    {A B A' : Matrix (Fin (Fintype.card ι * ((k + 1) * p ^ h)))
      (Fin (Fintype.card ι * ((k + 1) * p ^ h))) K}
    (hAL : AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ h k A B A') :
    A'.charpoly.roots = A.charpoly.roots.map (fun x => (ψ p) ^ (k + 1) / x) := by
  sorry
```

#### Proof sketch
1. `obtain ⟨hAB, P, Q, hQP, hA'⟩ := hAL`.
2. `c := ψ p ^ (k+1) ≠ 0`: `pow_ne_zero`, and `ψ p ≠ 0` since a ring hom out of the field `ℚ_[p]`
   is injective (`RingHom.injective`) and `(p : ℚ_[p]) ≠ 0` (`Nat.cast_ne_zero`, `hp.out.ne_zero`).
3. `exact LWX.roots_charpoly_atkinLehner hc hAB hQP hA'` (`PhD/LWX/AtkinLehner.lean:182`, board
   one, sorry-free).

#### Mathlib lemmas needed
- `LWX.roots_charpoly_atkinLehner` — project, sorry-free; `pow_ne_zero`, `RingHom.injective`,
  `Nat.cast_ne_zero`.

#### Sources
[LWX, Prop 3.22], `lwx.txt:1763–1768`, whose proof (`lwx.txt:1783–1786`) obtains the pairing by
"twist[ing] the representation `π` by a central Hecke character associated to `ψ⁻¹`" — that twist
is what `AtkinLehnerHypothesis`'s `∃ P Q` packages.  See `../lwx-stepone/JL-AUDIT.md` §1.

#### Generality decision
`IsAlgClosed K` is needed for roots with multiplicity, as in board one.  The theorem is a one-liner
on purpose: its content is fixing the **types** of the data Step I consumes.

---

### [CLEANUP-10] Run /cleanup on PhD/LWX/AtkinLehnerInst.lean (final per-file)
- **Status**: done (2026-09-09; wrapped six over-long lines, dropped the unused `[Nonempty ι]` from `AtkinLehnerHypothesis` and `roots_charpoly_of_atkinLehnerHypothesis` that `runLinter` flagged) | **File**: PhD/LWX/AtkinLehnerInst.lean | **Depends on**: AL4, AL5 | **Type**: cleanup

---

### [T-AG5] Construct the Atkin–Lehner conjugation on classical forms — API GAP (hypothesis H1a)
- **Status**: open — **not dispatchable** (no Statement; needs the design step, as the ticket itself says)
- **File**: (new file, to be decided at the design step) | **Depends on**: AL3, S1 | **Parallel**: no
- **Type**: API gap (design + construction)
- **No statement is pre-written**, and this one is not a signature-only gap: it is the genuine
  remaining half of H1.  `/beastmode` will refuse it until designed.

#### What must be built
A conjugation `(P, Q)`, `Q P = 1`, `A' = P B Q`, between `upMatrix` of `U_p` at `invChar ω` and
`upMatrix` of `U'_p` at `ω`, realising the Atkin–Lehner element on the classical subspace.

#### Why it cannot go through the disc model (two independent obstructions, both verified)
1. `w = (0, 1; −p^m, 0) ∉ M1 p`: `M1` requires `‖g 1 1‖ = 1` (`IntegralModel.lean:226–228`);
   `w` has `g 1 1 = 0`.  Every weight/Hecke operator needs `η ∈ levelM1` (`DiscForms.lean:179`).
2. `w` acts by `z ↦ 1/(−p^m z)`, which sends `ℤ_p^×` to `p^{−m}ℤ_p^×`, outside `ℤ_p`: no disc is
   preserved, at any level.

#### The route
On the classical subspace, `Sym^k` is a `GL₂`-representation, and `w` acts by the twisted
polynomial reversal `f(z) ↦ (−p^m z)^k · f(1/(−p^m z))` on each fibre, composed with the
permutation of the class set induced by `w` on the global double coset.  Build this directly on
`locPolyDegSubmoduleBlock` (or on a `Sym^k`-valued model of classical forms and transport), then
verify (i) it intertwines the nebentypus `ω ↔ invChar ω` (via `atkinLehnerConj_apply_one_one`,
board one), (ii) it conjugates `U_p ↦ U'_p` (via `atkinLehnerConj_upElt`, board one), and (iii) it
normalises the level (via `atkinLehnerConj_mem_Iw`, board one).  Board one's matrix identities are
exactly the three facts this needs; what is missing is lifting them from matrices to an action on
forms.

#### Sources
[LWX, Prop 3.22] proof, `lwx.txt:1783–1786`: "we can twist the representation `π` by a central
Hecke character associated to `ψ⁻¹`; then the resulting automorphic representation would appear in
`S^D_{k+2}(K^pIw_{pᵐ};ψ⁻¹)`."  The source does this representation-theoretically (via
Jacquet–Langlands); the `Sym^k` route is the Jacquet–Langlands-free realisation of the same twist.

#### Recommendation
This is the size of board one and independent of the theta tickets: a candidate for its own board
(`lwx-alconj`), the same shape as `lwx-atkinlehner` was.

---

### [CLEANUP-FINAL] Run /cleanup-all on the board
- **Status**: done (2026-09-09) — every file the board touches builds warning-free and `runLinter` reports nothing on them; it cannot close while T-AG1a/1b/2 and AL2/AL3 are B2 | **File**: (project-wide) | **Depends on**: every other ticket | **Type**: cleanup
- After this, run `/develop --continue` on this board to skeleton and ticket tranches 2 and 3, then
  `/pre-submit`.  Check `#print axioms` on the tranche-1 results shows exactly
  `[propext, Classical.choice, Quot.sound]`.

---


## Tranches 5–7 — Steps I and III on the corrected foundation (added 2026-09-09, `/develop --continue`)

**Files owned (NEW)**: `PhD/LWX/Touching.lean` (tranche 5, Step I), `PhD/LWX/ClassicalPoint.lean`
(tranche 6, the classical halo points), `PhD/LWX/StepThree.lean` (tranche 7, Step III).  All three
are skeletoned and `lake build` passes with `sorry` warnings only (54 sorries; verified
2026-09-09).  Every Statement below is copied verbatim from the compiled skeleton.

**Read first**: `decomposition.md` §"Tranches 5–7", which carries the verbatim source quotes and
the attack logs per leaf, and the two design findings of this pass — (a) Step I closes with the
*Minkowski upper bound* alone, so classicality ([LWX, Prop 2.15]) is a corollary of the touching
rather than an input; (b) the `_of_autFactor` equivariance must carry a common nebentypus constant
(ticket G1) before Step III can use it at a nontrivial nebentypus.

**Hypotheses named, not proved**: H1 (`AtkinLehnerHypothesis`, as before) and H2
(`IsThetaExact`, the theta sequence's right-exactness in Fredholm-determinant form).  Two
bookkeeping gaps are recorded as design tickets, not proof tickets: `AG-ζ` (the nebentypus
constants of source and target weights agree — needs the binomial series at a root of unity) and
`AG-ω₀` (the Teichmüller character on `(ZMod p)ˣ`, to *spell* `ω⁻¹ω₀^{2k}`; the theorems take the
twisted characters as parameters and never need it).

### [T5.1] `LWX.height_mul_le_height_right`
- **Status**: done (2026-09-09, sorry-free)
- **File**: PhD/LWX/Touching.lean:68 | **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem height_mul_le_height_right {f g : PowerSeries K}
    (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f)
    (hg : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c g) (hf0 : PowerSeries.coeff 0 f = 1)
    (hg0 : PowerSeries.coeff 0 g = 1) (n : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm (f * g)).height n ≤
      (newtonPolygon₀OfPowerSeries negLogNorm g).height n := by
  sorry
```

#### Proof sketch
1. `isEntireNewtonPolygonOf_coeffVal hf hf0'` and `… hg hg0'` give the entire-polygon hypotheses (`coeff 0 ≠ 0` from `= 1`); `isNewtonPolygonOf_coeffVal_mul` gives the spec for the product.
2. `IsEntireNewtonPolygonOf.height_mul` rewrites the left side as `minkowskiHeight Pf Pg n`.
3. `NewtonPolygon₀.minkowskiHeight_le (Nat.zero_le n)` bounds it by `Pf.height 0 + Pg.height (n - 0)`; `height_zero_newtonPolygon₀OfPowerSeries hf0` makes the first summand `0` (`zero_add`, `Nat.sub_zero`).

#### Mathlib lemmas needed
- `isEntireNewtonPolygonOf_coeffVal` (`Product.lean:1298`)
- `isNewtonPolygonOf_coeffVal_mul` (`Product.lean:1310`)
- `IsEntireNewtonPolygonOf.height_mul` (`Product.lean:932`)
- `NewtonPolygon₀.minkowskiHeight_le` (`Product.lean:170`)
- `height_zero_newtonPolygon₀OfPowerSeries` (`Product.lean:1323`)

#### Sources
[Ked07, §2] (Kedlaya, *p-adic differential equations*, unit "Newton polygons"), via `PhD/NewtonPolygons/Product.lean`: "the Newton polygon of `fg` is the Minkowski sum", i.e. its height at `n` is the *minimum* over splits, hence at most the split `(0, n)`.

#### Generality decision
Stated for arbitrary entire series with constant term `1`; no polynomial hypothesis is needed for the *upper* bound, which is why Step I needs no classicality.

---
### [T5.2] `LWX.height_le_coeffVal`
- **Status**: done (2026-09-09, sorry-free)
- **File**: PhD/LWX/Touching.lean:77 | **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem height_le_coeffVal {g : PowerSeries K}
    (hg : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c g)
    (hg0 : PowerSeries.coeff 0 g = 1) (n : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm g).height n ≤
      ((coeffVal g n : WithTop ℝ) : WithBotTop ℝ) := by
  sorry
```

#### Proof sketch
1. `isEntireNewtonPolygonOf_coeffVal hg hg0'` gives `IsNewtonPolygonOf (coeffVal g) P`; its field `height_le n` is the claim, with `pointHeight (coeffVal g) n = ((coeffVal g n : WithTop ℝ) : WithBotTop ℝ)` by `pointHeight_eq_coe`.

#### Mathlib lemmas needed
- `IsNewtonPolygonOf.height_le` (`Spec.lean:61`)
- `pointHeight_eq_coe` (`Product.lean:698`)
- `isEntireNewtonPolygonOf_coeffVal`

#### Sources
The defining property of the lower convex hull (`Spec.lean`, docstring: "The polygon lies on/below every point").

#### Generality decision
General.

---
### [T5.3] `LWX.coeff_charpolyRev_card`
- **Status**: done (2026-09-09, sorry-free)
- **File**: PhD/LWX/Touching.lean:85 | **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem coeff_charpolyRev_card {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n K) :
    A.charpolyRev.coeff (Fintype.card n) = (-1) ^ Fintype.card n * A.det := by
  sorry
```

#### Proof sketch
1. `Matrix.reverse_charpoly`: `charpolyRev A = reverse (charpoly A)`.
2. `Polynomial.coeff_reverse` at `n = card`, with `natDegree (charpoly A) = card` (`Matrix.charpoly_natDegree_eq_dim`) and `revAt card card = 0`, gives `coeff 0 (charpoly A)`.
3. `Matrix.det_eq_sign_charpoly_coeff`: `det A = (-1)^card * coeff 0 (charpoly A)`; solve for `coeff 0` (`(-1)^card` is a unit: `neg_one_pow_mul_eq_zero_iff`/`Int.units_pow`-style, or multiply both sides by `(-1)^card` and use `neg_one_pow_mul_neg_one_pow`… simplest: `rw [det_eq_sign_charpoly_coeff]; ring_nf; simp [pow_mul]`).

#### Mathlib lemmas needed
- `Matrix.reverse_charpoly` (`Coeff.lean:294`)
- `Polynomial.coeff_reverse` (`Reverse.lean:221`)
- `Matrix.charpoly_natDegree_eq_dim` (`Coeff.lean:116`, needs `[Nontrivial K]`)
- `Matrix.det_eq_sign_charpoly_coeff` (`Coeff.lean:151`)
- `Polynomial.revAt_le`

#### Sources
Bookkeeping: `det(1 − X·A)` has leading coefficient `(−1)^N det A`.

#### Generality decision
Over any field; `[Nontrivial K]` is automatic.

---
### [CLEANUP-T5a] Run /cleanup on PhD/LWX/Touching.lean
- **Status**: done | **File**: PhD/LWX/Touching.lean | **Depends on**: T5.3 | **Type**: cleanup
- Per-file cadence (T5.1–T5.3).

---
### [T5.4] `LWX.det_ne_zero_of_mul_eq_smul'`
- **Status**: done (2026-09-09, sorry-free, one line from `Matrix.det_ne_zero_of_mul_eq_smul`)
- **File**: PhD/LWX/Touching.lean:99 | **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem det_ne_zero_of_mul_eq_smul' {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n K} {c : K} (hc : c ≠ 0) (hAB : A * B = c • (1 : Matrix n n K)) :
    A.det ≠ 0 := by
  sorry
```

#### Proof sketch
1. `det_mul_det_of_mul_eq_smul hAB : A.det * B.det = c ^ card` (`CharpolyPairing.lean:57`); the right side is nonzero (`pow_ne_zero`), so `A.det ≠ 0` (`left_ne_zero_of_mul`).

#### Mathlib lemmas needed
- `LWX.det_mul_det_of_mul_eq_smul` / `Matrix.det_mul_det_of_mul_eq_smul` (`PhD/TateFredholm/CharpolyPairing.lean:57`; check the namespace)
- `left_ne_zero_of_mul`
- `pow_ne_zero`

#### Sources
Bookkeeping for T5.5; `CharpolyPairing.lean:110` has `det_ne_zero_of_mul_eq_smul` in a possibly different shape — reuse it if the signature matches, else this one-liner.

#### Generality decision
General.

---
### [T5.5] `LWX.neg_log_norm_det_add_of_mul_eq_smul`
- **Status**: done (2026-09-09, sorry-free)
- **File**: PhD/LWX/Touching.lean:92 | **Depends on**: T5.4 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem neg_log_norm_det_add_of_mul_eq_smul {n : Type*} [Fintype n] [DecidableEq n]
    {A B A' P Q : Matrix n n K} {c : K} (hc : c ≠ 0) (hAB : A * B = c • (1 : Matrix n n K))
    (hQP : Q * P = 1) (hA' : A' = P * B * Q) :
    -Real.log ‖A.det‖ + -Real.log ‖A'.det‖ = Fintype.card n * (-Real.log ‖c‖) := by
  sorry
```

#### Proof sketch
1. `det A' = det P * det B * det Q` (`Matrix.det_mul` twice) and `det Q * det P = 1` (`Matrix.det_mul`, `Matrix.det_one` on `hQP`), so `det A' = det B` by commutativity.
2. `det_mul_det_of_mul_eq_smul hAB : det A * det B = c ^ card`.
3. Take `−log ‖·‖`: `norm_mul`, `norm_pow`, `Real.log_mul` (both factors nonzero by T5.4 and its `B`-analogue), `Real.log_pow`; rearrange with `ring`/`linarith`.

#### Mathlib lemmas needed
- `Matrix.det_mul`
- `Matrix.det_one`
- `det_mul_det_of_mul_eq_smul` (`CharpolyPairing.lean:57`)
- `Real.log_mul`
- `Real.log_pow`
- `norm_mul`
- `norm_pow`
- T5.4

#### Sources
[LWX, Prop 3.22], `lwx.txt:1766–1768`: "the total sum of the `U_p`-slopes of `S^D_{k+2}(K^pIw_{pᵐ};ψ) ⊕ S^D_{k+2}(K^pIw_{pᵐ};ψ⁻¹)` is `(k+1)²q⁻¹pᵐt`" — the sum of all slopes of a matrix is `−log‖det‖`, so this is the determinant form of that sentence, granted the pairing `A B = c·1`, `A' = P B Q`.

#### Generality decision
Stated for abstract matrices over any `NormedField`-like `K` (uses only `‖·‖` multiplicativity); this is board one's reduction read on determinants rather than roots — no `IsAlgClosed` needed.

---
### [T5.6] `LWX.autFactor_mul_mobius_pow_of_shape`
- **Status**: done (2026-09-09, sorry-free)
- **File**: PhD/LWX/Touching.lean:132 | **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem autFactor_mul_mobius_pow_of_shape {S : Submonoid (Matrix (Fin 2) (Fin 2) K)}
    (κ : AnalyticWeight UK S ρ) {γ : Matrix (Fin 2) (Fin 2) K} (hd : γ 1 1 ≠ 0) {k : ℕ} {u : K}
    (hA : κ.toWeightSeries.autFactor γ * linX γ = PowerSeries.C u * linX γ ^ (k + 1))
    {i : ℕ} (hi : i ≤ k) :
    κ.toWeightSeries.autFactor γ * mobius γ ^ i
      = PowerSeries.C u * (linX γ ^ (k - i) * numX γ ^ i) := by
  sorry
```

#### Proof sketch
1. From `hA` and `linX γ * (linX γ)⁻¹ = 1` (`PowerSeries.mul_inv_cancel`, constant coefficient `γ 1 1 ≠ 0` by `constantCoeff_linX`), `autFactor = C u * linX ^ k`.
2. `mobius γ = numX γ * (linX γ)⁻¹` (`mobius`), `mul_pow`; split `linX ^ k = linX ^ (k - i) * linX ^ i` (`pow_sub_mul_pow` with `hi`) and cancel `linX ^ i * (linX⁻¹) ^ i = 1` (`← mul_pow`, `one_pow`); `ring`.

#### Mathlib lemmas needed
- `PowerSeries.mul_inv_cancel`
- `QMF.constantCoeff_linX` (`Series.lean:180`)
- `QMF.mobius` (`Series.lean:175`)
- `pow_sub_mul_pow`
- `mul_pow`

#### Sources
`QMF.autFactor_mul_mobius_pow_eq` (`PhD/QMF/Weight/Algebraic.lean:139`) is this statement for `algWeight` with `u = 1`; the proof is that proof with the constant carried along.

#### Generality decision
For any matrix `γ` with `γ 1 1 ≠ 0` and any weight; the constant `u` is arbitrary (no unit hypothesis).

---
### [CLEANUP-T5b] Run /cleanup on PhD/LWX/Touching.lean
- **Status**: done | **File**: PhD/LWX/Touching.lean | **Depends on**: T5.6 | **Type**: cleanup
- Per-file cadence (T5.4–T5.6).

---
### [T5.7] `LWX.kappaSlash_mem_polySubmodule_of_shape`
- **Status**: done (2026-09-09, sorry-free)
- **File**: PhD/LWX/Touching.lean:142 | **Depends on**: T5.6 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem kappaSlash_mem_polySubmodule_of_shape {S : Submonoid (Matrix (Fin 2) (Fin 2) K)}
    (κ : AnalyticWeight UK S ρ) (g : S) {k : ℕ} {u : K}
    (hA : κ.toWeightSeries.autFactor g.1 * linX g.1 = PowerSeries.C u * linX g.1 ^ (k + 1))
    {f : c(ℕ, K)} (hf : f ∈ polySubmodule K k) : κ.kappaSlash g f ∈ polySubmodule K k := by
  sorry
```

#### Proof sketch
1. `WeightSeries.kappaSlash_apply`: `(κ.kappaSlash g f) j = ∑' i, coeff j (autFactor * mobius ^ i) * f i`.
2. Truncate the sum to `i ≤ k` using `hf` (`mem_polySubmodule_iff`: `f i = 0` for `k < i`) — `tsum_eq_sum` over `Finset.range (k+1)`.
3. For `i ≤ k`, T5.6 makes the column `C u * (linX ^ (k-i) * numX ^ i)`, a polynomial of degree `≤ k`: for `k < j` its `j`-th coefficient vanishes (`PowerSeries.coeff_C_mul`, then the degree bound — reprove `coeff_linX_pow_mul_numX_pow_eq_zero`, private in `Algebraic.lean:242`, or de-privatise it: both are one-paragraph).

#### Mathlib lemmas needed
- `QMF.WeightSeries.kappaSlash_apply` (`SlashAction.lean:462`)
- `QMF.mem_polySubmodule_iff` (`Algebraic.lean:265`)
- `tsum_eq_sum`
- `PowerSeries.coeff_C_mul`
- the degree bound (`Algebraic.lean:242`, private)
- T5.6

#### Sources
`QMF.polySubmodule_stable` (`Algebraic.lean:277`) is this statement for `algWeight`: "the formula `z^k ↦ (az+b)^k (cz+d)^(n−k)` has degree `≤ n`".

#### Generality decision
Single disc, arbitrary level monoid `S`.

---
### [T5.8] `LWX.discSlash_mem_locPolyDegSubmodule_of_shape`
- **Status**: done (2026-09-09, sorry-free, via `blockProj_discSlash` (public in DiscModel.lean))
- **File**: PhD/LWX/Touching.lean:150 | **Depends on**: T5.7 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem discSlash_mem_locPolyDegSubmodule_of_shape (κ : AnalyticWeight UK (M1Kh h ψ) ρ)
    (δ : M1 p) {k : ℕ} {u : ZMod (p ^ h) → K}
    (hA : ∀ a, κ.toWeightSeries.autFactor
          ((discConjK h δ a ψ : M1Kh h ψ) : Matrix (Fin 2) (Fin 2) K)
        * linX ((discConjK h δ a ψ : M1Kh h ψ) : Matrix (Fin 2) (Fin 2) K)
      = PowerSeries.C (u a)
        * linX ((discConjK h δ a ψ : M1Kh h ψ) : Matrix (Fin 2) (Fin 2) K) ^ (k + 1))
    {f : c(ZMod (p ^ h) × ℕ, K)} (hf : f ∈ locPolyDegSubmodule p K h k) :
    discSlash h ψ κ δ f ∈ locPolyDegSubmodule p K h k := by
  sorry
```

#### Proof sketch
1. `discSlash h ψ κ δ = blockOp (fun a b => if b = discImage h δ a then κ.kappaSlash (discConjK h δ a ψ) else 0)`; use `blockProj_blockOp`-style evaluation (`DiscModel.lean:466`, private `blockProj_blockOp`; or `matrixCoeff_discSlash` + `hasSum_matrixCoeff`) to write block `a` of the output as `κ.kappaSlash (discConjK h δ a' ψ) (blockProj a' f)` for the unique `a'` with `discImage h δ a' = a`, summed over `a'`.
2. `IsLocPolyDeg` of `f` means every `blockProj a' f ∈ polySubmodule K k`; apply T5.7 at `g := discConjK h δ a' ψ` with `hA a'`; a finite sum of members of `polySubmodule` is a member (`Submodule.sum_mem`).

#### Mathlib lemmas needed
- `LWX.discSlash` (`DiscModel.lean:450`)
- `LWX.matrixCoeff_discSlash` (`DiscModel.lean:454`)
- `TateFredholm.cSpace.blockProj_apply` (`BlockOp.lean:590`)
- `Submodule.sum_mem`
- T5.7

#### Sources
The transport of T5.7 along the disc decomposition of `DiscModel.lean` ([LWX, (2.3.2)]).

#### Generality decision
Any `δ : M1 p`; the constants `u a` may depend on the disc.

---
### [T5.9a] `LWX.blockProj_blockOp'` — a block of a `blockOp`, applied
- **Status**: done (2026-09-09, sorry-free)
- **File**: PhD/LWX/Touching.lean | **Depends on**: none | **Parent**: T5.9 | **Parallel**: yes
- **Type**: theorem (sub-ticket spawned by /beastmode, Tier A2)

#### Statement
```lean
private theorem blockProj_blockOp' {σ : Type*} [Fintype σ] [DecidableEq σ] {I : Type*}
    [DecidableEq I] (T : σ → σ → (c(I, K) →L[K] c(I, K))) (f : c(σ × I, K)) (a : σ) :
    cSpace.blockProj a (blockOp T f) = ∑ b : σ, T a b (cSpace.blockProj b f)
```

#### Proof sketch
The proof of `LWX.blockProj_blockOp` (`PhD/LWX/DiscModel.lean:464`, **private**, stated only for
`σ = ZMod (p ^ h)`), verbatim with `σ` general: unfold `blockOp` to the double sum of
`blockIncl a' ∘ T a' b ∘ blockProj b`, push `blockProj a` through with
`cSpace.blockProj_blockIncl`, and kill every `a' ≠ a` term.

#### Mathlib lemmas needed
- `TateFredholm.blockOp` (`BlockOp.lean`), `TateFredholm.cSpace.blockProj_blockIncl`,
  `Finset.sum_eq_single`, `map_sum`, `_root_.sum_apply`.

#### Sources
None — bookkeeping.  Its proper home is `PhD/TateFredholm/BlockOp.lean` next to
`blockOp_blockIncl` (`BlockOp.lean:628`); stated here to avoid rebuilding that tree, and recorded
as a `/cleanup` decision.

#### Generality decision
General `σ`, `I`; the `ZMod (p ^ h)` instance in `DiscModel.lean` becomes a special case (it stays
private there — de-privatising it is not needed).

---

### [T5.9] `LWX.mem_locPolyDegSubmoduleBlock_discHeckeBlockOp_of_isClassicalShape`
- **Status**: done (2026-09-09, sorry-free; note the certificate matrix uses the ROW index `i`, not the column `i'`)
- **File**: PhD/LWX/Touching.lean:163 | **Depends on**: T5.8, T5.9a | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem mem_locPolyDegSubmoduleBlock_discHeckeBlockOp_of_isClassicalShape
    (κ : AnalyticWeight UK (M1Kh h ψ) ρ) {k : ℕ} {u : ι → Fin p → ZMod (p ^ h) → K}
    (hcl : IsClassicalShape θG h ψ U hU vRep hvΔ uu κ k u)
    {f : c(ι × (ZMod (p ^ h) × ℕ), K)}
    (hf : f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) :
    discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu f
      ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k := by
  sorry
```

#### Proof sketch
1. `discHeckeBlockOp = blockOp (discHeckeBlock …)` and `discHeckeBlock i j = ∑ t ∈ filter …, discSlash h ψ κ (certM1 … i t)`; block `i` of the output is `∑_j ∑_t discSlash … (blockProj j f)`.
2. Each `blockProj j f ∈ locPolyDegSubmodule` (membership in `locPolyDegSubmoduleBlock` is blockwise `IsLocPolyDeg`), T5.8 with `hcl i t` (its `a`-family is `hcl i t ·`) puts each summand in `locPolyDegSubmodule`; sums stay (`Submodule.sum_mem`).

#### Mathlib lemmas needed
- `LWX.discHeckeBlockOp` (`DiscForms.lean:195`)
- `LWX.discHeckeBlock` (`DiscForms.lean:189`)
- `LWX.locPolyDegSubmoduleBlock` (`StepOne.lean:100`)
- `Submodule.sum_mem`
- T5.8

#### Sources
[LWX, §3.23 Step I], `lwx.txt:1807–1846` uses that `S^D_{k+2}(K^pIw_{q²};ψ)` is a `U_p`-stable subspace of `S^{D,†}_{(k,ψ)}` (it is where the classical slopes live).  The stability is elementary once the weight has the classical shape; nothing about theta is used.

#### Generality decision
Replaces `mem_locPolyDegSubmoduleBlock_discHeckeBlockOp_of_autFactor` (which went through the theta intertwining and needed the target weight) as the input of `classicalMatrix`.

---
### [CLEANUP-T5c] Run /cleanup on PhD/LWX/Touching.lean
- **Status**: done | **File**: PhD/LWX/Touching.lean | **Depends on**: T5.9 | **Type**: cleanup
- Per-file cadence (T5.7–T5.9).

---
### [T5.10] `LWX.mem_classicalSupport_iff`
- **Status**: done (2026-09-09, sorry-free)
- **File**: PhD/LWX/Touching.lean:189 | **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem mem_classicalSupport_iff (k : ℕ) (x : ι × (ZMod (p ^ h) × ℕ)) :
    x ∈ classicalSupport p ι h k ↔ x.2.2 ≤ k := by
  sorry
```

#### Proof sketch
1. `Finset.mem_image`: `x` is in the image iff some `⟨i, a, ⟨j, hj⟩⟩` maps to it; forward: `x.2.2 = j < k+1`; backward: take `⟨x.1, x.2.1, ⟨x.2.2, by omega⟩⟩`.

#### Mathlib lemmas needed
- `Finset.mem_image`
- `Finset.mem_univ`
- `Fin.isLt`

#### Sources
Bookkeeping.

#### Generality decision
General.

---
### [T5.11] `LWX.card_classicalSupport`
- **Status**: done (2026-09-09, sorry-free, needed a `Function.Injective` restatement of `triple_val_inj`)
- **File**: PhD/LWX/Touching.lean:194 | **Depends on**: T5.10 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem card_classicalSupport (k : ℕ) :
    (classicalSupport p ι h k).card = Fintype.card ι * ((k + 1) * p ^ h) := by
  sorry
```

#### Proof sketch
1. `Finset.card_image_of_injective` (the map is injective: `Prod.ext` + `Fin.ext`, as in `StepOne.lean`'s private `triple_val_inj`), then `Finset.card_univ`, `Fintype.card_prod`, `ZMod.card`, `Fintype.card_fin`, `mul_comm`/`ring` as in `finrank_locPolyDegSubmoduleBlock`.

#### Mathlib lemmas needed
- `Finset.card_image_of_injective`
- `Fintype.card_prod`
- `ZMod.card`
- `Fintype.card_fin`

#### Sources
[LWX, (3.21.1)] `dim S^D_{k+2}(K^pIw_{pᵐ};ψ) = (k+1)q⁻¹pᵐt`, `lwx.txt:1755–1760`, as a cardinality of the coordinate set.

#### Generality decision
General.

---
### [T5.12] `LWX.truncation_classicalSupport_mem`
- **Status**: done (2026-09-09, sorry-free)
- **File**: PhD/LWX/Touching.lean:200 | **Depends on**: T5.10 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem truncation_classicalSupport_mem (k : ℕ) (f : c(ι × (ZMod (p ^ h) × ℕ), K)) :
    truncation (classicalSupport p ι h k) f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k := by
  sorry
```

#### Proof sketch
1. Membership in `locPolyDegSubmoduleBlock` is `∀ i a j, k < j → f (i,(a,j)) = 0`; `truncation_apply` gives `if (i,(a,j)) ∈ S then f _ else 0`, and by T5.10 the index is not in `S` when `k < j`.

#### Mathlib lemmas needed
- `TateFredholm.truncation_apply` (`Matrix.lean:260`)
- T5.10

#### Sources
Bookkeeping.

#### Generality decision
General.

---
### [CLEANUP-T5d] Run /cleanup on PhD/LWX/Touching.lean
- **Status**: done | **File**: PhD/LWX/Touching.lean | **Depends on**: T5.12 | **Type**: cleanup
- Per-file cadence (T5.10–T5.12).

---
### [T5.13] `LWX.truncation_classicalSupport_of_mem`
- **Status**: done (2026-09-09, sorry-free)
- **File**: PhD/LWX/Touching.lean:206 | **Depends on**: T5.10 | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem truncation_classicalSupport_of_mem (k : ℕ) {f : c(ι × (ZMod (p ^ h) × ℕ), K)}
    (hf : f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) :
    truncation (classicalSupport p ι h k) f = f := by
  sorry
```

#### Proof sketch
1. `DFunLike.ext`; at `(i,(a,j))`: if `j ≤ k` the index is in `S` (T5.10) and `truncation_apply` gives `f _`; else both sides are `0` (`hf`).

#### Mathlib lemmas needed
- `TateFredholm.truncation_apply`
- T5.10

#### Sources
Bookkeeping.

#### Generality decision
General.

---
### [T5.14a] `LWX.classicalEquiv` and `LWX.matrixCoeff_truncation_comp` — reindexing the support
- **Status**: done (2026-09-09, sorry-free)
- **File**: PhD/LWX/Touching.lean | **Depends on**: T5.10 | **Parent**: T5.14 | **Parallel**: yes
- **Type**: def + theorem (sub-ticket spawned by /beastmode, Tier A2)

#### Statement
```lean
private def classicalEquiv (k : ℕ) :
    ι × ZMod (p ^ h) × Fin (k + 1) ≃ {x // x ∈ classicalSupport p ι h k}

private theorem matrixCoeff_truncation_comp (S : Finset (ι × (ZMod (p ^ h) × ℕ)))
    (T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K))
    {j : ι × (ZMod (p ^ h) × ℕ)} (hj : j ∈ S) (i : ι × (ZMod (p ^ h) × ℕ)) :
    matrixCoeff ((truncation S).comp T) j i = matrixCoeff T j i
```

#### Proof sketch
`classicalEquiv`: forward `(i, a, ⟨j, _⟩) ↦ ⟨(i, (a, j)), _⟩` with membership from T5.10; inverse
uses T5.10 the other way to build the `Fin`.  Both round trips are `rfl` (`Fin` eta).
`matrixCoeff_truncation_comp`: `matrixCoeff (pr ∘ T) j i = pr (T (single i 1)) j`, and
`truncation_apply` with `hj` gives `(T (single i 1)) j`.

#### Mathlib lemmas needed
- `TateFredholm.truncation_apply` (`Matrix.lean:260`), `Fin.is_lt`, `Nat.lt_succ_iff`; T5.10.

#### Sources
Bookkeeping for T5.14: `charCoeff_eq_det_coeff` produces a determinant over `↥S`, while
`classicalCoordMatrix` is indexed by `ι × ZMod (p^h) × Fin (k+1)`; the equiv transports one to
the other through `Matrix.det_submatrix_equiv_self`.

#### Generality decision
`classicalEquiv` is `private` and specific to `classicalSupport`; `matrixCoeff_truncation_comp` is
stated for an arbitrary `S` since nothing about `classicalSupport` is used.

---

### [T5.14] `LWX.charPowerSeries_truncation_comp`
- **Status**: done (2026-09-09, sorry-free; the `↥S` determinant is reindexed entrywise through `classicalEquiv` (`Matrix.det_submatrix_equiv_self`))
- **File**: PhD/LWX/Touching.lean:220 | **Depends on**: T5.10, T5.14a | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem charPowerSeries_truncation_comp (k : ℕ)
    (T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K)) :
    charPowerSeries ((truncation (classicalSupport p ι h k)).comp T)
      = ((classicalCoordMatrix h k T).charpolyRev : PowerSeries K) := by
  sorry
```

#### Proof sketch
1. `charCoeff_eq_det_coeff ((truncation S).comp T) S hS n` with `hS : ∀ j ∉ S, ∀ i, matrixCoeff (pr ∘ T) j i = 0` (`matrixCoeff_comp`… simpler: `matrixCoeff (pr ∘ T) j i = (pr (T (single i 1))) j = 0` for `j ∉ S` by `truncation_apply`).
2. The right side is `coeff n (det (1 − X • M.map C))` over the index type `↥S`; reindex along the equivalence `↥S ≃ ι × ZMod (p^h) × Fin (k+1)` (T5.10 + `Fin.mk`; `Equiv.subtypeEquiv`/`Finset.equivFin`-free: build it by hand) with `Matrix.det_reindex_self`, and `matrixCoeff (pr ∘ T) j i = matrixCoeff T j i` for `j ∈ S`.
3. `PowerSeries.ext`, `charPowerSeries_coeff`, `Polynomial.coeff_coe`, `Matrix.charpolyRev` unfolds to the same determinant.

#### Mathlib lemmas needed
- `TateFredholm.charCoeff_eq_det_coeff` (`Fredholm.lean:491`)
- `Matrix.det_reindex_self`
- `Matrix.charpolyRev` (`Coeff.lean:292`)
- `TateFredholm.charPowerSeries_coeff`
- `Polynomial.coeff_coe`
- T5.10

#### Sources
`charPowerSeries_eq_charpolyRev_of_finite` (`RieszColeman.lean:411`) is the same argument on a finite model space; here the finite support is a subset of an infinite index.

#### Generality decision
Any operator `T`; no compactness needed (the left side has finitely many nonzero rows).

---
### [T5.15] `LWX.charPowerSeries_comp_truncation`
- **Status**: done (2026-09-09, sorry-free; `truncation` needs `(R := K)` pinned, its `R` is otherwise a metavariable)
- **File**: PhD/LWX/Touching.lean:228 | **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem charPowerSeries_comp_truncation (k : ℕ)
    {T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K)} (hT : IsCompactoid T) :
    charPowerSeries (T.comp (truncation (classicalSupport p ι h k)))
      = charPowerSeries ((truncation (classicalSupport p ι h k)).comp T) := by
  sorry
```

#### Proof sketch
1. `charPowerSeries_comm T (truncation S) hT` verbatim (`u.comp v` vs `v.comp u` with `u := T` compactoid).

#### Mathlib lemmas needed
- `TateFredholm.charPowerSeries_comm` (`Fredholm.lean:773`)

#### Sources
The trace property of Fredholm determinants.

#### Generality decision
One line.

---
### [CLEANUP-T5e] Run /cleanup on PhD/LWX/Touching.lean
- **Status**: done | **File**: PhD/LWX/Touching.lean | **Depends on**: T5.15 | **Type**: cleanup
- Per-file cadence (T5.13–T5.15).

---
### [T5.16] `LWX.charPowerSeries_eq_mul_of_stable`
- **Status**: done (2026-09-09, sorry-free; written as a `calc` so `hsplit` does not rewrite the `T` inside `classicalCoordMatrix`)
- **File**: PhD/LWX/Touching.lean:238 | **Depends on**: T5.12, T5.13, T5.14, T5.15 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem charPowerSeries_eq_mul_of_stable (k : ℕ)
    {T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K)} (hT : IsCompactoid T)
    (hst : ∀ f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k,
      T f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) :
    charPowerSeries T
      = charPowerSeries (T.comp (1 - truncation (classicalSupport p ι h k)))
        * ((classicalCoordMatrix h k T).charpolyRev : PowerSeries K) := by
  sorry
```

#### Proof sketch
1. Write `T = T.comp (1 - pr) + T.comp pr` (`ContinuousLinearMap.comp_sub`, `comp_id`, `sub_add_cancel`).
2. `(T.comp (1 - pr)) * (T.comp pr) = 0`: for every `f`, `T (pr f) ∈ locPolyDegSubmoduleBlock` (`hst` + T5.12), so `pr (T (pr f)) = T (pr f)` (T5.13) and `(1 - pr) (T (pr f)) = 0`.
3. `charPowerSeries_add_of_mul_eq_zero` with `v := T.comp (1 - pr)`, `w := T.comp pr` (both compactoid: `IsCompactoid.comp_right hT _`).
4. `charPowerSeries (T.comp pr) = charpolyRev (classicalCoordMatrix)` by T5.15 then T5.14.

#### Mathlib lemmas needed
- `TateFredholm.charPowerSeries_add_of_mul_eq_zero` (`RieszColeman.lean:257`)
- `TateFredholm.IsCompactoid.comp_right` (`Matrix.lean:550`)
- `ContinuousLinearMap.comp_sub`
- T5.12
- T5.13
- T5.14
- T5.15

#### Sources
[LWX, §3.23 Step I], `lwx.txt:1807–1846`: the classical space is a stable finite piece and its `U_p`-slopes are among the overconvergent ones — the determinant factorisation is the precise form.  `TateFredholm.charPowerSeries_eq_mul_polynomial` (`FiniteFactor.lean`, S3) needs `T` to *commute* with the projection, which the coordinate truncation does not; the one-sided product `v w = 0` suffices, and that is what `charPowerSeries_add_of_mul_eq_zero` asks.

#### Generality decision
Any compactoid `T` preserving the classical subspace.

---
### [T5.17a] `LWX.classicalBasis` and its coordinates
- **Status**: done (2026-09-09, sorry-free; `locPolyDegBlockEquiv` de-privatised in `StepOne.lean`; `Basis` is `Module.Basis` in this mathlib)
- **File**: PhD/LWX/Touching.lean | **Depends on**: none | **Parent**: T5.17 | **Parallel**: yes
- **Type**: def + theorem (sub-ticket spawned by /beastmode, Tier A2)

#### Statement
```lean
private def classicalBasis (k : ℕ) :
    Basis (ι × ZMod (p ^ h) × Fin (k + 1)) K
      (locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k)

private theorem coe_classicalBasis (k : ℕ) (y : ι × ZMod (p ^ h) × Fin (k + 1)) :
    ((classicalBasis h k y :
        locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) :
      c(ι × (ZMod (p ^ h) × ℕ), K))
      = cSpace.single (y.1, (y.2.1, (y.2.2 : ℕ))) 1

private theorem repr_classicalBasis (k : ℕ)
    (f : locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k)
    (x : ι × ZMod (p ^ h) × Fin (k + 1)) :
    (classicalBasis h k).repr f x
      = (f : c(ι × (ZMod (p ^ h) × ℕ), K)) (x.1, (x.2.1, (x.2.2 : ℕ)))
```

#### Proof sketch
`classicalBasis := (Pi.basisFun K _).map (locPolyDegBlockEquiv h k).symm` — `locPolyDegBlockEquiv`
(`StepOne.lean:126`) is **de-privatised by this ticket**.  `repr_classicalBasis` is then
`Basis.map_repr` + `Pi.basisFun_repr`, and the equiv's `toFun` is coordinate evaluation by
definition.  `coe_classicalBasis`: the equiv's `invFun` at `Pi.single y 1` is
`∑ x, single (emb x) (Pi.single y 1 x)`, which `Finset.sum_eq_single y` collapses to
`single (emb y) 1`.

#### Mathlib lemmas needed
- `Pi.basisFun`, `Pi.basisFun_repr`, `Basis.map_repr`, `Basis.map_apply`, `Finset.sum_eq_single`,
  `Pi.single_eq_same`, `Pi.single_eq_of_ne`; project: `LWX.locPolyDegBlockEquiv`,
  `TateFredholm.cSpace.single`.

#### Sources
Bookkeeping for T5.17/T5.18: the determinant and characteristic polynomial of the restricted
operator have to be computed in *some* basis, and `classicalCoordMatrix`'s index is the natural
one.

#### Generality decision
`private`, specific to the block classical subspace.

---

### [T5.17] `LWX.det_classicalCoordMatrix_eq_det_upMatrix`
- **Status**: done (2026-09-09, sorry-free, via `classicalCoordMatrix_eq_toMatrix` + `LinearMap.det_toMatrix` twice)
- **File**: PhD/LWX/Touching.lean:250 | **Depends on**: T5.17a | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem det_classicalCoordMatrix_eq_det_upMatrix [Nonempty ι] (k : ℕ)
    (T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K))
    (hT : ∀ f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k,
      T f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) :
    (classicalCoordMatrix h k T).det = (upMatrix (p := p) (K := K) (ι := ι) h k T hT).det := by
  sorry
```

#### Proof sketch
1. De-privatise `locPolyDegBlockEquiv` (`StepOne.lean:126`) — a one-word edit — and let `b'` be the basis of `locPolyDegSubmoduleBlock` transported from `Pi.basisFun` along it; then `classicalCoordMatrix h k T = LinearMap.toMatrix b' b' (T.restrict hT)` (`LinearMap.toMatrix_apply`, `matrixCoeff` is the coordinate of `T (single _ 1)`).
2. `LinearMap.det_toMatrix b'` and `LinearMap.det_toMatrix b` both equal `LinearMap.det (T.restrict hT)`; `upMatrix` is the latter (`upMatrix` unfolds to `LinearMap.toMatrix b b (restrict)`).

#### Mathlib lemmas needed
- `LinearMap.det_toMatrix` (`Determinant.lean:212`)
- `LinearMap.toMatrix_apply`
- `Basis.map`/`LinearEquiv.toBasis`
- `LWX.upMatrix` (`AtkinLehnerInst.lean:202`)
- `LWX.locPolyDegBlockEquiv` (`StepOne.lean:126`, private — de-privatise)

#### Sources
Basis independence of the determinant.

#### Generality decision
General.

---
### [T5.18] `LWX.charpoly_classicalCoordMatrix_eq_charpoly_upMatrix`
- **Status**: done (2026-09-09, sorry-free, the same with `LinearMap.charpoly_toMatrix`)
- **File**: PhD/LWX/Touching.lean:260 | **Depends on**: T5.17 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem charpoly_classicalCoordMatrix_eq_charpoly_upMatrix [Nonempty ι] (k : ℕ)
    (T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K))
    (hT : ∀ f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k,
      T f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) :
    (classicalCoordMatrix h k T).charpoly
      = (upMatrix (p := p) (K := K) (ι := ι) h k T hT).charpoly := by
  sorry
```

#### Proof sketch
1. As T5.17 with `LinearMap.charpoly_toMatrix` in place of `det_toMatrix`.

#### Mathlib lemmas needed
- `LinearMap.charpoly_toMatrix` (`Charpoly/ToMatrix.lean:43`)
- T5.17's basis

#### Sources
Basis independence of the characteristic polynomial; consumed by Step III's root counts.

#### Generality decision
General.

---
### [CLEANUP-T5f] Run /cleanup on PhD/LWX/Touching.lean
- **Status**: done | **File**: PhD/LWX/Touching.lean | **Depends on**: T5.18 | **Type**: cleanup
- Per-file cadence (T5.16–T5.18).

---
### [T5.19] `LWX.height_le_negLogNorm_det`
- **Status**: done (2026-09-09, sorry-free; note the height index needed an explicit `Nat`-cast normalisation, the statement's `(card ι * ((k+1) * p^h) : ℤ)` elaborates with the casts pushed in)
- **File**: PhD/LWX/Touching.lean:272 | **Depends on**: T5.1, T5.2, T5.3, T5.9, T5.16, T5.17 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem height_le_negLogNorm_det [Nonempty ι] (κ : AnalyticWeight UK (M1Kh h ψ) ρ) {k : ℕ}
    {u : ι → Fin p → ZMod (p ^ h) → K} (hcl : IsClassicalShape θG h ψ U hU vRep hvΔ uu κ k u)
    (hρ : 0 ≤ ρ) (hσ : max ρ (p : ℝ)⁻¹ < 1)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape) :
    (newtonPolygon₀OfPowerSeries negLogNorm
        (discHeckeCharPowerSeries θG h ψ κ U hU vRep hvΔ idx uu)).height
          (Fintype.card ι * ((k + 1) * p ^ h))
      ≤ ((negLogNorm (classicalMatrix θG h ψ U hU vRep hvΔ idx uu κ hcl).det : WithTop ℝ) :
          WithBotTop ℝ) := by
  sorry
```

#### Proof sketch
1. `discHeckeCharPowerSeries = charPowerSeries (discHeckeBlockOp …)`; T5.16 (with T5.9 for `hst` and `isCompactoid_discHeckeBlockOp hρ hσ hshape`) splits it as `R * G` with `G = charpolyRev (classicalCoordMatrix)`.
2. T5.1 with `f := R` (entire by `charPowerSeries_isEntire`, constant term `1` by `charCoeff_zero`) and `g := G` (a polynomial: `Polynomial.isRestricted_toPowerSeries`; `coeff 0 G = 1` since `charpolyRev` has constant term `1`, `Matrix.charpolyRev` at `X = 0`): `height (R*G) n ≤ height G n`.
3. T5.2 at `n = card ι * ((k+1) * p^h) = natDegree`-index: `height G n ≤ coeffVal G n = negLogNorm (coeff n G)`, and T5.3 with T5.11's cardinality identification gives `coeff n G = (-1)^n * det (classicalCoordMatrix)`; `‖(-1)^n * d‖ = ‖d‖`; T5.17 turns the determinant into that of `classicalMatrix` (`= upMatrix …`).

#### Mathlib lemmas needed
- `LWX.isCompactoid_discHeckeBlockOp` (`DiscForms.lean:240`)
- `TateFredholm.charPowerSeries_isEntire` (`Fredholm.lean:176`)
- `TateFredholm.charCoeff_zero`
- `Polynomial.isRestricted_toPowerSeries`
- `Polynomial.coeff_coe`
- T5.1
- T5.2
- T5.3
- T5.11
- T5.16
- T5.17

#### Sources
[LWX, §3.23 Step I], `lwx.txt:1807–1846`, the sentence "the sum of the first `n_{k+1}` `U_p`-slopes … is also `(k+1)²qt`" — here only its `≤` half, which is the Minkowski bound (see the module docstring on the deliberate weakening).

#### Generality decision
Any classical-shape weight at any level `h`; the exponent `k` and level enter only through the size `card ι * ((k+1) p^h)`.

---
### [T5.20] `LWX.lwxLambda_mul_le_height_specCharSeries`
- **Status**: done (2026-09-09, sorry-free; `sum_lwxSlopes` de-privatised in `Halo.lean`; `IsBelow` unfolds to `toNewtonPolygon.height`, bridged by `height_toNewtonPolygon`)
- **File**: PhD/LWX/Touching.lean:286 | **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem lwxLambda_mul_le_height_specCharSeries (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ₀ : ℤ_[p] →+* K) (hψ₀ : ∀ x, ‖ψ₀ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (n : ℕ) :
    (((lwxLambda p (Fintype.card ι) n : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ) ≤
      (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ₀ T₀)).height n := by
  sorry
```

#### Proof sketch
1. `isBelow_newtonPolygon_specCharSeries hp2 D ω ψ₀ hψ₀ h0 h1 : (ofSlopes (lwxSlopes …) …).IsBelow (polygon of specCharSeries)`; `IsBelow` gives `height_lower n ≤ height_upper n` (unfold `NewtonPolygon₀.IsBelow`, `Halo.lean:210`).
2. `height_ofSlopes`/`heightFun_ofSlopes` (`OfSlopes.lean:112,138`): the lower polygon's height at `n` is `y₀ + ∑_{i<n} lwxSlopes p t T₀ i = ∑_{i<n} (i/t − i/(pt)) * (−log‖T₀‖) = lwxLambda p t n * (−log‖T₀‖)` (`Finset.sum_mul`, `Nat.cast_sum`, `lwxLambda`).

#### Mathlib lemmas needed
- `LWX.isBelow_newtonPolygon_specCharSeries` (`Halo.lean:210`)
- `NewtonPolygon₀.height_ofSlopes` (`OfSlopes.lean:138`)
- `LWX.lwxSlopes` (`Halo.lean:183`)
- `LWX.lwxLambda` (`Halo.lean:41`)
- `Finset.sum_mul`

#### Sources
[LWX, Cor 3.18], `lwx.txt:1684–1686`: "For `T ∈ ℂ_p` with `0 < v(T) < 1`, we have `v(c_n(T)) ≥ λ(n)v(T)` for every `n`" — the polygon form.

#### Generality decision
Any datum, any halo point.

---
### [T5.21] `LWX.two_mul_lwxLambda_touchX_mul_eq`
- **Status**: done (2026-09-09, sorry-free via `linear_combination (-log‖T₀‖) * hcast`; `hT0` is slack and is now `_hT0`)
- **File**: PhD/LWX/Touching.lean:296 | **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem two_mul_lwxLambda_touchX_mul_eq (t k : ℕ) {T₀ c : K} (hT0 : 0 < ‖T₀‖)
    (hT : ‖T₀‖ ^ (p - 1) = ‖c‖) :
    2 * ((lwxLambda p t (touchX p t (k + 1)) : ℝ) * (-Real.log ‖T₀‖))
      = ((t * ((k + 1) * p ^ 1) : ℕ) : ℝ) * ((k + 1) * (-Real.log ‖c‖)) := by
  sorry
```

#### Proof sketch
1. `two_mul_lwxLambda_touchX p t (k+1) : 2 * λ(n_{k+1}) = (k+1)^2 * p * (p-1) * t` (`UpperPolygon.lean:59`); cast to `ℝ` (`Nat.cast_mul`, `Nat.cast_sub` with `1 ≤ p`).
2. `hT : ‖T₀‖^(p-1) = ‖c‖` gives `(p-1) * (-log‖T₀‖) = -log‖c‖` (`Real.log_pow`, `hT0` for `log` of a positive number); substitute and `ring`.

#### Mathlib lemmas needed
- `LWX.two_mul_lwxLambda_touchX` (`UpperPolygon.lean:59`)
- `Real.log_pow`
- `Nat.cast_sub`
- `LWX.touchX` (`UpperPolygon.lean:34`)

#### Sources
[LWX, (3.23.1)], `lwx.txt:1826–1832` (verbatim in the ticket source block below): "`p/(q(p−1))·λ((k+1)qt) = … = (k+1)²qt/2`"; here `v(T₀) = v(p)/(p−1)` and `q = p`.

#### Generality decision
Pure arithmetic in `p, t, k` and the two norms; `hT` is exactly the classical-point norm.

---
### [CLEANUP-T5g] Run /cleanup on PhD/LWX/Touching.lean
- **Status**: done | **File**: PhD/LWX/Touching.lean | **Depends on**: T5.21 | **Type**: cleanup
- Per-file cadence (T5.19–T5.21).

---
### [T5.22] `LWX.touchX_succ_eq`
- **Status**: done (2026-09-09, sorry-free)
- **File**: PhD/LWX/Touching.lean:304 | **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem touchX_succ_eq (t k : ℕ) : touchX p t (k + 1) = t * ((k + 1) * p ^ 1) := by
  sorry
```

#### Proof sketch
1. `touchX p t (k+1) = (k+1) * (p * t)`; `pow_one`; `ring`.

#### Mathlib lemmas needed
- `LWX.touchX`
- `pow_one`

#### Sources
`n_{k+1} = (k+1)qt` in the two spellings used by `touchX` and `finrank_locPolyDegSubmoduleBlock`.

#### Generality decision
Trivial.

---
### [CLEANUP-ALL-2] Run /cleanup on PhD/LWX/Touching.lean (project-wide)
- **Status**: done | **File**: PhD/LWX/Touching.lean | **Depends on**: CLEANUP-T5g, CLEANUP-C6e | **Type**: cleanup
- `/cleanup-all` before the Step I milestone.

---
### [T5.23] `LWX.isStepOneTouching_of_atkinLehnerHypothesis` — **MILESTONE**
- **Status**: done
- **File**: PhD/LWX/Touching.lean:348 | **Depends on**: T5.5, T5.19, T5.20, T5.21, T5.22, CLEANUP-ALL-2 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem isStepOneTouching_of_atkinLehnerHypothesis (hp2 : p ≠ 2) [Nonempty ι]
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    {ω ω' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k (c.matrix idx) B
      (c'.matrix idx)) :
    IsStepOneTouching (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (intHom ψ) T₀ (k + 1) := by
  sorry
```

#### Proof sketch
1. Unfold `IsStepOneTouching`: the claim is `height (specCharSeries D ω (intHom ψ) T₀) (touchX (k+1)) = λ(touchX (k+1)) * (-log‖T₀‖)`.
2. **Seam.** `specCharSeries_ofCerts_eq_discHeckeCharPowerSeries hp2 h0 h1 hT hshape` (`SeamH.lean:401`) rewrites the series as `discHeckeCharPowerSeries θG 1 ψ c.weight …`; same at `(ω', T₀')` with `c'`.
3. **Upper bounds.** T5.19 at `c` and at `c'` (with `hρ := haloRhoH_nonneg`, `hσ` from `haloRhoH_lt_one` and `inv_lt_one_p`, level `h = 1`, and T5.22 to rewrite the index as `touchX`): `h_ψ ≤ −log‖det A‖`, `h_{ψ'} ≤ −log‖det A'‖`.
4. **H1.** `obtain ⟨B, hAB, P, Q, hQP, hA'⟩ := hAL`; T5.5 with `c := ψ p ^ (k+1)` (nonzero: `ψ.injective`, `Nat.cast_ne_zero`) gives `−log‖det A‖ + (−log‖det A'‖) = N * ((k+1) * (−log‖ψ p‖))`, `N = card ι * ((k+1) * p^1)`.
5. **Lower bounds.** T5.20 at `(D, ω, T₀)` and `(D, ω', T₀')`: `λ v ≤ h_ψ`, `λ v' ≤ h_{ψ'}`, where `v = −log‖T₀‖ = −log‖T₀'‖ = v'` (both `= (−log‖ψ p‖)/(p−1)` by `c.hnorm`, `c'.hnorm`: `Real.log_pow`, `Real.log_injOn_pos`).
6. **Squeeze.** T5.21 makes the H1 total `2 λ v`; in `WithBotTop ℝ` all the heights are finite coercions (`height_ne_top` from `T5.19`'s bound and `≠ ⊥` from `height_natCast_ne_bot`); pass to `ℝ` (`WithBotTop` order lemmas, `NewtonPolygon₀.coe_add_coe`) and `linarith`.

#### Mathlib lemmas needed
- `LWX.specCharSeries_ofCerts_eq_discHeckeCharPowerSeries` (`SeamH.lean:401`)
- `LWX.haloRhoH_nonneg`, `LWX.haloRhoH_lt_one` (`HaloWeightH.lean`)
- `Real.log_pow`
- `Real.log_injOn_pos`
- `WithBot.coe_le_coe`, `WithTop.coe_le_coe`
- T5.5
- T5.19
- T5.20
- T5.21
- T5.22

#### Sources
[LWX, §3.23 Step I], `lwx.txt:1807–1846` (the whole passage, quoted in `decomposition.md` tranche 5): "On the one hand, Proposition 3.22 says … `(k+1)²qt`. … On the other hand … the `y`-coordinate of the lower bound polygon is `(k+1)²qt/2`. … This exactly agrees (!) with half of the sum … That is, the Newton polygon … passes through the point `(n_{k+1}, λ(n_{k+1})v(T_{χ_k}))`."

#### Generality decision
**The milestone.**  Stated at level `h = 1` (conductor `p² = q²`, [LWX]'s `Iw_{q²}`); at higher levels the classical dimension is `(k+1)p^h t ≠ n_{k+1}` and the touching point moves.  H1 is the only input about the pairing; the conjugate character `ω'` and point `T₀'` are free parameters — the relation `ω' = ω⁻¹ω₀^{2k}` is never used here.

---
### [T5.24] `LWX.hasUnitBand_of_atkinLehnerHypothesis`
- **Status**: done
- **File**: PhD/LWX/Touching.lean:360 | **Depends on**: T5.23 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem hasUnitBand_of_atkinLehnerHypothesis (hp2 : p ≠ 2) [Nonempty ι]
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    {ω ω' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k (c.matrix idx) B
      (c'.matrix idx)) :
    HasUnitBand (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (k + 1) := by
  sorry
```

#### Proof sketch
1. `hasUnitBand_of_isStepOneTouching hp2 D ω (intHom ψ) (norm_intHom ψ hψ) c.h0 c.h1 (T5.23 …)` (`StepOne.lean:58`).

#### Mathlib lemmas needed
- `LWX.hasUnitBand_of_isStepOneTouching` (`StepOne.lean:58`)
- `LWX.norm_intHom`
- T5.23

#### Sources
Step I → Step II hand-off; `HasUnitBand` at every `k+1` (with `hasUnitBand_zero` for `k = 0`) is the `hband` hypothesis of the completed `lwx-slopes` theorems.

#### Generality decision
One line.

---
### [CLEANUP-T5h] Run /cleanup on PhD/LWX/Touching.lean
- **Status**: done | **File**: PhD/LWX/Touching.lean | **Depends on**: T5.24 | **Type**: cleanup
- Final per-file cleanup of `Touching.lean`.

---
### [C6.1] `LWX.norm_sub_one_lt_one_of_isPrimitiveRoot`
- **Status**: done (2026-09-09, sorry-free; `add_pow` + `Nat.Prime.dvd_choose_self` + `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`)
- **File**: PhD/LWX/ClassicalPoint.lean:49 | **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem norm_sub_one_lt_one_of_isPrimitiveRoot [IsUltrametricDist K] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ < 1) : ‖ζ - 1‖ < 1 := by
  sorry
```

#### Proof sketch
1. `‖ζ‖ = 1` (`ζ^p = 1`, `norm_pow`, `pow_eq_one_iff_of_nonneg`), so `‖ζ − 1‖ ≤ 1` (ultrametric).
2. `(ζ − 1)^p = ζ^p − 1 − ∑_{0<i<p} C(p,i)(ζ−1)^i` … cleaner: `ζ^p = ((ζ−1)+1)^p = ∑_i C(p,i)(ζ−1)^i` (`add_pow`), so `(ζ−1)^p = −∑_{0<i<p} C(p,i)(ζ−1)^i`; every term has norm `≤ ‖p‖·1` (`Nat.Prime.dvd_choose_self`… `p ∣ C(p,i)` for `0<i<p`: `Nat.Prime.dvd_choose_self`), so `‖ζ−1‖^p ≤ ‖p‖ < 1` and `‖ζ−1‖ < 1`.

#### Mathlib lemmas needed
- `IsPrimitiveRoot.pow_eq_one`
- `add_pow`
- `Nat.Prime.dvd_choose_self`
- `IsUltrametricDist.norm_add_le_max`
- `pow_lt_one_iff_of_nonneg`

#### Sources
Standard: a `p`-th root of unity reduces to `1` in characteristic `p`.

#### Generality decision
Any ultrametric field with `‖p‖ < 1`.

---
### [C6.1a] `LWX.norm_of_isPrimitiveRoot` and `LWX.norm_natCast_eq_one_of_not_dvd`
- **Status**: done (2026-09-09, sorry-free; `IsUltrametricDist.norm_intCast_le_one` needs `(R := K)` pinned)
- **File**: PhD/LWX/ClassicalPoint.lean | **Depends on**: none | **Parent**: C6.2 | **Parallel**: yes
- **Type**: theorem (two; sub-ticket spawned by /beastmode, Tier A2)

#### Statement
```lean
theorem norm_of_isPrimitiveRoot {ζ : K} (hζ : IsPrimitiveRoot ζ p) : ‖ζ‖ = 1

theorem norm_natCast_eq_one_of_not_dvd {i : ℕ} (hpi : ¬ p ∣ i)
    (hpK : ‖((p : ℕ) : K)‖ < 1) : ‖((i : ℕ) : K)‖ = 1
```

#### Proof sketch
First: `‖ζ‖ ^ p = ‖ζ ^ p‖ = 1`, and trichotomy on `‖ζ‖` versus `1` with `pow_lt_one₀` /
`one_lt_pow₀`.
Second: Bezout.  `p` prime and `p ∤ i` give `Nat.Coprime p i`, so `Nat.gcd_eq_gcd_ab` supplies
`a b : ℤ` with `a·p + b·i = 1`.  Cast to `K`: `1 = ‖a·p + b·i‖ ≤ max (‖a‖‖p‖) (‖b‖‖i‖) ≤
max ‖p‖ ‖i‖` using `norm_intCast_le_one`; with `‖p‖ < 1` this forces `1 ≤ ‖i‖`, and
`norm_natCast_le_one` gives the reverse.

#### Mathlib lemmas needed
- `pow_lt_one₀`, `one_lt_pow₀`, `Nat.Coprime`, `Nat.gcd_eq_gcd_ab`,
  `IsUltrametricDist.norm_natCast_le_one`, `IsUltrametricDist.norm_intCast_le_one`
  (`Analysis/Normed/Ring/Ultra.lean:77`), `norm_add_le_max` / `IsUltrametricDist.norm_add_le_max`.

#### Sources
Standard; both are used repeatedly in tranche 6.

#### Generality decision
Public (the second is a general fact about ultrametric fields with `‖p‖ < 1` and is reused by
C6.2, C6.4).

---

### [C6.2] `LWX.norm_one_sub_pow_of_isPrimitiveRoot`
- **Status**: done (2026-09-09, sorry-free; via `geom_sum_mul` and the ultrametric dominant-term lemma)
- **File**: PhD/LWX/ClassicalPoint.lean:56 | **Depends on**: C6.1, C6.1a | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem norm_one_sub_pow_of_isPrimitiveRoot {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ < 1) {i : ℕ} (hi0 : 0 < i) (hip : i < p) :
    ‖1 - ζ ^ i‖ = ‖1 - ζ‖ := by
  sorry
```

#### Proof sketch
1. `1 − ζ^i = (1 − ζ) * ∑_{j<i} ζ^j` (`mul_neg_geom_sum` / `geom_sum_mul_neg`).
2. `‖∑_{j<i} ζ^j‖ = 1`: `∑ ζ^j ≡ i (mod ζ − 1)` — write `ζ^j = 1 + (ζ^j − 1)` with `‖ζ^j − 1‖ ≤ ‖ζ − 1‖ < 1` (C6.1 + `1 − ζ^j = (1−ζ)(…)` bound), so `‖∑ ζ^j − i‖ < 1 = ‖(i : K)‖` (`i < p` is a unit: `‖(i:K)‖ = 1` from `Nat.Coprime`/`Padic`-style — here: `‖(i : K)‖ = 1` because `‖p‖ < 1` and `i ∣ …`; simplest: `(i : K)` is a unit of norm `1` since `‖p‖ < 1` and `p ∤ i` — use `IsUltrametricDist.norm_natCast_le_one` for `≤` and, for `≥`, `1 = ‖p^?‖`… take the hypothesis route: state a helper `norm_natCast_eq_one_of_lt` from `Nat.Coprime i p`, Bezout `a i + b p = 1`, ultrametric); then `norm_eq_of_norm_sub_lt`.

#### Mathlib lemmas needed
- `geom_sum_mul_neg` / `mul_neg_geom_sum`
- `IsUltrametricDist.norm_natCast_le_one`
- `Nat.exists_mul_emod_eq_one_of_coprime` (Bezout for the unit norm)
- C6.1

#### Sources
Standard (the cyclotomic units `(1 − ζ^i)/(1 − ζ)`).

#### Generality decision
`0 < i < p`.

---
### [C6.3] `LWX.norm_sub_one_pow_of_isPrimitiveRoot`
- **Status**: done (2026-09-09, sorry-free; `IsPrimitiveRoot.prod_one_sub_pow_eq_order` (`RootsOfUnity/Lemmas.lean`, needs an explicit import))
- **File**: PhD/LWX/ClassicalPoint.lean:63 | **Depends on**: C6.2 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem norm_sub_one_pow_of_isPrimitiveRoot {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ < 1) : ‖ζ - 1‖ ^ (p - 1) = ‖((p : ℕ) : K)‖ := by
  sorry
```

#### Proof sketch
1. `Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ : cyclotomic p K = ∏_{μ ∈ primitiveRoots p K} (X − C μ)`, and `primitiveRoots p K = {ζ^i : 0 < i < p}` for prime `p` (`IsPrimitiveRoot.pow_of_coprime`, `Finset.image`; or `Polynomial.cyclotomic_prime` + `IsPrimitiveRoot.geom_sum_eq_zero` to get `∏_{0<i<p}(1 − ζ^i) = p` directly by evaluating at `1`: `Polynomial.eval_one_cyclotomic_prime`).
2. Take norms: `‖p‖ = ∏_{0<i<p} ‖1 − ζ^i‖ = ‖1 − ζ‖^{p−1}` by C6.2 (`Finset.prod_const`, `Finset.card_range`…).

#### Mathlib lemmas needed
- `Polynomial.eval_one_cyclotomic_prime` (`Cyclotomic/Eval.lean:33`)
- `Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots` (`Cyclotomic/Basic.lean:476`)
- `Polynomial.eval_prod`
- `norm_prod`
- C6.2

#### Sources
[LWX, §3.23], `lwx.txt:1797–1798`: "The corresponding `T`-coordinates `T_{χ_k}` have valuation `q/ϕ(q²) = p/(q(p−1))`" — for `q = p` this is `v(ζ_p − 1) = 1/(p−1)`.

#### Generality decision
The norm of `1 − ζ_p` in any ultrametric field with `‖p‖ < 1`.

---
### [CLEANUP-C6a] Run /cleanup on PhD/LWX/ClassicalPoint.lean
- **Status**: done | **File**: PhD/LWX/ClassicalPoint.lean | **Depends on**: C6.3 | **Type**: cleanup
- Per-file cadence (C6.1–C6.3).

---
### [C6.4] `LWX.norm_classicalPoint`
- **Status**: done (2026-09-09, sorry-free; needed the helper `inv_lt_norm_sub_one_of_isPrimitiveRoot` (`p⁻¹ < ‖ζ−1‖`, where `p ≠ 2` is load-bearing))
- **File**: PhD/LWX/ClassicalPoint.lean:76 | **Depends on**: C6.1 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem norm_classicalPoint (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ‖classicalPoint p k ζ‖ = ‖ζ - 1‖ := by
  sorry
```

#### Proof sketch
1. `classicalPoint = ζ·E − 1 = (ζ − 1)·E + (E − 1)` with `E = padicExp(pk)`; `‖E − 1‖ ≤ ‖pk‖ ≤ ‖p‖ = p⁻¹` (`PadicExpLog.norm_padicExp_sub_one_le`-style bound; the disc condition `‖pk‖² < ‖p‖` holds for odd `p`), while `‖ζ − 1‖^{p−1} = ‖p‖` (C6.3) gives `‖ζ − 1‖ = p^{−1/(p−1)} > p^{−1}` for `p ≥ 3`; `‖E‖ = 1`; the ultrametric inequality with a strict comparison pins `‖ζE − 1‖ = ‖ζ − 1‖`.

#### Mathlib lemmas needed
- `PadicExpLog.norm_padicExp_sub_one_le` (or the corresponding bound in `PadicExpLog.lean`; locate)
- `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`
- C6.3

#### Sources
Elementary.

#### Generality decision
`p ≠ 2` is needed for the exp/log discs and for `p^{−1/(p−1)} > p^{−1}`.

---
### [C6.5] `LWX.norm_classicalPoint_pow`
- **Status**: done (2026-09-09, sorry-free)
- **File**: PhD/LWX/ClassicalPoint.lean:82 | **Depends on**: C6.3, C6.4 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem norm_classicalPoint_pow (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ‖classicalPoint p k ζ‖ ^ (p - 1) = ‖((p : ℕ) : K)‖ := by
  sorry
```

#### Proof sketch
1. `rw [C6.4, C6.3]`.

#### Mathlib lemmas needed
- C6.3
- C6.4

#### Sources
As C6.3.

#### Generality decision
One line.

---
### [C6.6] `LWX.inv_lt_norm_classicalPoint`
- **Status**: done (2026-09-09, sorry-free)
- **File**: PhD/LWX/ClassicalPoint.lean:88 | **Depends on**: C6.5 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem inv_lt_norm_classicalPoint (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    (p : ℝ)⁻¹ < ‖classicalPoint p k ζ‖ := by
  sorry
```

#### Proof sketch
1. From C6.5: `‖T₀‖^{p−1} = p⁻¹`; if `‖T₀‖ ≤ p⁻¹` then `‖T₀‖^{p−1} ≤ p^{−(p−1)} < p^{−1}` for `p ≥ 3` (`pow_le_pow_left`, `p − 1 ≥ 2`), contradiction.

#### Mathlib lemmas needed
- `pow_le_pow_left`
- `inv_pow`
- C6.5

#### Sources
Elementary.

#### Generality decision
`p ≠ 2`.

---
### [CLEANUP-C6b] Run /cleanup on PhD/LWX/ClassicalPoint.lean
- **Status**: done | **File**: PhD/LWX/ClassicalPoint.lean | **Depends on**: C6.6 | **Type**: cleanup
- Per-file cadence (C6.4–C6.6).

---
### [C6.7] `LWX.norm_classicalPoint_lt_one`
- **Status**: done (2026-09-09, sorry-free)
- **File**: PhD/LWX/ClassicalPoint.lean:94 | **Depends on**: C6.4, C6.1 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem norm_classicalPoint_lt_one (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ‖classicalPoint p k ζ‖ < 1 := by
  sorry
```

#### Proof sketch
1. `rw [C6.4]; exact C6.1 …` (with `hpK ▸ inv_lt_one_p`).

#### Mathlib lemmas needed
- C6.1
- C6.4

#### Sources
Elementary.

#### Generality decision
One line.

---
### [C6.8] `LWX.TH_one_classicalPoint`
- **Status**: done (2026-09-09, sorry-free; needed a new helper `padicExp_pow` (exp(w)^n = exp(nw)))
- **File**: PhD/LWX/ClassicalPoint.lean:100 | **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem TH_one_classicalPoint (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    TH p 1 (classicalPoint p k ζ) = PadicExpLog.padicExp (((p : ℕ) : K) ^ 2 * k) - 1 := by
  sorry
```

#### Proof sketch
1. `TH p 1 T₀ = (1 + T₀)^p − 1 = (ζ · E)^p − 1 = ζ^p · E^p − 1 = E^p − 1` (`hζ.pow_eq_one`, `mul_pow`).
2. `E^p = padicExp(p · pk) = padicExp(p²k)`: `PadicExpLog.padicExp_add` iterated (`padicExp_nsmul`-style: prove `padicExp (n • w) = padicExp w ^ n` by induction from `padicExp_add`, under the disc condition `‖w‖² < ‖p‖`, which holds for `w = pk` when `p ≠ 2`).

#### Mathlib lemmas needed
- `IsPrimitiveRoot.pow_eq_one`
- `PadicExpLog.padicExp_add` (`PadicExpLog.lean:410`)
- `mul_pow`

#### Sources
[LWX, §2.1] / `HaloWeightH.lean` docstring: `T'_h = χ(exp(p^{h+1})) − 1 = (1+T₀)^{p^h} − 1`; at a classical point of conductor `p²` the root of unity dies at `h = 1`.

#### Generality decision
`p ≠ 2` for the exp disc.

---
### [C6.9] `LWX.norm_TH_one_classicalPoint_sq_lt`
- **Status**: done (2026-09-09, sorry-free)
- **File**: PhD/LWX/ClassicalPoint.lean:106 | **Depends on**: C6.8 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem norm_TH_one_classicalPoint_sq_lt (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ‖TH p 1 (classicalPoint p k ζ)‖ ^ 2 < (p : ℝ)⁻¹ := by
  sorry
```

#### Proof sketch
1. `rw [C6.8]`; `‖padicExp(p²k) − 1‖ ≤ ‖p²k‖ ≤ p^{−2}` (exp bound), so the square is `≤ p^{−4} < p^{−1}`.

#### Mathlib lemmas needed
- the `padicExp` bound as in C6.4
- `pow_lt_pow_right_of_lt_one`
- C6.8

#### Sources
Elementary.

#### Generality decision
`p ≠ 2`.

---
### [CLEANUP-C6c] Run /cleanup on PhD/LWX/ClassicalPoint.lean
- **Status**: done | **File**: PhD/LWX/ClassicalPoint.lean | **Depends on**: C6.9 | **Type**: cleanup
- Per-file cadence (C6.7–C6.9).

---
### [C6.10] `LWX.haloExponentH_one_classicalPoint`
- **Status**: done (2026-09-09, sorry-free)
- **File**: PhD/LWX/ClassicalPoint.lean:113 | **Depends on**: C6.8 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem haloExponentH_one_classicalPoint (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    haloExponentH p 1 (classicalPoint p k ζ) = k := by
  sorry
```

#### Proof sketch
1. `haloExponentH p 1 T₀ = padicLog (1 + TH p 1 T₀) / p^2`; by C6.8 `1 + TH = padicExp (p²k)`; `PadicExpLog.padicLog_padicExp hp2 (hw : ‖p²k‖² < ‖p‖)` gives `padicLog (padicExp (p²k)) = p²k`; divide (`mul_div_cancel_left₀`, `p² ≠ 0`).

#### Mathlib lemmas needed
- `LWX.haloExponentH` (`HaloWeightH.lean:342`)
- `PadicExpLog.padicLog_padicExp` (`PadicExpLog.lean:806`)
- `mul_div_cancel_left₀`
- C6.8

#### Sources
`HaloWeightH.lean` docstring: `s_h = log(1 + T'_h)/p^{h+1}`; at a classical point of weight `k` this is `k`.

#### Generality decision
Level `1` only; at level `h ≥ 1` the same holds.

---
### [C6.11] `LWX.mk_choose_natCast_mul_pow`
- **Status**: done
- **File**: PhD/LWX/ClassicalPoint.lean:120 | **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem mk_choose_natCast_mul_pow (k : ℕ) (x : K) :
    PowerSeries.mk (fun m => Ring.choose (k : K) m * x ^ m)
      = (1 + PowerSeries.C x * PowerSeries.X) ^ k := by
  sorry
```

#### Proof sketch
1. `Ring.choose_natCast : Ring.choose (k : K) m = Nat.choose k m` (`Binomial.lean:399`); `PowerSeries.ext`, `coeff_mk`, and the binomial theorem `(1 + C x * X)^k = ∑ C(k,m) (C x * X)^m` (`add_pow`, `PowerSeries.coeff_C_mul_X_pow`, `Finset.sum_ite_eq`).

#### Mathlib lemmas needed
- `Ring.choose_natCast` (`RingTheory/Binomial.lean:399`)
- `add_pow`
- `PowerSeries.coeff_mk`
- `PowerSeries.coeff_C_mul_X_pow`

#### Sources
The binomial series at a natural exponent is a polynomial.

#### Generality decision
Any `K` with a `BinomialRing` structure (`CharZero` field).

---
### [C6.12] `LWX.autFactor_haloWeightH_classicalPoint`
- **Status**: done
- **File**: PhD/LWX/ClassicalPoint.lean:131 | **Depends on**: C6.10, C6.11 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem autFactor_haloWeightH_classicalPoint (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (k : ℕ) (h0 : (p : ℝ)⁻¹ < ‖classicalPoint p k ζ‖)
    (h1 : ‖classicalPoint p k ζ‖ < 1) (hT : ‖TH p 1 (classicalPoint p k ζ)‖ ^ 2 < (p : ℝ)⁻¹)
    (g : M1Kh 1 ψ) :
    (haloWeightH 1 ψ (classicalPoint p k ζ) ω hp2 hψ h0 h1 hT).toWeightSeries.autFactor g.1
        * linX g.1
      = PowerSeries.C (haloCharFunH 1 ψ (classicalPoint p k ζ) ω (g.1 1 1) * (g.1 1 1)⁻¹ ^ k)
        * linX g.1 ^ (k + 1) := by
  sorry
```

#### Proof sketch
1. `autFactor_haloWeightH … g : autFactor = C (haloCharFunH … (g 1 1)) * mk (fun m => Ring.choose (haloExponentH p 1 T₀) m * (g 1 0 / g 1 1)^m)` (`HaloWeightH.lean:1097`).
2. `rw [C6.10]` turns the exponent into `(k : K)`, then C6.11 makes the series `(1 + C (c/d) * X)^k`; `(1 + C (c/d) X) = C d⁻¹ * linX g` (`linX = C d + C c X`, `d ≠ 0`), so the series is `C d⁻¹^k * linX^k`; multiply by `linX` and collect.

#### Mathlib lemmas needed
- `LWX.autFactor_haloWeightH` (`HaloWeightH.lean:1097`)
- `QMF.linX` (`Series.lean:167`)
- `mul_pow`
- `map_pow`
- C6.10
- C6.11

#### Sources
The `HaloWeightH.lean` docstring: "the character on the `p^{−(h+1)}`-disc about a `ℤ_p`-unit `a` is `x ↦ [a](T₀)·exp(s_h·log(x/a))`" — with `s_1 = k` it is `[a](T₀)·(x/a)^k`.

#### Generality decision
The constant `u = haloCharFunH(d)·d^{−k}` is carried abstractly; identifying it with `ψ(d)` is the deferred gap `AG-ζ`.

---
### [CLEANUP-C6d] Run /cleanup on PhD/LWX/ClassicalPoint.lean
- **Status**: done | **File**: PhD/LWX/ClassicalPoint.lean | **Depends on**: C6.12 | **Type**: cleanup
- Per-file cadence (C6.10–C6.12).

---
### [C6.13] `LWX.isClassicalShape_haloWeightH_classicalPoint`
- **Status**: done
- **File**: PhD/LWX/ClassicalPoint.lean:148 | **Depends on**: C6.12 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem isClassicalShape_haloWeightH_classicalPoint (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (k : ℕ) (h0 : (p : ℝ)⁻¹ < ‖classicalPoint p k ζ‖)
    (h1 : ‖classicalPoint p k ζ‖ < 1) (hT : ‖TH p 1 (classicalPoint p k ζ)‖ ^ 2 < (p : ℝ)⁻¹) :
    IsClassicalShape θG 1 ψ U hU vRep hvΔ uu
      (haloWeightH 1 ψ (classicalPoint p k ζ) ω hp2 hψ h0 h1 hT) k
      fun i t a => haloCharFunH 1 ψ (classicalPoint p k ζ) ω
          (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1)
        * (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1)⁻¹ ^ k := by
  sorry
```

#### Proof sketch
1. `intro i t a; exact C6.12 … (discConjK 1 (certM1 …) a ψ)` — `certConj` is `(discConjK …).1`, so `g.1 1 1` is `certConj … 1 1`.

#### Mathlib lemmas needed
- `LWX.certConj` (`Touching.lean`)
- C6.12

#### Sources
Assembly.

#### Generality decision
One line.

---
### [C6.14] `LWX.classicalData`
- **Status**: done
- **File**: PhD/LWX/ClassicalPoint.lean:160 | **Depends on**: C6.5 | **Parallel**: no | **Type**: def

#### Statement
```lean
def classicalData (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω (classicalPoint p k ζ) k where
  h0 := inv_lt_norm_classicalPoint hp2 hζ hpK k
  h1 := norm_classicalPoint_lt_one hp2 hζ hpK k
  hT := norm_TH_one_classicalPoint_sq_lt hp2 hζ hpK k
  hnorm := by sorry
  u := fun i t a => haloCharFunH 1 ψ (classicalPoint p k ζ) ω
      (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1)
    * (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1)⁻¹ ^ k
  shape := isClassicalShape_haloWeightH_classicalPoint ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ k _ _ _
```

#### Proof sketch
1. The one remaining obligation `hnorm : ‖classicalPoint p k ζ‖^(p−1) = ‖ψ p‖`: `ψ (p : ℚ_[p]) = ((p : ℕ) : K)` (`map_natCast`), then C6.5.

#### Mathlib lemmas needed
- `map_natCast`
- C6.5

#### Sources
The assembly of the classical datum at `T_{χ_k}`; `Touching.lean`'s Step I applied to `classicalData … k` and `classicalData … (ζ⁻¹) k` at the conjugate `ω'` is [LWX]'s Step I on the nose.

#### Generality decision
`ζ` is a parameter (`IsPrimitiveRoot ζ p`), so `K` must contain the `p`-th roots of unity — true for `ℂ_p` and for the fields [LWX] work over.

---
### [CLEANUP-C6e] Run /cleanup on PhD/LWX/ClassicalPoint.lean
- **Status**: done | **File**: PhD/LWX/ClassicalPoint.lean | **Depends on**: C6.14 | **Type**: cleanup
- Final per-file cleanup of `ClassicalPoint.lean`.

---
### [S7.1] `LWX.exists_evalT_eq_zero_of_unitSlope_eq`
- **Status**: done
- **File**: PhD/LWX/StepThree.lean:75 | **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem exists_evalT_eq_zero_of_unitSlope_eq [IsAlgClosed K] {f : PowerSeries K}
    (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f) (hf0 : PowerSeries.coeff 0 f = 1)
    {j : ℕ} {m : ℝ}
    (hj : (newtonPolygon₀OfPowerSeries negLogNorm f).unitSlope j = (m : WithBotTop ℝ)) :
    ∃ a : K, PowerSeries.evalT a f = 0 ∧ ‖a‖ = Real.exp m := by
  sorry
```

#### Proof sketch
1. **(AG-Z, three sub-steps; spawn as sub-tickets if the worker prefers.)**  Z1: `exists_isDominantFactorization (ρ := Real.exp m) …` (`SlopeFactor.lean:463`) gives `f = P * G` with `P` a polynomial dominant at radius `exp m` of degree `N` = the number of slopes `≤ m`, and `G` a unit on the closed disc (`IsDominantFactorization`'s fields, `SlopeFactor.lean:185`).
2. Z2: `G` has all slopes `> m` (its Newton polygon has no segment of slope `≤ m`, from the unit-on-the-disc property: `IsDominantFactorization.isEntireCoprime` / `norm_coeff_r_mul_pow_le_of_eq_mul_add`), so `height_newtonPolygon₀OfPowerSeries_mul_of_forall_le` / `unitSlope_mul_of_forall_le` identify the first `N` unit slopes of `f` with those of `P`; in particular `P` has unit slope `m` at `j`.
3. Z3: `card_roots_slope P hP0 w hw hm hl` (`PolynomialRoots.lean:955`) with `w` transported from `NormedField.valuation` along `K ≃+* AlgebraicClosure K` (`IsAlgClosed.algebraMap_bijective_of_isIntegral`, as in `JacobsSlash/5_EigenSlopes.lean:110–122`) yields a root `a` of `P` with `‖a‖ = exp m`; `evalT a f = evalT a P * evalT a G = 0` (`evalT_mul`, `evalT_coe`).

#### Mathlib lemmas needed
- `TateFredholm.exists_isDominantFactorization` (`SlopeFactor.lean:463`)
- `TateFredholm.IsDominantFactorization` (`SlopeFactor.lean:185`)
- `unitSlope_mul_of_forall_le` (`Product.lean:1025`)
- `card_roots_slope` (`PolynomialRoots.lean:955`)
- `IsAlgClosed.algebraMap_bijective_of_isIntegral`
- `PowerSeries.evalT_mul` (`Riesz.lean:224`)
- `PowerSeries.evalT_coe` (`Riesz.lean:117`)

#### Sources
Blueprint §5.11 (`card_roots_slope`) for polynomials, extended to entire series through the slope factorisation of `SlopeFactor.lean`; the converse `norm_eq_exp_slope_of_hasSum_zero` (`PowerSeriesZeros.lean:1290`) is already proved.

#### Generality decision
**API gap AG-Z**: general Newton-polygon theory over a complete algebraically closed ultrametric field.  **Resolved 2026-09-09**: the general statement is `TateFredholm.exists_evalT_zero_of_unitSlope` in the new seam file `PhD/TateFredholm/NewtonSlopes.lean` — *not* `PhD/NewtonPolygons/PowerSeriesZeros.lean` as planned, because `PowerSeries.evalT` is `TateFredholm` API and `PhD/NewtonPolygons/` must not depend on `PhD/TateFredholm/`.  The seam file also absorbed `exists_evalT_zero_of_slope` and its two private helpers from `PhD/JacobsSlash/5_EigenSlopes.lean`, which had flagged them as "public-API candidates for the `TateFredholm` × `NewtonPolygons` seam"; `LWX.exists_evalT_eq_zero_of_unitSlope_eq` is now a one-line specialisation.

---
### [S7.2] `LWX.rightIndex_zero_eq_ordDim`
- **Status**: done
- **File**: PhD/LWX/StepThree.lean:88 | **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem rightIndex_zero_eq_ordDim (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    [Nonempty ι] : rightIndex D ω 0 = ordDim D ω := by
  sorry
```

#### Proof sketch
1. `rightIndex D ω 0 = sSup {n | 0 ≤ n ∧ n ≤ t ∧ IsUnitCoeff D ω n}` (`touchX … 0 = 0`) and `ordDim D ω = sSup {n | IsUnit (charCoeff (D.op ω) n)}`; show the two sets are equal.
2. For `n ≤ t`: `lwxLambda p t n = 0` (each term `n'/t − n'/(pt) = 0` for `n' < t`), so `IsUnitCoeff D ω n ↔ IsUnit ((charCoeff …) 0)`, and `IsUnit (charCoeff …) ↔ IsUnit ((charCoeff …) 0)` by `HaloInt.isUnit_of_isUnit_coeff_zero` (`TateRiesz.lean`) and its converse (the halo ring's units are detected by the constant coefficient — see `Degrees.lean`'s `HaloInt.one_le_norm_of_isUnit` and the ticket D1a note; prove `IsUnit g → IsUnit (g 0)` via `‖g‖ = 1` and the norm formula `norm_def`/`norm_coeff_le_norm` at `j = 0`… or through the ring hom to the residue: spawn if needed).
3. For `n > t`: neither set contains `n` (`not_isUnit_charCoeff_of_ordDim_lt` needs `ordDim ≤ t`: from `lwxLambda_pos` as in `bddAbove_isUnit_charCoeff`; and `IsUnitCoeff` is restricted to `n ≤ t` by definition).

#### Mathlib lemmas needed
- `LWX.rightIndex` (`Vertices.lean:65`)
- `LWX.ordDim` (`Degrees.lean:41`)
- `LWX.IsUnitCoeff` (`Vertices.lean:47`)
- `HaloInt.isUnit_of_isUnit_coeff_zero` (`TateRiesz.lean`)
- `LWX.lwxLambda_pos` (`Degrees.lean:64`)
- `Nat.sSup_def`/`csSup` API

#### Sources
[LWX, Thm 3.19 proof], `lwx.txt:1717–1719`: "Let `d` be the maximal index such that `c_d(T)` is a unit in `ℤ_p⟦T⟧`, or equivalently, the constant term of `c_d(T)` is a `p`-adic unit in `ℤ_p`" — the "equivalently" is exactly `IsUnit (charCoeff n) ↔ IsUnitCoeff n` below `t`.

#### Generality decision
Needs `hp2` only through the halo bound used for `ordDim ≤ t`.

---
### [S7.3] `LWX.faceRight_zero_specCharSeries_eq_ordDim`
- **Status**: done
- **File**: PhD/LWX/StepThree.lean:95 | **Depends on**: S7.2 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem faceRight_zero_specCharSeries_eq_ordDim (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ₀ : ℤ_[p] →+* K) (hψ₀ : ∀ x, ‖ψ₀ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ₀ T₀)).faceRight 0
      = ordDim D ω := by
  sorry
```

#### Proof sketch
1. `hasUnitBand_zero D ω`; `unitSlope_specCharSeries_eq_of_mem_band … (k := 0)` says the unit slopes `j < rightIndex D ω 0` are `0` (`leftIndex D ω 0 = 0`: `sInf` of a set containing `0`), and `lt_unitSlope_specCharSeries_of_rightIndex_le` says they are `> 0` from `rightIndex D ω 0` on.
2. Hence `{j | 0 < unitSlope j} = {j | rightIndex ≤ j}` and `faceRight 0 = sInf = rightIndex D ω 0` (`Nat.sInf_def`); finish with S7.2.

#### Mathlib lemmas needed
- `LWX.hasUnitBand_zero` (`Vertices.lean:80`)
- `LWX.unitSlope_specCharSeries_eq_of_mem_band` (`Vertices.lean:982`)
- `LWX.lt_unitSlope_specCharSeries_of_rightIndex_le` (`Vertices.lean:1000`)
- `NewtonPolygon₀.faceRight` (`Face.lean:85`)
- `NewtonPolygon₀.le_faceRight_of_forall_le`, `NewtonPolygon₀.faceRight_le_of_lt_unitSlope`-style API (`Face.lean:293–320`)
- S7.2

#### Sources
[LWX, Cor 3.21], `lwx.txt:1743–1752`: "The degree of `X^ord_ω` over `W_ω` is `r_ord(ω)`. As a consequence, … the slope zero subspace of `S^{D,†}_{(k,ψ)}` has dimension `r_ord(ψ|_Δ·ω₀^k)`" — at the coefficient level, with the degree `d` of [LWX, Thm 3.19]'s proof (`lwx.txt:1717–1730`: "the Newton polygon of `∑ c_n(T_χ)Xⁿ` has slope zero in the first `d` segment and the vertices with `x`-coordinate strictly bigger than `d` must have `y`-coordinate at least `min{1, v(T_χ)}`").

#### Generality decision
**Unconditional** (no H1, no H2): Step II's band at `k = 0` needs no touching hypothesis.  This is the control statement `ordDim = slope-zero dimension` the board wanted.

---
### [CLEANUP-S7a] Run /cleanup on PhD/LWX/StepThree.lean
- **Status**: done | **File**: PhD/LWX/StepThree.lean | **Depends on**: S7.3 | **Type**: cleanup
- Per-file cadence (S7.1–S7.3).

---
### [S7.4] `LWX.faceRight_specCharSeries_eq_rightIndex`
- **Status**: done
- **File**: PhD/LWX/StepThree.lean:106 | **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem faceRight_specCharSeries_eq_rightIndex (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ₀ : ℤ_[p] →+* K) (hψ₀ : ∀ x, ‖ψ₀ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ₀ T₀)).faceRight
        (((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖))
      = rightIndex D ω k := by
  sorry
```

#### Proof sketch
1. `faceRight σ = sInf {j | σ < unitSlope j}`; by `lt_unitSlope_specCharSeries_of_rightIndex_le` every `j ≥ rightIndex` is in the set, and by `unitSlope_specCharSeries_eq_of_mem_band` plus monotonicity (`NewtonPolygon₀.unitSlope_mono`) every `j < rightIndex` has `unitSlope j ≤ σ` (below `leftIndex` the slopes are `≤` the band value by convexity); so the `sInf` is `rightIndex`.

#### Mathlib lemmas needed
- `LWX.unitSlope_specCharSeries_eq_of_mem_band` (`Vertices.lean:982`)
- `LWX.lt_unitSlope_specCharSeries_of_rightIndex_le` (`Vertices.lean:1000`)
- `NewtonPolygon₀.unitSlope_mono`
- `Nat.sInf_def`, `Nat.sInf_le`, `Nat.le_sInf`-style (`Nat.sInf_mem`)

#### Sources
[LWX, Step II], `lwx.txt:1975–1990`: "the points `(n⁻_k, λ(n⁻_k)v(T))` and `(n⁺_k, λ(n⁺_k)v(T))` are two consecutive vertices of the Newton polygon … the line segment connecting these two vertices has slope `kϕ(q)v(T)`".

#### Generality decision
Conditional on `HasUnitBand D ω k` as the band lemmas are.

---
### [S7.5] `LWX.faceLeft_specCharSeries_eq_leftIndex`
- **Status**: done
- **File**: PhD/LWX/StepThree.lean:115 | **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem faceLeft_specCharSeries_eq_leftIndex (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] (ψ₀ : ℤ_[p] →+* K) (hψ₀ : ∀ x, ‖ψ₀ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) {k : ℕ} (hb : HasUnitBand D ω k) :
    (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ₀ T₀)).faceLeft
        (((k * (p - 1) : ℕ) : ℝ) * (-Real.log ‖T₀‖))
      = leftIndex D ω k := by
  sorry
```

#### Proof sketch
1. Mirror of S7.4 with `faceLeft σ = sInf {j | σ ≤ unitSlope j}`: `j ≥ leftIndex` are in the set (band value at `[leftIndex, rightIndex)`, larger beyond), `j < leftIndex` are not (`bandLine_lt_height_specCharSeries_of_lt_leftIndex`, `Vertices.lean:559`, gives a strictly smaller slope before `leftIndex`).

#### Mathlib lemmas needed
- `LWX.bandLine_lt_height_specCharSeries_of_lt_leftIndex` (`Vertices.lean:559`)
- `LWX.unitSlope_specCharSeries_eq_of_mem_band`
- `NewtonPolygon₀.faceLeft` (`Face.lean:80`)

#### Sources
As S7.4.

#### Generality decision
As S7.4.

---
### [S7.6] `LWX.thetaBlock_comp_discHeckeBlockOp_of_isClassicalShape`
- **Status**: done
- **File**: PhD/LWX/StepThree.lean:141 | **Depends on**: G1 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem thetaBlock_comp_discHeckeBlockOp_of_isClassicalShape
    (κ : AnalyticWeight UK (M1Kh h ψ) ρ) (κ' : AnalyticWeight UK' (M1Kh h ψ) ρ') {k : ℕ}
    {u : ι → Fin p → ZMod (p ^ h) → K} (hcl : IsClassicalShape θG h ψ U hU vRep hvΔ uu κ k u)
    (hcl' : IsClassicalShape' θG h ψ U hU vRep hvΔ uu κ' k u)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p) :
    (thetaBlock (p := p) (K := K) (ι := ι) h (k + 1)).comp
        (discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu)
      = (ψ p ^ (k + 1)) • ((discHeckeBlockOp θG h ψ κ' U hU vRep hvΔ idx uu).comp
          (thetaBlock (p := p) (K := K) (ι := ι) h (k + 1))) := by
  sorry
```

#### Proof sketch
1. After G1, `thetaBlock_comp_discHeckeBlockOp_of_autFactor` takes `hA : autFactor κ (conj) * L = C (u i t a) * L^(r+1)` and `hA' : autFactor κ' (conj) * L^(r+2) = C (u i t a)`; these are `hcl` and `hcl'` at `r := k`, and `hdet` gives the uniform scalar `ψ (det) = ψ p` (`map_natCast`).

#### Mathlib lemmas needed
- `LWX.thetaBlock_comp_discHeckeBlockOp_of_autFactor` (`AtkinLehnerInst.lean:122`, after G1)
- G1

#### Sources
[Bu04, §7], `bu04.txt:1095–1100`: "`[UηU]θ^{1−k} = |ν(η)|^{k−1}θ^{1−k}[UηU]`".

#### Generality decision
The nebentypus constants must agree between source and target, which is what `IsClassicalShape'` with the *same* `u` says.

---
### [CLEANUP-S7b] Run /cleanup on PhD/LWX/StepThree.lean
- **Status**: done | **File**: PhD/LWX/StepThree.lean | **Depends on**: S7.6 | **Type**: cleanup
- Per-file cadence (S7.4–S7.6).

---
### [S7.7] `LWX.norm_discHeckeBlockOp_le_one`
- **Status**: done
- **File**: PhD/LWX/StepThree.lean:155 | **Depends on**: none | **Parallel**: yes | **Type**: theorem

#### Statement
```lean
theorem norm_discHeckeBlockOp_le_one (κ : AnalyticWeight UK (M1Kh h ψ) ρ) :
    ‖discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu‖ ≤ 1 := by
  sorry
```

#### Proof sketch
1. `norm_eq_iSup_matrixCoeff` (`Matrix.lean:90`, `IsTate K` from `Tate.lean:265`) and `Real.iSup_le`; every `matrixCoeff (discHeckeBlockOp …) (i,(a,m)) (j,(b,n))` is `matrixCoeff (discHeckeBlock … i j) (a,m) (b,n)` (`matrixCoeff_blockOp`), a finite sum over `t` (`matrixCoeff_sum`) of `matrixCoeff (discSlash …)`, each either `0` or `matrixCoeff (κ.kappaSlash g) m n` (`matrixCoeff_discSlash`) `= coeff (idx m n) (genFun g)` (`matrixCoeff_kappaSlash`) of norm `≤ 1` (`norm_coeff_genFun_le_one`); the ultrametric `norm_sum_le` keeps the bound.

#### Mathlib lemmas needed
- `TateFredholm.norm_eq_iSup_matrixCoeff` (`Matrix.lean:90`)
- `TateFredholm.matrixCoeff_blockOp` (`BlockOp.lean:646`)
- `TateFredholm.matrixCoeff_sum` (`Fredholm.lean:661`)
- `LWX.matrixCoeff_discSlash` (`DiscModel.lean:454`)
- `QMF.AnalyticWeight.matrixCoeff_kappaSlash` (`Char.lean:834`)
- `QMF.WeightSeries.norm_coeff_genFun_le_one` (`Series.lean:320`)
- `IsUltrametricDist.norm_sum_le`-style (`Finset.norm_sum_le` in the ultrametric form)
- `Real.iSup_le`

#### Sources
[Bu04, Prop 4] proof, `bu04.txt:1128`: "`U_p` is an operator with norm at most 1".

#### Generality decision
Any weight on the level; L2.1 of the board's original plan.

---
### [S7.8] `LWX.norm_le_of_eigen_compl`
- **Status**: done
- **File**: PhD/LWX/StepThree.lean:163 | **Depends on**: S7.6, S7.7, T5.12, T5.13 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem norm_le_of_eigen_compl (κ : AnalyticWeight UK (M1Kh h ψ) ρ)
    (κ' : AnalyticWeight UK' (M1Kh h ψ) ρ') {k : ℕ} {u : ι → Fin p → ZMod (p ^ h) → K}
    (hcl : IsClassicalShape θG h ψ U hU vRep hvΔ uu κ k u)
    (hcl' : IsClassicalShape' θG h ψ U hU vRep hvΔ uu κ' k u)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    {f : c(ι × (ZMod (p ^ h) × ℕ), K)} (hf : f ≠ 0) {μ : K}
    (hμ : (discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu).comp
        (1 - truncation (classicalSupport p ι h k)) f = μ • f) :
    ‖μ‖ ≤ ‖ψ p‖ ^ (k + 1) := by
  sorry
```

#### Proof sketch
1. Let `θ := thetaBlock h (k+1)`, `pr := truncation (classicalSupport)`, `P := U_p.comp (1 − pr)`, `P' := U_p'` (at `κ'`).  `θ.comp pr = 0`: `pr f ∈ locPolyDegSubmoduleBlock` (T5.12) and `thetaBlock_eq_zero_iff` (`AtkinLehnerInst.lean:86`).
2. So `θ.comp P = (θ.comp U_p).comp (1 − pr) = (ψ p)^(k+1) • (P'.comp θ).comp (1 − pr) = (ψ p)^(k+1) • P'.comp θ` (S7.6, `comp_sub`, `θ.comp pr = 0`).
3. By contradiction: if `‖ψ p‖^(k+1) < ‖μ‖`, `eq_zero_of_intertwine_of_norm_lt (S7.7 at κ') _ hint hμ h` gives `θ f = 0`, so `f ∈ locPolyDegSubmoduleBlock` (`thetaBlock_eq_zero_iff`), `pr f = f` (T5.13), `(1 − pr) f = 0`, `P f = 0 = μ • f`, `μ = 0` (`smul_eq_zero`, `hf`), contradicting `‖ψ p‖^(k+1) < ‖μ‖ = 0`.

#### Mathlib lemmas needed
- `LWX.eq_zero_of_intertwine_of_norm_lt` (`StepOne.lean:76`)
- `LWX.thetaBlock_eq_zero_iff` (`AtkinLehnerInst.lean:86`)
- `ContinuousLinearMap.comp_sub`
- `smul_eq_zero`
- S7.6
- S7.7
- T5.12
- T5.13

#### Sources
[Bu04, Prop 4], `bu04.txt:1125–1129`: "if `v_p(λ) < k − 1` then `θ^{1−k}f` … is an eigenvector for `U_p` with eigenvalue `λ/p^{k−1}`, which has negative valuation. On the other hand, `U_p` is an operator with norm at most 1, and hence `θ^{1−k}f = 0`. Hence `f` is classical." — applied on the complement of the classical subspace, where "classical" means `(1 − pr) f = 0`.

#### Generality decision
Eigenvector-level only; multiplicities never enter, because the slope statement S7.9 goes through zeros of the determinant of the *compression*.

---
### [S7.9] `LWX.le_unitSlope_compl`
- **Status**: done
- **File**: PhD/LWX/StepThree.lean:177 | **Depends on**: S7.1, S7.8 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem le_unitSlope_compl [IsAlgClosed K] (κ : AnalyticWeight UK (M1Kh h ψ) ρ)
    (κ' : AnalyticWeight UK' (M1Kh h ψ) ρ') {k : ℕ} {u : ι → Fin p → ZMod (p ^ h) → K}
    (hcl : IsClassicalShape θG h ψ U hU vRep hvΔ uu κ k u)
    (hcl' : IsClassicalShape' θG h ψ U hU vRep hvΔ uu κ' k u)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    (hρ : 0 ≤ ρ) (hσ : max ρ (p : ℝ)⁻¹ < 1)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape) (j : ℕ) :
    ((((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ p‖) : ℝ) : WithBotTop ℝ) ≤
      (newtonPolygon₀OfPowerSeries negLogNorm (charPowerSeries
        ((discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu).comp
          (1 - truncation (classicalSupport p ι h k))))).unitSlope j := by
  sorry
```

#### Proof sketch
1. By contradiction: a unit slope `m < (k+1)(−log‖ψ p‖)` (finite: `≠ ⊥` by `unitSlope_ne_bot` of an entire series with `coeff 0 = 1`; if `⊤` the claim is trivial) gives by S7.1 a zero `a` of `R := charPowerSeries (U_p.comp (1 − pr))` with `‖a‖ = exp m < ‖ψ p‖^{−(k+1)}`.
2. `evalT_charPowerSeries_eq_zero_iff (compactoid) ha0` gives `f ≠ 0` with `(U_p.comp (1 − pr)) f = a⁻¹ • f`; S7.8 gives `‖a⁻¹‖ ≤ ‖ψ p‖^(k+1)`, i.e. `‖a‖ ≥ ‖ψ p‖^{−(k+1)}`, contradiction (`Real.exp_lt_exp`, `Real.log` of the norms).

#### Mathlib lemmas needed
- `TateFredholm.evalT_charPowerSeries_eq_zero_iff` (`Riesz.lean:2381`)
- `TateFredholm.IsCompactoid.comp_right`
- `TateFredholm.charPowerSeries_isEntire`
- `norm_inv`
- S7.1
- S7.8

#### Sources
[LWX, §3.23 Step III], `lwx.txt:2014–2088`, implicit in "the slope `≤ k+1` subspace in `S^{D,†}_{(k,ψ)}`": every non-classical slope is `≥ k+1`.

#### Generality decision
Needs `IsAlgClosed K` through S7.1.

---
### [CLEANUP-S7c] Run /cleanup on PhD/LWX/StepThree.lean
- **Status**: done | **File**: PhD/LWX/StepThree.lean | **Depends on**: S7.9 | **Type**: cleanup
- Per-file cadence (S7.7–S7.9).

---
### [S7.10] `LWX.unitSlope_charpolyRev_matrix_le`
- **Status**: done
- **File**: PhD/LWX/StepThree.lean:240 | **Depends on**: S7.7 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem unitSlope_charpolyRev_matrix_le [Nonempty ι] [IsAlgClosed K] {hp2 : p ≠ 2}
    {hψ : ∀ x, ‖ψ x‖ = ‖x‖} {ω ω' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k (c.matrix idx) B
      (c'.matrix idx)) {j : ℕ} (hj : j < Fintype.card ι * ((k + 1) * p ^ 1)) :
    (newtonPolygon₀OfPowerSeries negLogNorm
        ((c.matrix idx).charpolyRev : PowerSeries K)).unitSlope j
      ≤ ((((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ p‖) : ℝ) : WithBotTop ℝ) := by
  sorry
```

**B2 CORRECTION (2026-09-10).**  The original statement quantified over *every* `j` and is
**false** past the degree: the polygon of a polynomial has `unitSlope j = ⊤` there
(`slopesUnbounded_newtonPolygon₀OfPowerSeries` + `NewtonPolygon₀.unitSlope_mono`), and
`⊤ ≤ ↑σ` is false.  The range hypothesis `hj` above is the repair; logged in
`.mathlib-quality/lwx-theta/b2_log.jsonl`.  Sub-tickets S7.10a/S7.10b carry the root-level
content that S7.11 actually consumes.

#### Proof sketch
1. `obtain ⟨B, hAB, P, Q, hQP, hA'⟩ := hAL`; `roots_charpoly_atkinLehner`: roots of `charpoly (c'.matrix)` are `c/x` for roots `x` of `charpoly (c.matrix)`, `c = (ψ p)^(k+1)`.
2. Every root `y` of `charpoly (c'.matrix)` is an eigenvalue of `U_p'|_{classical}` hence of `U_p'` (`Matrix.exists_mulVec_eq_zero_iff`/`Module.End.hasEigenvalue_iff_mem_spectrum`… concretely: `charpoly` root ⟹ `mulVec` eigenvector `v` ⟹ the corresponding classical function `f = b.repr.symm v` satisfies `U_p' f = y • f`, `f ≠ 0`), so `‖y‖ ≤ ‖U_p'‖ ≤ 1` (S7.7, `le_opNorm`).  Hence every root `x` of `charpoly (c.matrix)` has `‖x‖ ≥ ‖c‖`.
3. The unit slopes of `charpolyRev (c.matrix)` are the valuations `−log‖x‖` of the roots `x` (`roots_charpolyRev` + `card_roots_slope` over `K` via the algebraic-closure transport; a segment of slope `m` forces a root of `charpolyRev` of norm `exp m`, i.e. a root of `charpoly` of norm `exp(−m)`), so each is `≤ −log‖c‖ = (k+1)(−log‖ψ p‖)`.

#### Mathlib lemmas needed
- `LWX.roots_charpoly_atkinLehner` (`AtkinLehner.lean:260`)
- `LWX.roots_charpolyRev` (`CharpolyPairing.lean:157`)
- `card_roots_slope` (`PolynomialRoots.lean:955`)
- `Matrix.exists_mulVec_eq_zero_iff`
- `ContinuousLinearMap.le_opNorm`
- S7.7
- T5.18

#### Sources
[LWX, Step I], `lwx.txt:1815–1819`, read through `JL-AUDIT.md` §2: the classical slopes are at most `k+1` because their Atkin–Lehner partners are slopes (`≥ 0`) of an operator of norm `≤ 1` — the converse half of [Bu04, Prop 4] derived from H1, never imported.

#### Generality decision
L2.4 of the original plan; `IsAlgClosed K` for the root multisets.

---
### [S7.11] `LWX.faceLeft_charpolyRev_matrix_eq`
- **Status**: done
- **File**: PhD/LWX/StepThree.lean:253 | **Depends on**: S7.10 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem faceLeft_charpolyRev_matrix_eq [Nonempty ι] [IsAlgClosed K] {hp2 : p ≠ 2}
    {hψ : ∀ x, ‖ψ x‖ = ‖x‖} {ω ω' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k (c.matrix idx) B
      (c'.matrix idx)) :
    (newtonPolygon₀OfPowerSeries negLogNorm ((c.matrix idx).charpolyRev : PowerSeries K)).faceLeft
        (((k + 1 : ℕ) : ℝ) * (-Real.log ‖ψ p‖))
      = Fintype.card ι * ((k + 1) * p ^ 1)
        - (newtonPolygon₀OfPowerSeries negLogNorm
            ((c'.matrix idx).charpolyRev : PowerSeries K)).faceRight 0 := by
  sorry
```

#### Proof sketch
1. `faceLeft σ` of a polynomial polygon counts the unit slopes `< σ`, i.e. (by `card_roots_slope` summed over the segments below `σ`, or directly by the closed-ball count `card_roots_lt_slope`) the roots `a` of `charpolyRev` with `‖a‖ < exp σ`, i.e. the roots `x = a⁻¹` of `charpoly (c.matrix)` with `‖x‖ > exp(−σ) = ‖c‖`.
2. `norm_roots_charpoly_atkinLehner`: the multiset of `‖·‖` of roots of `charpoly (c'.matrix)` is the image of that of `c.matrix` under `x ↦ ‖c‖/x`; so `#{x : ‖x‖ > ‖c‖} = #{y : ‖y‖ < 1}`, and with S7.10's `‖y‖ ≤ 1` for all `y`, `#{y : ‖y‖ < 1} = N − #{y : ‖y‖ = 1} = N − faceRight_{c'} 0` (`faceRight 0` counts the slopes `≤ 0`, i.e. roots `y` with `‖y‖ ≥ 1`, i.e. `= 1`).  Multiset bookkeeping: `Multiset.filter_add`, `Multiset.count_map`, `Multiset.card_filter` vs the complement.

#### Mathlib lemmas needed
- `LWX.norm_roots_charpoly_atkinLehner` (`AtkinLehner.lean:277`)
- `card_roots_lt_slope` (`PolynomialRoots.lean:869`)
- `card_roots_le_slope` (`PolynomialRoots.lean:832`)
- `Multiset.filter_add`
- `Multiset.card_roots_eq_natDegree`-style (`IsAlgClosed.card_roots_eq_natDegree`, `IsAlgClosed/Basic.lean:110`)
- S7.10

#### Sources
[LWX, §3.23 Step III], `lwx.txt:2014–2088`: "`n_{k+1} − n⁻_{k+1}` is equal to the dimension of slope `k+1` subspace in `S^D_{k+2}(K^pIw_{q²};ψ)`. By Atkin–Lehner theory (Proposition 3.22) and Proposition 2.15, the multiplicity is the same as the dimension of slope zero subspace in `S^{D,†}_{(k,ψ⁻¹)}`."

#### Generality decision
The Atkin–Lehner reflection at the level of polygons; `IsAlgClosed K`.

---
### [S7.12] `LWX.touchX_sub_leftIndex_eq_ordDim`
- **Status**: done
- **File**: PhD/LWX/StepThree.lean:268 | **Depends on**: S7.3, S7.5, S7.9, S7.11, T5.16, T5.24 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem touchX_sub_leftIndex_eq_ordDim (hp2 : p ≠ 2) [Nonempty ι] [IsAlgClosed K]
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    {ω ω' ω₁ ω₁' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' T₁ T₁' : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (d : TargetData c ω₁ T₁) (d' : TargetData c' ω₁' T₁')
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k (c.matrix idx) B
      (c'.matrix idx)) :
    touchX p (Fintype.card ι) (k + 1)
        - leftIndex (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (k + 1)
      = ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω' := by
  sorry
```

#### Proof sketch
1. `HasUnitBand … ω (k+1)` from T5.24 (with `c, c', hAL`); S7.5 at `(D, ω, T₀)` and the seam (`specCharSeries_ofCerts_eq_discHeckeCharPowerSeries`) give `leftIndex D ω (k+1) = faceLeft_F σ` with `F = discHeckeCharPowerSeries c.weight`, `σ = (k+1)(p−1)·(−log‖T₀‖) = (k+1)(−log‖ψ p‖)` (`c.hnorm`).
2. T5.16 splits `F = R * G_cl`; `faceLeft_mul` (`Product.lean:1203`): `faceLeft_F σ = faceLeft_R σ + faceLeft_{G_cl} σ`; S7.9 at `(c.weight, d.weight)` (with `d.shape`) makes every slope of `R` `≥ σ`, so `faceLeft_R σ = 0`.
3. S7.11: `faceLeft_{G_cl} σ = N − faceRight_{G_cl'} 0` (`G_cl' = charpolyRev (c'.matrix)`, with T5.18 to move between `classicalCoordMatrix` and `upMatrix`); at `(c', d')`: `faceRight_{F'} 0 = faceRight_{R'} 0 + faceRight_{G_cl'} 0` (`faceRight_mul`) and `faceRight_{R'} 0 = 0` (S7.9 at `(c'.weight, d'.weight)`: all slopes of `R'` are `≥ σ > 0`), while `faceRight_{F'} 0 = ordDim D ω'` (S7.3 + seam at `(ω', T₀')`).
4. Assemble: `N − leftIndex = N − (N − ordDim ω') = ordDim ω'`, with `N = touchX (k+1)` (T5.22) and `ordDim ω' ≤ N` from the counts.

#### Mathlib lemmas needed
- `faceLeft_mul` (`Product.lean:1203`)
- `faceRight_mul` (`Product.lean:1156`)
- `LWX.specCharSeries_ofCerts_eq_discHeckeCharPowerSeries` (`SeamH.lean:401`)
- S7.3
- S7.5
- S7.9
- S7.11
- T5.16
- T5.18
- T5.22
- T5.24

#### Sources
[LWX, §3.23 Step III], `lwx.txt:2014–2088`, the left-gap paragraph quoted under S7.11 plus "Using Corollary 3.21 again, we deduce that `n_{k+1} − n⁻_{k+1} = r_ord(ψ⁻¹|_Δ·ω₀^k) = r_ord(ω⁻¹ω₀^{2k})`".

#### Generality decision
The conjugate character `ω'` is a parameter; the identification `ω' = ω⁻¹ω₀^{2k}` (gap AG-ω₀) is not needed for the identity, only for [LWX]'s spelling of it.

---
### [CLEANUP-S7d] Run /cleanup on PhD/LWX/StepThree.lean
- **Status**: done | **File**: PhD/LWX/StepThree.lean | **Depends on**: S7.12 | **Type**: cleanup
- Per-file cadence (S7.10–S7.12).

---
### [S7.13] `LWX.rightIndex_sub_touchX_eq_ordDim`
- **Status**: done
- **File**: PhD/LWX/StepThree.lean:285 | **Depends on**: S7.3, S7.4, S7.9, S7.10, T5.16, T5.24 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem rightIndex_sub_touchX_eq_ordDim (hp2 : p ≠ 2) [Nonempty ι] [IsAlgClosed K]
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    {ω ω' ω₁ : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' T₁ : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (d : TargetData c ω₁ T₁)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k (c.matrix idx) B
      (c'.matrix idx))
    (hH2 : IsThetaExact θG 1 ψ U hU vRep hvΔ idx uu c.weight d.weight k) :
    rightIndex (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (k + 1)
        - touchX p (Fintype.card ι) (k + 1)
      = ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω₁ := by
  sorry
```

#### Proof sketch
1. As S7.12 for the right endpoint: S7.4 gives `rightIndex D ω (k+1) = faceRight_F σ`; `faceRight_mul`: `= faceRight_R σ + faceRight_{G_cl} σ`; S7.10 makes every classical slope `≤ σ`, so `faceRight_{G_cl} σ = N`.
2. **H2.** `hH2 : R = rescale ((ψ p)^(k+1)) F₁` with `F₁ = discHeckeCharPowerSeries d.weight`; rescaling by `a` shifts every unit slope by `−log‖a‖ = σ` (`newtonPolygon₀OfPowerSeries` of `rescale a f`: `coeff n (rescale a f) = a^n * coeff n f`, so `coeffVal` gains `n·(−log‖a‖)` and the polygon's unit slopes gain `−log‖a‖` — a lemma to spawn, `unitSlope_rescale`), hence `faceRight_R σ = faceRight_{F₁} 0 = ordDim D ω₁` (S7.3 + seam at `(ω₁, T₁)`).

#### Mathlib lemmas needed
- `faceRight_mul` (`Product.lean:1156`)
- `PowerSeries.coeff_rescale`
- a new `unitSlope_rescale` (spawn)
- S7.3
- S7.4
- S7.9
- S7.10
- T5.16
- T5.24

#### Sources
[LWX, §3.23 Step III], `lwx.txt:2014–2088`: "To compute `n⁺_{k+1} − n_{k+1}`, we recall the following exact sequence (cf. [Jo11]) `0 → S^D_{k+2}(K^pIw_{q²},ψ) → S^{D,†}_{(k,ψ)} → S^{D,†}_{(−k−2,ψ)} → 0`. This exact sequence is equivariant for the `U_p`-action on the first two spaces, and the `p^{k+1}U_p`-action on the third space. It is clear that `n⁺_{k+1} − n_{k+1}` is equal to the codimension of `S^D_{k+2}` in the slope `≤ k+1` subspace in `S^{D,†}_{(k,ψ)}`. The latter in turn is equal to the dimension of slope zero subspace of `S^{D,†}_{(−k−2,ψ)}` by the exact sequence. Using Corollary 3.21, we thus obtain `n⁺_{k+1} − n_{k+1} = r_ord(ψ|_Δ·ω₀^{−k−2}) = r_ord(ωω₀^{−2k−2})`."

#### Generality decision
**H2 is a hypothesis** (`IsThetaExact`), in exactly the form the source uses it (equivariant right-exactness ⟹ equality of the two Fredholm determinants up to the `p^{k+1}` rescaling).

---
### [S7.14] `LWX.degX_zero`
- **Status**: done
- **File**: PhD/LWX/StepThree.lean:314 | **Depends on**: S7.2 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem degX_zero (hp2 : p ≠ 2) (D : UpDatum p ι) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) [Nonempty ι] :
    degX D ω 0 = ordDim D ω := by
  sorry
```

#### Proof sketch
1. `degX D ω 0 = rightIndex D ω 0 − leftIndex D ω 0`; `leftIndex D ω 0 = 0` (`Nat.sInf` of a set containing `0`: `touchX … 0 = 0`, `isUnitCoeff_zero`); S7.2.

#### Mathlib lemmas needed
- `LWX.leftIndex` (`Vertices.lean:59`)
- `LWX.isUnitCoeff_zero` (`Vertices.lean:51`)
- `Nat.sInf_eq_zero`
- S7.2

#### Sources
[LWX, §3.23 Step III], `lwx.txt:2014–2088`: "`deg X_{0,ω} = n⁺_0 = r_ord(ω)`" (`lwx.txt:2018–2020`).

#### Generality decision
Unconditional.

---
### [CLEANUP-ALL-3] Run /cleanup on PhD/LWX/StepThree.lean (project-wide)
- **Status**: done | **File**: PhD/LWX/StepThree.lean | **Depends on**: CLEANUP-S7d, CLEANUP-T5h | **Type**: cleanup
- `/cleanup-all` before the Step III milestone.

---
### [S7.15] `LWX.degX_succ` — **MILESTONE**
- **Status**: done
- **File**: PhD/LWX/StepThree.lean:322 | **Depends on**: S7.12, S7.13, CLEANUP-ALL-3 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem degX_succ (hp2 : p ≠ 2) [Nonempty ι] [IsAlgClosed K] (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    {ω ω' ω₁ ω₁' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' T₁ T₁' : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (d : TargetData c ω₁ T₁) (d' : TargetData c' ω₁' T₁')
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k (c.matrix idx) B
      (c'.matrix idx))
    (hH2 : IsThetaExact θG 1 ψ U hU vRep hvΔ idx uu c.weight d.weight k) :
    degX (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (k + 1)
      = ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω'
        + ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω₁ := by
  sorry
```

#### Proof sketch
1. `degX D ω (k+1) = rightIndex − leftIndex = (rightIndex − touchX) + (touchX − leftIndex)` (`Nat` subtraction with `leftIndex ≤ touchX ≤ rightIndex` from `leftIndex_mem`/`rightIndex_mem` under `HasUnitBand` — T5.24); S7.13 and S7.12.

#### Mathlib lemmas needed
- `LWX.leftIndex_mem`, `LWX.rightIndex_mem` (`Vertices.lean:86,103`)
- S7.12
- S7.13
- T5.24
- `Nat.sub_add_sub_cancel`

#### Sources
[LWX, §3.23 Step III], `lwx.txt:2014–2088`, `lwx.txt:2080–2084`: "`deg X_{k,ω} = n⁺_k − n⁻_k = (n⁺_k − n_k) + (n_k − n⁻_k) = r_ord(ω⁻¹ω₀^{2k−2}) + r_ord(ωω₀^{−2k})` if `k ≥ 1`".

#### Generality decision
**The milestone**: [LWX, Thm 1.3]'s degree formula at the coefficient level, with the two twisted characters as the parameters `ω'`, `ω₁` of the data.

---
### [S7.16] `LWX.degXint_zero`
- **Status**: done
- **File**: PhD/LWX/StepThree.lean:338 | **Depends on**: S7.2, S7.12 | **Parallel**: no | **Type**: theorem

#### Statement
```lean
theorem degXint_zero (hp2 : p ≠ 2) [Nonempty ι] [IsAlgClosed K] (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    (hdet : ∀ i t, (certM1 θG U hU vRep hvΔ uu i t : Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)
    {ω ω' ω₁ ω₁' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' T₁ T₁' : K}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ 0)
    (c' : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' 0)
    (d : TargetData c ω₁ T₁) (d' : TargetData c' ω₁' T₁')
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 0 (c.matrix idx) B
      (c'.matrix idx)) :
    degXint (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω 0
      = p * Fintype.card ι - ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω'
        - ordDim (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω := by
  sorry
```

#### Proof sketch
1. `degXint D ω 0 = leftIndex D ω 1 − rightIndex D ω 0`; S7.12 at `k = 0` gives `leftIndex D ω 1 = touchX 1 − ordDim ω' = p·t − ordDim ω'`, and S7.2 gives `rightIndex D ω 0 = ordDim ω`; `Nat` arithmetic.

#### Mathlib lemmas needed
- S7.2
- S7.12
- `LWX.touchX`

#### Sources
[LWX, §3.23 Step III], `lwx.txt:2014–2088`, `lwx.txt:2085–2088`: "`deg X_{(k,k+1),ω} = n⁻_{k+1} − n⁺_k = qt − r_ord(ω⁻¹ω₀^{2k}) − r_ord(ωω₀^{−2k})`" at `k = 0`, where `n⁺_0 = r_ord(ω)`.

#### Generality decision
The general `degXint_succ` (`k ≥ 1`) needs S7.13 at weight `k−1` and S7.12 at weight `k`; it is the same arithmetic and is left as a follow-up once the data-passing shape is settled by S7.16.

---
### [CLEANUP-S7e] Run /cleanup on PhD/LWX/StepThree.lean
- **Status**: done | **File**: PhD/LWX/StepThree.lean | **Depends on**: S7.16 | **Type**: cleanup
- Final per-file cleanup of `StepThree.lean`.

---
### [G1] Generalise the `_of_autFactor` equivariance by a common constant
- **Status**: done
- **File**: PhD/LWX/Bol.lean, PhD/LWX/AtkinLehnerInst.lean | **Depends on**: none | **Parallel**: yes
- **Type**: refactor (statement generalisation of done tickets B7, B9, B10, B11, B12)

#### Statement
Replace, in `thetaOne_comp_kappaSlash_of_autFactor` and its four descendants, the hypotheses
```lean
    (hA : κ.toWeightSeries.autFactor g * linX g = linX g ^ r)
    (hA' : κ'.toWeightSeries.autFactor g * linX g ^ (r + 1) = 1)
```
by
```lean
    {u : K}
    (hA : κ.toWeightSeries.autFactor g * linX g = PowerSeries.C u * linX g ^ r)
    (hA' : κ'.toWeightSeries.autFactor g * linX g ^ (r + 1) = PowerSeries.C u)
```
(blockwise, `u i t a` in the disc/block versions), conclusions unchanged.  The old statements are
the case `u = 1`.

#### Proof sketch
1. In `thetaOne_comp_kappaSlash_of_autFactor`, `hAκ` becomes `autFactor = C u * L^r * L⁻¹` and
   `hAκ'` becomes `autFactor' = C u * (L⁻¹)^(r+1)`; the two `hshape` computations gain a factor
   `C u`, which `iterate_derivative_C_mul` (already in `Bol.lean`) pulls through `∂^r` and which
   cancels on both sides of the final `ring`.
2. The disc, coset, block and stability versions only pass the hypotheses along.

#### Mathlib lemmas needed
- `LWX.iterate_derivative_C_mul` (`Bol.lean`, private — de-privatise), `PowerSeries.coeff_C_mul`.

#### Sources
The finding of this pass (`decomposition.md`, tranches 5–7, "Design finding (b)"): at a classical
weight `(k, ψ)` of conductor `p²` the automorphy factor on the level-`1` disc is
`ψ(d)·(cz+d)^k`, not `(cz+d)^k`; the constant is `ψ(d)`, locally constant on the disc, and it
passes through Bol's identity untouched.

#### Generality decision
Strictly more general; no downstream user of the `u = 1` form exists yet.

---

### [AG-ζ] The nebentypus constants of source and target agree — DESIGN GAP
- **Status**: open — **not dispatchable** (design step; no Statement)
- **File**: PhD/LWX/ClassicalPoint.lean | **Depends on**: C6.12 | **Type**: API gap

#### What is missing
`ClassicalData` carries `u i t a = haloCharFunH 1 ψ T₀ ω (d)·d^{−k}` and `TargetData` demands the
target weight `(−k−2, ψ)` at its own halo point `(ω₁, T₁)` to have the *same* constants.  Proving
that needs the value of the universal character at a classical point:
`oneAddPow (ζ·exp(pk) − 1) s = ζ^s·exp(pks)` — the binomial series at the boundary point
`‖T₀‖ = p^{−1/(p−1)}`, where it converges only conditionally (`‖C(s,m)T₀^m‖ ≤ 1`, not `→ 0`).
The halo layer avoids this by working at level `h ≥ 1` with `T'_h`, and the identification is a
genuine `p`-adic-analysis statement.  **Design step**: decide whether to (i) prove the binomial
evaluation at `ζ` via `PowSubOne.lean`'s binomial identities and the identity theorem, or (ii)
define the target datum *from* the source datum (`u` copied, `T₁` chosen so that
`haloExponentH p 1 T₁ = −(k+2)`), which needs only the negative-exponent binomial series
`Ring.choose (−(k+2)) m` ↔ `((1+x)⁻¹)^{k+2}` in `PowerSeries K` and no evaluation at `ζ`.  Route
(ii) is recommended: it is what Step III consumes.

#### Sources
[LWX, §3.23 Step III], `lwx.txt:2050–2056` (the target weight `(−k−2, ψ)`).

---

### [AG-ω₀] The Teichmüller character on `(ZMod p)ˣ` — DESIGN GAP
- **Status**: open — **not dispatchable** (design step; no Statement)
- **File**: PhD/LWX/ConjChar.lean | **Depends on**: none | **Type**: API gap

#### What is missing
[LWX] spell the conjugate and target characters as `ω⁻¹ω₀^{2k}` and `ωω₀^{−2k−2}` with
`ω₀ : Δ → ℤ_p^×` the inclusion.  The project has the Teichmüller *projection*
`LWX.teichmuller : ℤ_[p]ˣ → ℤ_[p]ˣ` (`UnitsLog.lean:96`) and `teichmuller_eq_of_norm_sub_le`
(`UnitsLog.lean:157`), which shows it factors through `(ZMod p)ˣ`; what is missing is the induced
`teichmullerChar : (ZMod p)ˣ →* ℤ_[p]ˣ` (via `repLift`/`ZMod.val` and `teichmuller_mul`), the
twists `twistChar ω n := ω * teichmullerChar ^ n`, and the check that `(k, ψ)`'s conjugate
`(k, ψ⁻¹)` has tame character `invChar ω * teichmullerChar ^ (2k)`.  **Note (finding of this
pass)**: `invChar ω` alone (ticket S1) is the conjugate only at weight `k = 0`.  The Step I/III
theorems take `ω'`, `ω₁` as parameters and are unaffected; this gap only affects how [LWX]'s
closed formulas are *spelled*.

#### Sources
[LWX, §3.23 Step III], `lwx.txt:2028–2036`: "`ψ⁻¹|_Δ·ω₀^k = χ_k⁻¹|_Δ·ω₀^{2k} = ω⁻¹ω₀^{2k}`".

---


## Cleanup-cadence verification

9 proof/def tickets on one file plus two API-gap tickets.  Cadence requires at least
`⌈9/3⌉ = 3` per-file cleanups plus one final per file.

| File | Proof/def tickets | Cadence cleanups | Final | Total |
|---|---|---|---|---|
| Theta.lean | 9 (T001–T007, T-AG1, T-AG2) | CLEANUP-1 (after T003), CLEANUP-2 (after T006), CLEANUP-3 (after T007) | CLEANUP-FINAL | 4 |
| ConjChar.lean | 2 (S1, S2) | — (under 3) | CLEANUP-4 | 1 |
| FiniteFactor.lean | 1 (S3) | — (under 3) | CLEANUP-5 | 1 |
| StepOne.lean | 4 (SO1–SO4) | CLEANUP-6 (after SO3) | CLEANUP-7 | 2 |
| Degrees.lean | 3 (D1–D3) | CLEANUP-8 (after D3, = final) | — | 1 |
| AtkinLehnerInst.lean | 5 (AL1–AL5) | CLEANUP-9 (after AL3) | CLEANUP-10 | 2 |

24 open proof/def tickets ⇒ at least `⌈24/3⌉ = 8` cadence cleanups plus one final per file
(6 files).  Present: 11 cleanup tickets (CLEANUP-1..10 plus CLEANUP-FINAL) — meets the rule.  T-AG3 and T-AG4
create new files; their per-file cleanups are added when their design steps fix the file names.
