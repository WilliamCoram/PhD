# Ticket Board — slopes-hecke (`.mathlib-quality/slopes-hecke/`)

**BOARD PATH: `.mathlib-quality/slopes-hecke/`.**  Workers: `/beastmode` with this path.
**Status: AWAITING USER VERDICT (2026-08-20).**  Four independent groups: **A** slopes, **B**
Hecke algebra, **C** level dictionary, **D** compact open levels (= forms-riesz T009, undeferred).

Governing principles (inherited): no duplicate code; deletions/renames → `.mathlib-quality/renames.jsonl`;
`lia` → `omega`; never touch `PhD/PR'd/`.  Skeleton (18 sorries) builds:
`lake build PhD.TateFredholm.Slopes PhD.QMF.Weight.Slopes PhD.QMF.Weight.HeckeAlgebra
PhD.QMF.Weight.AdicLevel PhD.QMF.Level`.

## Summary
- Total: 16 proof/def/refactor tickets + 7 cleanup = 23
- Open: 23 | In Progress: 0 | Done: 0
- Parallel capacity at start: 5 (A0 ∥ A1 ∥ B1 ∥ C1 ∥ D1)
- Milestones: **A5** (Newton polygon of `det(1 − T·[UηU])` lies above, general weight),
  **B4** (system of eigenvalues on the finite-slope subspace).

## Dependency fronts
```
A0 (move ofSlopes) ──────────────────────────────────────────────► A5
A1 (TateFredholm/Slopes) ─► A2 (fork instances) ─► CLEANUP-1
A1 ─► A3 (row decay of the blocks) ─► A4 (charCoeff bound) ─► CLEANUP-2 ─► A5 (MILESTONE) ─► CLEANUP-3
B1 (comm criterion) ; B2 (mapsTo_ker) ; B3 (common eigenvector) ─► CLEANUP-4 ─► B4 (MILESTONE) ─► CLEANUP-5
C1 ─► C2 ─► C3 ─► CLEANUP-6 ─► C4 (fork dedup)
D1 ─► D2 ─► D3 (fork U0/U₁(9)) ─► CLEANUP-7
all ─► CLEANUP-FINAL
```

---

## Group A — slopes at a general weight

### [A0] Move `NewtonPolygon₀.ofSlopes` and its API out of the fork
- **Status**: done (2026-08-20, slopes-hecke beastmode) |
- **Progress**: DONE — new `PhD/NewtonPolygons/OfSlopes.lean` (root namespace + `namespace
  NewtonPolygon₀`), holding `ofSlopes` and its simp API, the two junk-value `private` lemmas, and
  the four general spec lemmas that had been sitting inside `namespace JacobsSlash`.  Statements
  unchanged; `4_SlopeReading.lean` imports it and keeps only the two Jacobs cases plus the
  `C(m,2)` / `m²/2` arithmetic.  No external call sites needed fixing (only a docstring mention in
  `1_SlopeTheorem.lean`, still accurate).  Builds through `10_Eigenforms`; linter zero on the new
  file; 4 theorems on standard axioms. **Files**: NEW PhD/NewtonPolygons/OfSlopes.lean, PhD/JacobsSlash/4_SlopeReading.lean | **Depends on**: none | **Parallel**: yes | **Type**: refactor
#### Statement
Move the `namespace NewtonPolygon₀` section of `4_SlopeReading.lean` (`ofSlopes`,
`ofSlopes_starting_point`, `heightFun_ofSlopes`, `height_ofSlopes`, `unitSlope_ofSlopes`,
`isNewtonPolygonOf_ofSlopes`, `unitSlope_newtonPolygon₀OfSeq_ofSlopes`, `height_newtonPolygon₀OfSeq_ofSlopes`
— i.e. everything before `namespace JacobsSlash`) verbatim into `PhD/NewtonPolygons/OfSlopes.lean`;
`4_SlopeReading.lean` imports it.  No statement changes.
#### Proof sketch
1. `sed`-move the block; add the file header (module docstring naming [Kob84, Ch. IV §3] and the
   blueprint Definition 1, as the fork's header does).
2. `import PhD.NewtonPolygons.OfSlopes` in `4_SlopeReading.lean`; rebuild `PhD.JacobsSlash.U3.«9_EigenvaluesU3»`.
3. renames.jsonl (file move); `PhD/NewtonPolygons/` header table if one exists.
#### Mathlib lemmas needed — none (pure move).
#### Sources — [Jac03, proof of Thm 2.12 pp. 34–35]; [Kob84, Ch. IV §3].
#### Generality decision — unchanged (already `Γ = ℝ`, weight-free).

### [A1] `TateFredholm/Slopes.lean`: the weighted slope bound
- **Status**: done (2026-08-20, slopes-hecke beastmode) |
- **Progress**: DONE — all five sorries filled, 0 sorries, standard axioms, linter zero.
  Two deliberate deviations from the skeleton, both strict generalisations:
  (i) `norm_det_le_pow_of_row_bound` is stated for an arbitrary `[Fintype n] [DecidableEq n]`
  index rather than `Fin n` — this makes `norm_minor_le_pow_sum` a two-line consequence
  (`Finset.sum_coe_sort`) instead of needing an order-iso transport, and the fork's `Fin n` use
  is a special case; (ii) the unused `hσ1 : σ ≤ 1` was dropped from both (the Hadamard bound
  never needs it — only `norm_charCoeff_le_pow` does, where it is `σ < 1`).
  `sum_div_le_sum_block` was proved by the "peel the largest second coordinate" induction:
  `S ⊆ ι × {0,…,M.2}` gives `n ≤ |ι|(M.2+1)`, hence `⌊(n−1)/|ι|⌋ ≤ M.2`.
  `choose_two_lt_sum_of_ne_range` (the strict half) was moved here from the fork too, so the
  `{0,…,n−1}`-minimality induction is not duplicated. **File**: PhD/TateFredholm/Slopes.lean | **Depends on**: none | **Parallel**: yes | **Type**: theorems (5 sorries)
#### Statement — in the skeleton: `norm_det_le_pow_of_row_bound`, `norm_minor_le_pow_sum`,
`norm_charCoeff_le_pow`, `choose_two_le_sum`, `sum_div_le_sum_block` (+ the two corollaries,
already proved from them).
#### Proof sketch
1. `norm_det_le_pow_of_row_bound`: `rw [Matrix.det_apply]`;
   `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)`; per permutation,
   `‖sign σ • ∏ i, A (σ i) i‖ = ‖∏ …‖` (`Int.units_eq_one_or`), `norm_prod`, then
   `Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hA _ _)` and
   `Finset.prod_pow_eq_pow_sum`-style regrouping (`← Finset.prod_pow_eq_pow_sum` or
   `Finset.prod_congr` + `pow_sum`); the permutation reindexes `∑ w` (`Equiv.Perm.sum_comp`).
   Template: fork `norm_det_le_of_row_bound` (`1_SlopeTheorem.lean:67`).
2. `norm_minor_le_pow_sum`: `Matrix.det_submatrix_equiv_self` along `S.orderIsoOfFin`, then step 1
   with `w ∘ e`; `Equiv.sum_comp` for the exponent.  Template: fork's private
   `norm_minor_le_pow_sum` (`:223`).
3. `choose_two_le_sum`: the fork's `sum_range_le_sum_and_eq` (`:97`) gives
   `∑_{i<n} i ≤ ∑_{i∈S} i`; `Finset.sum_range_id` rewrites the left side as `n.choose 2`
   (`Nat.choose_two_right`/`Gauss` — check the exact name with `lean_loogle`).
4. `sum_div_le_sum_block`: induct on `n` via a "peel the minimal element" argument, or: the map
   `S → ℕ, p ↦ p.2` has fibres of size `≤ |ι|`, so `#{p ∈ S | p.2 < m} ≤ |ι| · m`; hence the
   `k`-th smallest second coordinate is `≥ ⌊k/|ι|⌋`, and summing gives the claim.  Use
   `Finset.sum_le_sum_of_injOn`-style comparison against `range n` ordered by `p.2`.
5. `norm_charCoeff_le_pow`: `charCoeff`, `norm_mul`, `norm_pow`, `norm_neg`, `norm_one`;
   `norm_tsum_le_iSup (tendsto_minor_cofinite u hu n)` (the shape used at `Fredholm.lean:242`),
   then `Real.iSup_le` with step 2 + `hf` + `pow_le_pow_of_le_one hσ0 hσ1.le`.
#### Mathlib lemmas needed
`Matrix.det_apply`, `Matrix.det_submatrix_equiv_self`, `Finset.orderIsoOfFin`, `Equiv.sum_comp`,
`Finset.prod_le_prod`, `Finset.prod_pow_eq_pow_sum`, `Finset.sum_range_id`, `Nat.choose_two_right`,
`pow_le_pow_of_le_one`, `Real.iSup_le`; project `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`,
`norm_tsum_le_iSup`, `tendsto_minor_cofinite`, `summable_minor`, `minor`, `charCoeff`.
#### Sources — [Ser62, §5]; [Jac03, Thm 2.12 pp. 34–35] (the fork's `‖3‖`-pinned proofs are the template).
#### Generality decision — arbitrary index type `I` with a row weight `w : I → ℕ` and an arbitrary
lower bound `f`; the `ℕ`/`ι × ℕ` cases are corollaries (the block model forces this).

### [A2] The fork's `1_SlopeTheorem` statements as instances of A1
- **Status**: done (2026-08-20, slopes-hecke beastmode) |
- **Progress**: DONE — deleted `norm_det_le_of_row_bound`, `norm_minor_le_pow_sum`,
  `sum_range_le_sum_and_eq`, `choose_two_lt_sum_of_ne_range` from the fork; `1_SlopeTheorem.lean`
  now imports `PhD.TateFredholm.Slopes` and `norm_charCoeff_of_unit_minors` calls
  `norm_minor_le_pow_sum (norm_nonneg _) (fun j => j) hdiv _`.  The equality statement and the
  dominant-block argument are unchanged.  Builds through `10_Eigenforms`; linter zero; 0 sorries.
  renames.jsonl: 3 entries. **File**: PhD/JacobsSlash/1_SlopeTheorem.lean | **Depends on**: A1 | **Parallel**: no | **Type**: refactor
#### Statement
Replace the private `norm_det_le_of_row_bound`, `norm_minor_le_pow_sum` by
`TateFredholm.norm_det_le_pow_of_row_bound`/`norm_minor_le_pow_sum` at `σ = ‖(3:K)‖`, `w = id`;
keep `norm_charCoeff_of_unit_minors` (the *equality*, which needs `hmin`) but prove its `≤` half
by `TateFredholm.norm_charCoeff_le_pow_choose_two`.
#### Proof sketch
1. Delete the two private lemmas; fix their call sites (`norm_minor_range`, `norm_charCoeff_of_unit_minors`).
2. In `norm_charCoeff_of_unit_minors`, the `hoff` bound stays (it is the *strict* version); the
   dominant-term argument is unchanged.  Rebuild `PhD.JacobsSlash.U3.«9_EigenvaluesU3»`.
3. renames.jsonl.
#### Mathlib lemmas needed — none new.  #### Sources — as A1.
#### Generality decision — the fork keeps its `‖3‖` statements; only the proofs are re-routed.

### [CLEANUP-1] /cleanup PhD/TateFredholm/Slopes.lean + PhD/JacobsSlash/1_SlopeTheorem.lean
- **Status**: done (2026-08-20, inline: "SKELETON" dropped from the header, main-declaration list
  completed, fork header now points at the general file; both linter-zero) | **Depends on**: A2 | **Type**: cleanup

### [A3] Row decay of the certificate blocks at a general weight
- **Status**: done (2026-08-20, slopes-hecke beastmode) |
- **Progress**: DONE — both sorries filled exactly per the sketch (`unfold heckeBlock`,
  `matrixCoeff_sum`, ultrametric max bound, then `norm_matrixCoeff_kappaSlash_le` fed by
  `norm_det_toMatrix_certificate_le` + `norm_apply_zero_zero_le_of_norm_det_le`; the block
  operator by `matrixCoeff_blockOp`).  Planning defect fixed: `hσ : σ < 1` is *not* needed for
  row decay (only for compactness), so it was dropped from both statements — the linter flagged
  it.  `hσ0 : 0 ≤ σ` comes free from `bounds.rho_nonneg.trans hρσ`. **File**: PhD/QMF/Weight/Slopes.lean | **Depends on**: A1 | **Parallel**: no | **Type**: theorems (2 sorries)
#### Statement — skeleton: `norm_matrixCoeff_heckeBlock_le`, `norm_matrixCoeff_heckeBlockOp_le`.
#### Proof sketch
1. `heckeBlock` unfolds to `∑ t ∈ filter …, χ(w t) • κ.kappaSlash (w t)` with
   `w t = levelMonoidOfToS θ S ⟨u i t * vRep t, _⟩`.  `matrixCoeff_sum`, `matrixCoeff_smul`.
2. Bound the sum by the max (`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `by positivity`).
3. Per term: `norm_mul`, `hnorm` (‖χ‖ ≤ 1), and
   `norm_matrixCoeff_kappaSlash_le κ.toWeightSeries (w t) hρσ ha m r` where
   `ha : ‖(w t).1 0 0‖ ≤ σ` comes from `norm_det_toMatrix_certificate_le θ U hU κ.toWeightSeries.bounds hdet hv (u i t) t`
   (Compact.lean) followed by `LevelBounds.norm_apply_zero_zero_le_of_norm_det_le`.
4. Block operator: `matrixCoeff_blockOp` (BlockOp.lean:654) reduces to step 1–3 at `(p.1, q.1)`.
#### Mathlib lemmas needed — `matrixCoeff_sum`, `matrixCoeff_smul`, `matrixCoeff_blockOp`,
`IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `norm_mul`, `mul_le_one₀`; project
`norm_matrixCoeff_kappaSlash_le`, `norm_det_toMatrix_certificate_le`,
`LevelBounds.norm_apply_zero_zero_le_of_norm_det_le`.
#### Sources — [Jac03, Lemma 2.7]; [Buz07, Lemma 12.2 p. 78] (norm-decreasing at supremum-norm-1 weights).
#### Generality decision — `hnorm : ∀ g, ‖χ g‖ ≤ 1` is Buzzard's hypothesis on the twist; at `χ = 1`
it is `norm_one`.

### [A4] `norm_charCoeff_heckeCharPowerSeries_le`
- **Status**: done (2026-08-20, slopes-hecke beastmode) |
- **Progress**: DONE — three lines, exactly the planned composition
  (`heckeCharPowerSeries` → `charPowerSeries_coeff` → `TateFredholm.norm_charCoeff_le_pow_block`
  with `isCompactoid_heckeBlockOp` and A3).  0 sorries in the file; standard axioms; linter zero. **File**: PhD/QMF/Weight/Slopes.lean | **Depends on**: A3 | **Parallel**: no | **Type**: theorem (1 sorry)
#### Statement — skeleton.
#### Proof sketch
`rw [heckeCharPowerSeries, charPowerSeries_coeff]`; `exact TateFredholm.norm_charCoeff_le_pow_block
hσ0 hσ (isCompactoid_heckeBlockOp …) (fun p q => norm_matrixCoeff_heckeBlockOp_le … p q) n`.
#### Mathlib lemmas needed — project `charPowerSeries_coeff`, `isCompactoid_heckeBlockOp`, A1, A3.
#### Sources — [Ser62 §5]; [Jac03 Thm 2.12]. #### Generality — as A3.

### [CLEANUP-2] /cleanup PhD/QMF/Weight/Slopes.lean (interim)
- **Status**: done (2026-08-20, inline: "SKELETON" dropped from the header, unused `hσ` removed,
  linter zero) | **Depends on**: A4 | **Type**: cleanup

### [A5] **MILESTONE**: the Newton polygon of `det(1 − T·[UηU])` lies above the block-slope polygon
- **Status**: done (2026-08-20, slopes-hecke beastmode) |
- **Progress**: **MILESTONE PROVED**, sorry-free, standard axioms, linter zero.
  `QMF.Weight.isBelow_newtonPolygon_heckeCharPowerSeries`.  One planning correction: the ticket
  proposed `(ϖ …).val` for the coefficient valuation, but `PseudoUniformizer.val` is
  `log‖x‖/log‖ϖ‖`, which would force every slope to be divided by `−log‖ϖ‖`; the ticket's own
  slope `⌊k/|ι|⌋·(−log σ)` is the *unnormalised* one, so the statement uses
  `newtonPolygon₀OfPowerSeries negLogNorm` (`PhD.NewtonPolygons.CoeffVal`) instead — the
  canonical `−log‖·‖` valuation, and the polygon file's own choice.  Rescaling to `v₃` is the
  fork's job (`4_SlopeReading`), noted in the module header.
  Supporting API added: `blockSlopes d σ = fun k => ⌊k/d⌋·(−log σ)`, `monotone_blockSlopes`,
  `sum_blockSlopes`.  Admissibility came free from `‖cₙ‖ ≤ σ^… ≤ 1` (affine bound `m=b=0`), the
  anchor from `charCoeff_zero` via `newtonPolygon₀_starting_point_of_coeff_zero_eq_one`. **File**: PhD/QMF/Weight/Slopes.lean | **Depends on**: A0, CLEANUP-2 | **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem isBelow_newtonPolygon_heckeCharPowerSeries {σ : ℝ} (hρσ : ρ ≤ σ) (hσ0 : 0 < σ)
    (hσ : σ < 1) {η : G} (hdet : ‖(θ η).det‖ ≤ σ) (hnorm : ∀ g : S, ‖((χ g : Kˣ) : K)‖ ≤ 1)
    {vRep : T → G} (hvΔ : ∀ t, vRep t ∈ levelMonoidOf θ S) (hv : Set.BijOn …)
    (idx : ι → T → ι) (u : ι → T → U) :
    (NewtonPolygon₀.ofSlopes (fun k => (k / Fintype.card ι : ℕ) * (-Real.log σ))
        (by …monotone…) 0).IsBelow
      (newtonPolygon₀OfPowerSeries (ϖ …).val
        (heckeCharPowerSeries θ κ U hU χ vRep hvΔ idx u)) := by sorry
```
(the exact normalisation `(ϖ …).val` follows `4_SlopeReading`'s `ϖ₃`; the worker fixes the
pseudo-uniformizer argument to match `PhD/NewtonPolygons/SpecConstruction.lean`'s API.)
#### Proof sketch
1. `newtonPolygon₀OfPowerSeries` satisfies `IsNewtonPolygonOf` (`isNewtonPolygonOf_newtonPolygon₀OfPowerSeries`
   in `NewtonPolygons/SpecConstruction.lean` — the fork uses it at `4_SlopeReading.lean:367`).
2. Apply its `isGreatest` field to `Q := ofSlopes …`: need (i) same starting `x` — both `0`, since
   `charCoeff u 0 = 1 ≠ 0` (`charCoeff_zero`); (ii) `Q.height k ≤ pointHeight v k` for all `k`,
   which by `height_ofSlopes` is `∑_{i<k} ⌊i/|ι|⌋ · (−log σ) ≤ val (cₖ)`, i.e. exactly A4 after
   `PseudoUniformizer.val` unfolds to `−log‖·‖ / −log‖ϖ‖`-normalisation (the fork's `ϖ₃.val`
   dictionary lemmas in `1_SlopeTheorem.lean` show the pattern).
#### Mathlib lemmas needed — project `IsNewtonPolygonOf.isGreatest` (Spec.lean:71),
`isNewtonPolygonOf_newtonPolygon₀OfPowerSeries`, `height_ofSlopes`, `charCoeff_zero`, A4.
#### Sources — [Jac03, Thm 2.12] (the polygon reading); [Kob84, Ch. IV §3]; [Buz07, §13].
#### Generality decision — inequality form (`IsBelow`), valid at every analytic weight and every
`U_ϖ`-type `η`; the fork's exact-slope theorem stays as the unit-minor special case.

### [CLEANUP-3] /cleanup PhD/QMF/Weight/Slopes.lean (final)
- **Status**: done (2026-08-20, inline: module header records the `negLogNorm` normalisation and
  the new declarations; linter zero, 0 sorries) | **Depends on**: A5 | **Type**: cleanup

---

## Group B — the Hecke-algebra datum

### [B1] `heckeOperatorSlash_comm_of_reps`
- **Status**: done (2026-08-20, slopes-hecke beastmode) |
- **Progress**: DONE.  Route as sketched, with one implementation choice that removed all the
  `attach`-subtype friction: the slash is packaged as `F z = if hz : z ∈ Δ' then a ∣ₛ ⟨z,hz⟩ else 0`,
  so both iterated expansions become honest double sums over `s`, `s'` (`Finset.sum_attach`), then
  `Finset.sum_comm` + `Finset.sum_product'` puts both sides over `s ×ˢ s'` and `Equiv.sum_comp e`
  + `he` finishes.  A generic `hexp` (`[UkU]([Uk'U]a) = ∑_{y ∈ t} ∑_{x ∈ t'} F (x*y)`) is proved
  once and used for both orders. **File**: PhD/QMF/Weight/HeckeAlgebra.lean | **Depends on**: none | **Parallel**: yes | **Type**: theorem (1 sorry)
#### Statement — skeleton.
#### Proof sketch
1. `Subtype.ext`; expand both sides with `heckeOperatorSlash_eq_finsetSum` twice (outer then
   inner), giving `∑_{y ∈ s'} (∑_{x ∈ s} a ∣ₛ x) ∣ₛ y` and its mirror.
2. Push the slash through the sum (`map_sum` of `slashAddHom`, as in `heckeOperatorSlash`'s own
   `map_add'`), then `slash_mul` (`RightSlashAction.slash_mul`) turns each term into
   `a ∣ₛ ⟨x * y, _⟩`.
3. Both sides are now sums over `s ×ˢ s'` (`Finset.sum_product`); apply
   `Finset.sum_equiv e` and `he` termwise.
#### Mathlib lemmas needed — `Finset.sum_product`, `Finset.sum_equiv`, `map_sum`; project
`heckeOperatorSlash_eq_finsetSum`, `RightSlashAction.slash_mul`, `subtype_slash_mul`.
#### Sources — [Buz07, §9 p. 69] (coset expansion), §5 p. 33 (commutativity is data).
#### Generality decision — the pairing bijection is the hypothesis because representatives `η·u`
at different places do **not** commute elementwise; a "disjoint support" hypothesis would be false.

### [B2] `mapsTo_ker_of_commute`
- **Status**: done (2026-08-20, slopes-hecke beastmode; exactly the sketched `Commute.pow_left`
  calc) | **File**: PhD/QMF/Weight/HeckeAlgebra.lean | **Depends on**: none | **Parallel**: yes | **Type**: theorem (1 sorry)
#### Statement — skeleton.
#### Proof sketch
`have : Commute ((1 - a • φ) ^ n) t := ((Commute.one_left t).sub_left (hcomm.smul_left a)).pow_left n`;
then `((1 - a•φ)^n) (t x) = t (((1 - a•φ)^n) x) = t 0 = 0` via `Module.End.mul_apply`/`LinearMap.congr_fun`
on `this.eq` and `hx`, `map_zero`.
#### Mathlib lemmas needed — `Commute.one_left`, `Commute.sub_left`, `Commute.smul_left`,
`Commute.pow_left`, `Module.End.mul_apply`, `map_zero`.
#### Sources — [Buz07, §5 p. 33]. #### Generality — any `K`-module `M`; no finiteness.

### [B3] `exists_common_eigenvector`
- **Status**: done (2026-08-20, slopes-hecke beastmode) |
- **Progress**: DONE — used mathlib's packaged
  `iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute` (the `Pairwise`
  form) together with `Module.End.iSup_maxGenEigenspace_eq_top` (triangularizability over an
  algebraically closed field), then `Submodule.exists_mem_ne_zero_of_ne_bot`. **File**: PhD/QMF/Weight/HeckeAlgebra.lean | **Depends on**: none | **Parallel**: yes | **Type**: theorem (1 sorry)
#### Statement — skeleton (shared-witness existential: `χ`, `x` are one witness pair — documented
exception to the splitting rule, per `references/statement-splitting.md`).
#### Proof sketch
1. `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo` (Eigenspace/Pi.lean:148) with
   `MapsTo` from `hcomm` (each `t j` preserves each `maxGenEigenspace (t i) μ` — mathlib's
   `Module.End.mapsTo_maxGenEigenspace_of_comm`).
2. `⊤ ≠ ⊥` (from `Nontrivial M`), so some summand is nonzero: `Submodule.exists_mem_ne_zero_of_ne_bot`
   after `iSup_eq_bot`-style contraposition.
#### Mathlib lemmas needed — `Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo`,
`Module.End.mapsTo_maxGenEigenspace_of_comm`, `Submodule.eq_bot_iff`, `iSup_eq_bot`.
#### Sources — standard; used implicitly by [Buz07, §5] ("systems of eigenvalues").
#### Generality — `[IsAlgClosed K] [FiniteDimensional K M]`, both necessary.

### [CLEANUP-4] /cleanup PhD/QMF/Weight/HeckeAlgebra.lean (interim)
- **Status**: done (2026-08-20, inline: "SKELETON" dropped, main-declaration list corrected to the
  real names, unused `[IsUltrametricDist]`/`[CompleteSpace]` omitted; linter zero) | **Depends on**: B1, B2, B3 | **Type**: cleanup

### [B4] **MILESTONE**: a system of eigenvalues on the finite-slope subspace
- **Status**: done (2026-08-20, slopes-hecke beastmode) |
- **Progress**: **MILESTONE PROVED** — `QMF.Weight.exists_eigensystem_of_riesz`, sorry-free,
  standard axioms, linter zero.  Statement simplified against the ticket draft in two ways, both
  strict improvements: (i) it is stated for an arbitrary `K`-module `M` with `N : Submodule K M`
  (so it covers `Forms` *and* any other Riesz situation, e.g. the `Pr` route) and (ii) the
  conclusion is about the **ambient** `maxGenEigenspace (t i) (lam i)`, which avoids the
  `LinearMap.restrict` coercion in the statement entirely — the restriction appears only in the
  proof, transported by `Module.End.genEigenspace_restrict`.  Finiteness is `[FiniteDimensional K N]`
  and nonvanishing is `N ≠ ⊥` (the Riesz output gives `finrank K N = n ≥ 1`, which supplies both). **File**: PhD/QMF/Weight/HeckeAlgebra.lean | **Depends on**: CLEANUP-4 | **Parallel**: no | **Type**: theorem
#### Statement
```lean
theorem exists_eigensystem_of_riesz {ι' : Type*} [IsAlgClosed K]
    (t : ι' → Module.End K (Forms Γ θ κ U hU χ)) (φ : Module.End K (Forms Γ θ κ U hU χ))
    (hcomm : ∀ i j, Commute (t i) (t j)) (hφ : ∀ i, Commute φ (t i))
    (n : ℕ) (hn : 1 ≤ n) (N : Submodule K (Forms Γ θ κ U hU χ))
    (hN : ∀ ψ ∈ N, ((1 - a • φ) ^ n) ψ = 0) (hNrank : Module.finrank K N = n)
    (hNmem : ∀ ψ, ((1 - a • φ) ^ n) ψ = 0 → ψ ∈ N) :
    ∃ (lam : ι' → K) (ψ : Forms Γ θ κ U hU χ), ψ ≠ 0 ∧ ψ ∈ N ∧
      ∀ i, ψ ∈ ((t i).restrict (fun x hx => …)).maxGenEigenspace (lam i) := by sorry
```
(the worker fixes the `restrict` coercion; the mathematical content is fixed.)
#### Proof sketch
1. `N` is `t`-stable by B2 (`hφ` + `hN`/`hNmem`), so each `t i` restricts to `N`.
2. `N` is finite-dimensional (`hNrank`, `1 ≤ n` ⇒ `Nontrivial N`).
3. B3 on `N` with the restricted family gives `lam` and a nonzero `ψ ∈ N`.
#### Mathlib lemmas needed — `LinearMap.restrict`, `Module.finrank_pos_iff`,
`FiniteDimensional.of_finrank_eq_succ`; project B2, B3, `exists_riesz_decomposition_forms`.
#### Sources — [Buz07, §5 p. 33]. #### Generality — takes the Riesz data as hypotheses so that it
applies to both `heckeCharPowerSeries` (neat) and `heckeCharPowerSeriesPr` (any level).

### [CLEANUP-5] /cleanup PhD/QMF/Weight/HeckeAlgebra.lean (final)
- **Status**: done (2026-08-20, inline: header + declaration list already updated in CLEANUP-4;
  final linter/axiom pass clean, 0 sorries) | **Depends on**: B4 | **Type**: cleanup

---

## Group C — the level dictionary

### [C1] `Sigma0'.levelBounds_valued`
- **Status**: done (2026-08-20, slopes-hecke beastmode) |
- **Progress**: DONE first try — the planning-verified proof transplanted verbatim. **File**: PhD/QMF/Weight/AdicLevel.lean | **Depends on**: none | **Parallel**: yes | **Type**: theorem (1 sorry)
#### Statement — skeleton.
#### Proof sketch (**verified during planning — this proof compiles at `v.adicCompletion F`**)
```lean
  have hy1 : ‖y‖ < 1 := Valued.toNormedField.norm_lt_one_iff.mpr (hy ▸ hγ)
  refine Sigma0'.levelBounds (norm_nonneg _) hy1 (fun x hx => ?_) (fun x hx => ?_) (fun x hx => ?_)
  · exact Valued.toNormedField.norm_le_one_iff.mpr hx
  · exact le_antisymm (Valued.toNormedField.norm_le_one_iff.mpr hx.le)
      (Valued.toNormedField.one_le_norm_iff.mpr hx.ge)
  · exact Valued.toNormedField.norm_le_iff.mpr (hy ▸ hx)
```
#### Mathlib lemmas needed — `Valued.toNormedField.norm_le_iff`, `norm_le_one_iff`,
`one_le_norm_iff`, `norm_lt_one_iff`; project `Sigma0'.levelBounds` (SlashAction.lean:941).
#### Sources — mathlib `Topology/Algebra/Valued/NormedValued.lean`.
#### Generality — any `Valued K Γ₀` with `RankOne`; the norm must be the valued one (`open scoped
Valued`), which is the case at adic completions by our ForMathlib instance.

### [C2] `SigmaOne` and `levelBounds_sigmaOne`
- **Status**: done (2026-08-20, slopes-hecke beastmode) |
- **Progress**: DONE — fork proof ported at general `ρ`; `d_unit` inlines the three-line 1-unit
  argument (`IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`) instead of importing the fork's
  `norm_eq_one_of_norm_sub_one_lt_one`, keeping the layering (general file must not import JacobsSlash). **File**: PhD/QMF/Weight/AdicLevel.lean | **Depends on**: C1 | **Parallel**: no | **Type**: def + theorem (3 sorries)
#### Statement — skeleton.
#### Proof sketch — the fork's `sigma1Norm`/`levelBounds_sigma1Norm` (`5_KappaWeight.lean`,
sorry-free) verbatim with `ρ` for `‖3‖`: `one_mem'` by `Matrix.one_apply_ne`; `mul_mem'` by the
ultrametric expansion `(gh)₁₁ − 1 = g₁₀h₀₁ + (g₁₁−1)(h₁₁−1) + (g₁₁−1) + (h₁₁−1)`;
`levelBounds_sigmaOne` by `hg.2.1.trans (ρ² ≤ ρ)` and `norm_eq_one_of_norm_sub_one_lt_one`.
#### Mathlib lemmas needed — `IsUltrametricDist.norm_add_le_max`, `Matrix.mul_apply`,
`Fin.sum_univ_two`, `mul_le_one₀`; project `norm_eq_one_of_norm_sub_one_lt_one` (1_PadicAnalytic.lean:183 —
**move it to a general file or restate**, it is currently in the fork).
#### Sources — [Jac03, §2.1 p. 29].
#### Generality — `ρ` arbitrary in `[0,1)`; the `Σ₁(p^k)` levels are `ρ = ‖ϖ‖^k`-instances.

### [C3] `mem_sigmaOne_iff_valued`
- **Status**: done (2026-08-20, slopes-hecke beastmode) |
- **Progress**: DONE — three `norm_le_iff`/`norm_le_one_iff` rewrites each way, with `norm_pow`/`map_pow`
  for the `ρ²` clause.  Planning defect fixed: the `ϖ ≠ 0` hypothesis is unnecessary (the dictionary is
  unconditional) — dropped, linter zero. **File**: PhD/QMF/Weight/AdicLevel.lean | **Depends on**: C2 | **Parallel**: no | **Type**: theorem (1 sorry)
#### Statement — skeleton.
#### Proof sketch — `constructor` + three `Valued.toNormedField.norm_le_iff` rewrites, using
`‖ϖ‖^2 = ‖ϖ^2‖` (`norm_pow`) and `Valued.v (ϖ^2) = (Valued.v ϖ)^2` (`map_pow`), and
`‖x‖ ≤ 1 ↔ v x ≤ 1` for the integrality clause.
#### Mathlib lemmas needed — `norm_pow`, `map_pow`, `Valued.toNormedField.norm_le_iff`,
`norm_le_one_iff`.  #### Sources — as C1.  #### Generality — as C1.

### [CLEANUP-6] /cleanup PhD/QMF/Weight/AdicLevel.lean
- **Status**: done (2026-08-20, inline: header updated, unused hypothesis dropped, linter zero) | **Depends on**: C3 | **Type**: cleanup

### [C4] Fork dedup: `sigma1Norm := SigmaOne K₃ ‖3‖`; delete the hand-rolled dictionary lemmas
- **Status**: done (2026-08-20, slopes-hecke beastmode) |
- **Progress**: DONE — `sigma1Norm` is now `abbrev … := QMF.SigmaOne K ‖(3:K)‖ (norm_nonneg _) h3`
  and `levelBounds_sigma1Norm := QMF.levelBounds_sigmaOne _ _`.  Both fork dictionary lemmas
  deleted; the three call sites re-routed through `Valued.toNormedField.norm_le_iff` /
  `norm_le_one_iff`.  `4_KappaColumn`, `5_KappaWeight`, `9_EigenvaluesU3`, `10_Eigenforms` all
  build, 0 sorries.  renames.jsonl updated (3 entries). **Files**: PhD/JacobsSlash/U3/5_KappaWeight.lean, PhD/JacobsSlash/U3/4_KappaColumn.lean | **Depends on**: CLEANUP-6 | **Parallel**: no | **Type**: refactor
#### Statement
`sigma1Norm K h3 := SigmaOne K ‖(3:K)‖ (norm_nonneg _) h3` (abbrev), `levelBounds_sigma1Norm :=
levelBounds_sigmaOne …`; delete `JacobsSlash.norm_le_of_valued_le` and
`JacobsSlash.norm_eq_one_of_valued_eq_one` (`4_KappaColumn.lean:51,62`), re-routing
`norm_sigma1_entry_le_one`, `norm_sigma1_lower_right_sub_one_le`, `norm_sigma1_lower_left_le`,
`norm_sigma1_lower_right` through `Valued.toNormedField.norm_le_iff` / `norm_le_one_iff`.
#### Proof sketch
1. Replace the two lemmas' uses: `norm_le_of_valued_le hy h` ↦ `Valued.toNormedField.norm_le_iff.mpr h`
   (note the fork's version takes `y ≠ 0`, mathlib's does not — strictly better);
   `norm_eq_one_of_valued_eq_one h` ↦ `le_antisymm (norm_le_one_iff.mpr h.le) (one_le_norm_iff.mpr h.ge)`.
2. `sigma1₃_le_sigma1Norm` becomes C3 + the `Σ₁(3)` valuation bounds.
3. Rebuild the fork through `9_EigenvaluesU3`, `10_Eigenforms`; renames.jsonl.
#### Mathlib lemmas needed — as C1.  #### Sources — as C1.
#### Generality decision — the fork keeps `Sigma1₃` (valuation-defined); only the dictionary is
delegated.

---

## Group D — compact open levels (forms-riesz T009, undeferred)

### [D1] `Units.isCompact_of_isCompact`
- **Status**: done (2026-08-20, slopes-hecke beastmode) |
- **Progress**: DONE — the set is *definitionally* `embedProduct R ⁻¹' (s ×ˢ (unop ⁻¹' s))`
  (`hset := rfl`), so `Units.isClosedEmbedding_embedProduct.isCompact_preimage` applies directly;
  `unop ⁻¹' s = op '' s` supplies compactness of the second factor. **File**: PhD/QMF/Level.lean | **Depends on**: none | **Parallel**: yes | **Type**: theorem (1 sorry)
#### Statement — skeleton.
#### Proof sketch
1. `Units.isClosedEmbedding_embedProduct` (`Mathlib/Topology/Algebra/Group/Basic.lean:1422`,
   hypotheses `[T1Space α] [ContinuousMul α]`).
2. The set is `embedProduct ⁻¹' (s ×ˢ MulOpposite.op '' s)`; `IsCompact.prod` and
   `IsCompact.image` (`MulOpposite.opHomeomorph.isCompact_image`) give compactness of the target,
   and `IsClosedEmbedding.isCompact_preimage` transports it.
#### Mathlib lemmas needed — `Units.isClosedEmbedding_embedProduct`, `IsCompact.prod`,
`IsClosedEmbedding.isCompact_preimage`, `MulOpposite.opHomeomorph`.
#### Sources — [Buz07, §9 p. 68] ("compact open subgroup").
#### Generality — any `T1` topological monoid with continuous multiplication.

### [D2] `isCompact_integralTensor`
- **Status**: done (2026-08-20, slopes-hecke beastmode) |
- **Progress**: DONE, and the planning RISK did **not** materialise — no sub-development was
  needed.  The key move avoids linear-map API entirely: with the (local, non-global) right algebra
  structure `Algebra.TensorProduct.rightAlgebra`, `d ⊗ₜ x = x • (d ⊗ₜ 1)`
  (`right_algebraMap_apply` + `tmul_mul_tmul`), so each summand is `(continuous_apply i).smul
  continuous_const`, continuous from `IsModuleTopology.toContinuousSMul` alone.  The file now
  takes `[IsModuleTopology 𝔸ᶠ (D ⊗[F] 𝔸ᶠ)]` as a hypothesis (it must: with an arbitrary
  `TopologicalSpace` instance the statement is false), and `[Module.Finite F D]` was dropped as
  genuinely unused (the basis argument carries it). **File**: PhD/QMF/Level.lean | **Depends on**: D1 | **Parallel**: no | **Type**: def + theorem (1 sorry)
#### Statement — skeleton.
#### Proof sketch
1. `{a | ∀ i, a i ∈ integralAdeles}` is `Set.pi univ (fun _ => integralAdeles)`, compact by
   `isCompact_univ_pi` + `FiniteAdeleRing.isCompact_integralAdeles`.
2. `IsCompact.image` with continuity of `a ↦ ∑ i, b i ⊗ₜ a i`: each summand is
   `(TensorProduct.mk F D 𝔸 (b i)) ∘ (eval i)`, continuous for the module topology
   (`IsModuleTopology.continuous_of_linearMap`-style; FLTstuff's
   `Mathlib/Topology/Algebra/Module/ModuleTopology.lean` has the API).
**RISK (recorded at planning time)**: if the continuity of the tensor map is not directly
available, spawn a sub-ticket for `IsModuleTopology (FiniteAdeleRing …) (D ⊗ 𝔸)` +
`continuous_tensor_of_basis`; FLTstuff already carries `IsModuleTopology` instances for these
objects (`locallyCompactSpaceOfFinite`, `instIsModuleTopology…`).
#### Mathlib lemmas needed — `isCompact_univ_pi`, `IsCompact.image`, `Continuous.sum`,
`TensorProduct.mk`; project `FiniteAdeleRing.isCompact_integralAdeles`.
#### Sources — [Buz07, §9 p. 68].
#### Generality — `Module.Finite F D` (no division-algebra hypothesis); a basis is an argument.

### [D3] The fork's `U0`, `U₁(9)` are compact open; Hecke finiteness for free
- **Status**: done (2026-08-20) — `U₀(1)` here, `U₁(9)` in [D3b] below |
- **Progress**: New file `PhD/JacobsSlash/U3/2_LevelTopology.lean` (0 sorries, standard axioms,
  linter zero) proves **`JacobsSlash.isCompact_U0`**, through the ticket's step 1 in full:
  * `hurwitzBasis` — the fork's `hurwitzCoord` packaged as a `Module.Basis (Fin 4) ℚ ℍ[ℚ]`
    (`Module.Basis.ofEquivFun`); `hurwitzBasis'` is the `Fin (finrank ℚ D)` reindexing that
    `QMF.integralTensor` wants.
  * `coordMapAdelic`, `evalAlgHom_coordMapAdelic`, `sum_coordMapAdelic` — the adelic twin of the
    fork's local `coordMap`, its local–global compatibility, and the reconstruction identity.
  * `mem_integralAdeles_iff` — integral adeles = everywhere-integral (range of the structure map).
  * `forall_toLocal_mem_localOrder_iff` — **the lattice identity** the ticket flagged as the
    RISK: `{x | ∀ w, toLocal w x ∈ localOrder w} = QMF.integralTensor ℚ D hurwitzBasis'`.
  **Key discovery that made this tractable**: the fork *already had* half the machinery in
  `2_Level.lean` (`localSpan`, `localOrder_le_localSpan`, `coordMap`,
  `coordMap_mem_of_mem_localSpan`, `mem_hurwitzOrder_iff_coords`,
  `isInt_of_forall_mem_adicCompletionIntegers`), built for the *global* statement
  `mem_hurwitzOrder_of_forall_local`; those five were un-`private`d and reused rather than
  duplicated.  Also added: `Module.Basis.rightBaseChange'` (module version of FLT's
  algebra-only `rightBaseChange`) in `PhD/QMF/FLTstuff/Mathlib/RingTheory/TensorProduct/Basis.lean`.

### [D3b] `U₁(9)` compact open, and Hecke finiteness without explicit representatives
- **Status**: done (2026-08-20, follow-up session) |
- **Progress**: DONE — `isOpen_U0`, `isCompact_U1_9`, `isOpen_U1_9`, `finite_image_doubleCoset_U1_9`,
  all sorry-free on standard axioms, linter zero.  Both scouting notes held:
  * **no `lTensor'` was needed** — `toLocal` is *semilinear* over the evaluation `𝔸 → K_v`, so
    `IsModuleTopology.continuous_of_linearMapₛₗ` applies directly (`QMF.toLocalₛₗ`,
    `QMF.continuous_toLocal`; σ-continuity is `RestrictedProduct.continuous_eval`);
  * **`RigidificationAt` was not changed** — the missing `F_v`-linearity is carried by the new
    `Prop` mixin `QMF.RigidificationAt.IsCompletionLinear` (`θ(1 ⊗ z) = z·1`), whose fork instance
    is `theta_one_tmul`; `continuous_rigidificationEquiv` and `continuous_toMatrix` follow.
  Openness of `U₀(1)` needed one extra step not in the sketch: `integralTensor` as a *preimage*
  (`coordsAdelic`, an `𝔸`-linear coordinate map, and `integralTensor_eq_preimage`) plus
  `QMF.isOpen_integralAdeles` (`RestrictedProduct.isOpenEmbedding_structureMap`).
  `Sigma1Set` (the `Σ₁(9)` conditions without `det ≠ 0`) is clopen by
  `IsUltrametricDist.isOpen_closedBall` + `Metric.isClosed_closedBall`, and
  `mem_Sigma1_iff_of_det_ne_zero` discharges the `det` clause via `QMF.toMatrix_det_ne_zero`.
  **Defect found and fixed**: the file was initially missing
  `attribute [local instance 2000] …instAlgebraAdicCompletion`, which made the `IsCompletionLinear`
  instance fail into a `sorry` that Lean reports only as a *warning* — the build gate now also
  greps for "uses `sorry`" and `#print axioms`. **Files**: PhD/JacobsSlash/U3/2_LevelTopology.lean | **Depends on**: D3 | **Type**: theorems
#### Statement
```lean
theorem isCompact_U1_9 : IsCompact (U1_9 : Set (QMF.Dfx ℚ D))
theorem isOpen_U1_9 : IsOpen (U1_9 : Set (QMF.Dfx ℚ D))
example : (((Quotient.mk'' : QMF.Dfx ℚ D → RightCosets U1_9) ''
    ({eta3} * (U1_9 : Set (QMF.Dfx ℚ D)))) : Set (RightCosets U1_9)).Finite :=
  AbstractHeckeOperatorSlash.finite_image_doubleCoset_of_isOpen_of_isCompact
    isOpen_U1_9 isCompact_U1_9 _
```
#### Proof sketch
1. `U₁(9) = U₀(1) ∩ {g | toMatrix v₃ g ∈ Σ₁} ∩ {g | toMatrix v₃ g⁻¹ ∈ Σ₁}`, so compactness is
   `isCompact_U0.inter_right` of a **closed** condition and openness is an **open** condition;
   `Σ₁` is a *clopen* ball-condition in `M₂(K₃)` (nonarchimedean: `‖x‖ ≤ r` is clopen).
2. The missing ingredient is continuity of `toMatrix ℚ D v₃ = theta3 ∘ toLocal v₃` for the
   module topologies:
   * `toLocal ℚ D w : D ⊗ 𝔸_f → D ⊗ K_w` is `LinearMap.lTensor D (eval_w)` — semilinear over the
     continuous ring map `eval_w : 𝔸_f → K_w`; FLTstuff has `ContinuousLinearMap.rTensor'` and
     `evalContinuousAlgebraMap` for the *other* side (`𝔸 ⊗ V`), so a `lTensor'` companion is
     needed (or transport through `TensorProduct.RightActions.Module.TensorProduct.comm`).
   * `theta3 : D ⊗ K₃ ≃ₐ[K₃] M₂(K₃)` is continuous by
     `IsModuleTopology.continuous_of_linearMap` once `IsModuleTopology K₃ (M₂ K₃)` is available.
   * unit-group continuity of `u ↦ ↑u` and `u ↦ ↑u⁻¹` is `Units.continuous_val` /
     `Units.continuous_coe_inv`.
3. Then the `example` re-derives `finite_image_eta3` without explicit representatives; the
   explicit version stays (it is what computes the *matrix*).
#### Mathlib lemmas needed — `IsCompact.inter_right`, `IsClosed.preimage`, `Metric.isOpen_ball`
/ a clopen-ball lemma for a discretely valued field, `IsModuleTopology.continuous_of_linearMapₛₗ`,
`Units.continuous_val`, `Units.continuous_coe_inv`.
#### Scouting notes (2026-08-20, recorded before the run ended)
* **`Σ₁` clopen is cheap**: in *any* ultrametric space a closed ball is open
  (`‖y − x‖ < r` ⇒ `‖y‖ ≤ max(‖x‖, ‖y − x‖) ≤ r`), so no discreteness of the value group is
  needed — only `IsUltrametricDist K₃`, which is available.
* **`theta` is secretly `K₃`-linear**: `QMF.RigidificationAt` records only the `ℚ`-algebra
  equivalence, but the fork's instance is `theta ν₃ sq_ν₃ = thetaK ∘ Algebra.TensorProduct.comm`
  (`U3/1_Setting.lean:355–476`) and `thetaK` **is** a `K₃`-algebra map; the transport
  `Algebra.TensorProduct.comm` has a `K₃`-linear form in the `TensorProduct.RightActions` scope
  (`Module.TensorProduct.comm`).  So `IsModuleTopology.continuous_of_linearMap` applies without
  strengthening the class.  *Open design question for the user*: whether `RigidificationAt` should
  carry the `F_v`-algebra equivalence instead of the `F`-one, which would make this automatic for
  every instantiation rather than a fork-local unfolding.
* **The one genuinely missing piece** is a continuity companion for `LinearMap.lTensor` on the
  `D ⊗ 𝔸` side: FLTstuff has `ContinuousLinearMap.rTensor'` + `evalContinuousAlgebraMap` for
  `𝔸 ⊗ V` only.  Either add `lTensor'`, or transport through `Module.TensorProduct.comm` and reuse
  `rTensor'`.
#### Sources — [Buz07, §9 pp. 68–69]; [Jac03, Def 1.20].
#### Generality — fork-specific; the general halves are D1, D2 and `isCompact_U0`. **Files**: PhD/JacobsSlash/U3/2_Level.lean (+ 3_EtaDecomposition.lean) | **Depends on**: D2 | **Parallel**: no | **Type**: theorems
#### Statement
```lean
theorem isCompact_U0 : IsCompact (U0 : Set (Dfx ℚ D))
theorem isCompact_U1_9 : IsCompact (U1_9 : Set (Dfx ℚ D))
theorem isOpen_U1_9 : IsOpen (U1_9 : Set (Dfx ℚ D))
example : (((Quotient.mk'' : Dfx ℚ D → RightCosets U1_9) '' ({eta3} * (U1_9 : Set (Dfx ℚ D)))) :
    Set (RightCosets U1_9)).Finite :=
  AbstractHeckeOperatorSlash.finite_image_doubleCoset_of_isOpen_of_isCompact isOpen_U1_9 isCompact_U1_9 _
```
#### Proof sketch
1. `U0` is `{u | ∀ w, toLocal w u ∈ localOrder w ∧ toLocal w u⁻¹ ∈ localOrder w}`; identify
   `{x | ∀ w, toLocal w x ∈ localOrder w}` with `integralTensor ℚ D b` for the Hurwitz basis
   `b = (1, i, j, (1+i+j+k)/2)` (an equality of sets — the closure defining `localOrder` is the
   image of `𝒪_Hurwitz ⊗ ℤ_w`).  Then D1 + D2.
2. `U1_9` is the intersection of `U0` with a *closed* congruence condition at `3`, hence compact;
   openness from the congruence being open (`toLocal` continuous, the congruence class open in
   `Σ₁(9)`).
3. The `example` then re-proves `finite_image_eta3` without explicit representatives — keep both
   (the explicit one is used for the *matrix*), but record the general route in the docstring.
**RISK**: step 1's set identity is the substantive part; if it resists, spawn a sub-ticket for
`localOrder_eq_image` (the closure of the generated subring equals the `ℤ_w`-span of the basis).
#### Mathlib lemmas needed — `IsCompact.inter_right`, `IsClosed.inter`, continuity of `toLocal`;
project D1, D2, `finite_image_doubleCoset_of_isOpen_of_isCompact`.
#### Sources — [Buz07, §9 pp. 68–69]; [Jac03, Def 1.20].
#### Generality — fork-specific (the Hurwitz order is `ℍ[ℚ]`-specific); the general statement is
D1+D2.

### [CLEANUP-7] /cleanup PhD/QMF/Level.lean + fork 2_Level.lean
- **Status**: done (2026-08-20, inline: "SKELETON" dropped from `Level.lean`'s header and the
  `TensorProduct.RightActions` choice documented there; five `2_Level.lean` lemmas un-`private`d
  with their docstrings kept; new `2_LevelTopology.lean` linter-zero) | **Depends on**: D3 | **Type**: cleanup

---

### [CLEANUP-FINAL] /cleanup-all on the whole board surface + README/PROGRESS/memory
- **Status**: done (2026-08-20, slopes-hecke beastmode: every touched module rebuilt with 0 errors
  and 0 sorries; `runLinter` zero on each new/edited file; `PhD/QMF/README.md` §5 and
  `PhD/JacobsSlash/PROGRESS.md` updated; memory `slopes-hecke-board`, `adelic-lattice-api`,
  `parallel-ticket-boards`, MEMORY.md updated; renames.jsonl 10 new entries) | **Depends on**: every other ticket | **Type**: cleanup-all.  README §1
(`TateFredholm/Slopes`, `NewtonPolygons/OfSlopes`, `Weight/{Slopes,HeckeAlgebra,AdicLevel}`,
`QMF/Level`), §3 (the slope bound; the Hecke datum; the level dictionary), §4 (dead-code sweep),
§5 (tick off the four items; the remaining opens are families + `RigidificationAt` + housekeeping);
`PhD/JacobsSlash/PROGRESS.md`; memory `parallel-ticket-boards`, `analyticweight-headline`.
