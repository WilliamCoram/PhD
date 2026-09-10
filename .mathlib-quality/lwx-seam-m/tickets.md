# Tickets — `lwx-seam-m`

LWX Proposition 2.17 at every analyticity level `m = h + 1`.

- Open: 0 | In Progress: 0 | Done: 186  (135 proof, 51 cleanup)

**Milestones**: `SH-M` (`specCharSeries_ofCerts_eq_discHeckeCharPowerSeries`), `QH-M`
(`specCharSeries_ofCerts_eq_discHeckeCharPowerSeriesQ`).

**Board rules.** Statements are transcribed verbatim from the compiling skeleton; do not edit a
ticketed statement (`theorem_statement_protected`) — if it is wrong, file a B2.  Every proof
sketch and citation below was checked in the decomposition pass (`decomposition.md`); the two
corrections found there are already baked into the skeleton.

**Files owned by this board** (never touch the concurrent `tate-riesz` board's files):
`PhD/TateFredholm/Unitriangular.lean`, `PhD/TateFredholm/BlockMap.lean`,
`PhD/LWX/{AmiceValuation,PowSubOne,AmiceBasis,HaloWeightH,DiscModel,DiscForms,SeamH,QuaternionicH}.lean`.

**Standing context.** `{p : ℕ} [hp : Fact p.Prime]`, `K` a complete ultrametric
`NontriviallyNormedField` of characteristic zero, `ψ : ℚ_[p] →+* K` isometric (`hψ`), `hp2 : p ≠ 2`,
`h0 : p⁻¹ < ‖T₀‖`, `h1 : ‖T₀‖ < 1`, `hT : ‖TH p h T₀‖² < p⁻¹`.

---

## Group U — `PhD/TateFredholm/Unitriangular.lean`

Perturbed unitriangular matrices are isometric equivalences of `c(ℕ, K)`.  This replaces Colmez's
reduction-mod-`p` route (Prop 1.1.5, which needs `L` discretely valued) by a direct argument valid
over any complete ultrametric field.  Source: `colmez.txt:673–682`.

### [U-1] `IsUnitriangularPerturbation.tendsto_col` — done
**Statement**: `(hM : IsUnitriangularPerturbation M q) (n : ℕ) : Tendsto (fun k => M k n) cofinite (𝓝 0)`.
**Sketch**: `hM.col_finite n` says the support is finite; a function with finite support tends to
`0` along `cofinite` (`Filter.Tendsto.congr'` with `EventuallyEq` on the cofinite filter, as in
`Seam.lean`'s `mahlerOfPow`).
**Lemmas**: `Filter.eventually_cofinite`, `Set.Finite.subset`, `tendsto_const_nhds`.
**Deps**: none.

### [U-2] `norm_ofPerturbation_le` — done
**Statement**: `‖ofPerturbation hM a‖ ≤ ‖a‖`.
**Sketch**: coordinatewise, `‖∑' n, M k n * a n‖ ≤ sup_n ‖M k n‖‖a n‖ ≤ ‖a‖` by
`IsUltrametricDist.norm_tsum_le` and `hM.norm_le_one`; then `cSpace.norm_le_of_forall`.
**Lemmas**: `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `cSpace.norm_le_of_forall`,
`ofCoeffs_apply`.
**Deps**: U-1.

### [U-3] `norm_ofPerturbation` — done
**Statement**: `‖ofPerturbation hM a‖ = ‖a‖`.
**Sketch** (the largest-index argument): for `a = 0` both sides vanish.  Otherwise
`S = {n : ‖a n‖ = ‖a‖}` is finite (`a ∈ c₀`) and nonempty; let `n₀ = max S`.  Then
`(ofPerturbation hM a) n₀ = M n₀ n₀ · a n₀ + ∑_{n < n₀} M n₀ n a n + ∑_{n > n₀} M n₀ n a n`.  The
first term has norm exactly `‖a‖` (`hM.norm_diag`); the second `≤ q‖a‖ < ‖a‖`
(`hM.norm_le_of_lt`); the third `< ‖a‖` by maximality of `n₀`.  Ultrametric ⇒ the norm is `‖a‖`.
Combine with U-2.
**Lemmas**: `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `Set.Finite.exists_maximal_wrt`,
`tsum_eq_add_tsum_ite`.
**Source**: Colmez's "éléments inversibles sur la diagonale" (`colmez.txt:678`).
**Deps**: U-2.

### [U-4] `surjective_of_forall_exists_approx` — done
**Statement**: `(Ψ : c(I,K) →L[K] c(J,K)) (hq' : q' < 1) (happ : ∀ t, ∃ b, ‖b‖ ≤ ‖t‖ ∧ ‖t − Ψ b‖ ≤ q'‖t‖) : Surjective Ψ`.
**Sketch**: iterate `happ` from `t₀ = t` to get `bₙ` with `‖bₙ‖ ≤ q'ⁿ‖t‖` and residues
`‖tₙ‖ ≤ q'ⁿ‖t‖`; `∑ bₙ` converges (complete, `q' < 1`) and `Ψ (∑ bₙ) = t` by continuity.
**Lemmas**: `summable_of_norm_bounded` + geometric, `ContinuousLinearMap.map_tsum`, `HasSum.tsum_eq`.
**Note**: stated for `c(I,K) →L c(J,K)` deliberately — a general `NormedSpace K E` version times
out (there is no `NormedSpace K c(ℕ,K)` instance).
**Deps**: none.

### [U-5] `exists_approx_single` — done
**Statement**: `∃ b, ‖b‖ ≤ 1 ∧ ‖cSpace.single k 1 − ofPerturbation hM b‖ ≤ q`.
**Sketch**: strong induction on `k`.  Take `b₀ = (M k k)⁻¹ • single k 1`; then
`single k 1 − ofPerturbation hM b₀` is supported on `{j ≠ k}` with entries `≤ 1`, and is `≤ q` on
`j > k` (below diagonal).  The finitely many `j < k` are corrected by the inductive hypothesis
applied to each `single j 1`, scaled by the residue.
**Lemmas**: `Nat.strong_induction_on`, `hM.norm_diag`, `hM.norm_le_of_lt`, `hM.col_finite`.
**Deps**: U-3.

### [U-6] `exists_approx` — done
**Statement**: `∃ b, ‖b‖ ≤ ‖t‖ ∧ ‖t − ofPerturbation hM b‖ ≤ q‖t‖`.
**Sketch**: choose a finite `S` with `‖t n‖ ≤ q‖t‖` off `S`; write `t|_S = ∑_{k∈S} t k • single k 1`
and sum the U-5 witnesses scaled by `t k`.  Ultrametric ⇒ the bounds add up.
**Lemmas**: `Finset.sum`, `cSpace.sum_apply`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`.
**Deps**: U-5.

### [U-7] `injective_ofPerturbation` — done
**Statement**: `Function.Injective (ofPerturbation hM)`.
**Sketch**: immediate from U-3 (an isometry between normed groups is injective).
**Lemmas**: `norm_eq_zero`, `sub_eq_zero`.
**Deps**: U-3.

### [U-8] `equivOfPerturbation` + `norm_equivOfPerturbation_symm` — done
**Statement**: `equivOfPerturbation hM : c(ℕ,K) ≃L[K] c(ℕ,K)` (the `continuous_invFun` bound), and
`‖(equivOfPerturbation hM).symm b‖ = ‖b‖`.
**Sketch**: `LinearEquiv.ofBijective` from U-7 and `surjective_ofPerturbation`; the inverse is
bounded by `1` because the forward map is an isometry (U-3), so
`‖e.symm b‖ = ‖ofPerturbation hM (e.symm b)‖ = ‖b‖`.
**Lemmas**: `AddMonoidHomClass.continuous_of_bound`, `LinearEquiv.ofBijective_apply`.
**Deps**: U-3, U-7.

### [CLEANUP-U1] `/cleanup PhD/TateFredholm/Unitriangular.lean` — done (after U-3)
### [CLEANUP-U2] `/cleanup PhD/TateFredholm/Unitriangular.lean` — done (after U-6)
### [CLEANUP-U3] `/cleanup PhD/TateFredholm/Unitriangular.lean` — done (final, after U-8)
**Progress**: 2026-09-05T23:33 — group U complete.  `lake build` clean (2525 jobs), no sorries, no warnings,
`runLinter` clean on the module, `#print axioms` standard on `norm_ofPerturbation`,
`surjective_ofPerturbation`, `equivOfPerturbation`, `norm_equivOfPerturbation_symm`.
Style pass: one line wrapped to ≤ 100 chars; two private helpers added during the proofs —
`norm_smul_le_mul` (there is no `NormSMulClass K c(I,K)` instance, so `norm_smul` is unusable on
the model space) and `sum_smul_single_apply` (coordinates of a finite combination of basis
vectors), both used by U-5 and U-6.  `omit [IsUltrametricDist K] [CompleteSpace K]` added on
`tendsto_col`.

---

## Group BM — `PhD/TateFredholm/BlockMap.lean`

Rectangular block maps `c(σ × I, R) →L c(σ × I', R)`.  Infrastructure; every proof transcribes the
corresponding `blockDiag` proof in `PhD/TateFredholm/Conjugation.lean` with `I ≠ I'`.

### [BM-1] `blockOpMap_blockIncl` + `matrixCoeff_blockOpMap` — done
**Sketch**: copy `blockOp_blockIncl` / `matrixCoeff_blockOp` (`BlockOp.lean:628,646`); the only
change is that the inclusion is into `c(σ × I', R)`.
**Lemmas**: `cSpace.blockProj_blockIncl`, `cSpace.sum_apply`, `cSpace.blockIncl_single`.

### [BM-2] `blockMap_blockIncl` + `matrixCoeff_blockMap` — done
**Sketch**: `blockMap f = blockOpMap (if a = b then f else 0)`; specialise BM-1 and
`Finset.sum_ite_eq`.
**Deps**: BM-1.

### [BM-3] `blockMap_eq_blockDiag` + `blockMap_id` — done
**Sketch**: `ext_matrixCoeff`, then BM-2 against `matrixCoeff_blockDiag` (`Conjugation.lean:146`)
and `matrixCoeff_id`.
**Deps**: BM-2.

### [BM-4] `blockMap_comp_blockOp` + `blockOp_comp_blockMap` + `blockMap_comp` — done
**Sketch**: `ContinuousLinearMap.ext` on `blockIncl`s, then BM-1/BM-2; transcribes
`blockDiag_comp_blockOp` and `blockOp_comp_blockDiag` (`Conjugation.lean:124,135`).
**Deps**: BM-2.

### [BM-5] `blockMapEquiv` — done
**Sketch**: `ContinuousLinearEquiv.equivOfInverse`; the two round-trip fields follow from BM-4
(`blockMap_comp`) plus `blockMap_id`, exactly as `diagBlockEquiv` (`Conjugation.lean:162`).
**Deps**: BM-3, BM-4.

### [CLEANUP-BM1] `/cleanup PhD/TateFredholm/BlockMap.lean` — done (after BM-3)
### [CLEANUP-BM2] `/cleanup PhD/TateFredholm/BlockMap.lean` — done (final, after BM-5)
**Progress**: 2026-09-06T09:12 — group BM complete.  `lake build` clean (2294 jobs), no sorries, no warnings,
`#print axioms` standard on `blockMapEquiv` and `blockMap_comp_blockOp`; lines ≤ 100.
`blockMap_eq_blockDiag` turned out to be `rfl` (both sides are the same `blockOpMap`), so
`blockMap_id` is `blockDiag_id` transported.  Six `omit [DecidableEq …]` lines added.

---

## Group A — `PhD/LWX/AmiceValuation.lean` (Colmez, Lemme 1.4.9)

Source: `colmez.txt:666–671` (statement) and `colmez.txt:684–760` (proof).  **The indexing is
re-centred**: discs are `a` with `0 ≤ a < pʰ` (Colmez's `−j`, `j = pʰ − a`), so `a = n mod pʰ` is
the disc `j = i(n)` and `a < n mod pʰ` is `j > i(n)`.  Colmez's `m(n)` **is** `⌊n/pʰ⌋` (verified
exhaustively).  Read the extracted reference with care: it renders `≤` as `<`, and clause (ii)'s
third bullet is `deg ḡ_{n,j} ≤ m(n)` — see `decomposition.md`, group A, "A reading trap in the
extracted text".

### [A-1] `card_filter_range_mod_eq` — done
**Statement**: `((range n).filter fun k => k % q = r).card = n / q + if r < n % q then 1 else 0` for `0 < q`, `r < q`.
**Sketch**: the map `k ↦ (k − r)/q` is a bijection onto `range (n/q + [r < n%q])`; or count
`{k < n : k ≡ r}` by `Nat.Ioc_filter_dvd_card_eq_div` after the shift `k ↦ k + q − r`.
**Lemmas**: `Nat.Ioc_filter_dvd_card_eq_div`, `Nat.card_multiples`, `Finset.card_nbij'`.
**Note**: `Nat.count_modEq_card` does **not** exist in this mathlib (checked); do not cite it.
**Source**: `colmez.txt:686–689` (`|K_{n,j}| = ⌊(j+n−1)/pʰ⌋ − ⌊(j−1)/pʰ⌋`, re-centred).

### [A-2] `padicValNat_factorial_sub_factorial_div_pow` — done
**Statement**: `padicValNat p (n !) = padicValNat p ((n / p ^ h)!) + ∑ ℓ ∈ Icc 1 h, n / p ^ ℓ`.
**Sketch**: apply `padicValNat_factorial` to both `n` and `n / p^h` with a common bound
`b > max (Nat.log p n) h`, then `Nat.div_div_eq_div_mul` reindexes the tail sum.
**Lemmas**: `padicValNat_factorial (hnb : Nat.log p n < b)`, `Nat.div_div_eq_div_mul`,
`Finset.sum_Ico_consecutive`.
**Source**: `colmez.txt:727` ("l'identité `v_p(n!) − v_p(⌊n/pʰ⌋!) = ∑_{ℓ=1}^h ⌊n/p^ℓ⌋`").

### [A-3] `min_padicValNat_eq_card` — done
**Statement**: `min h (padicValNat p x) = ((Icc 1 h).filter fun ℓ => p ^ ℓ ∣ x).card` for `x ≠ 0`.
**Sketch**: `p^ℓ ∣ x ↔ ℓ ≤ padicValNat p x` (`padicValNat_dvd_iff`), so the filter is
`Icc 1 (min h (padicValNat p x))`, of that cardinality.
**Lemmas**: `padicValNat.pow_dvd_iff` / `padicValNat_dvd_iff`, `Nat.card_Icc`.
**Source**: `colmez.txt:728–735` (`∑_k inf(v_p(j+k), h) = ∑_ℓ #{…}`).

### [CLEANUP-A1] `/cleanup PhD/LWX/AmiceValuation.lean` — done (after A-3)

### [A-4] `colmezPoly_eval_natCast` + `natDegree_colmezPoly` — done
**Statement**: `(colmezPoly h n).eval (j : ℚ_[p]) = ((n / p^h)! * j.choose n : ℕ)`; `natDegree = n`.
**Sketch**: `descPochhammer ℚ_[p] n` evaluated at `j` is `n! · C(j,n)`
(`descPochhammer_eval_coe_nat` / `Nat.descFactorial`), and `colmezPoly = C(⌊n/pʰ⌋!/n!) * descPochhammer`.
Degree: `natDegree_descPochhammer` and `C ≠ 0` (char zero).
**Lemmas**: `descPochhammer_eval_eq_descFactorial`, `Nat.descFactorial_eq_factorial_mul_choose`,
`Polynomial.natDegree_C_mul`, `natDegree_descPochhammer`.

### [A-5] `discPoly_eval` + `natDegree_discPoly_le` — done
**Statement**: `(discPoly h n a).eval w = (colmezPoly h n).eval (a + pʰ w)`; `natDegree ≤ n`.
**Sketch**: `Polynomial.eval_comp`; `natDegree_comp_le` with `natDegree (C a + C pʰ * X) = 1`.
**Lemmas**: `Polynomial.eval_comp`, `Polynomial.natDegree_comp_le`, A-4.
**Deps**: A-4.

### [A-6] `card_discSupport` — done
**Statement**: `(discSupport h n a).card = n / p^h + if a < n % p^h then 1 else 0` for `a < pʰ`.
**Sketch**: immediate from A-1 with `q = pʰ`, `r = a`.
**Deps**: A-1.

### [CLEANUP-A2] `/cleanup PhD/LWX/AmiceValuation.lean` — done (after A-6)

### [A-7] `descPochhammer_comp_eq_prod` — done
**Statement**: `(descPochhammer ℚ_[p] n).comp q = ∏ k ∈ range n, (q - C (k : ℚ_[p]))`.
**Sketch**: induction on `n` using `descPochhammer_succ_right` and `Polynomial.add_comp`,
`mul_comp`, `Finset.prod_range_succ`.
**Lemmas**: `descPochhammer_succ_right`, `Polynomial.mul_comp`, `Polynomial.sub_comp`.

### [A-8] `discPoly_eq` — done
**Statement**: `discPoly h n a = C (discConst h n a) * discFactor h n a` for `a < pʰ`.
**Sketch**: by A-7, `discPoly h n a = C(⌊n/pʰ⌋!/n!) * ∏_{k<n} (a − k + pʰ X)`.  Factor each
linear term: if `pʰ ∣ k − a` (i.e. `k % pʰ = a`) write `a − k + pʰX = pʰ·(X − (k−a)/pʰ)`; else
`a − k` is a unit multiple and `a − k + pʰX = (a − k)(1 + (pʰ/(a−k))X)`.  Collect the scalars into
`discConst`.
**Lemmas**: `Finset.prod_congr`, `Polynomial.C_mul`, `mul_div_cancel₀`.
**Source**: `colmez.txt:697` ("On a `g_{n,j} = c_{n,j} f_{n,j}`").
**Deps**: A-7.

### [A-9] `norm_coeff_discFactorTerm_le` + `norm_coeff_discFactor_le` — done
**Statement**: each normalised factor, and their product, have coefficients of norm `≤ 1`.
**Sketch**: for `k % pʰ = a` the factor is `X − C((k−a)/pʰ : ℕ)`, integral.  Otherwise the
coefficient is `pʰ/(a−k)`, and `‖a − k‖ ≥ p^{−(h−1)}·…`: since `pʰ ∤ (k − a)` we have
`v_p(a − k) < h`, so `‖pʰ/(a−k)‖ ≤ 1`.  Product: `Polynomial.coeff_prod` + ultrametric.
**Lemmas**: `Polynomial.coeff_prod`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`,
`PadicInt.norm_le_one`, `padicValNat_dvd_iff`.
**Deps**: A-8.

### [CLEANUP-A3] `/cleanup PhD/LWX/AmiceValuation.lean` — done (after A-9)

### [A-10] `norm_coeff_discFactor_le_inv_of_lt` — done
**Statement**: `‖(discFactor h n a).coeff i‖ ≤ p⁻¹` for `i > (discSupport h n a).card`.
**Sketch**: mod `p`, each factor with `k % pʰ ≠ a` reduces to `1` (its `X`-coefficient
`pʰ/(a−k)` has positive valuation, because `v_p(a−k) < h` gives `v_p(pʰ/(a−k)) ≥ 1`), so the
reduction of `discFactor` is `∏_{k ∈ discSupport} (X − β_k)`, of degree `|discSupport|`.
**Lemmas**: `Polynomial.coeff_prod`, degree bookkeeping via `Finset.prod`, `PadicInt.norm_le_one`.
**Source**: `colmez.txt:700–702` ("a pour réduction `f̄_{n,j} = ∏_{k∈K_{n,j}}(x − β_k)`").
**Deps**: A-9.

### [A-11] `norm_coeff_discFactor_card` — done
**Statement**: `‖(discFactor h n a).coeff (discSupport h n a).card‖ = 1`.
**Sketch**: the reduction is monic of that degree (A-10's computation), so the coefficient is a
unit.
**Deps**: A-10.

### [A-12] `norm_discConst` — done
**Statement**: `‖discConst h n a‖ = p⁻¹ ^ ((Icc 1 h).filter fun ℓ => a % p^ℓ < n % p^ℓ).card` for `a < pʰ`.
**Sketch**: `v_p(discConst) = v_p(⌊n/pʰ⌋!) − v_p(n!) + h·|discSupport| + ∑_{k ∉ discSupport} v_p(a−k)`.
Rewrite `h·|K| + ∑_{k∉K} v_p(a−k) = ∑_{k<n} min(h, v_p(a−k))`, then A-3 turns each summand into a
count and A-2 handles the factorials; Colmez's telescoping
`∑_{ℓ=1}^h (⌊(n+j−1)/p^ℓ⌋ − ⌊(j−1)/p^ℓ⌋ − ⌊n/p^ℓ⌋)` becomes, re-centred,
`#{1 ≤ ℓ ≤ h : a mod p^ℓ < n mod p^ℓ}` (each bracket is `0` or `1` and equals `1` exactly then).
**Lemmas**: A-1, A-2, A-3, `padicValNat_natCast`, `Nat.add_div_le_div_add`.
**Source**: `colmez.txt:722–740` (the displayed `v_p(c_{n,j})` formula and "chacun des termes de la
somme est `≥ 0`").
**Deps**: A-1, A-2, A-3.

### [CLEANUP-A4] `/cleanup PhD/LWX/AmiceValuation.lean` — done (after A-12)

### [A-13] `norm_discConst_le_one` + `norm_discConst_res` + `norm_discConst_le_inv_of_lt` — done
**Statement**: `‖c‖ ≤ 1` always; `= 1` at `a = n % pʰ`; `≤ p⁻¹` for `a < n % pʰ`.
**Sketch**: from A-12.  The count is `≥ 0` always; it is `0` at `a = n mod pʰ` because then
`a mod p^ℓ = n mod p^ℓ` for every `ℓ ≤ h` (as `a ≡ n mod pʰ`); it is `≥ 1` for `a < n mod pʰ`
because `ℓ = h` contributes.
**Lemmas**: `Nat.mod_mod_of_dvd`, `Finset.card_pos`, `Finset.card_eq_zero`.
**Source**: `colmez.txt:703–708` (the three bullet points).
**Deps**: A-12.

### [A-14] `norm_coeff_discPoly_le` — done
**Statement**: (i) of Lemme 1.4.9: `‖(discPoly h n a).coeff i‖ ≤ 1`.
**Sketch**: `discPoly = C(c)·f` (A-8), `‖c‖ ≤ 1` (A-13), `‖f.coeff‖ ≤ 1` (A-9).
**Deps**: A-8, A-9, A-13.

### [A-15] `norm_coeff_discPoly_le_inv_of_lt` + `norm_coeff_discPoly_le_inv_of_res_lt` — done
**Statement**: coefficients at degree `> ⌊n/pʰ⌋` are `p`-divisible on **every** disc; the
coefficient at degree `⌊n/pʰ⌋` is `p`-divisible on discs `a < n mod pʰ`.
**Sketch**: `|discSupport| = ⌊n/pʰ⌋ + [a < n mod pʰ]` (A-6).  If `a ≥ n mod pʰ` then
`|discSupport| = ⌊n/pʰ⌋` and A-10 gives the first claim directly.  If `a < n mod pʰ` then
`‖c‖ ≤ p⁻¹` (A-13) kills **all** coefficients, giving both claims at once.
**Note**: this routing through A-13 is required — A-10 alone is not enough when
`|discSupport| = ⌊n/pʰ⌋ + 1` (recorded in `decomposition.md`, attack A-2).
**Deps**: A-6, A-10, A-13.

### [CLEANUP-A5] `/cleanup PhD/LWX/AmiceValuation.lean` — done (after A-15)

### [A-16] `norm_coeff_discPoly_diag` — done
**Statement**: `‖(discPoly h n (n % p^h)).coeff (n / p^h)‖ = 1`.
**Sketch**: at `a = n mod pʰ`, `|discSupport| = ⌊n/pʰ⌋` (A-6) and `‖c‖ = 1` (A-13), so the
coefficient is `c` times the leading coefficient of the reduction (A-11), a unit.
**Source**: `colmez.txt:669` ("`deg(ḡ_{n,j}) = m(n)` si `j = i(n)`"), with `m(n) = ⌊n/pʰ⌋`.
**Deps**: A-6, A-11, A-13.

### [CLEANUP-A6] `/cleanup PhD/LWX/AmiceValuation.lean` — done (final, after A-16)
**Progress**: 2026-09-06T08:57 — group A complete.  `lake build` clean (2100 jobs), no sorries, no warnings,
`runLinter` clean on the module, `#print axioms` standard on `norm_discConst`, `discPoly_eq`,
`norm_coeff_discPoly_diag`, `norm_coeff_discPoly_le_inv_of_lt`.  Lines wrapped to ≤ 100.
Route notes for later boards: `Mathlib.Algebra.Polynomial.BigOperators` had to be added to the
imports (for `natDegree_prod_of_monic`); `mul_le_mul_right'` and `pow_le_pow_right_of_le_one` do
not exist here (`Nat.mul_le_mul_right`, `pow_le_pow_of_le_one`); `Nat.Ico_succ_right` is
`Finset.Ico_add_one_right_eq_Icc`; `push_neg` is deprecated in favour of `push Not`.
New private helpers, all reused across the group: `norm_p_lt_one`, `inv_p_le_one`, `sep`
(`|a − k|` as a natural, with `sep_eq_zero_iff`, `norm_natCast_sub_eq_sep`, `dvd_sep_iff`),
`norm_pow_le_norm_natCast_sub`, `norm_div_natCast_sub_le_inv`, `norm_coeff_mul_le`,
`norm_coeff_mul_le_one`, `norm_coeff_prod_sub_one`, `exists_discFactor_eq_add`.
The last one is the shape that discharges both A-10 and A-11: `f_{n,a} = F + F·G` with `F` monic
of degree `|K_{n,a}|` and `G` coefficientwise `≤ p⁻¹`.

---

## Group X — `PhD/LWX/PowSubOne.lean`

The extension formula (`lwx.txt:457–461`) and the analyticity threshold (`lwx.txt:882`).

### [X-1] `oneAddPow_natCast` + `norm_choose_intHom_le_one` — done
**Statement**: `oneAddPow T (n : K) = (1 + T)^n`; `‖Ring.choose (intHom ψ u) r‖ ≤ 1`.
**Sketch**: `Ring.choose (n : K) r = (n.choose r : ℕ)` (`Ring.choose_natCast`), so the series is
the finite binomial expansion (`add_pow`, terms vanish for `r > n`).  Second: `Ring.map_choose`
moves `Ring.choose` across `intHom ψ`, and `‖·‖ ≤ 1` on `ℤ_[p]`.
**Lemmas**: `Ring.choose_natCast` (`Binomial.lean:399`), `add_pow`, `Ring.map_choose`,
`PadicInt.norm_le_one`, `norm_intHom`.

### [X-2] `continuous_oneAddPow_intHom` — done
**Statement**: `Continuous fun u : ℤ_[p] => oneAddPow T (intHom ψ u)` for `‖T‖ < 1`.
**Sketch**: `continuous_tsum` with the uniform bound `‖Ring.choose (ψu) r · T^r‖ ≤ ‖T‖^r`
(X-1) and each term continuous by `PadicInt.continuous_choose` composed with the continuous
`intHom ψ`.
**Lemmas**: `continuous_tsum`, `PadicInt.continuous_choose` (`MahlerBasis.lean:93`),
`summable_geometric_of_lt_one`, `Ring.map_choose`.
**Deps**: X-1.

### [CLEANUP-X1] `/cleanup PhD/LWX/PowSubOne.lean` — done (after X-2)

### [X-3] `oneAddPow_pow_mul` — done (**key**)
**Statement**: `oneAddPow T (intHom ψ (p^h * u)) = oneAddPow ((1+T)^{p^h} − 1) (intHom ψ u)`.
**Sketch**: both sides are continuous in `u` (X-2, applied to `T` and to `(1+T)^{pʰ} − 1`, whose
norm is `< 1` by the ultrametric bound); on `u = (j : ℕ)` both equal `(1+T)^{p^h j}` by X-1 and
`pow_mul`.  `ℕ` is dense in `ℤ_[p]`, so `DenseRange.equalizer` closes it.
**Lemmas**: `PadicInt.denseRange_natCast`, `DenseRange.equalizer`, `pow_mul`, `map_natCast`.
**Source**: `lwx.txt:457–461` ("`χ(a·x) = χ(a)·χ(exp(pᵐ))^{(log x)/pᵐ}`").
**Deps**: X-1, X-2.

### [X-4] `norm_choose_prime_pow_le` — done
**Statement**: `‖((p^h).choose k : K)‖ ≤ ‖(p:K)‖^h * k` for `1 ≤ k ≤ p^h`.
**Sketch**: Kummer: `v_p(C(p^h,k)) = h − v_p(k)` (`Nat.emultiplicity_choose_prime_pow`), so
`‖C(p^h,k)‖ = ‖p‖^{h − v_p k} = ‖p‖^h · p^{v_p k} ≤ ‖p‖^h · k` since `p^{v_p k} ∣ k` and `k ≥ 1`.
**Lemmas**: `Nat.emultiplicity_choose_prime_pow (hp) (hkn : k ≤ p^n) (hk0 : k ≠ 0)`,
`norm_natCast_eq_pow_padicValNat` (`PadicExpLog.lean:77`, takes `h3`), `Nat.ordProj_le`.

### [X-5] `exists_norm_pow_prime_pow_sub_one_le` — done
**Statement**: `∃ B ≥ 0, ∀ h, ‖(1+T)^{p^h} − 1‖ ≤ ‖(p:K)‖^h * B`.
**Sketch**: `(1+T)^{p^h} − 1 = ∑_{k=1}^{p^h} C(p^h,k) T^k`; ultrametric + X-4 gives
`≤ ‖p‖^h · sup_{k ≥ 1} k‖T‖^k`, and that sup is finite for `‖T‖ < 1` (the sequence `k‖T‖^k` tends
to `0`).  Take `B` to be that sup.
**Lemmas**: `add_pow`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`,
`tendsto_self_mul_pow_atTop_nhds_zero` (or `isBoundedUnder` of a convergent sequence).
**Deps**: X-4.

### [CLEANUP-X2] `/cleanup PhD/LWX/PowSubOne.lean` — done (after X-5)

### [X-6] `tendsto_pow_prime_pow_sub_one` — done
**Statement**: `Tendsto (fun h => (1+T)^{p^h} − 1) atTop (𝓝 0)`.
**Sketch**: squeeze with X-5 and `‖p‖^h → 0` (`‖p‖ < 1`).
**Lemmas**: `squeeze_zero_norm`, `tendsto_pow_atTop_nhds_zero_of_lt_one`.
**Deps**: X-5.

### [X-7] `exists_sq_norm_pow_prime_pow_sub_one_lt` — done (**the threshold**)
**Statement**: `∃ h, ‖(1+T)^{p^h} − 1‖^2 < p⁻¹`.
**Sketch**: from X-6, eventually `‖T'_h‖ < p^{−1/2}`; `Metric.tendsto_atTop` at `ε = p^{−1/2}`.
**Source**: `lwx.txt:882` ("Choose `m ∈ ℕ` such that `r < p^{−q/pᵐ(p−1)}`").
**Deps**: X-6.

### [CLEANUP-X3] `/cleanup PhD/LWX/PowSubOne.lean` — done (final, after X-7)
**Progress**: 2026-09-06T09:07 — group X complete, but **two ticketed statements were replaced** (both logged in
`b2_log.jsonl`; the milestone statements are untouched):

* **X-4 `norm_choose_prime_pow_le` was FALSE as stated.**  It claimed
  `‖C(pʰ,k)‖ ≤ ‖p‖ʰ·k` over an arbitrary complete ultrametric `K`; the planning silently assumed
  the standard normalisation `‖p‖ = 1/p`, whereas the hypothesis is only `‖p‖ < 1`.
  Counterexample: `K = ℚ_p` with the equivalent norm `‖x‖' = ‖x‖_p²`, `h = 1`, `k = p`, where the
  left side is `1` and the right side is `p⁻¹`.  Replaced by the true one-step bound
  `norm_one_add_pow_prime_sub_one_le : ‖(1+T)^p − 1‖ ≤ max (‖p‖·‖T‖) (‖T‖^p)`.
* **X-5 `exists_norm_pow_prime_pow_sub_one_le` is true but was orphaned.**  Its only route went
  through X-4, and a direct proof needs a two-phase argument no downstream leaf consumes.
  Replaced by `norm_pow_prime_pow_sub_one_le : ‖(1+T)^{pʰ} − 1‖ ≤ max(‖p‖, ‖T‖^{p−1})ʰ · ‖T‖`,
  the iteration of the one-step bound, which yields X-6 and X-7 directly.

Everything downstream (X-6 `tendsto_pow_prime_pow_sub_one`, X-7
`exists_sq_norm_pow_prime_pow_sub_one_lt`) keeps its ticketed statement verbatim.
`lake build` clean (2605 jobs), no sorries, no warnings, `#print axioms` standard on
`oneAddPow_pow_mul` and `exists_sq_norm_pow_prime_pow_sub_one_lt`; lines ≤ 100.
New public helpers: `norm_one_add_le`, `norm_one_add_pow_sub_one_le` (both reused by the density
argument in `oneAddPow_pow_mul` and available to `HaloWeightH`).  Import added:
`Mathlib.Analysis.Normed.Group.FunctionSeries` (for `continuous_tsum`).

---

## Group AB — `PhD/LWX/AmiceBasis.lean` (Colmez, Théorème 1.4.7 = Amice)

Source: `colmez.txt:634–635` (statement), `colmez.txt:673–682` (proof strategy),
`colmez.txt:621–627` (Lemme 1.4.5, which *is* the disc model, taken as a definition here).

### [AB-1] `revIdx` + `revIdx_div` + `revIdx_mod` — done
**Statement**: `revIdx q : ℕ ≃ ℕ`, `n ↦ ⌊n/q⌋q + (q−1−n mod q)`, an involution; it preserves
`⌊·/q⌋` and reverses `· mod q`.
**Sketch**: `q − 1 − n%q < q`, so `divMod` of the image is `(⌊n/q⌋, q−1−n%q)`
(`Nat.add_mul_div_left`, `Nat.add_mul_mod_self_left`); involutivity is
`q − 1 − (q − 1 − n%q) = n%q` for `n%q ≤ q−1`.
**Lemmas**: `Nat.add_mul_div_left`, `Nat.add_mul_mod_self_left`, `Nat.sub_sub_self`, `omega`.

### [AB-2] `discIdx` — done
**Statement**: `discIdx h : ZMod (p^h) × ℕ ≃ ℕ`, `(a,k) ↦ k·pʰ + (pʰ − 1 − a.val)`.
**Sketch**: same divmod computation as AB-1, plus `ZMod.val_lt` and `ZMod.natCast_val` /
`ZMod.natCast_rightInverse` to round-trip the residue.
**Lemmas**: `ZMod.val_lt`, `ZMod.natCast_zmod_val`, `Nat.sub_sub_self`.
**Source**: `colmez.txt:678–680` ("blocs de taille `pʰ × pʰ` … triangulaire supérieure par blocs
… chacun des blocs diagonaux triangulaire inférieur").

### [AB-3] `discIdx_res_div` — done
**Statement**: `discIdx h ((n % p^h : ℕ), n / p^h) = revIdx (p^h) n`.
**Sketch**: `((n % p^h : ℕ) : ZMod (p^h)).val = n % p^h` by `ZMod.val_natCast_of_lt`; then both
sides are `⌊n/pʰ⌋pʰ + (pʰ − 1 − n mod pʰ)` by definition.
**Lemmas**: `ZMod.val_natCast_of_lt`, `Nat.mod_lt`.
**Note**: an earlier draft stated `= n`, which is **false** — see `decomposition.md`, group AB,
"Defect found and fixed".
**Deps**: AB-1, AB-2.

### [CLEANUP-AB1] `/cleanup PhD/LWX/AmiceBasis.lean` — done (after AB-3)

### [AB-4] `lt_discIdx_iff` — done
**Statement**: `revIdx (p^h) n < discIdx h x ↔ n / p^h < x.2 ∨ (x.2 = n / p^h ∧ x.1.val < n % p^h)`.
**Sketch**: both sides are `k·pʰ + s` with `s < pʰ`; compare lexicographically on `(k, s)` and
note `s` is the *reversed* residue on both sides, so the inner comparison flips.
**Lemmas**: `Nat.add_lt_add_iff_left`, `Nat.div_add_mod`, `omega`.
**Deps**: AB-1, AB-2.

### [AB-5] `isUnitriangularPerturbation_colmezMatrix` — done (**the junction A ⋈ U**)
**Statement**: `IsUnitriangularPerturbation (colmezMatrix ψ h) (p:ℝ)⁻¹`.
**Sketch**: five fields.  `q_pos`/`q_lt_one`: `0 < p⁻¹ < 1` (`inv_pos.mpr`,
`inv_lt_one_of_one_lt₀`; note `positivity` cannot do `0 < (p:ℝ)⁻¹` for `p : ℕ`).
`norm_le_one`: A-14 through `hψ`.  `norm_diag`: at `k = n` the position `(discIdx h).symm n` is
the diagonal position of column `revIdx n` (AB-3 + AB-2's round trip), so A-16 applies.
`norm_le_of_lt`: `n < k` gives, by AB-4, either degree `> ⌊·/pʰ⌋` (A-15 first half) or the
boundary case (A-15 second half).  `col_finite`: `natDegree_discPoly_le` (A-5) bounds the support.
**Deps**: A-5, A-14, A-15, A-16, AB-3, AB-4.

### [AB-6] `norm_comap_equiv` + `surjective_comap_equiv` — done
**Statement**: reindexing along a bijection is an isometry and is surjective.
**Sketch**: `cSpace.comap φ f = f ∘ φ`; for a bijection the sup over the index set is unchanged
(`Equiv.iSup_comp` / `Set.range_comp`), and the inverse reindexing is a right inverse.
**Lemmas**: `cSpace.comap` (`BlockOp.lean:89`), `cSpace.norm_le_of_forall`, `Equiv.surjective`.

### [CLEANUP-AB2] `/cleanup PhD/LWX/AmiceBasis.lean` — done (after AB-6)

### [AB-7] `matrixCoeff_colmezToDisc` — done
**Statement**: `matrixCoeff (colmezToDisc ψ hψ h) x n = ψ (discCoeff h n x)`.
**Sketch**: unfold the triple composition.  `comap (revIdx) (single n 1) = single (revIdx n) 1`
(involution); `ofPerturbation` reads off column `revIdx n`; `comap (discIdx h)` evaluates the row
at `discIdx h x`; `(discIdx h).symm (discIdx h x) = x` and `revIdx (revIdx n) = n`, so the two
reversals cancel.
**Lemmas**: `matrixCoeff_comp`, `matrixCoeff_ofPerturbation`, `cSpace.comap` computation,
`Equiv.symm_apply_apply`.
**Deps**: AB-1, AB-5, AB-6.

### [AB-8] `colmezToDisc_apply` — done
**Statement**: `colmezToDisc ψ hψ h c x = ∑' n, ψ (discCoeff h n x) * c n`.
**Sketch**: `ofCoeffs_apply` through the two reindexings, then reindex the sum by the bijection
`revIdx` (`Equiv.tsum_eq`).
**Lemmas**: `ofPerturbation_apply`, `Equiv.tsum_eq`.
**Deps**: AB-7.

### [AB-9] `norm_colmezToDisc` — done (**Amice, isometry half**)
**Statement**: `‖colmezToDisc ψ hψ h c‖ = ‖c‖`.
**Sketch**: `norm_ofPerturbation` (U-3) sandwiched between the two isometric reindexings (AB-6).
**Source**: `colmez.txt:634–635`.
**Deps**: U-3, AB-6.

### [CLEANUP-AB3] `/cleanup PhD/LWX/AmiceBasis.lean` — done (after AB-9)

### [AB-10] `surjective_colmezToDisc` + `injective_colmezToDisc` — done
**Statement**: `colmezToDisc` is bijective.
**Sketch**: `surjective_ofPerturbation` (U-4/U-6) composed with the surjective reindexings
(AB-6); injectivity from AB-9.
**Deps**: U-6, U-7, AB-6, AB-9.

### [AB-11] `colmezDiscEquiv` — done (**Amice's theorem**)
**Statement**: `c(ℕ,K) ≃L[K] c(ZMod (p^h) × ℕ, K)`.
**Sketch**: `LinearEquiv.ofBijective` + `AddMonoidHomClass.continuous_of_bound e.symm 1`, the
bound coming from AB-9 exactly as in `equivOfPerturbation` (U-8).
**Source**: `colmez.txt:634–635`; `lwx.txt:950–959`.
**Deps**: AB-9, AB-10.

### [AB-12] `diagFactorialH` — done
**Statement**: the two `ofCoeffs` side conditions for `diag(⌊m/pʰ⌋!)`.
**Sketch**: entries are `0` or a natural number cast, so `‖·‖ ≤ 1`
(`IsUltrametricDist.norm_natCast_le_one`); each column has a single nonzero entry, so
`Tendsto … cofinite (𝓝 0)`.  Transcribes `diagFactorial` (`Colmez.lean:397`).
**Lemmas**: `IsUltrametricDist.norm_natCast_le_one`, `Filter.eventually_cofinite`.

### [CLEANUP-AB4] `/cleanup PhD/LWX/AmiceBasis.lean` — done (after AB-12)

### [AB-13] `discToMahler_colmezToDisc` — done
**Statement**: `discToMahler ψ hψ h (colmezToDisc ψ hψ h c) m = (⌊m/pʰ⌋! : K) * c m`.
**Sketch**: `colmezDiscEquiv.symm ∘ colmezToDisc = id`, then `matrixCoeff_diagFactorialH` and
`tsum_eq_single`.
**Deps**: AB-11, AB-12.

### [AB-14] `discCoord` + `appr_add_pow_mul_discCoord` — done
**Statement**: `discCoord h z ∈ ℤ_[p]` and `appr z h + pʰ · discCoord h z = z`.
**Sketch**: `PadicInt.appr_spec` gives `z − appr z h ∈ (pʰ)`, so the quotient has norm `≤ 1`;
the identity is then division cancellation in `ℚ_[p]` (`p ≠ 0`) lifted by `Subtype.ext`.
**Lemmas**: `PadicInt.appr_spec`, `Ideal.mem_span_singleton`, `PadicInt.norm_le_pow_iff_mem_span_pow`.

### [AB-15] `appr_natCast` + `discCoord_natCast` — done
**Statement**: `(j : ℤ_[p]).appr h = j % p^h`; `discCoord h (j : ℤ_[p]) = ((j / p^h : ℕ) : ℤ_[p])`.
**Sketch**: `appr` is characterised by `appr x h < p^h` and `x − appr x h ∈ (p^h)`
(`PadicInt.appr_lt`, `appr_spec`) — both hold for `j % p^h`, and the characterisation is unique
(`PadicInt.zmod_congr_of_sub_mem_span`).  Then `discCoord` is `(j − j%pʰ)/pʰ = ⌊j/pʰ⌋`.
**Lemmas**: `PadicInt.appr_lt`, `PadicInt.appr_spec`, `PadicInt.zmod_congr_of_sub_mem_span`,
`Nat.div_add_mod`.
**Deps**: AB-14.

### [CLEANUP-AB5] `/cleanup PhD/LWX/AmiceBasis.lean` — done (after AB-15)

### [AB-16] `discEval_colmezToDisc_natCast` — done
**Statement**: `discEval ψ h (colmezToDisc ψ hψ h c) (j : ℤ_[p]) = ∑' n, c n * (⌊n/pʰ⌋! * C(j,n) : ℕ)`.
**Sketch**: by AB-15 the disc of `j` is `j mod pʰ` and the coordinate is `⌊j/pʰ⌋`; by AB-8 the
Taylor coefficients on that disc are `ψ(discCoeff h n x)`, so `evalAt` of the Taylor series at
`⌊j/pʰ⌋` is `∑' n c n · ψ((discPoly h n (j mod pʰ)).eval ⌊j/pʰ⌋)`, and `discPoly_eval` (A-5) plus
`colmezPoly_eval_natCast` (A-4) evaluate that to `⌊n/pʰ⌋!·C(j,n)`.  Interchange of the two sums is
by absolute summability.
**Lemmas**: A-4, A-5, AB-8, AB-15, `evalAt`, `tsum_comm` / `Summable.tsum_mul_left`.
**Deps**: A-4, A-5, AB-8, AB-15.

### [AB-17] `discToMahler_apply_eq_fwdDiff` — done (**the level-`h` Mahler bridge**)
**Statement**: `discToMahler ψ hψ h f m = Δ_[1]^[m] (fun j : ℕ => discEval ψ h f (j : ℤ_[p])) 0`.
**Sketch**: both sides are continuous linear in `f`, so check on `f = colmezToDisc (single n 1)`
(AB-11).  Left side is `⌊n/pʰ⌋!·[m = n]` (AB-13).  Right side is
`⌊n/pʰ⌋!·Δ^m (j ↦ C(j,n)) 0 = ⌊n/pʰ⌋!·[m = n]` by AB-16 and `fwdDiff_iter_choose_zero`.
**Lemmas**: `fwdDiff_iter_choose_zero` (`ForwardDiff.lean:197`), `fwdDiff_iter_eq_sum_shift`,
AB-13, AB-16.
**Deps**: AB-11, AB-13, AB-16.

### [CLEANUP-AB6] `/cleanup PhD/LWX/AmiceBasis.lean` — done (final, after AB-17)
**Progress**: 2026-09-06T09:35 — group AB complete: **Amice's theorem at level `h` is proved**
(`colmezDiscEquiv`, sorry-free).  `lake build` clean (2609 jobs), no sorries, no warnings,
lines within 100 chars, `#print axioms` standard on `colmezDiscEquiv`, `norm_colmezToDisc`,
`isUnitriangularPerturbation_colmezMatrix`, `discToMahler_apply_eq_fwdDiff`.

Route notes:
* The index arithmetic had to be factored through **variable-modulus** natural-number lemmas
  (`sub_one_sub_lt`, `div_mul_add_mod`, `div_mul_add_sub_sub`, `lt_add_sub_iff`): `omega` cannot
  see inside `x / q`, `x % q` or `q - 1 - r` when the modulus is `p ^ h` rather than a bare
  variable, so every such step is stated once over a variable `q` and applied at `q = p ^ h`.
* AB-16 (`discEval_colmezToDisc_natCast`) needs a genuine **double-sum interchange**.  The
  family `(k, n)` maps to `psi(discCoeff h n (a,k)) * c n * w^k`; it vanishes off `k <= n` and is
  bounded by the norm of `c n`, so summability comes from
  `TateFredholm.summable_of_tendsto_cofinite` and the swap from `Summable.tsum_comm` --- which
  must be given its curried function **explicitly** (`f := fun k n => ...`), otherwise the
  higher-order unification blows the `whnf` heartbeat budget.
* AB-17 needs `fwdDiff_iter_choose_zero` over `K`; mathlib only has the integer-valued form, so
  it is transported by `LWX.map_fwdDiff_iter` (`Colmez.lean:118`) along `Int.castAddHom K`.
* Do not `show`-unfold `colmezToDisc`: it carries the `IsUnitriangularPerturbation` proof term,
  and forcing `whnf` through it times out.  Use `rw [discEval]` and the proved
  `colmezToDisc_apply` instead.

---

## Group WH — `PhD/LWX/HaloWeightH.lean`

The level-`h` halo weight.  Every leaf mirrors the corresponding declaration of
`PhD/LWX/HaloWeight.lean` (the `h = 0` case, sorry-free); the mirror is stated per ticket, and
**the `h = 0` proof should be read first and adapted, not re-invented**.
Source: `lwx.txt:455–461` (the extension formula), `lwx.txt:610–613` (the level).

### [WH-1] `Mh` — done
**Mirror**: `M1` (`IntegralModel.lean:226`).  Two `Submonoid` fields.
**Sketch**: same computation with `p⁻¹` replaced by `(p⁻¹)^{h+1}`; the `c`-entry of a product is
`g₁₀h₀₀ + g₁₁h₁₀`, both terms `≤ (p⁻¹)^{h+1}`.
### [WH-2] `Mh_le_M1` — done. `(p⁻¹)^{h+1} ≤ p⁻¹` (`pow_le_pow_right_of_le_one`).
### [WH-3] `Mh_zero` — done. `Submonoid.ext`; `(p⁻¹)^1 = p⁻¹` (`pow_one`).
### [CLEANUP-WH1] `/cleanup PhD/LWX/HaloWeightH.lean` — done (after WH-3)
### [WH-4] `M1Kh_le_M1K` — done. `Submonoid.map_le_map_of_le` from WH-2.
### [WH-5] `norm_apply_le_one_of_mem_M1Kh` — done. Mirror `mem_M1K_iff` unfolding + `hψ`.
### [WH-6] `norm_apply_one_zero_le_of_mem_M1Kh` — done. Mirror `norm_apply_one_zero_le_of_mem_M1K`.
### [CLEANUP-WH2] `/cleanup PhD/LWX/HaloWeightH.lean` — done (after WH-6)
### [WH-7] `norm_apply_one_one_of_mem_M1Kh` — done. Mirror `norm_apply_one_one_of_mem_M1K`.
### [WH-8] `haloUnitsH` — done. Mirror `haloUnits` (`HaloWeight.lean:197`), three `Subgroup`
fields; the ultrametric computations are identical with `p⁻¹ → (p⁻¹)^{h+1}`.
### [WH-9] `haloUnitsH_le_haloUnits` — done. `(p⁻¹)^{h+1} ≤ p⁻¹`.
### [CLEANUP-WH3] `/cleanup PhD/LWX/HaloWeightH.lean` — done (after WH-9)
### [WH-10] `isUnit_natCast_val_pow` — done. Mirror `isUnit_natCast_val`: `r ∈ (ZMod (p^{h+1}))ˣ`
⇒ `p ∤ r.val` ⇒ `‖(r.val : ℤ_[p])‖ = 1` ⇒ unit (`PadicInt.isUnit_iff`, `ZMod.isUnit_iff_coprime`).
### [WH-11] `toZModPow_repLift` — done. `PadicInt.toZModPow_natCast` + `ZMod.natCast_val` /
`ZMod.natCast_rightInverse`, then `Units.ext`.
### [WH-12] `repLift_injective` — done. From WH-11 (`toZModPow ∘ repLift = id`).
### [CLEANUP-WH4] `/cleanup PhD/LWX/HaloWeightH.lean` — done (after WH-12)
### [WH-13] `norm_sub_repLift_le` — done. `ker_toZModPow` (`RingHoms.lean:459`) +
`PadicInt.norm_le_pow_iff_mem_span_pow`; mirror `norm_sub_teichRes_le`.
### [WH-14] `norm_intHom_repLift` — done. `norm_intHom` + `PadicInt.norm_units`.
### [WH-15] `repLift_eq_of_norm_sub_le` — done. Mirror `teichRes_eq_of_norm_sub_le` with
`toZModPow (h+1)` in place of `toZMod`.
### [CLEANUP-WH5] `/cleanup PhD/LWX/HaloWeightH.lean` — done (after WH-15)
### [WH-16] `exists_unique_repLift_of_mem_haloUnitsH` — done. Mirror
`exists_unique_teichRes_of_mem_haloUnits` (WH-13 for existence, WH-15 for uniqueness).
### [WH-17] `TH_zero` + `haloExponentH_zero` — done. `pow_zero`, `pow_one`; identifies the `h = 0`
case with `HaloWeight.haloExponent`.
### [WH-18] `norm_haloExponentH` — done. Mirror `norm_haloExponent`: `norm_padicLog_eq` gives
`‖log(1+T'_h)‖ = ‖T'_h‖`, then divide by `‖p‖^{h+1}`.
### [CLEANUP-WH6] `/cleanup PhD/LWX/HaloWeightH.lean` — done (after WH-18)
### [WH-19] `norm_haloExponentH_mul_padicLog_le` — done. Mirror
`norm_haloExponent_mul_padicLog_le`: `‖log x‖ ≤ ‖x−1‖ ≤ (p⁻¹)^{h+1}` and WH-18.
### [WH-20] `sq_norm_haloExponentH_mul_padicLog_lt` — done. From WH-19 and `hT`.
### [WH-21] `norm_padicExp_haloExponentH_mul_padicLog` — done.
`PadicExpLog.norm_eq_one_of_norm_sub_one_lt_one` + `norm_padicExp_sub_one_le` with WH-20.
### [CLEANUP-WH7] `/cleanup PhD/LWX/HaloWeightH.lean` — done (after WH-21)
### [WH-22] `unitsMap_toZMod_eq_one_of_norm_sub_one_le` — done.
`norm_le_inv_iff_toZMod_eq_zero` applied to `u − 1`, then `Units.ext`.
### [WH-23] `teichmuller_eq_one_of_norm_sub_one_le` — done. `teichRes_toZMod` /
`unitsMap_toZMod_teichmuller` with WH-22 and `teichmuller_one`.
### [WH-24] `coe_logQuot_of_norm_sub_one_le` — done. `logQuot` unfolds to
`qlog (oneUnitPart u)/p`, and `oneUnitPart u = u` by WH-23.
### [CLEANUP-WH8] `/cleanup PhD/LWX/HaloWeightH.lean` — done (after WH-24)
### [WH-25] `exists_pow_mul_eq_logQuot` — done.
**Sketch**: by WH-24, `ℓ⟨u⟩ = log(u)/p`; `norm_padicLog_eq` gives `‖log u‖ = ‖u−1‖ ≤ p^{−(h+1)}`,
so `log(u)/p^{h+1} ∈ ℤ_p` and `ℓ⟨u⟩ = pʰ · (log u/p^{h+1})`.
**Deps**: WH-24.
### [WH-26] `specialize_univChar_eq_padicExp` — done (**junction with X-3**)
**Statement**: for `‖u − 1‖ ≤ p^{−(h+1)}`,
`HaloInt.specialize (intHom ψ) T₀ (univChar ω u) = padicExp (s_h · log (intHom ψ u))`.
**Sketch**: `specialize_univChar` (`Specialize.lean:216`) gives
`ψ(ω(ū))·oneAddPow T₀ (ψ(ℓ⟨u⟩))`.  `ū = 1` by WH-22, so the first factor is `1`.  By WH-25,
`ℓ⟨u⟩ = pʰ v`, so X-3 rewrites `oneAddPow T₀ (ψ(pʰ v)) = oneAddPow (T'_h) (ψ v)`.  Finally the
binomial theorem `hasSum_choose_mul_pow` (`Binomial.lean:464`) at `c = ‖T'_h‖` identifies that
with `padicExp (ψ(v)·log(1+T'_h)) = padicExp (s_h · log ψ(u))` using `map_padicLog` and
`ψ(v) = ψ(log u)/‖p‖^{h+1}`.
**Deps**: X-3, WH-22, WH-25.
### [CLEANUP-WH9] `/cleanup PhD/LWX/HaloWeightH.lean` — done (after WH-26)
### [WH-27] `haloCharFunH_of_norm_sub_le` — done. Mirror `haloCharFun_of_norm_sub_le`: the sum has
at most one nonzero term by WH-15.
### [WH-28] `haloCharFunH_one` — done. Mirror `haloCharFun_one` (`r = 1`, `padicLog 1 = 0`).
### [WH-29] `haloCharFunH_mul` — done. Mirror `haloCharFun_mul`: `univChar_mul`, `padicLog_mul`,
`padicExp_add`, using WH-20 for the `exp` hypotheses.
### [CLEANUP-WH10] `/cleanup PhD/LWX/HaloWeightH.lean` — done (after WH-29)
### [WH-30] `norm_haloCharFunH` — done. Mirror `norm_haloCharFun` via WH-21 and WH-14.
### [WH-31] `haloCharFunH_psi` — done (**the character is the specialised universal character**).
**Sketch**: write `a = repLift r · u` with `u` a `1`-unit mod `p^{h+1}` (WH-13), use
`univChar_mul`, `specialize_mul`, and WH-26 on the `u` factor; the `repLift r` factor is the
defining summand of `haloCharFunH`.
**Deps**: WH-26, WH-27.
### [WH-32] `haloCharH` — done. Mirror `haloChar`: three `MonoidHom` fields from WH-28/29/30.
### [CLEANUP-WH11] `/cleanup PhD/LWX/HaloWeightH.lean` — done (after WH-32)
### [WH-33] `haloRhoH_nonneg` — done. `mul_nonneg`, `Real.sqrt_nonneg`.
### [WH-34] `haloRhoH_lt_one` — done. `max(p^{−(h+1)}, ‖T'_h‖)²·p < 1`: the first branch gives
`p^{−2(h+1)+1} ≤ p⁻¹ < 1`, the second is `hT`.  Mirror `haloRho_lt_one` (uses
`lt_of_pow_lt_pow_left₀`, `Real.sq_sqrt`).
### [WH-35] `inv_pow_le_haloRhoH` + `norm_TH_le_haloRhoH` — done. `le_max_left/right` and
`1 ≤ √p` (`Real.sqrt_le_sqrt`, `Real.sqrt_one`).
### [CLEANUP-WH12] `/cleanup PhD/LWX/HaloWeightH.lean` — done (after WH-35)
### [WH-36] `mem_haloUnitsH_of_mem_M1Kh` — done. Mirror `mem_haloUnits_of_mem_M1K` (use the
`obtain ⟨d, hd⟩ : ∃ d : ℤ_[p], (d : ℚ_[p]) = δ 1 1` trick to avoid the `Monoid {x // ‖x‖ ≤ 1}`
instance trap recorded in the `lwx-seam` notes).
### [WH-37] `norm_div_mul_le_of_mem_M1Kh` — done. Mirror `norm_div_mul_le_of_mem_M1K`.
### [WH-38] `norm_choose_haloExponentH_mul_pow_le` — done (**row decay**).
**Sketch**: mirror `norm_choose_haloExponent_mul_pow_le`.  `‖C(s_h, m)‖ ≤ ‖s_h‖^m/‖m!‖` and
`sq_norm_factorial_ge` bound `‖m!‖`; with `‖s_h‖ = p^{h+1}‖T'_h‖` (WH-18) and
`‖w‖ ≤ p^{−(h+1)}`, the product is `≤ (‖T'_h‖√p)^m ≤ haloRhoH^m`.
**Deps**: WH-18, WH-35.
### [CLEANUP-WH13] `/cleanup PhD/LWX/HaloWeightH.lean` — done (after WH-38)
### [WH-39] `norm_coeff_haloColH_le` — done. Mirror `norm_coeff_haloCol_le`: WH-38 for the
binomial part, and multiplying by `(cz+d)²` (coefficients `d², 2cd, c²`) preserves the bound since
`p^{−(h+1)} ≤ haloRhoH` (WH-35).
**Deps**: WH-30, WH-38.
### [WH-40] `evalAt_mk_choose_haloExponentH` — done. Mirror `evalAt_mk_choose_haloExponent`:
`hasSum_choose_mul_pow` at `c = ‖T'_h‖`, then WH-27.
**Deps**: WH-27, WH-38.
### [WH-41] `haloCharFunH_mul_one_add` — done. Mirror `haloCharFun_mul_one_add` from WH-29.
### [CLEANUP-WH14] `/cleanup PhD/LWX/HaloWeightH.lean` — done (after WH-41)
### [WH-42] `evalAt_haloColH` — done. Mirror `evalAt_haloCol`: `evalAt_mul`/`evalAt_pow` with the
`AbsSummable` side conditions from WH-38, then WH-40 and WH-41.
**Deps**: WH-39, WH-40, WH-41.
### [WH-43] `autFactor_haloWeightH` — done. Mirror `autFactor_haloWeight` (the `linX·linX⁻¹`
cancellation; `PowerSeries.mul_inv_cancel` at `constantCoeff = d ≠ 0`).
### [WH-44] `evalAt_autFactor_haloWeightH` — done. Mirror `evalAt_autFactor_haloWeight`.
**Deps**: WH-42, WH-43.
### [CLEANUP-WH15] `/cleanup PhD/LWX/HaloWeightH.lean` — done (final, after WH-44)

---

## Group D — `PhD/LWX/DiscModel.lean`

The disc action.  Source: `lwx.txt:630–639`.

### [D-1] `discConjMat_mem_Mh` — done (**the conjugation is integral**)
**Statement**: `discConjMat h δ a ∈ Mh p h`.
**Sketch**: four clauses.  `a`-entry `δ₀₀ − a'δ₁₀`: integral (ultrametric).  `c`-entry `δ₁₀pʰ`:
`‖δ₁₀‖ ≤ p⁻¹` gives `≤ p^{−(h+1)}`.  `d`-entry `δ₁₀a + δ₁₁`: `‖δ₁₀a‖ ≤ p⁻¹ < 1 = ‖δ₁₁‖`, so
`norm_add_eq_max_of_norm_ne_norm` gives `= 1`.  `b`-entry: rewrite
`δ₀₀a + δ₀₁ − a'(δ₁₀a + δ₁₁) = (δ₁₀a + δ₁₁)·(möb δ (a) − a')`, whose norm is `≤ p^{−h}` because
`a' = toZModPow h (möb δ a)` (`ker_toZModPow`); divide by `pʰ`.  Determinant:
`det (t_{a'}⁻¹ δ t_a) = det δ ≠ 0`.
**Lemmas**: `IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm`, `PadicInt.ker_toZModPow`,
`PadicInt.norm_le_pow_iff_mem_span_pow`, `LocalMat.mobiusFun`, `Matrix.det_fin_two_of`.
**Source**: `lwx.txt:610–613`.

### [D-2] `denUnit_discConj` — done
**Statement**: `den_{δ'}(w) = den_δ(a + pʰw)` as elements of `ℤ_[p]`.
**Sketch**: `c'w + d' = δ₁₀pʰw + δ₁₀a + δ₁₁ = δ₁₀(a + pʰw) + δ₁₁`; `ring` after
`M1.coe_toLocalMat_c/_d` and `Subtype.ext`.
**Deps**: D-1.

### [D-3] `mobiusFun_add_pow_mul` — done (**the conjugation identity**)
**Statement**: `möb δ (a + pʰw) = a' + pʰ·möb δ' (w)`.
**Sketch**: over `ℚ_[p]`, `möb δ (a + pʰw) = (δ₀₀(a+pʰw) + δ₀₁)/(δ₁₀(a+pʰw) + δ₁₁)`, and by D-2
the denominator is `c'w + d'`.  Subtract `a'` and simplify: the numerator becomes
`pʰ(δ'₀₀ w + δ'₀₁)` by the definition of `discConjMat`.  Then divide by `pʰ` and lift to `ℤ_[p]`
by `Subtype.ext` (both sides are integral).
**Lemmas**: `coe_mobiusFun` (private in `IntegralModel.lean:557` — restate locally if needed),
`field_simp`, `ring`.
**Deps**: D-1, D-2.

### [CLEANUP-D1] `/cleanup PhD/LWX/DiscModel.lean` — done (after D-3)

### [D-4] `toZModPow_mobiusFun` — done
**Statement**: `toZModPow h (möb δ z) = discImage h δ (toZModPow h z)`.
**Sketch**: write `z = a + pʰw` with `a = appr z h` (AB-14), apply D-3, and `toZModPow h` kills
the `pʰ`-multiple.
**Deps**: AB-14, D-3.

### [D-5] `discImage_one` + `discConj_one` — done
**Sketch**: `möb 1 = id`, so `a' = a`; then `discConjMat h 1 a = !![1, 0; 0, 1]` by direct
computation (`Subtype.ext`, `Matrix.ext`, `fin_cases`).

### [D-6] `discImage_mul` — done
**Statement**: `discImage h (δ₁δ₂) a = discImage h δ₁ (discImage h δ₂ a)`.
**Sketch**: `möb (δ₁δ₂) = möb δ₁ ∘ möb δ₂` (`mobius_cocycle`), then D-4.
**Deps**: D-4.

### [CLEANUP-D2] `/cleanup PhD/LWX/DiscModel.lean` — done (after D-6)

### [D-7] `discConj_mul` — done (**the matrix cocycle**)
**Statement**: `discConj h (δ₁δ₂) a = discConj h δ₁ (discImage h δ₂ a) · discConj h δ₂ a`.
**Sketch**: both sides are `t_{a''}⁻¹δ₁δ₂t_a` written two ways; since `t_{a'}` is invertible over
`ℚ_[p]` (determinant `pʰ ≠ 0`), the identity is `Matrix.ext` + `field_simp` + `ring` on the four
entries, using D-6 to identify the intermediate disc.
**Deps**: D-6.

### [D-8] `matrixCoeff_discSlash` + `blockProj_discSlash` — done
**Sketch**: `matrixCoeff_blockOp` and `blockOp_blockIncl` with the `if`.
**Lemmas**: `matrixCoeff_blockOp` (`BlockOp.lean:646`), `cSpace.blockProj_blockIncl`.

### [D-9] `discSlash_one` — done. From D-5 and `AnalyticWeight.kappaSlash_one`, then
`ext_matrixCoeff` against `matrixCoeff_id`.
**Deps**: D-5, D-8.

### [CLEANUP-D3] `/cleanup PhD/LWX/DiscModel.lean` — done (after D-9)

### [D-10] `discSlash_mul` — done
**Statement**: `discSlash (δ₁δ₂) = (discSlash δ₂).comp (discSlash δ₁)`.
**Sketch**: `blockOp_comp` turns the right side into a `blockOp` whose `(a,c)` block is
`∑_b [c = discImage δ₂ b]·[b = discImage δ₁ a]·kappaSlash(δ₂'_b) ∘ kappaSlash(δ₁'_a)`; only
`b = discImage δ₁ a` survives, and `AnalyticWeight.kappaSlash_mul` with D-7 identifies the
composite with `kappaSlash ((δ₁δ₂)'_a)`.  Careful with the variance:
`kappaSlash (g*h) = (kappaSlash h).comp (kappaSlash g)`.
**Lemmas**: `blockOp_comp` (`BlockOp.lean:691`), `AnalyticWeight.kappaSlash_mul`
(`Char.lean:826`), `Finset.sum_ite_eq`.
**Deps**: D-6, D-7, D-8.

### [D-11] `discSlashAction` + `discSMulSlashClass` — done
**Sketch**: the four `RightSlashAction` fields from D-9, D-10 and linearity of `blockOp`; the
`SMulSlashClass` field is `map_smul` of a continuous linear map.  Mirror `seqSlashAction` /
`cfunSMulSlash` (`IntegralModel.lean:1284`, `:695`) and `AnalyticWeight.kappaSlashAction`.
**Deps**: D-9, D-10.

### [D-12] `isCompactoid_discSlash` — done
**Sketch**: `isCompactoid_blockOp` blockwise; each nonzero block is
`κ.kappaSlash (discConjK h δ a ψ)` and `‖δ'₀₀‖ = ‖δ₀₀ − a'δ₁₀‖ ≤ max(p⁻¹, p⁻¹) = p⁻¹ ≤ σ`, so
`WeightSeries.isCompactoid_kappaSlash` applies at `σ = max ρ p⁻¹`.
**Lemmas**: `isCompactoid_blockOp` (`BlockOp.lean:675`),
`WeightSeries.isCompactoid_kappaSlash (ha : ‖g.1 0 0‖ ≤ σ)` (`SlashAction.lean:394`).
**Deps**: D-1, D-8.

### [CLEANUP-D4] `/cleanup PhD/LWX/DiscModel.lean` — done (after D-12)

### [D-13] `evalAt_mk_kappaSlash` — done
**Statement**: `evalAt (mk fun j => κ.kappaSlash g f j) w = evalAt (autFactor g) w * evalAt (mk f) (evalAt (mobius g) w)`.
**Sketch**: `WeightSeries.kappaSlash_apply` expands the `j`-th coordinate as
`∑' i, coeff j (autFactor · möb^i) · f i`; swap the `j` and `i` sums (absolutely summable), then
`evalAt_mul` and `evalAt_pow`.
**Lemmas**: `WeightSeries.kappaSlash_apply` (`SlashAction.lean:462`), `evalAt_mul`, `evalAt_pow`,
`QMF.AbsSummable`.

### [D-14] `discEval_discSlash` — done (**[LWX, (2.3.2)] pointwise**)
**Statement**: `discEval ψ h (discSlash h ψ (haloWeightH …) δ f) z =
specialize (intHom ψ) T₀ (univChar ω (den_δ z)) · discEval ψ h f (möb δ z)`.
**Sketch**: let `a = toZModPow h z`, `w = discCoord h z`.  `blockProj_discSlash` (D-8) reduces the
left side to the single-disc action of `δ'_a`; `evalAt_mk_kappaSlash` (D-13) splits it as
`evalAt (autFactor ψδ'_a) (ψw) · evalAt (mk f_{a'}) (evalAt (mobius ψδ'_a) (ψw))`.  The first
factor is `haloCharFunH (ψ(c'w + d'))` (`evalAt_autFactor_haloWeightH`, WH-44) `=
haloCharFunH (ψ(den_δ z))` (D-2) `= specialize (univChar ω (den_δ z))` (WH-31).  The second
factor is `discEval ψ h f (möb δ z)` because `intHom_mobiusFun` identifies
`evalAt (mobius ψδ'_a) (ψw) = ψ(möb δ'_a w)` and D-3/D-4 identify the disc and coordinate of
`möb δ z` as `a'` and `möb δ'_a w`.
**Lemmas**: `intHom_mobiusFun` (`Seam.lean:289`), WH-31, WH-44, D-2, D-3, D-4, D-8, D-13.
**Deps**: D-2, D-3, D-4, D-8, D-13, WH-31, WH-44.

### [CLEANUP-D5] `/cleanup PhD/LWX/DiscModel.lean` — done (final, after D-14)
**Note (execution)**: `DiscModel.lean` gained `import PhD.LWX.Seam` (for `intHom_denUnit` and
`intHom_mobiusFun`, which the D-14 sketch cites); no cycle, `SeamH` already imported both.
`discConjK`/`coe_discConjK` dropped the unused `[IsUltrametricDist K] [CompleteSpace K]`
instance binders.  D-12 avoids an isometry hypothesis by deriving `‖ψ p‖ < 1` and
`‖ψ y‖ ≤ 1` from the level bounds themselves (`norm_map_p_lt_one`, `norm_map_le_one`), so the
ticketed statement stands unchanged; `hρ` is unused there and was renamed `_hρ`.

---

## Group DF — `PhD/LWX/DiscForms.lean`

`S^{D,†,m}` in the disc model.  Source: `lwx.txt:686–692`.  Every leaf transcribes the
corresponding declaration of `PhD/QMF/Weight/{Forms,Compact,Fredholm}.lean` (or, for the level
handling, `PhD/LWX/Certificates.lean`).

### [DF-1] `discLevelSMulSlashClass` — done. Mirror `seqLevelSMulSlash`
(`IntegralModel.lean:1380`): pull `discSMulSlashClass` back along `levelM1ToM1`.
### [DF-2] `mem_discForms_iff` — done. Unfold `slashFixedPointsOfLE` and
`RightSlashAction.comap_slash`; mirror `mem_forms_iff`.
### [DF-3] `discEvalAtReps` — done (two `LinearMap` fields). Mirror `evalAtReps`
(`Compact.lean:92`): `Finset.sum_add_distrib`, `Finset.smul_sum`.
### [CLEANUP-DF1] `/cleanup PhD/LWX/DiscForms.lean` — done (after DF-3)
### [DF-4] `blockProj_discEvalAtReps` — done. Mirror `blockProj_evalAtReps` (`Compact.lean:98`).
### [DF-5] `bijective_discEvalAtReps_of_stabilizer_eq_bot` — done. Mirror
`bijective_intEvalAtReps_of_stabilizer_eq_bot` (`Certificates.lean:232`) — the longest
transcription in the group; it uses `AutomorphicFunction.bijective_evalAtRepsSlash`,
`slash_apply_mul`, `left_invt'`, `DoubleCoset.rel_iff`.
### [DF-6] `discEvalAtReps_discHeckeOperator` — done. Mirror `evalAtReps_heckeOperator`
(`Compact.lean:199`) via `AutomorphicFunction.heckeOperatorSlash_apply_rep`
(`HeckeMatrix.lean:57`).
### [CLEANUP-DF2] `/cleanup PhD/LWX/DiscForms.lean` — done (after DF-6)
### [DF-7] `isCompactoid_discHeckeBlockOp` — done. `isCompactoid_blockOp` +
`IsCompactoid.finset_sum` + D-12, with `‖a‖ ≤ p⁻¹` from `hshape`.
**Deps**: D-12.
### [DF-8] `evalT_discHeckeCharPowerSeries_eq_zero_iff` — done. Mirror
`evalT_heckeCharPowerSeries_eq_zero_iff` (`Fredholm.lean:57`): `evalT_charPowerSeries_eq_zero_iff`
(`Riesz.lean:2381`) transported along DF-5 with DF-6 and DF-7.
**Deps**: DF-5, DF-6, DF-7.
### [CLEANUP-DF3] `/cleanup PhD/LWX/DiscForms.lean` — done (final, after DF-8)

---

## Group SH — `PhD/LWX/SeamH.lean` (**milestone SH-M**)

Source: `lwx.txt:966–1010` (Prop 2.17 and its proof), `lwx.txt:735–737` and `lwx.txt:888–891`
([Bu04, Lemma 4]).

### [SH-1] `entry_eq_fwdDiff` — done
**Statement**: `entry ω δ m n = Δ_[1]^[m] (fun z => univChar ω (δ.denUnit z) * HaloInt.const (Ring.choose (δ.mobiusFun z) n)) 0`.
**Sketch**: this is `IntegralModel.lean:1160`'s `private theorem entry_eq_fwdDiff`; restate it
publicly here and reproduce the proof (coefficientwise: `HaloInt` elements are compared by their
`T`-coefficients, `coeff_univChar_mul_const` expands the product, `entryCoeff` is the definition,
and `Δ` commutes with taking a fixed coefficient).
**Note**: the `m = 1` seam used the *monomial* form `fwdDiff_iter_cfunSlash_pow` (public); the
disc model needs the *binomial* form because the Colmez basis is built from binomials.
**Lemmas**: `entryCoeff`, `fwdDiff` coefficientwise, `HaloInt.const`.

### [SH-2] `specialize_entry_eq_fwdDiff` — done
**Sketch**: apply `HaloInt.specializeHom` to SH-1; `map_fwdDiff_iter` moves it inside, and
`fwdDiff_iter_comp_natCast` (`Seam.lean:242`) restricts from `ℤ_[p]` to `ℕ`.  Then
`specialize_const` and `Ring.map_choose`.
**Lemmas**: `HaloInt.specializeHom`, `map_fwdDiff_iter`, `fwdDiff_iter_comp_natCast`.
**Deps**: SH-1.

### [SH-3] `discEval_colmezToDisc_single` — done
**Statement**: `discEval ψ h (colmezToDisc ψ hψ h (single n 1)) z = (⌊n/pʰ⌋! : K) * intHom ψ (Ring.choose z n)`.
**Sketch**: by AB-8 the Taylor coefficients on the disc of `z` are `ψ(discCoeff h n ·)`, so
`discEval` is `ψ((discPoly h n a).eval w) = ψ((colmezPoly h n).eval z)` (A-5) `=
⌊n/pʰ⌋!·ψ(Ring.choose z n)` (A-4 extended from `ℕ` to `ℤ_[p]` by density/continuity, or directly
via `descPochhammer` and `Ring.choose`).
**Deps**: A-4, A-5, AB-8, AB-14.

### [CLEANUP-SH1] `/cleanup PhD/LWX/SeamH.lean` — done (after SH-3)

### [SH-4] `discToMahler_comp_discSlash` — done (**the seam for one matrix**)
**Statement**: `(discToMahler ψ hψ h).comp (discSlash h ψ (haloWeightH …) δ) = (specEntryOp … (M1.toLocalMat δ)).comp (discToMahler ψ hψ h)`.
**Sketch**: both sides are continuous linear; `colmezDiscEquiv` is an isomorphism (AB-11), so it
suffices to check on `colmezToDisc (single n 1)` for every `n`.  Left side at coordinate `m`:
`discToMahler_apply_eq_fwdDiff` (AB-17) then `discEval_discSlash` (D-14) then SH-3, giving
`⌊n/pʰ⌋!·Δ^m (j ↦ specialize(univChar ω (den_δ j))·ψ(C(möb δ j, n))) 0`, which is
`⌊n/pʰ⌋!·specialize(entry ω (toLocalMat δ) m n)` by SH-2.  Right side at coordinate `m`:
`discToMahler_colmezToDisc` (AB-13) gives `⌊n/pʰ⌋!·e_n`, and `matrixCoeff_specEntryOp` gives the
same value.
**Deps**: AB-11, AB-13, AB-17, D-14, SH-2, SH-3.

### [SH-5] `matrixCoeff_diagFactorialHBlock` + the two `_comp` variants — done
**Sketch**: transcribe `matrixCoeff_diagFactorialBlock` and its two companions
(`Seam.lean:472–508`), replacing `m !` by `(m / p^h)!`.
**Deps**: AB-12.

### [SH-6] `discToMahlerBlock_eq` — done
**Statement**: `discToMahlerBlock = diagFactorialHBlock ∘ colmezDiscEquivBlock.symm`.
**Sketch**: `blockMap_comp` (BM-4) and `blockMap_eq_blockDiag` (BM-3) applied to
`discToMahler = diagFactorialH ∘ colmezDiscEquiv.symm`; mirror `monomialToMahlerBlock_eq`
(`Seam.lean:418`).
**Deps**: BM-3, BM-4, AB-11, AB-12.

### [CLEANUP-SH2] `/cleanup PhD/LWX/SeamH.lean` — done (after SH-6)

### [SH-7] `discToMahlerBlock_comp_discHeckeBlockOp` — done
**Sketch**: `blockMap_comp_blockOp` and `blockOp_comp_blockMap` (BM-4) reduce to a blockwise
identity; each block is a finite sum of SH-4 over the certificates with target `j`.  Mirror
`monomialToMahlerBlock_comp_heckeBlockOp` (`Seam.lean:432`).
**Deps**: BM-4, SH-4.

### [SH-8] `isCompactoid_discHeckeBlockOp_haloWeightH` — done
**Sketch**: DF-7 at `σ = max (haloRhoH p h T₀) p⁻¹`, which is `< 1` by WH-34 and `p⁻¹ < 1`.
**Deps**: DF-7, WH-34.

### [SH-9] `diagFactorialHBlock_comp_colmezConj` — done
**Sketch**: rewrite SH-7 through SH-6 and cancel `colmezDiscEquivBlock.symm ∘ colmezDiscEquivBlock
= id` (use `ContinuousLinearMap.ext fun x => e.symm_apply_apply x`, **not**
`ContinuousLinearEquiv.symm_comp_self`, which is function-level).  Mirror
`diagFactorialBlock_comp_colmezConj` (`Seam.lean:510`).
**Deps**: SH-6, SH-7.

### [CLEANUP-SH3] `/cleanup PhD/LWX/SeamH.lean` — done (after SH-9)
### [CLEANUP-ALL-1] `/cleanup-all` — done (before the milestone SH-M)

### [SH-M] `specCharSeries_ofCerts_eq_discHeckeCharPowerSeries` — done (**MILESTONE**)
**Statement**: `specCharSeries (UpDatum.ofCerts …) ω (intHom ψ) T₀ = discHeckeCharPowerSeries θ h ψ (haloWeightH …) U hU vRep hvΔ idx u`.
**Sketch**: `charPowerSeries_conj` along `colmezDiscEquivBlock` (compactoid by SH-8) turns
`det(1 − X[UηU])` into `det(1 − XP′)`; `charPowerSeries_eq_of_diag_intertwine` with
`d = fun a => ((a.2 / p^h)! : K)` (units, char zero) and SH-9 turns that into `det(1 − XP(T₀))`;
`charPowerSeries_specOp` (`Seam.lean:135`) identifies the latter with `specCharSeries`.
Mirror `specCharSeries_ofCerts_eq_heckeCharPowerSeries` (`Seam.lean:548`) line for line.
**Source**: `lwx.txt:993–1010`.
**Deps**: SH-5, SH-8, SH-9.

### [SH-10] `discHeckeCharPowerSeries_eq_of_levels` — done ([Bu04, Lemma 4])
**Sketch**: both sides equal `specCharSeries` of the same certificate datum by SH-M at `h` and at
`h'`; transitivity.
**Source**: `lwx.txt:888–891`.
**Deps**: SH-M.

### [SH-11] `exists_level_specCharSeries_eq_heckeCharPowerSeries` — done (coverage)
**Sketch**: X-7 produces `h` with `hT`; then SH-M.
**Deps**: X-7, SH-M.

### [SH-12] `discHeckeCharPowerSeries_zero_eq_heckeCharPowerSeries` — done (`h = 0` compatibility)
**Sketch**: both sides equal `specCharSeries` of the same datum — the left by SH-M at `h = 0`, the
right by `Seam.specCharSeries_ofCerts_eq_heckeCharPowerSeries`.  Requires `Mh p 0 = M1 p` (WH-3)
and the `ψ`-seam transport that `Seam.lean` already performs.
**Risk**: the riskiest leaf on the board (a defeq mismatch between the two level presentations is
plausible); if a transport lemma is needed, spawn it as a sub-ticket rather than filing a B2.
**Deps**: WH-3, WH-17, SH-M.

### [CLEANUP-SH4] `/cleanup PhD/LWX/SeamH.lean` — done (final, after SH-12)
**Note (execution)**: SH-1 needed `IntegralModel.lean`'s `private coeff_slash_choose`; it was made
public and renamed `LWX.coeff_univChar_mul_const` (the name the SH-1 sketch uses).  `SeamH.lean`
keeps its own `haloCoeffHom` (the `T^r`-coefficient additive map) rather than un-privatising
`IntegralModel.coeffHom`.

---

## Group QH — `PhD/LWX/QuaternionicH.lean` (**milestone QH-M**)

Source: `lwx.txt:672–692` (§2.4), `lwx.txt:879–891` (Definition 2.13).

### [CLEANUP-ALL-2] `/cleanup-all` — done (before the milestone QH-M)

### [QH-M] `specCharSeries_ofCerts_eq_discHeckeCharPowerSeriesQ` — done (**MILESTONE**)
**Statement**: [LWX, Prop 2.17] for `D/ℚ` at level `m = h + 1`.
**Sketch**: direct instantiation of SH-M at `θ = thetaInt p D`, `ψ = padicComparison p`,
`Γ = globalUnits ℚ D`.  Unlike the `m = 1` file, **no** `thetaK`/`toMatrix` transport is needed:
`DiscForms` consumes the integral `θ` directly.
**Deps**: SH-M.

### [QH-2] `evalT_specCharSeries_eq_zero_iff_disc` — done
**Sketch**: rewrite by QH-M, then `evalT_discHeckeCharPowerSeries_eq_zero_iff` (DF-8) with
`hshape = isUpShape_certM1 …` and the neatness hypotheses, exactly as
`Quaternionic.evalT_specCharSeries_eq_zero_iff` (`Quaternionic.lean:205`).
**Deps**: DF-8, QH-M.

### [QH-3] `exists_level_evalT_specCharSeries_eq_zero_iff` — done (**the every-point statement**)
**Sketch**: X-7 gives the level; QH-2 at that level.
**Source**: `lwx.txt:879–891` (Def 2.13: "Choose `m ∈ ℕ` such that … the universal character is
`m`-locally analytic").
**Deps**: X-7, QH-2.

### [CLEANUP-QH1] `/cleanup PhD/LWX/QuaternionicH.lean` — done (final, after QH-3)

---

### [CLEANUP-FINAL] `/cleanup-all` — done (last ticket)
Run after every proof ticket is done: `lake build`, `lake exe runLinter` on all ten modules,
`#print axioms` on the two milestones, and a final README pass
(`PhD/LWX/README.md` if present, plus a row in `PhD/TateFredholm/README.md` for
`Unitriangular.lean` and `BlockMap.lean`).

**Result (2026-09-06)**: `lake build` clean (3825 jobs); `lake exe runLinter` reports nothing on
any of the ten modules; `#print axioms` on `specCharSeries_ofCerts_eq_discHeckeCharPowerSeries`
and `specCharSeries_ofCerts_eq_discHeckeCharPowerSeriesQ` (and on
`evalT_specCharSeries_eq_zero_iff_disc`, `exists_level_evalT_specCharSeries_eq_zero_iff`,
`discHeckeCharPowerSeries_eq_of_levels`,
`exists_level_specCharSeries_eq_heckeCharPowerSeries`,
`discHeckeCharPowerSeries_zero_eq_heckeCharPowerSeries`) gives
`[propext, Classical.choice, Quot.sound]` in every case.  `PhD/LWX/README.md` does not exist, so
the README pass added the two rows plus the dependency-tree entries in
`PhD/TateFredholm/README.md` and a `PhD/LWX/` bullet in the root `README.md`.

---

## Post-completion addendum (2026-09-06, not a ticket)

`PhD/LWX/SlopesSeam.lean` (new, sorry-free, linter-clean) composes the `lwx-slopes` polygon
theorems with this board's seam, so the halo estimate and the slope theorems read on the genuine
`U_p` rather than on `specCharSeries`.  Six statements, each a one-line rewrite through
`specCharSeries_ofCerts_eq_discHeckeCharPowerSeries`:
`isBelow_newtonPolygon_discHeckeCharPowerSeries` ([LWX, Cor 3.18]),
`hasUnitBand_of_height_discHeckeCharPowerSeries_eq` (**the interface [LWX, Step I] must hit**),
`unitSlope_discHeckeCharPowerSeries_eq_iff` and `_mem_Ioo` ([LWX, Thm 1.3]),
`unitSlope_discHeckeCharPowerSeries_eq_slopeRatio` ([LWX, Thm 1.5 (1.5.1)]), and
`exists_level_unitSlope_discHeckeCharPowerSeries_eq_slopeRatio` (the same at every halo point).
Imports `PhD.LWX.SlopeRatios` and `PhD.LWX.QuaternionicH`; the two branches were disjoint, so no
cycle.  No ticket counts changed.

**Why this board was needed for [LWX, Step I]** (arithmetic from the paper, not formalised):
Step I is a statement at the classical weights, where [LWX, p. 25] records
`|T_{χ_k}| = p^{−p/(q(p−1))}`, i.e. `p^{−1/(p−1)}` for odd `p`.  That is a halo point, but
`|T_{χ_k}|² < p⁻¹` holds only for `p < 3`.  So for every odd prime the weights Step I is about
lie outside the `m = 1` region that `lwx-seam` covered, and Step I could not have been connected
to the formalised determinant before this board.  `m = 2` suffices at those weights.

**Second follow-up (2026-09-06): `PhD/LWX/SlopeGrowth.lean`** (sorry-free, std axioms, linter
clean; imports `SlopeRatios` only).  The `lwx-slopes` board proved the identity
`slope_j(T) = v(T)·slopeRatio j` but not the other two clauses of [LWX, Thm 1.5]'s first half,
that the ratios are "in increasing order and tending to infinity".  Both are now proved, and
both are **unconditional**: they need neither the small-annulus hypothesis `hκ` nor the touching
hypothesis `hband` that the identity carries.
`monotone_slopeRatio` is convexity of the shape polygon (`monotone_toReal_unitSlope` plus
`height_shapePolygon_ne_top`).  `tendsto_slopeRatio_atTop` runs off the halo estimate: units of
the integral matrix occur only at heights `≥ λ(n)` (`lwxLambda_le_of_isUnit`), so the shape
sequence dominates `λ`, and for each `M` the line `y = M·x − M²pt` lies below every point
(`le_div_sub_div`: the increments `⌊k/t⌋ − ⌊k/(pt)⌋` exceed `M` once `k ≥ M·p·t`).
`IsNewtonPolygonOf.line_le_height` puts that line below the polygon; comparing with
`toReal_height_shapePolygon` (height as the sum of the first `n` slopes) and using monotonicity
gives a slope `≥ M − 1`.
