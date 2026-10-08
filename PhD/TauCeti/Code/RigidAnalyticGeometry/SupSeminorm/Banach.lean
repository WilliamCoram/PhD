/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.PadicFunctionalAnalysis.PowerBounded
import PhD.TauCeti.Code.RigidAnalyticGeometry.BanachAlgebra.Continuity
import PhD.TauCeti.Code.RigidAnalyticGeometry.SupSeminorm.Integral

/-!
# The supremum seminorm on Banach algebras

Layer 2, §2.1 and §2.3 at the level of Banach algebras (BGR 3.8.2/3–3.8.2/6). For a `K`-Banach
algebra `A` with algebraic residue fields, `|·|_sup ≤ ‖·‖` (Layer 0, 3.8.2/2); when `|·|_sup` is a
norm every homomorphism from a Banach algebra into `A` is continuous (3.8.2/3) and all complete
algebra norms on `A` are equivalent (3.8.2/4). Along an integral monomorphism `B → A` as in
3.8.1/7 with `B → A` continuous for `|·|_sup`, `|f|_sup = inf ‖fⁱ‖^{1/i}` (3.8.2/5, Mathlib's
`smoothingFun`), and the power-bounded / topologically nilpotent elements are those with
`|f|_sup ≤ 1`, resp. `< 1` (3.8.2/6).

## Main declarations

* `AlgHom.continuous_of_supSeminorm_eq_zero_imp`: BGR 3.8.2/3.
* `AlgEquiv.exists_forall_norm_le_mul_of_supSeminorm_eq_zero_imp`: BGR 3.8.2/4.
* `Affinoid.supSeminorm_le_smoothingFun`, `Affinoid.IsPowerBounded.supSeminorm_le_one`,
  `Affinoid.IsTopologicallyNilpotent.supSeminorm_lt_one`: `|f|_sup ≤ inf ‖fⁱ‖^{1/i}`, `|f|_sup ≤ 1`
  for power-bounded `f` and `|f|_sup < 1` for topologically nilpotent `f` (from 3.8.2/2).
* `Affinoid.smoothingFun_le_of_eval₂_eq_zero`: BGR 3.1.2/1 for the smoothing seminorm, and
  `Affinoid.smoothingFun_le_mul_supSpectralValue_of_eval₂_eq_zero`: `μ'(f) ≤ max 1 C · σ(q)`.
* `Affinoid.supSeminorm_eq_smoothingFun_of_forall_le`: the constant in `μ' ≤ C |·|_sup` disappears
  (BGR 1.3.1/2).
* `Affinoid.isTopologicallyNilpotent_of_norm_pow_lt_one`: one small power suffices.
* `Affinoid.isPowerBounded_of_eval₂_eq_zero`: a root of a monic polynomial whose coefficients lie
  in a subring of bounded image is power-bounded.
* `Affinoid.supSeminorm_eq_smoothingFun_of_isIntegral`: BGR 3.8.2/5.
* `Affinoid.isPowerBounded_of_supSeminorm_le_one_of_isIntegral`,
  `Affinoid.isTopologicallyNilpotent_iff_supSeminorm_lt_one_of_isIntegral`: BGR 3.8.2/6.
-/

open Filter Polynomial PowerBounded Topology

section Continuity

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A] [IsUltrametricDist A]
  [NormOneClass A]
  {B : Type*} [NormedCommRing B] [NormedAlgebra K B] [CompleteSpace B]

omit [IsUltrametricDist K] [IsUltrametricDist A] [NormOneClass A] in
/-- **BGR 3.8.2/3.** If `|·|_sup` is a norm on the Banach algebra `A` (with algebraic residue
fields), every `K`-algebra homomorphism from a Banach algebra `B` into `A` is continuous. Proof:
closed graph through the maximal ideals (`AlgHom.continuous_of_forall_isClosed_of_finiteDimensional`
with `𝔅 = {𝔪 | 𝔪.IsMaximal}`: maximal ideals of a Banach algebra are closed, their contractions
are maximal hence closed, the residue fields are finite over `K`, and `⋂ 𝔪 = 0` by 3.8.1/9). -/
theorem AlgHom.continuous_of_supSeminorm_eq_zero_imp
    [Affinoid.HasSupSeminorm K A]
    (hfin : ∀ x : MaximalSpectrum A, FiniteDimensional K (A ⧸ x.asIdeal))
    (hA : ∀ f : A, Affinoid.supSeminorm K f = 0 → f = 0) (φ : B →ₐ[K] A) : Continuous φ := by
  refine φ.continuous_of_forall_isClosed_of_finiteDimensional {𝔪 | 𝔪.IsMaximal}
    (fun 𝔪 h𝔪 ↦ haveI : 𝔪.IsMaximal := h𝔪; Ideal.IsMaximal.isClosed)
    (fun 𝔪 h𝔪 ↦ haveI := Affinoid.isMaximal_comap_of_isAlgebraic φ (⟨𝔪, h𝔪⟩ : MaximalSpectrum A)
      Ideal.IsMaximal.isClosed)
    (fun 𝔪 h𝔪 ↦ hfin ⟨𝔪, h𝔪⟩) ?_
  -- `⋂ 𝔪 = 0` because `|·|_sup` is a norm (BGR 3.8.1/9)
  refine eq_bot_iff.2 fun f hf ↦ Ideal.mem_bot.2 (hA f ?_)
  rw [Affinoid.supSeminorm_eq_zero_iff_forall_mem]
  exact fun x ↦ Ideal.mem_sInf.1 hf x.isMaximal

omit [IsUltrametricDist A] [NormOneClass A] in
/-- Maximal ideals of a Banach algebra are closed (Mathlib `Ideal.IsMaximal.isClosed`, stated for
the maximal spectrum). -/
theorem MaximalSpectrum.isClosed_asIdeal (x : MaximalSpectrum A) :
    IsClosed (x.asIdeal : Set A) :=
  Ideal.IsMaximal.isClosed

omit [IsUltrametricDist K] [IsUltrametricDist A] [NormOneClass A] in
/-- **BGR 3.8.2/4.** All complete `K`-algebra norms on `A` are equivalent when `|·|_sup` is a norm:
for an algebra isomorphism `e : A ≃ B` between such Banach algebras there is `C` with
`‖e a‖ ≤ C * ‖a‖`. -/
theorem AlgEquiv.exists_forall_norm_le_mul_of_supSeminorm_eq_zero_imp [Affinoid.HasSupSeminorm K A]
    (hfin : ∀ x : MaximalSpectrum A, FiniteDimensional K (A ⧸ x.asIdeal))
    (hA : ∀ f : A, Affinoid.supSeminorm K f = 0 → f = 0) (e : A ≃ₐ[K] B) :
    ∃ C : ℝ, ∀ a : A, ‖e a‖ ≤ C * ‖a‖ := by
  have hsymm : Continuous e.symm :=
    AlgHom.continuous_of_supSeminorm_eq_zero_imp hfin hA e.symm.toAlgHom
  -- open mapping: the inverse of the continuous bijection `e.symm` is continuous
  have he : Continuous e := e.symm.toLinearEquiv.continuous_symm hsymm
  obtain ⟨C, -, hC⟩ := SemilinearMapClass.bound_of_continuous e.toAlgHom he
  exact ⟨C, hC⟩

end Continuity

namespace Affinoid

section Smoothing

variable (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A] [IsUltrametricDist A]
  [NormOneClass A]

omit [NormOneClass A] in
/-- `|f|_sup ≤ ‖fⁱ‖^{1/i}` for every `i ≥ 1`, by 3.8.2/2 and power-multiplicativity. -/
theorem supSeminorm_le_norm_pow_rpow [HasSupSeminorm K A] (f : A) (i : ℕ+) :
    supSeminorm K f ≤ ‖f ^ (i : ℕ)‖ ^ (1 / (i : ℝ)) := by
  have hi : (i : ℕ) ≠ 0 := i.ne_zero
  calc supSeminorm K f = (supSeminorm K f ^ (i : ℕ)) ^ ((i : ℕ) : ℝ)⁻¹ :=
        (Real.pow_rpow_inv_natCast (supSeminorm_nonneg K f) hi).symm
    _ = supSeminorm K (f ^ (i : ℕ)) ^ ((i : ℕ) : ℝ)⁻¹ := by rw [supSeminorm_pow K f hi]
    _ ≤ ‖f ^ (i : ℕ)‖ ^ ((i : ℕ) : ℝ)⁻¹ :=
        Real.rpow_le_rpow (supSeminorm_nonneg K _) (supSeminorm_le_norm (K := K) _)
          (inv_nonneg.2 (Nat.cast_nonneg _))
    _ = ‖f ^ (i : ℕ)‖ ^ (1 / (i : ℝ)) := by rw [one_div]

omit [NormOneClass A] in
/-- `|f|_sup ≤ inf_i ‖fⁱ‖^{1/i}` (BGR 3.8.2/5, the first inequality: "From Corollary 2 one deduces
immediately that `|f|_sup ≤ |f|_r`"). -/
theorem supSeminorm_le_smoothingFun [HasSupSeminorm K A] (f : A) :
    supSeminorm K f ≤ smoothingFun (SeminormedRing.toRingSeminorm A) f :=
  le_ciInf fun i ↦ supSeminorm_le_norm_pow_rpow K f i

omit [CompleteSpace A] in
/-- The smoothing seminorm bounds a root of a monic polynomial by the spectral value for the
seminorm `inf ‖·ⁱ‖^{1/i}` (BGR 3.8.2/5: "one can apply Proposition 3.1.2/1 … and one gets
`|f|_r ≤ max |φ(b_i)|_r^{1/i}`"), with the coefficients bounded by `‖φ(b_i)‖`. -/
theorem smoothingFun_le_of_eval₂_eq_zero {B : Type*} [CommRing B] (φ : B →+* A) {q : B[X]}
    (hq : q.Monic) {f : A} (hf : q.eval₂ φ f = 0) :
    smoothingFun (SeminormedRing.toRingSeminorm A) f ≤
      ⨆ n : Fin q.natDegree, ‖φ (q.coeff n)‖ ^ (1 / (q.natDegree - n : ℝ)) := by
  set μ := SeminormedRing.toRingSeminorm A
  have hμ1 : μ 1 ≤ 1 := norm_one.le
  have hna : IsNonarchimedean μ := IsUltrametricDist.isNonarchimedean_norm
  -- `μ' = inf ‖·ⁱ‖^{1/i}` is a power-multiplicative nonarchimedean ring seminorm below `‖·‖`
  set μ' := smoothingSeminorm μ hμ1 hna
  have hμ' : ∀ x, smoothingFun μ x = μ' x := fun _ ↦ rfl
  have hpow : ∀ (x : A) (n : ℕ), μ' (x ^ n) ≤ μ' x ^ n := by
    intro x n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [pow_zero, pow_zero]
      exact smoothingFun_one_le μ hμ1
    · exact (isPowMul_smoothingFun μ hμ1 x (Nat.one_le_iff_ne_zero.2 hn)).le
  have hbdd : BddAbove (Set.range fun n : Fin q.natDegree ↦
      ‖φ (q.coeff n)‖ ^ (1 / (q.natDegree - n : ℝ))) := (Set.finite_range _).bddAbove
  have hS : 0 ≤ ⨆ n : Fin q.natDegree, ‖φ (q.coeff n)‖ ^ (1 / (q.natDegree - n : ℝ)) :=
    Real.iSup_nonneg fun _ ↦ Real.rpow_nonneg (norm_nonneg _) _
  rw [hμ']
  rcases Nat.eq_zero_or_pos q.natDegree with hn0 | hn
  · -- `q = 1`, so `A` is the zero ring and `f = 0`
    rw [eq_one_of_monic_natDegree_zero hq hn0, eval₂_one] at hf
    have hf0 : f = 0 := by rw [← mul_one f, hf, mul_zero]
    rw [hf0, map_zero]
    exact hS
  -- `fⁿ = -∑_{i<n} φ(bᵢ) fⁱ` and some term dominates (BGR 3.1.2/1 for `μ'`)
  have hsum : f ^ q.natDegree = -∑ i ∈ Finset.range q.natDegree, φ (q.coeff i) * f ^ i := by
    rw [eval₂_eq_sum_range, Finset.sum_range_succ, hq.coeff_natDegree, map_one, one_mul] at hf
    exact eq_neg_of_add_eq_zero_right hf
  obtain ⟨j, hj, hle⟩ := IsNonarchimedean.finset_image_add_of_nonempty
    (isNonarchimedean_smoothingFun μ hμ1 hna) (fun i ↦ φ (q.coeff i) * f ^ i)
    (Finset.nonempty_range_iff.2 hn.ne')
  have hjn : j < q.natDegree := Finset.mem_range.1 hj
  have key : μ' f ^ q.natDegree ≤ ‖φ (q.coeff j)‖ * μ' f ^ j :=
    calc μ' f ^ q.natDegree = μ' (f ^ q.natDegree) :=
          (isPowMul_smoothingFun μ hμ1 f (Nat.one_le_iff_ne_zero.2 hn.ne')).symm
      _ = μ' (∑ i ∈ Finset.range q.natDegree, φ (q.coeff i) * f ^ i) := by
          rw [hsum, map_neg_eq_map]
      _ ≤ μ' (φ (q.coeff j) * f ^ j) := hle
      _ ≤ μ' (φ (q.coeff j)) * μ' (f ^ j) := map_mul_le_mul μ' _ _
      _ ≤ ‖φ (q.coeff j)‖ * μ' f ^ j :=
          mul_le_mul (smoothingFun_le_self μ _) (hpow f j) (apply_nonneg μ' _) (norm_nonneg _)
  rcases (apply_nonneg μ' f).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact hS
  -- divide by `μ'(f)ʲ` and take the `(n - j)`-th root
  have hdiv : μ' f ^ (q.natDegree - j) ≤ ‖φ (q.coeff j)‖ :=
    le_of_mul_le_mul_right (by rwa [pow_sub_mul_pow _ hjn.le]) (pow_pos hpos j)
  calc μ' f = (μ' f ^ (q.natDegree - j)) ^ ((q.natDegree - j : ℕ) : ℝ)⁻¹ :=
        (Real.pow_rpow_inv_natCast hpos.le (Nat.sub_pos_of_lt hjn).ne').symm
    _ ≤ ‖φ (q.coeff j)‖ ^ ((q.natDegree - j : ℕ) : ℝ)⁻¹ :=
        Real.rpow_le_rpow (pow_nonneg hpos.le _) hdiv (inv_nonneg.2 (Nat.cast_nonneg _))
    _ = ‖φ (q.coeff (⟨j, hjn⟩ : Fin q.natDegree))‖ ^
          (1 / (q.natDegree - ((⟨j, hjn⟩ : Fin q.natDegree) : ℕ) : ℝ)) := by
        rw [Nat.cast_sub hjn.le, one_div]
    _ ≤ _ := le_ciSup hbdd (⟨j, hjn⟩ : Fin q.natDegree)


omit [IsUltrametricDist K] [CompleteSpace K] [NormedAlgebra K A] [CompleteSpace A] in
/-- `μ'(f) ≤ max 1 C · σ(q)` for a root `f` of a monic `q ∈ B[X]` under `φ : B → A` with
`‖φ b‖ ≤ C |b|_sup`: each term `‖φ(bᵢ)‖^{1/(n-i)}` of `smoothingFun_le_of_eval₂_eq_zero` is at most
`max 1 C · |bᵢ|_sup^{1/(n-i)}` (BGR 3.8.2/5, "`|f|_r ≤ C|f|_sup`"). -/
theorem smoothingFun_le_mul_supSpectralValue_of_eval₂_eq_zero {B : Type*} [CommRing B]
    [Algebra K B] (φ : B →+* A) {C : ℝ} (hC : ∀ b : B, ‖φ b‖ ≤ C * supSeminorm K b) {q : B[X]}
    (hq : q.Monic) {f : A} (hf : q.eval₂ φ f = 0) :
    smoothingFun (SeminormedRing.toRingSeminorm A) f ≤ max 1 C * supSpectralValue K q := by
  have hC' : 0 ≤ max 1 C := zero_le_one.trans (le_max_left _ _)
  refine (smoothingFun_le_of_eval₂_eq_zero φ hq hf).trans
    (Real.iSup_le (fun m ↦ ?_) (mul_nonneg hC' (supSpectralValue_nonneg K q)))
  have hm : (m : ℕ) < q.natDegree := m.2
  have hk : (1 : ℝ) ≤ (q.natDegree : ℝ) - (m : ℕ) := by
    have h : (m : ℕ) + 1 ≤ q.natDegree := hm
    have h' : ((m : ℕ) : ℝ) + 1 ≤ q.natDegree := by exact_mod_cast h
    linarith
  have hexp : 0 ≤ 1 / ((q.natDegree : ℝ) - (m : ℕ)) := one_div_nonneg.2 (zero_le_one.trans hk)
  have hexp1 : 1 / ((q.natDegree : ℝ) - (m : ℕ)) ≤ 1 := (div_le_one (zero_lt_one.trans_le hk)).2 hk
  calc ‖φ (q.coeff m)‖ ^ (1 / ((q.natDegree : ℝ) - (m : ℕ)))
      ≤ (max 1 C * supSeminorm K (q.coeff m)) ^ (1 / ((q.natDegree : ℝ) - (m : ℕ))) :=
        Real.rpow_le_rpow (norm_nonneg _) ((hC _).trans (mul_le_mul_of_nonneg_right
          (le_max_right 1 C) (supSeminorm_nonneg K _))) hexp
    _ = max 1 C ^ (1 / ((q.natDegree : ℝ) - (m : ℕ))) *
          supSeminorm K (q.coeff m) ^ (1 / ((q.natDegree : ℝ) - (m : ℕ))) :=
        Real.mul_rpow hC' (supSeminorm_nonneg K _)
    _ ≤ max 1 C * supSpectralValue K q := by
        refine mul_le_mul ((Real.rpow_le_rpow_of_exponent_le (le_max_left 1 C) hexp1).trans_eq
          (Real.rpow_one _)) ?_ (Real.rpow_nonneg (supSeminorm_nonneg K _) _) hC'
        rw [← supSpectralValueTerms_of_lt_natDegree K _ hm]
        exact supSpectralValueTerms_le_supSpectralValue K _ m

/-- If `μ'(g) ≤ C |g|_sup` for every `g`, then `|f|_sup = μ'(f)`: both sides are
power-multiplicative, so the constant disappears in the `n`-th root (BGR 1.3.1/2, as in 3.8.2/5). -/
theorem supSeminorm_eq_smoothingFun_of_forall_le [HasSupSeminorm K A] {C : ℝ}
    (h : ∀ g : A, smoothingFun (SeminormedRing.toRingSeminorm A) g ≤ C * supSeminorm K g)
    (f : A) : supSeminorm K f = smoothingFun (SeminormedRing.toRingSeminorm A) f := by
  set μ := SeminormedRing.toRingSeminorm A
  have hμ1 : μ 1 ≤ 1 := norm_one.le
  refine le_antisymm (supSeminorm_le_smoothingFun K f) (le_of_not_gt fun hlt ↦ ?_)
  rcases (supSeminorm_nonneg K f).eq_or_lt with h0 | hpos
  · have h' := h f
    rw [← h0, mul_zero] at h'
    exact absurd hlt (not_lt.2 (h'.trans_eq h0))
  have hr : 1 < smoothingFun μ f / supSeminorm K f := (one_lt_div hpos).2 hlt
  obtain ⟨n, hn, hn1⟩ := (((tendsto_pow_atTop_atTop_of_one_lt hr).eventually_gt_atTop C).and
    (Filter.eventually_ge_atTop 1)).exists
  have h1 : smoothingFun μ f ^ n ≤ C * supSeminorm K f ^ n := by
    rw [← isPowMul_smoothingFun μ hμ1 f hn1, ← supSeminorm_pow K f (by omega)]
    exact h (f ^ n)
  rw [div_pow, lt_div_iff₀ (pow_pos hpos n)] at hn
  exact absurd h1 (not_le.2 hn)

omit [NormOneClass A] in
/-- **BGR 3.8.2/6 (a') ⇒ (c')** needs no integrality: power-bounded implies `|f|_sup ≤ 1`, since
`|·|_sup ≤ ‖·‖` and `|·|_sup` is power-multiplicative. -/
theorem IsPowerBounded.supSeminorm_le_one [HasSupSeminorm K A] {f : A} (hf : IsPowerBounded f) :
    supSeminorm K f ≤ 1 := by
  obtain ⟨C, hC⟩ := PowerBounded.IsPowerBounded.exists_norm_pow_le K hf
  refine le_of_not_gt fun h ↦ ?_
  obtain ⟨n, hn, hn1⟩ := (((tendsto_pow_atTop_atTop_of_one_lt h).eventually_gt_atTop C).and
    (Filter.eventually_ge_atTop 1)).exists
  exact absurd ((supSeminorm_pow K f (by omega)).symm.le.trans
    ((supSeminorm_le_norm (K := K) _).trans (hC n))) (not_le.2 hn)

omit [NormOneClass A] in
/-- A topologically nilpotent element has `|f|_sup < 1`: some `‖fⁿ‖ < 1` with `n ≥ 1`, and
`|f|_supⁿ = |fⁿ|_sup ≤ ‖fⁿ‖` (BGR 3.8.2/2). -/
theorem IsTopologicallyNilpotent.supSeminorm_lt_one [HasSupSeminorm K A] {f : A}
    (hf : IsTopologicallyNilpotent f) : supSeminorm K f < 1 := by
  have h0 : Tendsto (fun n ↦ ‖f ^ n‖) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.1 hf
  obtain ⟨n, hn, hn1⟩ :=
    ((h0.eventually (gt_mem_nhds zero_lt_one)).and (Filter.eventually_ge_atTop 1)).exists
  have hpow : supSeminorm K f ^ n < 1 :=
    ((supSeminorm_pow K f (by omega)).symm.le.trans (supSeminorm_le_norm (K := K) _)).trans_lt hn
  exact (pow_lt_one_iff_of_nonneg (supSeminorm_nonneg K f) (by omega)).1 hpow

omit [CompleteSpace A] [IsUltrametricDist A] in
/-- If some power `fᵐ`, `m ≥ 1`, has norm `< 1`, then `f` is topologically nilpotent (BGR p. 177:
"an element `f` is topologically nilpotent in `A` if and only if `inf |fⁱ|^{1/i} < 1`"):
`‖fⁿ‖ ≤ ‖fᵐ‖^{⌊n/m⌋} · max_{r<m} ‖fʳ‖`. -/
theorem isTopologicallyNilpotent_of_norm_pow_lt_one {f : A} {m : ℕ} (hm : m ≠ 0)
    (h : ‖f ^ m‖ < 1) : IsTopologicallyNilpotent f := by
  have hbound : ∀ n, ‖f ^ n‖ ≤ (∑ r ∈ Finset.range m, ‖f ^ r‖) * ‖f ^ m‖ ^ (n / m) := by
    intro n
    have hn : f ^ n = (f ^ m) ^ (n / m) * f ^ (n % m) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    rw [hn, mul_comm (∑ r ∈ Finset.range m, ‖f ^ r‖)]
    calc ‖(f ^ m) ^ (n / m) * f ^ (n % m)‖ ≤ ‖(f ^ m) ^ (n / m)‖ * ‖f ^ (n % m)‖ := norm_mul_le _ _
      _ ≤ ‖f ^ m‖ ^ (n / m) * ∑ r ∈ Finset.range m, ‖f ^ r‖ :=
          mul_le_mul (norm_pow_le _ _) (Finset.single_le_sum (fun _ _ ↦ norm_nonneg _)
            (Finset.mem_range.2 (Nat.mod_lt n (Nat.pos_of_ne_zero hm)))) (norm_nonneg _)
            (pow_nonneg (norm_nonneg _) _)
  unfold IsTopologicallyNilpotent
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun n ↦ norm_nonneg _) hbound ?_
  have h1 : Tendsto (fun n : ℕ ↦ ‖f ^ m‖ ^ (n / m)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h).comp (Nat.tendsto_div_const_atTop hm)
  simpa using h1.const_mul (∑ r ∈ Finset.range m, ‖f ^ r‖)

omit [CompleteSpace A] [NormOneClass A] in
/-- A root `f` of a monic `q ∈ B[X]` whose coefficients lie in a subring `S` of `B` with
`‖φ c‖ ≤ M` on `S` is power-bounded: each `fʲ` is `Σ_{i ≤ deg q} φ(cᵢ) fⁱ` with `cᵢ ∈ S`, the
remainder of `Xʲ` modulo `q` (BGR 3.8.2/6, 6.2.3/1: the powers of `f` lie in the bounded
`S`-module `Σ φ(S) fⁱ`). -/
theorem isPowerBounded_of_eval₂_eq_zero {B : Type*} [CommRing B] (φ : B →+* A) (S : Subring B)
    {q : B[X]} (hq : q.Monic) (hqS : ∀ i, q.coeff i ∈ S) {M : ℝ} (hM : ∀ c ∈ S, ‖φ c‖ ≤ M)
    {f : A} (hf : q.eval₂ φ f = 0) : IsPowerBounded f := by
  have hcoeffs : (q.coeffs : Set B) ⊆ S := by
    intro b hb
    obtain ⟨i, -, rfl⟩ := mem_coeffs_iff.1 hb
    exact hqS i
  have hq₀ : (q.toSubring S hcoeffs).Monic := (monic_toSubring _ _ _).2 hq
  refine isPowerBounded_of_norm_pow_le
    (C := max M 0 * ∑ i ∈ Finset.range (q.natDegree + 1), ‖f ^ i‖) fun j ↦ ?_
  -- `fʲ` is the value of the remainder of `Xʲ` modulo `q`, whose coefficients lie in `S`
  have hr : ((X ^ j : B[X]) %ₘ q).eval₂ φ f = f ^ j := by
    have h := congrArg (eval₂ φ f) (modByMonic_add_div (X ^ j : B[X]) q)
    rw [eval₂_add, eval₂_mul, hf, zero_mul, add_zero, eval₂_X_pow] at h
    exact h
  have hrdeg : ((X ^ j : B[X]) %ₘ q).natDegree < q.natDegree + 1 :=
    Nat.lt_succ_of_le (natDegree_modByMonic_le _ hq)
  have hrS : ∀ i, ((X ^ j : B[X]) %ₘ q).coeff i ∈ S := by
    intro i
    have h : ((X ^ j : B[X]) %ₘ q) = (((X ^ j : S[X]) %ₘ q.toSubring S hcoeffs)).map S.subtype := by
      rw [map_modByMonic _ hq₀, map_toSubring, Polynomial.map_pow, map_X]
    rw [h, coeff_map]
    exact ((X ^ j %ₘ q.toSubring S hcoeffs).coeff i).2
  rw [← hr, eval₂_eq_sum_range' φ hrdeg]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg
    (mul_nonneg (le_max_right _ _) (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)) fun i hi ↦ ?_
  exact (norm_mul_le _ _).trans (mul_le_mul ((hM _ (hrS i)).trans (le_max_left _ _))
    (Finset.single_le_sum (fun _ _ ↦ norm_nonneg _) hi) (norm_nonneg _) (le_max_right _ _))

variable {B : Type*} [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra K B] [IsDomain A]
  [Algebra B A] [IsScalarTower K B A] [Algebra.IsIntegral B A] [Module.IsTorsionFree B A]
  [HasSupSeminorm K A] [HasSupSeminorm K B]

/-- **BGR 3.8.2/5**: under the hypotheses of 3.8.1/7, if `B → A` is continuous for `|·|_sup`
(`‖algebraMap b‖ ≤ C * |b|_sup`), then `|f|_sup = inf_i ‖fⁱ‖^{1/i}`. -/
theorem supSeminorm_eq_smoothingFun_of_isIntegral {C : ℝ}
    (hC : ∀ b : B, ‖algebraMap B A b‖ ≤ C * supSeminorm K b) (f : A) :
    supSeminorm K f = smoothingFun (SeminormedRing.toRingSeminorm A) f := by
  refine supSeminorm_eq_smoothingFun_of_forall_le K (C := max 1 C) (fun g ↦ ?_) f
  -- `μ'(g) ≤ max 1 C · σ(minpoly g) = max 1 C · |g|_sup` (BGR 3.8.2/5: "`|f|_r ≤ C|f|_sup`")
  have hqg : (minpoly B g).eval₂ (algebraMap B A) g = 0 := by
    rw [← Polynomial.aeval_def]
    exact minpoly.aeval B g
  rw [supSeminorm_eq_supSpectralValue_minpoly K (B := B) g]
  exact smoothingFun_le_mul_supSpectralValue_of_eval₂_eq_zero K (algebraMap B A) hC
    (minpoly.monic (Algebra.IsIntegral.isIntegral g)) hqg

omit [CompleteSpace A] [NormOneClass A] in
/-- **BGR 3.8.2/6 (c') ⇒ (a')**: under the hypotheses of 3.8.2/5, `|f|_sup ≤ 1` makes `f`
power-bounded (the powers of `f` lie in the bounded `B̊`-module `Σ_{i<n} φ(B̊) fⁱ`). -/
theorem isPowerBounded_of_supSeminorm_le_one_of_isIntegral {C : ℝ}
    (hC : ∀ b : B, ‖algebraMap B A b‖ ≤ C * supSeminorm K b) {f : A}
    (hf : supSeminorm K f ≤ 1) : IsPowerBounded f := by
  have hq : (minpoly B f).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral f)
  -- the unit ball `B̊ = {|b|_sup ≤ 1}` is a subring of `B` containing the coefficients of `q`
  let S : Subring B :=
    { carrier := {b | supSeminorm K b ≤ 1}
      mul_mem' := fun {a b} ha hb ↦
        (supSeminorm_mul_le K a b).trans (mul_le_one₀ ha (supSeminorm_nonneg K b) hb)
      one_mem' := supSeminorm_one_le K
      add_mem' := fun {a b} ha hb ↦ (supSeminorm_add_le_max K a b).trans (max_le ha hb)
      zero_mem' := (supSeminorm_zero K).trans_le zero_le_one
      neg_mem' := fun {a} ha ↦ (supSeminorm_neg K a).trans_le ha }
  have hσ : supSpectralValue K (minpoly B f) ≤ 1 :=
    (supSeminorm_eq_supSpectralValue_minpoly K (B := B) f) ▸ hf
  -- a coefficient in `B̊` maps to an element of norm `≤ max C 0`
  have hcoef : ∀ c ∈ S, ‖algebraMap B A c‖ ≤ max C 0 := fun c hc ↦ (hC c).trans (by
    rcases le_total 0 C with hC0 | hC0
    · exact (mul_le_of_le_one_right hC0 hc).trans (le_max_left _ _)
    · exact (mul_nonpos_iff.2 (Or.inr ⟨hC0, supSeminorm_nonneg K c⟩)).trans (le_max_right _ _))
  refine isPowerBounded_of_eval₂_eq_zero (algebraMap B A) S hq (fun i ↦ ?_) hcoef ?_
  · exact (supSeminorm_coeff_le_supSpectralValue_pow_of_monic K hq i).trans
      (pow_le_one₀ (supSpectralValue_nonneg K _) hσ)
  · rw [← aeval_def]
    exact minpoly.aeval B f

/-- **BGR 3.8.2/6 (a) ⇔ (c)**: topologically nilpotent iff `|f|_sup < 1`, under 3.8.2/5. -/
theorem isTopologicallyNilpotent_iff_supSeminorm_lt_one_of_isIntegral {C : ℝ}
    (hC : ∀ b : B, ‖algebraMap B A b‖ ≤ C * supSeminorm K b) (f : A) :
    IsTopologicallyNilpotent f ↔ supSeminorm K f < 1 := by
  constructor
  · exact fun hf ↦ IsTopologicallyNilpotent.supSeminorm_lt_one K hf
  · -- `inf ‖fⁱ‖^{1/i} = |f|_sup < 1` (BGR 3.8.2/5), so some `‖fⁱ‖ < 1`
    intro hf
    rw [supSeminorm_eq_smoothingFun_of_isIntegral K hC] at hf
    obtain ⟨i, hi⟩ := exists_lt_of_ciInf_lt hf
    refine isTopologicallyNilpotent_of_norm_pow_lt_one i.ne_zero (lt_of_not_ge fun h ↦ ?_)
    exact absurd hi (not_lt.2 (Real.one_le_rpow h (by positivity)))

end Smoothing

end Affinoid
