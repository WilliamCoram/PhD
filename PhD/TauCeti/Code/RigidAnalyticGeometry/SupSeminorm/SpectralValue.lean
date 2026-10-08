/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.RigidAnalyticGeometry.SupSeminorm.Seminorm

/-!
# The spectral value of a monic polynomial for the supremum seminorm

Layer 2, §2.1.4 (second half): BGR 1.5.4 defines the spectral value
`σ(q) = max_{1 ≤ i ≤ n} |b_i|^{1/i}` of a monic polynomial `q = Xⁿ + b₁Xⁿ⁻¹ + ⋯ + bₙ` over a
seminormed ring. Mathlib's `spectralValue` needs a `SeminormedRing`, so for the supremum SEMInorm we
define `Affinoid.supSpectralValue` directly, with the same shape as `spectralValueTerms`.

## Main declarations

* `Affinoid.supSpectralValue K q`: `⨆ n, if n < natDegree q then |coeff n|_sup ^ (1/(natDegree - n))
  else 0`.
* `Affinoid.supSpectralValue_eq_spectralValue`: Mathlib's `spectralValue` when `|·|_sup = ‖·‖`.
* `Affinoid.supSpectralValue_mul_le`, `supSpectralValue_pow_le`,
  `supSpectralValue_prod_le_of_forall_le`: the inequality half of BGR 1.5.4/1,
  `σ(pq) ≤ max {σ(p), σ(q)}`.
* `Affinoid.supSpectralValue_map_le`: coefficients through a contraction (BGR 6.2.2/4,
  "`σ(p) ≥ σ(q)`").
* `Affinoid.supSeminorm_le_supSpectralValue_of_eval₂_eq_zero`: BGR 6.2.2/3 (= 3.8.1/6 (b)):
  `q(f) = 0` with `q` monic over `B` implies `|f|_sup ≤ σ(q)`.
-/

open Polynomial

namespace Affinoid

section Def

variable (K : Type*) [NormedField K] {B : Type*} [CommRing B] [Algebra K B]

/-- The terms `|coeff n q|_sup ^ (1 / (natDegree q - n))` for `n < natDegree q`, and `0`
otherwise (the shape of Mathlib's `spectralValueTerms`). -/
noncomputable def supSpectralValueTerms (q : B[X]) : ℕ → ℝ := fun n ↦
  if n < q.natDegree then supSeminorm K (q.coeff n) ^ (1 / (q.natDegree - n : ℝ)) else 0

/-- The spectral value `σ(q) = max_{1≤i≤n} |b_i|_sup^{1/i}` of a monic polynomial
`q = Xⁿ + b₁Xⁿ⁻¹ + ⋯ + bₙ` for the supremum seminorm (BGR 1.5.4). -/
noncomputable def supSpectralValue (q : B[X]) : ℝ := iSup (supSpectralValueTerms K q)

theorem supSpectralValueTerms_of_lt_natDegree (q : B[X]) {n : ℕ} (hn : n < q.natDegree) :
    supSpectralValueTerms K q n = supSeminorm K (q.coeff n) ^ (1 / (q.natDegree - n : ℝ)) := by
  simp only [supSpectralValueTerms, if_pos hn]

theorem supSpectralValueTerms_of_natDegree_le (q : B[X]) {n : ℕ} (hn : q.natDegree ≤ n) :
    supSpectralValueTerms K q n = 0 := by
  simp only [supSpectralValueTerms, if_neg (not_lt.2 hn)]

theorem supSpectralValueTerms_nonneg (q : B[X]) (n : ℕ) : 0 ≤ supSpectralValueTerms K q n := by
  simp only [supSpectralValueTerms]
  split_ifs
  · exact Real.rpow_nonneg (supSeminorm_nonneg K _) _
  · exact le_rfl

theorem supSpectralValueTerms_finite_range (q : B[X]) :
    (Set.range (supSpectralValueTerms K q)).Finite :=
  Set.Finite.subset (Set.Finite.union (Set.finite_singleton 0) <|
    (Set.finite_Iio q.natDegree).image
      fun n ↦ supSeminorm K (q.coeff n) ^ (1 / (q.natDegree - n : ℝ))) <| by
    rintro _ ⟨n, rfl⟩
    by_cases hn : n < q.natDegree
    · exact Or.inr ⟨n, hn, (supSpectralValueTerms_of_lt_natDegree K q hn).symm⟩
    · exact Or.inl (supSpectralValueTerms_of_natDegree_le K q (not_lt.1 hn))

theorem supSpectralValueTerms_bddAbove (q : B[X]) :
    BddAbove (Set.range (supSpectralValueTerms K q)) :=
  (supSpectralValueTerms_finite_range K q).bddAbove

theorem supSpectralValue_nonneg (q : B[X]) : 0 ≤ supSpectralValue K q :=
  Real.iSup_nonneg (supSpectralValueTerms_nonneg K q)

theorem supSpectralValueTerms_le_supSpectralValue (q : B[X]) (n : ℕ) :
    supSpectralValueTerms K q n ≤ supSpectralValue K q :=
  le_ciSup (supSpectralValueTerms_bddAbove K q) n

theorem supSpectralValue_le_of_forall {q : B[X]} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ n, n < q.natDegree → supSeminorm K (q.coeff n) ^ (1 / (q.natDegree - n : ℝ)) ≤ C) :
    supSpectralValue K q ≤ C :=
  ciSup_le fun n ↦ by
    by_cases hn : n < q.natDegree
    · rw [supSpectralValueTerms_of_lt_natDegree K q hn]
      exact h n hn
    · rw [supSpectralValueTerms_of_natDegree_le K q (not_lt.1 hn)]
      exact hC

theorem supSpectralValue_X_pow (n : ℕ) : supSpectralValue K (X ^ n : B[X]) = 0 := by
  refine le_antisymm (supSpectralValue_le_of_forall K le_rfl fun m hm ↦ ?_)
    (supSpectralValue_nonneg K _)
  rw [coeff_X_pow, if_neg (hm.trans_le (natDegree_X_pow_le n)).ne, supSeminorm_zero,
    Real.zero_rpow (one_div_pos.2 (sub_pos.2 (Nat.cast_lt.2 hm))).ne']

/-- BGR 1.5.4: `|b_i|_sup ≤ σ(q)^i` (here `i = natDegree - n` for the coefficient of `X^n`). -/
theorem supSeminorm_coeff_le_supSpectralValue_pow (q : B[X]) {n : ℕ} (hn : n < q.natDegree) :
    supSeminorm K (q.coeff n) ≤ supSpectralValue K q ^ (q.natDegree - n) := by
  have h := supSpectralValueTerms_le_supSpectralValue K q n
  rw [supSpectralValueTerms_of_lt_natDegree K q hn] at h
  have hcast : ((q.natDegree - n : ℕ) : ℝ) = (q.natDegree : ℝ) - n := Nat.cast_sub hn.le
  calc supSeminorm K (q.coeff n)
      = (supSeminorm K (q.coeff n) ^ (1 / (q.natDegree - n : ℝ))) ^ (q.natDegree - n) := by
        rw [← hcast, one_div,
          Real.rpow_inv_natCast_pow (supSeminorm_nonneg K _) (Nat.sub_pos_of_lt hn).ne']
    _ ≤ supSpectralValue K q ^ (q.natDegree - n) :=
        pow_le_pow_left₀ (Real.rpow_nonneg (supSeminorm_nonneg K _) _) h _

/-- For a monic `p`, `|coeff i|_sup ≤ σ(p) ^ (natDegree p - i)` for every `i`: the leading
coefficient is `1` and the coefficients above the degree vanish. -/
theorem supSeminorm_coeff_le_supSpectralValue_pow_of_monic {p : B[X]} (hp : p.Monic) (i : ℕ) :
    supSeminorm K (p.coeff i) ≤ supSpectralValue K p ^ (p.natDegree - i) := by
  rcases lt_trichotomy i p.natDegree with hi | rfl | hi
  · exact supSeminorm_coeff_le_supSpectralValue_pow K p hi
  · rw [hp.coeff_natDegree, Nat.sub_self, pow_zero]
    exact supSeminorm_one_le K
  · rw [coeff_eq_zero_of_natDegree_lt hi, supSeminorm_zero]
    exact pow_nonneg (supSpectralValue_nonneg K p) _

/-- The supremum spectral value is attained at some coefficient (finitely many terms). -/
theorem exists_supSpectralValue_eq {q : B[X]} (hq : 0 < q.natDegree) :
    ∃ n, n < q.natDegree ∧
      supSpectralValue K q = supSeminorm K (q.coeff n) ^ (1 / (q.natDegree - n : ℝ)) := by
  obtain ⟨n, hn, hmax⟩ := (Finset.range q.natDegree).exists_max_image
    (fun n ↦ supSeminorm K (q.coeff n) ^ (1 / (q.natDegree - n : ℝ))) ⟨0, Finset.mem_range.2 hq⟩
  refine ⟨n, Finset.mem_range.1 hn, le_antisymm (supSpectralValue_le_of_forall K
    (Real.rpow_nonneg (supSeminorm_nonneg K _) _) fun m hm ↦ hmax m (Finset.mem_range.2 hm)) ?_⟩
  rw [← supSpectralValueTerms_of_lt_natDegree K q (Finset.mem_range.1 hn)]
  exact supSpectralValueTerms_le_supSpectralValue K q n

end Def

section NormedRing

variable (K : Type*) [NormedField K] {B : Type*} [NormedCommRing B] [NormedAlgebra K B]

/-- When the supremum seminorm is the norm of `B`, `supSpectralValue` is Mathlib's
`spectralValue`. -/
theorem supSpectralValue_eq_spectralValue (h : ∀ b : B, supSeminorm K b = ‖b‖) (q : B[X]) :
    supSpectralValue K q = spectralValue q := by
  unfold supSpectralValue spectralValue
  congr 1
  funext n
  simp only [supSpectralValueTerms, spectralValueTerms, h]

end NormedRing

section Bounds

variable (K : Type*) [NormedField K] [IsUltrametricDist K] {A B C : Type*} [CommRing A]
  [Algebra K A] [CommRing B] [Algebra K B] [CommRing C] [Algebra K C]

omit [IsUltrametricDist K] in
/-- Coefficientwise contraction: for `φ : C →ₐ[K] B`, `σ(q.map φ) ≤ σ(q)` (BGR 3.8.1/4 applied to
each coefficient, as in the proof of 6.2.2/4). -/
theorem supSpectralValue_map_le [HasSupSeminorm K B] [HasSupSeminorm K C] (φ : C →ₐ[K] B)
    {q : C[X]} (hq : q.Monic) :
    supSpectralValue K (q.map (φ : C →+* B)) ≤ supSpectralValue K q := by
  refine supSpectralValue_le_of_forall K (supSpectralValue_nonneg K q) fun m hm ↦ ?_
  rcases subsingleton_or_nontrivial B with hB | hB
  · simp [natDegree_of_subsingleton] at hm
  rw [hq.natDegree_map] at hm ⊢
  rw [coeff_map]
  calc supSeminorm K ((φ : C →+* B) (q.coeff m)) ^ (1 / (q.natDegree - m : ℝ))
      ≤ supSeminorm K (q.coeff m) ^ (1 / (q.natDegree - m : ℝ)) :=
        Real.rpow_le_rpow (supSeminorm_nonneg K _) (supSeminorm_map_le φ _)
          (one_div_nonneg.2 (sub_nonneg.2 (Nat.cast_le.2 hm.le)))
    _ = supSpectralValueTerms K q m := (supSpectralValueTerms_of_lt_natDegree K q hm).symm
    _ ≤ supSpectralValue K q := supSpectralValueTerms_le_supSpectralValue K q m

variable [HasSupSeminorm K B]

/-- BGR 1.5.4/1 (the inequality): `σ(pq) ≤ max {σ(p), σ(q)}` for monic `p, q`. -/
theorem supSpectralValue_mul_le {p q : B[X]} (hp : p.Monic) (hq : q.Monic) :
    supSpectralValue K (p * q) ≤ max (supSpectralValue K p) (supSpectralValue K q) := by
  set s := max (supSpectralValue K p) (supSpectralValue K q) with hs_def
  have hs : 0 ≤ s := le_max_of_le_left (supSpectralValue_nonneg K p)
  refine supSpectralValue_le_of_forall K hs fun k hk ↦ ?_
  have hdeg : (p * q).natDegree = p.natDegree + q.natDegree := hp.natDegree_mul hq
  -- every term `aᵢ bⱼ` of the coefficient `c_k` is bounded by `s ^ (N - k)` (BGR 1.5.4/1 (1))
  have hterm : ∀ x ∈ Finset.HasAntidiagonal.antidiagonal k,
      supSeminorm K (p.coeff x.1 * q.coeff x.2) ≤ s ^ ((p * q).natDegree - k) := by
    rintro ⟨i, j⟩ hij
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hij
    dsimp only at hij ⊢
    rcases lt_or_ge p.natDegree i with hi | hi
    · rw [coeff_eq_zero_of_natDegree_lt hi, zero_mul, supSeminorm_zero]
      exact pow_nonneg hs _
    rcases lt_or_ge q.natDegree j with hj | hj
    · rw [coeff_eq_zero_of_natDegree_lt hj, mul_zero, supSeminorm_zero]
      exact pow_nonneg hs _
    calc supSeminorm K (p.coeff i * q.coeff j)
        ≤ supSeminorm K (p.coeff i) * supSeminorm K (q.coeff j) := supSeminorm_mul_le K _ _
      _ ≤ s ^ (p.natDegree - i) * s ^ (q.natDegree - j) :=
          mul_le_mul ((supSeminorm_coeff_le_supSpectralValue_pow_of_monic K hp i).trans
              (pow_le_pow_left₀ (supSpectralValue_nonneg K p) (le_max_left _ _) _))
            ((supSeminorm_coeff_le_supSpectralValue_pow_of_monic K hq j).trans
              (pow_le_pow_left₀ (supSpectralValue_nonneg K q) (le_max_right _ _) _))
            (supSeminorm_nonneg K _) (pow_nonneg hs _)
      _ = s ^ ((p * q).natDegree - k) := by
          rw [← pow_add, hdeg]
          congr 1
          omega
  -- the nonarchimedean inequality bounds the coefficient `c_k` by its largest term
  have hck : supSeminorm K ((p * q).coeff k) ≤ s ^ ((p * q).natDegree - k) := by
    rw [coeff_mul]
    obtain ⟨x, hx, hle⟩ := IsNonarchimedean.finset_image_add_of_nonempty
      (isNonarchimedean_supSeminorm K) (fun x : ℕ × ℕ ↦ p.coeff x.1 * q.coeff x.2)
      (⟨(0, k), Finset.HasAntidiagonal.mem_antidiagonal.2 (zero_add k)⟩ :
        (Finset.HasAntidiagonal.antidiagonal k).Nonempty)
    exact hle.trans (hterm x hx)
  -- take the `(N - k)`-th root
  calc supSeminorm K ((p * q).coeff k) ^ (1 / ((p * q).natDegree - k : ℝ))
      ≤ (s ^ ((p * q).natDegree - k)) ^ (1 / ((p * q).natDegree - k : ℝ)) :=
        Real.rpow_le_rpow (supSeminorm_nonneg K _) hck
          (one_div_nonneg.2 (sub_nonneg.2 (Nat.cast_le.2 hk.le)))
    _ = s := by
        rw [← Nat.cast_sub hk.le, one_div,
          Real.pow_rpow_inv_natCast hs (Nat.sub_pos_of_lt hk).ne']

theorem supSpectralValue_prod_le_of_forall_le {ι : Type*} {s : Finset ι} {q : ι → B[X]}
    (hq : ∀ i ∈ s, (q i).Monic) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ i ∈ s, supSpectralValue K (q i) ≤ C) : supSpectralValue K (∏ i ∈ s, q i) ≤ C := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, show (1 : B[X]) = X ^ 0 from (pow_zero X).symm, supSpectralValue_X_pow]
    exact hC
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hqs : ∀ i ∈ s, (q i).Monic := fun i hi ↦ hq i (Finset.mem_insert_of_mem hi)
    exact (supSpectralValue_mul_le K (hq a (Finset.mem_insert_self a s))
      (monic_prod_of_monic s q hqs)).trans (max_le (h a (Finset.mem_insert_self a s))
        (ih hqs fun i hi ↦ h i (Finset.mem_insert_of_mem hi)))

theorem supSpectralValue_pow_le {q : B[X]} (hq : q.Monic) (e : ℕ) :
    supSpectralValue K (q ^ e) ≤ supSpectralValue K q := by
  induction e with
  | zero =>
    rw [pow_zero, show (1 : B[X]) = X ^ 0 from (pow_zero X).symm, supSpectralValue_X_pow]
    exact supSpectralValue_nonneg K q
  | succ e ih =>
    rw [pow_succ]
    exact (supSpectralValue_mul_le K (hq.pow e) hq).trans (max_le ih le_rfl)

/-- BGR 6.2.2/3 (= 3.8.1/6 (b)): if `fⁿ + φ(b₁)fⁿ⁻¹ + ⋯ + φ(bₙ) = 0`, then
`|f|_sup ≤ max_i |b_i|_sup^{1/i} = σ(q)`. The proof is purely seminorm-theoretic (BGR p. 239):
`|f|ⁿ_sup = |fⁿ|_sup ≤ |φ(b_j) fⁿ⁻ʲ|_sup ≤ |b_j|_sup |f|_sup^{n−j}` for some `j`. -/
theorem supSeminorm_le_supSpectralValue_of_eval₂_eq_zero [HasSupSeminorm K A] (φ : B →ₐ[K] A)
    {q : B[X]} (hq : q.Monic) {f : A} (hf : q.eval₂ (φ : B →+* A) f = 0) :
    supSeminorm K f ≤ supSpectralValue K q := by
  rcases Nat.eq_zero_or_pos q.natDegree with hn0 | hn
  · -- `q = 1`, so `A` is the zero ring and `f = 0`
    rw [eq_one_of_monic_natDegree_zero hq hn0, eval₂_one] at hf
    have hf0 : f = 0 := by rw [← mul_one f, hf, mul_zero]
    rw [hf0, supSeminorm_zero]
    exact supSpectralValue_nonneg K q
  -- `fⁿ = -∑_{i<n} φ(bᵢ) fⁱ`
  have hsum : f ^ q.natDegree = -∑ i ∈ Finset.range q.natDegree, φ (q.coeff i) * f ^ i := by
    rw [eval₂_eq_sum_range, Finset.sum_range_succ, hq.coeff_natDegree, map_one, one_mul] at hf
    exact eq_neg_of_add_eq_zero_right hf
  -- some term dominates the sum (BGR p. 239)
  obtain ⟨j, hj, hle⟩ := IsNonarchimedean.finset_image_add_of_nonempty
    (isNonarchimedean_supSeminorm K) (fun i ↦ φ (q.coeff i) * f ^ i)
    (Finset.nonempty_range_iff.2 hn.ne')
  have hjn : j < q.natDegree := Finset.mem_range.1 hj
  have key : supSeminorm K f ^ q.natDegree ≤ supSeminorm K (q.coeff j) * supSeminorm K f ^ j :=
    calc supSeminorm K f ^ q.natDegree = supSeminorm K (f ^ q.natDegree) :=
          (supSeminorm_pow K f hn.ne').symm
      _ = supSeminorm K (∑ i ∈ Finset.range q.natDegree, φ (q.coeff i) * f ^ i) := by
          rw [hsum, supSeminorm_neg]
      _ ≤ supSeminorm K (φ (q.coeff j) * f ^ j) := hle
      _ ≤ supSeminorm K (φ (q.coeff j)) * supSeminorm K (f ^ j) := supSeminorm_mul_le K _ _
      _ ≤ supSeminorm K (q.coeff j) * supSeminorm K f ^ j :=
          mul_le_mul (supSeminorm_map_le φ _) (supSeminorm_pow_le K f j)
            (supSeminorm_nonneg K _) (supSeminorm_nonneg K _)
  rcases (supSeminorm_nonneg K f).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact supSpectralValue_nonneg K q
  -- divide by `|f|ʲ` and take the `(n - j)`-th root
  have hdiv : supSeminorm K f ^ (q.natDegree - j) ≤ supSeminorm K (q.coeff j) :=
    le_of_mul_le_mul_right (by rwa [pow_sub_mul_pow _ hjn.le]) (pow_pos hpos j)
  calc supSeminorm K f
      = (supSeminorm K f ^ (q.natDegree - j)) ^ ((q.natDegree - j : ℕ) : ℝ)⁻¹ :=
        (Real.pow_rpow_inv_natCast hpos.le (Nat.sub_pos_of_lt hjn).ne').symm
    _ ≤ supSeminorm K (q.coeff j) ^ ((q.natDegree - j : ℕ) : ℝ)⁻¹ :=
        Real.rpow_le_rpow (pow_nonneg hpos.le _) hdiv (inv_nonneg.2 (Nat.cast_nonneg _))
    _ = supSpectralValueTerms K q j := by
        rw [supSpectralValueTerms_of_lt_natDegree K q hjn, Nat.cast_sub hjn.le, one_div]
    _ ≤ supSpectralValue K q := supSpectralValueTerms_le_supSpectralValue K q j

end Bounds

end Affinoid
