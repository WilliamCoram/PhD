/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.«01_AmiceValuation»
import PhD.LWX.«07_PowSubOne»
import PhD.TateFredholm.«06_Unitriangular»

/-!
# Amice's theorem at level `h`: the Colmez basis of the disc model — SKELETON

[LWX, §2.16] (quoting [Colmez, Thm 1.4.7]): "the functions `⌊n/(q⁻¹pᵐ)⌋!·(z choose n)`, `n ≥ 0`,
form an orthonormal basis of `OB_{qp^{-m}}` for the norm `|·|_{qp^{-m},an}`".  With `h = m − 1`
(odd `p`), `OB_{p^{-h}}` — the functions analytic on every disc `a + pʰℤ_p` with the max of the
Gauss norms — is modelled by `c(ZMod (p^h) × ℕ, K)`: the Taylor coefficients on each disc in the
coordinate `z = a + pʰw`, `a` the natural representative.

Colmez's proof orders the basis by `n = (m(n)+1)pʰ − i(n)`, `1 ≤ i(n) ≤ pʰ`, and the discs by
their centres `−i(n)`; in that order the reduction of the basis-change matrix is "block upper
triangular … each diagonal block lower triangular with invertible diagonal entries".  Here the
same order is `discIdx (a, k) = k·pʰ + (pʰ − 1 − a)` on the disc model (increasing in the Taylor
degree `k`, **decreasing** in the disc `a`), and the position of `g_n` in it is `revIdx (pʰ) n`,
the reversal of each block of `pʰ` consecutive integers.  Reindexing the columns by that same
involution makes the matrix a perturbed unitriangular matrix (`06_Unitriangular.lean`), hence an
isometric equivalence `colmezDiscEquiv`; the two reindexings cancel in
`matrixCoeff_colmezToDisc`, so `colmezToDisc` sends `eₙ` to the disc model of `g_n` on the nose.

The diagonal `diag(⌊n/pʰ⌋!)` then turns Colmez coordinates into Mahler coefficients
(`discToMahler`), and the Mahler coefficients of a disc-model function are the forward
differences of its values at `ℕ`-points (`discToMahler_apply_eq_fwdDiff`), the level-`h` form of
`fwdDiff_iter_evalAt_natCast`.

## Main declarations

* `LWX.discIdx`, `LWX.revIdx`, `LWX.lt_discIdx_iff` — Colmez's order and the position of `g_n`.
* `LWX.discCoeff`, `LWX.colmezMatrix`, `LWX.isUnitriangularPerturbation_colmezMatrix`.
* `LWX.colmezToDisc`, `LWX.norm_colmezToDisc`, `LWX.surjective_colmezToDisc`,
  **`LWX.colmezDiscEquiv`**.
* `LWX.diagFactorialH`, `LWX.discToMahler`, `LWX.discCoord`, `LWX.discEval`,
  **`LWX.discToMahler_apply_eq_fwdDiff`**.
-/

open Filter Topology TateFredholm QMF

open scoped Nat TateFredholm fwdDiff

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]

section Index

private theorem sub_one_sub_lt {q : ℕ} (hq : 0 < q) (r : ℕ) : q - 1 - r < q := by omega

private theorem div_mul_add_mod (q n : ℕ) : n / q * q + n % q = n := by
  rw [Nat.mul_comm (n / q) q]
  exact Nat.div_add_mod n q

private theorem div_mul_add_sub_sub {q : ℕ} (hq : 0 < q) (n : ℕ) :
    n / q * q + (q - 1 - (q - 1 - n % q)) = n := by
  have hm : n % q < q := Nat.mod_lt _ hq
  have hdm := div_mul_add_mod q n
  omega

/-- Colmez's order compares first by the Taylor degree and then by the **reversed** disc. -/
private theorem lt_add_sub_iff {q : ℕ} (hq : 0 < q) {k k' r r' : ℕ} (hr : r < q) (hr' : r' < q) :
    k * q + (q - 1 - r) < k' * q + (q - 1 - r') ↔ k < k' ∨ (k' = k ∧ r' < r) := by
  rcases lt_trichotomy k k' with hk | hk | hk
  · have h1 : (k + 1) * q ≤ k' * q := Nat.mul_le_mul_right q hk
    rw [add_mul, one_mul] at h1
    exact ⟨fun _ => Or.inl hk, fun _ => by omega⟩
  · subst hk
    exact ⟨fun hlt => Or.inr ⟨rfl, by omega⟩, fun hc => by
      rcases hc with h | ⟨_, h⟩ <;> omega⟩
  · have h1 : (k' + 1) * q ≤ k * q := Nat.mul_le_mul_right q hk
    rw [add_mul, one_mul] at h1
    exact ⟨fun hlt => by omega, fun hc => by rcases hc with h | ⟨h, _⟩ <;> omega⟩

/-- **The reversal of each block of `q` consecutive integers**: `n ↦ ⌊n/q⌋q + (q − 1 − n mod q)`,
an involution of `ℕ`.  It is the position of the Colmez basis element `g_n` in the order
`discIdx` below (Colmez's `n = (m(n)+1)pʰ − i(n)` read forwards). -/
def revIdx (q : ℕ) [NeZero q] : ℕ ≃ ℕ where
  toFun n := n / q * q + (q - 1 - n % q)
  invFun n := n / q * q + (q - 1 - n % q)
  left_inv n := by
    have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    have hd : (n / q * q + (q - 1 - n % q)) / q = n / q := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq,
        Nat.div_eq_of_lt (sub_one_sub_lt hq _), Nat.zero_add]
    have hr : (n / q * q + (q - 1 - n % q)) % q = q - 1 - n % q := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (sub_one_sub_lt hq _)]
    show (n / q * q + (q - 1 - n % q)) / q * q + (q - 1 - (n / q * q + (q - 1 - n % q)) % q) = n
    rw [hd, hr]
    exact div_mul_add_sub_sub hq n
  right_inv n := by
    have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
    have hd : (n / q * q + (q - 1 - n % q)) / q = n / q := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq,
        Nat.div_eq_of_lt (sub_one_sub_lt hq _), Nat.zero_add]
    have hr : (n / q * q + (q - 1 - n % q)) % q = q - 1 - n % q := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (sub_one_sub_lt hq _)]
    show (n / q * q + (q - 1 - n % q)) / q * q + (q - 1 - (n / q * q + (q - 1 - n % q)) % q) = n
    rw [hd, hr]
    exact div_mul_add_sub_sub hq n

theorem revIdx_apply (q : ℕ) [NeZero q] (n : ℕ) :
    revIdx q n = n / q * q + (q - 1 - n % q) := rfl

theorem revIdx_div (q : ℕ) [NeZero q] (n : ℕ) : revIdx q n / q = n / q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hm : n % q < q := Nat.mod_lt _ hq
  rw [revIdx_apply, Nat.add_comm, Nat.add_mul_div_right _ _ hq, Nat.div_eq_of_lt (by omega),
    Nat.zero_add]

theorem revIdx_revIdx (q : ℕ) [NeZero q] (n : ℕ) : revIdx q (revIdx q n) = n :=
  (revIdx q).left_inv n

theorem revIdx_mod (q : ℕ) [NeZero q] (n : ℕ) : revIdx q n % q = q - 1 - n % q := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hm : n % q < q := Nat.mod_lt _ hq
  rw [revIdx_apply, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]

/-- **Colmez's order on the disc model**: `(a, k) ↦ k·pʰ + (pʰ − 1 − a)`, increasing in the Taylor
degree `k` and decreasing in the disc `a` ([Colmez, proof of Thm 1.4.7]: "block upper triangular …
each diagonal block lower triangular with invertible diagonal entries"). -/
def discIdx (h : ℕ) : ZMod (p ^ h) × ℕ ≃ ℕ where
  toFun x := x.2 * p ^ h + (p ^ h - 1 - x.1.val)
  invFun n := (((p ^ h - 1 - n % p ^ h : ℕ) : ZMod (p ^ h)), n / p ^ h)
  left_inv x := by
    obtain ⟨a, k⟩ := x
    have hq : 0 < p ^ h := pow_pos hp.out.pos h
    have hv : a.val < p ^ h := ZMod.val_lt a
    have hd : (k * p ^ h + (p ^ h - 1 - a.val)) / p ^ h = k := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hq,
        Nat.div_eq_of_lt (sub_one_sub_lt hq _), Nat.zero_add]
    have hr : (k * p ^ h + (p ^ h - 1 - a.val)) % p ^ h = p ^ h - 1 - a.val := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (sub_one_sub_lt hq _)]
    show ((((p ^ h - 1 - (k * p ^ h + (p ^ h - 1 - a.val)) % p ^ h : ℕ)) : ZMod (p ^ h)),
      (k * p ^ h + (p ^ h - 1 - a.val)) / p ^ h) = (a, k)
    rw [hd, hr, show p ^ h - 1 - (p ^ h - 1 - a.val) = a.val from by omega,
      ZMod.natCast_val, ZMod.cast_id]
  right_inv n := by
    have hq : 0 < p ^ h := pow_pos hp.out.pos h
    show n / p ^ h * p ^ h
      + (p ^ h - 1 - (((p ^ h - 1 - n % p ^ h : ℕ) : ZMod (p ^ h))).val) = n
    rw [ZMod.val_natCast_of_lt (sub_one_sub_lt hq _)]
    exact div_mul_add_sub_sub hq n

theorem discIdx_apply (h : ℕ) (a : ZMod (p ^ h)) (k : ℕ) :
    discIdx (p := p) h (a, k) = k * p ^ h + (p ^ h - 1 - a.val) := rfl

theorem discIdx_symm_apply (h n : ℕ) :
    (discIdx (p := p) h).symm n = (((p ^ h - 1 - n % p ^ h : ℕ) : ZMod (p ^ h)), n / p ^ h) := rfl

/-- **The diagonal position of `g_n`** in Colmez's order is `revIdx (pʰ) n`. -/
theorem discIdx_res_div (h n : ℕ) :
    discIdx (p := p) h (((n % p ^ h : ℕ) : ZMod (p ^ h)), n / p ^ h) = revIdx (p ^ h) n := by
  rw [discIdx_apply, revIdx_apply,
    ZMod.val_natCast_of_lt (Nat.mod_lt _ (pow_pos hp.out.pos h))]

/-- The disc-coefficient array of the Colmez basis element `g_n`: the `k`-th Taylor coefficient of
`g_n` on the disc `a`. -/
def discCoeff (h n : ℕ) (x : ZMod (p ^ h) × ℕ) : ℚ_[p] := (discPoly h n x.1.val).coeff x.2

/-- **The unitriangularity criterion in Colmez's order**: a position `x` lies strictly beyond the
diagonal position of `g_n` iff its Taylor degree exceeds `⌊n/pʰ⌋`, or equals it on a disc below
`n mod pʰ` — exactly the two cases in which `01_AmiceValuation.lean` gives a `p`-divisible
coefficient. -/
theorem lt_discIdx_iff (h n : ℕ) (x : ZMod (p ^ h) × ℕ) :
    revIdx (p ^ h) n < discIdx (p := p) h x
      ↔ n / p ^ h < x.2 ∨ (x.2 = n / p ^ h ∧ x.1.val < n % p ^ h) := by
  have hq : 0 < p ^ h := pow_pos hp.out.pos h
  rw [revIdx_apply, discIdx_apply]
  exact lt_add_sub_iff hq (Nat.mod_lt _ hq) (ZMod.val_lt x.1)

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] (ψ : ℚ_[p] →+* K)

/-- The disc-coefficient matrix, with rows in Colmez's order and the columns reindexed by the
same reversal so that the diagonal sits on the diagonal. -/
def colmezMatrix (h : ℕ) : ℕ → ℕ → K :=
  fun k n => ψ (discCoeff h (revIdx (p ^ h) n) ((discIdx h).symm k))

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **[Colmez, Lemme 1.4.9] packaged**: in Colmez's order the disc-coefficient matrix is a
perturbed unitriangular matrix with `q = p⁻¹` — integral entries (`norm_coeff_discPoly_le`), unit
diagonal (`norm_coeff_discPoly_diag`), `p`-divisible below the diagonal
(`norm_coeff_discPoly_le_inv_of_lt` and `norm_coeff_discPoly_le_inv_of_res_lt` through
`lt_discIdx_iff`), finitely supported columns (`natDegree_discPoly_le`). -/
theorem isUnitriangularPerturbation_colmezMatrix (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h : ℕ) :
    IsUnitriangularPerturbation (colmezMatrix ψ h) (p : ℝ)⁻¹ := by
  have hq : 0 < p ^ h := pow_pos hp.out.pos h
  have hval : ∀ k : ℕ, ((discIdx (p := p) h).symm k).1.val = p ^ h - 1 - k % p ^ h := fun k => by
    rw [discIdx_symm_apply, ZMod.val_natCast_of_lt (sub_one_sub_lt hq _)]
  have hsnd : ∀ k : ℕ, ((discIdx (p := p) h).symm k).2 = k / p ^ h := fun _ => rfl
  refine ⟨inv_pos.mpr (by exact_mod_cast hp.out.pos),
    inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt), fun k n => ?_, fun n => ?_,
    fun k n hnk => ?_, fun n => ?_⟩
  · rw [colmezMatrix, hψ, discCoeff]
    exact norm_coeff_discPoly_le _ _ _ (ZMod.val_lt _) _
  · rw [colmezMatrix, hψ, discCoeff, hval, hsnd,
      show p ^ h - 1 - n % p ^ h = revIdx (p ^ h) n % p ^ h from (revIdx_mod _ _).symm,
      show n / p ^ h = revIdx (p ^ h) n / p ^ h from (revIdx_div _ _).symm]
    exact norm_coeff_discPoly_diag _ _
  · have hlt : revIdx (p ^ h) (revIdx (p ^ h) n) < discIdx (p := p) h ((discIdx h).symm k) := by
      rw [revIdx_revIdx, Equiv.apply_symm_apply]
      exact hnk
    rw [colmezMatrix, hψ, discCoeff]
    rcases (lt_discIdx_iff h (revIdx (p ^ h) n) _).mp hlt with hcase | ⟨hk2, hk1⟩
    · exact norm_coeff_discPoly_le_inv_of_lt _ _ _ (ZMod.val_lt _) hcase
    · rw [hk2]
      exact norm_coeff_discPoly_le_inv_of_res_lt _ _ _ hk1
  · refine Set.Finite.subset (Set.finite_Iio ((revIdx (p ^ h) n + 1) * p ^ h)) fun k hk => ?_
    rw [Set.mem_ofPred_eq, colmezMatrix, ne_eq, ← norm_eq_zero, hψ, norm_eq_zero] at hk
    by_contra hcon
    rw [Set.mem_Iio, not_lt] at hcon
    refine hk ?_
    rw [discCoeff, hsnd]
    refine Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (natDegree_discPoly_le _ _ _) ?_)
    have h1 : (revIdx (p ^ h) n + 1) * p ^ h ≤ k := hcon
    have h2 : revIdx (p ^ h) n + 1 ≤ k / p ^ h := (Nat.le_div_iff_mul_le hq).mpr (by linarith)
    omega

end Index

section Basis

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] (ψ : ℚ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h : ℕ)

omit [CharZero K] in
/-- Reindexing `c(ℕ, K) → c(J, K)` along a bijection `J ≃ ℕ` is an isometry. -/
theorem norm_comap_equiv {J : Type*} (e : J ≃ ℕ) (f : c(ℕ, K)) :
    ‖cSpace.comap (⇑e) e.injective f‖ = ‖f‖ := by
  rw [cSpace.norm_eq_iSup, cSpace.norm_eq_iSup]
  exact e.iSup_comp (g := fun n => ‖f n‖)

omit [CharZero K] in
/-- Reindexing along a bijection is surjective. -/
theorem surjective_comap_equiv {J : Type*} (e : J ≃ ℕ) :
    Function.Surjective (cSpace.comap (R := K) (⇑e) e.injective) := fun g =>
  ⟨cSpace.comap (⇑e.symm) e.symm.injective g, DFunLike.ext _ _ fun j => by
    show g (e.symm (e j)) = g j
    rw [Equiv.symm_apply_apply]⟩

/-- **Colmez coordinates to the disc model**: `(c_n) ↦ ∑ c_n·g_n`, read as Taylor coefficients on
each disc.  The two reindexings by `revIdx` and `discIdx` cancel, giving the matrix
`matrixCoeff_colmezToDisc`. -/
def colmezToDisc : c(ℕ, K) →L[K] c(ZMod (p ^ h) × ℕ, K) :=
  ((cSpace.comap (⇑(discIdx h)) (discIdx h).injective).comp
    (ofPerturbation (isUnitriangularPerturbation_colmezMatrix ψ hψ h))).comp
    (cSpace.comap (⇑(revIdx (p ^ h))) (revIdx (p ^ h)).injective)

omit [CharZero K] in
/-- Reindexing a basis vector by the reversal. -/
private theorem comap_revIdx_single (n : ℕ) :
    cSpace.comap (⇑(revIdx (p ^ h))) (revIdx (p ^ h)).injective (cSpace.single n (1 : K))
      = cSpace.single (revIdx (p ^ h) n) 1 :=
  DFunLike.ext _ _ fun m => by
    show cSpace.single n (1 : K) (revIdx (p ^ h) m) = _
    by_cases hm : m = revIdx (p ^ h) n
    · subst hm
      rw [revIdx_revIdx, cSpace.single_apply_self, cSpace.single_apply_self]
    · rw [cSpace.single_apply_of_ne (fun hc => hm (by rw [← hc, revIdx_revIdx])),
        cSpace.single_apply_of_ne hm]

omit [CharZero K] in
/-- The matrix of `colmezToDisc` is the disc-coefficient array itself (the reversals cancel). -/
theorem matrixCoeff_colmezToDisc (x : ZMod (p ^ h) × ℕ) (n : ℕ) :
    matrixCoeff (colmezToDisc ψ hψ h) x n = ψ (discCoeff h n x) := by
  show ofPerturbation (isUnitriangularPerturbation_colmezMatrix ψ hψ h)
    (cSpace.comap (⇑(revIdx (p ^ h))) (revIdx (p ^ h)).injective (cSpace.single n (1 : K)))
      (discIdx h x) = _
  rw [comap_revIdx_single, ofPerturbation_apply,
    tsum_eq_single (revIdx (p ^ h) n) fun j hj => by
      rw [cSpace.single_apply_of_ne hj, mul_zero],
    cSpace.single_apply_self, mul_one, colmezMatrix, Equiv.symm_apply_apply, revIdx_revIdx]

omit [CharZero K] in
theorem colmezToDisc_apply (c : c(ℕ, K)) (x : ZMod (p ^ h) × ℕ) :
    colmezToDisc ψ hψ h c x = ∑' n, ψ (discCoeff h n x) * c n := by
  show ofPerturbation (isUnitriangularPerturbation_colmezMatrix ψ hψ h)
    (cSpace.comap (⇑(revIdx (p ^ h))) (revIdx (p ^ h)).injective c) (discIdx h x) = _
  rw [ofPerturbation_apply, ← (revIdx (p ^ h)).tsum_eq
    fun j => colmezMatrix ψ h (discIdx h x) j
      * cSpace.comap (⇑(revIdx (p ^ h))) (revIdx (p ^ h)).injective c j]
  refine tsum_congr fun n => ?_
  show colmezMatrix ψ h (discIdx h x) (revIdx (p ^ h) n) * c (revIdx (p ^ h) (revIdx (p ^ h) n))
    = _
  rw [revIdx_revIdx, colmezMatrix, Equiv.symm_apply_apply, revIdx_revIdx]

omit [CharZero K] in
/-- **Amice's theorem, isometry half**: `‖∑ c_n g_n‖ = sup ‖c_n‖`. -/
theorem norm_colmezToDisc (c : c(ℕ, K)) : ‖colmezToDisc ψ hψ h c‖ = ‖c‖ := by
  show ‖cSpace.comap (⇑(discIdx h)) (discIdx h).injective
    (ofPerturbation (isUnitriangularPerturbation_colmezMatrix ψ hψ h)
      (cSpace.comap (⇑(revIdx (p ^ h))) (revIdx (p ^ h)).injective c))‖ = _
  rw [norm_comap_equiv (discIdx h), norm_ofPerturbation, norm_comap_equiv (revIdx (p ^ h))]

omit [CharZero K] in
/-- **Amice's theorem, completeness half**: every disc-model function has Colmez coordinates. -/
theorem surjective_colmezToDisc : Function.Surjective (colmezToDisc ψ hψ h) := fun g => by
  obtain ⟨y, hy⟩ := surjective_comap_equiv (K := K) (discIdx (p := p) h) g
  obtain ⟨z, hz⟩ := surjective_ofPerturbation (isUnitriangularPerturbation_colmezMatrix ψ hψ h) y
  obtain ⟨c, hc⟩ := surjective_comap_equiv (K := K) (revIdx (p ^ h)) z
  refine ⟨c, ?_⟩
  show cSpace.comap (⇑(discIdx h)) (discIdx h).injective
    (ofPerturbation (isUnitriangularPerturbation_colmezMatrix ψ hψ h)
      (cSpace.comap (⇑(revIdx (p ^ h))) (revIdx (p ^ h)).injective c)) = g
  rw [hc, hz, hy]

omit [CharZero K] in
theorem injective_colmezToDisc : Function.Injective (colmezToDisc ψ hψ h) := fun x y hxy => by
  rw [← sub_eq_zero, ← norm_eq_zero, ← norm_colmezToDisc ψ hψ h, map_sub, hxy, sub_self,
    norm_zero]

/-- **The Colmez basis of the disc model** as an isometric continuous linear equivalence
([Colmez, Thm 1.4.7]; [LWX, §2.16]). -/
def colmezDiscEquiv : c(ℕ, K) ≃L[K] c(ZMod (p ^ h) × ℕ, K) :=
  let e := LinearEquiv.ofBijective (colmezToDisc ψ hψ h).toLinearMap
    ⟨injective_colmezToDisc ψ hψ h, surjective_colmezToDisc ψ hψ h⟩
  { e with
    continuous_toFun := (colmezToDisc ψ hψ h).continuous
    continuous_invFun := AddMonoidHomClass.continuous_of_bound e.symm 1 fun b => by
      rw [one_mul]
      have hb := norm_colmezToDisc ψ hψ h (e.symm b)
      rw [show colmezToDisc ψ hψ h (e.symm b) = b from e.apply_symm_apply b] at hb
      exact hb.symm.le }

omit [CharZero K] in
@[simp] theorem coe_colmezDiscEquiv :
    (colmezDiscEquiv ψ hψ h : c(ℕ, K) →L[K] c(ZMod (p ^ h) × ℕ, K)) = colmezToDisc ψ hψ h := rfl

/-- The diagonal `diag(⌊n/pʰ⌋!)` of [LWX, Prop 2.17, proof] at level `h`. -/
def diagFactorialH : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofCoeffs (fun m k => if m = k then (((m / p ^ h)! : ℕ) : K) else 0)
    ⟨1, fun m k => by
      split_ifs
      · exact IsUltrametricDist.norm_natCast_le_one K _
      · simp⟩
    (fun k => by
      refine tendsto_const_nhds.congr' ?_
      rw [Filter.EventuallyEq, Filter.eventually_cofinite]
      refine (Set.finite_singleton k).subset fun m hm => ?_
      rw [Set.mem_singleton_iff]
      by_contra hcon
      exact hm (by simp [hcon]))

omit hp [CharZero K] in
theorem matrixCoeff_diagFactorialH (m k : ℕ) :
    matrixCoeff (diagFactorialH (p := p) (K := K) h) m k
      = if m = k then (((m / p ^ h)! : ℕ) : K) else 0 :=
  matrixCoeff_ofCoeffs _ _ _ m k

/-- **Disc model to Mahler coefficients**: `diag(⌊n/pʰ⌋!) ∘ colmezDiscEquiv⁻¹`. -/
def discToMahler : c(ZMod (p ^ h) × ℕ, K) →L[K] c(ℕ, K) :=
  (diagFactorialH (p := p) h).comp
    ((colmezDiscEquiv ψ hψ h).symm : c(ZMod (p ^ h) × ℕ, K) →L[K] c(ℕ, K))

omit [CharZero K] in
theorem discToMahler_colmezToDisc (c : c(ℕ, K)) (m : ℕ) :
    discToMahler ψ hψ h (colmezToDisc ψ hψ h c) m = (((m / p ^ h)! : ℕ) : K) * c m := by
  have hsymm : (colmezDiscEquiv ψ hψ h).symm (colmezToDisc ψ hψ h c) = c :=
    (colmezDiscEquiv ψ hψ h).symm_apply_apply c
  show diagFactorialH (p := p) h ((colmezDiscEquiv ψ hψ h).symm (colmezToDisc ψ hψ h c)) m = _
  rw [hsymm, diagFactorialH, ofCoeffs_apply,
    tsum_eq_single m fun i hi => by rw [if_neg (Ne.symm hi), zero_mul], if_pos rfl]

end Basis

section Evaluation

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K] (ψ : ℚ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h : ℕ)

/-- The disc coordinate `w = (z − appr z h)/pʰ ∈ ℤ_p` of `z ∈ ℤ_p` (`appr_spec`). -/
def discCoord (z : ℤ_[p]) : ℤ_[p] :=
  ⟨((z : ℚ_[p]) - (z.appr h : ℚ_[p])) / (p : ℚ_[p]) ^ h, by
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp (PadicInt.appr_spec h z)
    have hp0 : ((p : ℚ_[p]) ^ h) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
    have hcast : (z : ℚ_[p]) - (z.appr h : ℚ_[p]) = (p : ℚ_[p]) ^ h * (y : ℚ_[p]) := by
      have hy' := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) hy
      push_cast at hy'
      exact hy'
    rw [hcast, mul_div_cancel_left₀ _ hp0]
    exact y.2⟩

theorem coe_discCoord (z : ℤ_[p]) :
    (discCoord h z : ℚ_[p]) = ((z : ℚ_[p]) - (z.appr h : ℚ_[p])) / (p : ℚ_[p]) ^ h := rfl

/-- `z = appr z h + pʰ·w`. -/
theorem appr_add_pow_mul_discCoord (z : ℤ_[p]) :
    (z.appr h : ℤ_[p]) + (p : ℤ_[p]) ^ h * discCoord h z = z := by
  have hp0 : ((p : ℚ_[p]) ^ h) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  refine Subtype.ext ?_
  show (z.appr h : ℚ_[p]) + (p : ℚ_[p]) ^ h
    * (((z : ℚ_[p]) - (z.appr h : ℚ_[p])) / (p : ℚ_[p]) ^ h) = (z : ℚ_[p])
  field_simp
  ring

/-- The approximation of a natural number is its residue. -/
theorem appr_natCast (j : ℕ) : (j : ℤ_[p]).appr h = j % p ^ h := by
  have hq : 0 < p ^ h := pow_pos hp.out.pos h
  have h1 : (j : ℤ_[p]).appr h < p ^ h := PadicInt.appr_lt _ _
  have h2 : j % p ^ h < p ^ h := Nat.mod_lt _ hq
  have hmod : ((j : ℤ_[p]) - ((j % p ^ h : ℕ) : ℤ_[p])) ∈ Ideal.span {(p : ℤ_[p]) ^ h} := by
    refine Ideal.mem_span_singleton.mpr ⟨((j / p ^ h : ℕ) : ℤ_[p]), ?_⟩
    have hj : (j / p ^ h) * p ^ h + j % p ^ h = j := div_mul_add_mod (p ^ h) j
    have : ((j : ℕ) : ℤ_[p]) = ((p ^ h * (j / p ^ h) + j % p ^ h : ℕ) : ℤ_[p]) := by
      rw [show p ^ h * (j / p ^ h) + j % p ^ h = j from by rw [Nat.mul_comm]; exact hj]
    rw [this]
    push_cast
    ring
  have hz := PadicInt.zmod_congr_of_sub_mem_span h (j : ℤ_[p]) _ _
    (PadicInt.appr_spec h (j : ℤ_[p])) hmod
  have := congrArg ZMod.val hz
  rwa [ZMod.val_natCast_of_lt h1, ZMod.val_natCast_of_lt h2] at this

theorem discCoord_natCast (j : ℕ) : discCoord h (j : ℤ_[p]) = ((j / p ^ h : ℕ) : ℤ_[p]) := by
  have hp0 : ((p : ℚ_[p]) ^ h) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  have hj : (j / p ^ h) * p ^ h + j % p ^ h = j := div_mul_add_mod (p ^ h) j
  refine Subtype.ext ?_
  show (((j : ℤ_[p]) : ℚ_[p]) - (((j : ℤ_[p]).appr h : ℕ) : ℚ_[p])) / (p : ℚ_[p]) ^ h
    = (((j / p ^ h : ℕ)) : ℚ_[p])
  rw [appr_natCast, div_eq_iff hp0]
  have : ((j : ℕ) : ℚ_[p]) = ((j / p ^ h : ℕ) : ℚ_[p]) * (p : ℚ_[p]) ^ h
      + ((j % p ^ h : ℕ) : ℚ_[p]) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_add, hj]
  push_cast at this ⊢
  linear_combination this

/-- **Evaluation of a disc-model function at `z ∈ ℤ_p`**: the Taylor series of the disc of `z`
at the coordinate `(z − appr z h)/pʰ`. -/
def discEval (f : c(ZMod (p ^ h) × ℕ, K)) (z : ℤ_[p]) : K :=
  evalAt (PowerSeries.mk fun k => f (((z.appr h : ℕ) : ZMod (p ^ h)), k)) (intHom ψ (discCoord h z))

/-- The disc-coefficient array vanishes beyond the degree of `g_n`. -/
private theorem discCoeff_eq_zero_of_lt {h n : ℕ} {x : ZMod (p ^ h) × ℕ} (hx : n < x.2) :
    discCoeff (p := p) h n x = 0 := by
  rw [discCoeff]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt
    (lt_of_le_of_lt (natDegree_discPoly_le _ _ _) hx)

/-- The disc model of `∑ c_n g_n` takes the value `∑ c_n·⌊n/pʰ⌋!·C(j, n)` at `j ∈ ℕ`. -/
theorem discEval_colmezToDisc_natCast (c : c(ℕ, K)) (j : ℕ) :
    discEval ψ h (colmezToDisc ψ hψ h c) (j : ℤ_[p])
      = ∑' n, c n * (((n / p ^ h)! * j.choose n : ℕ) : K) := by
  classical
  rw [discEval, appr_natCast, discCoord_natCast, map_natCast, evalAt]
  set a : ZMod (p ^ h) := ((j % p ^ h : ℕ) : ZMod (p ^ h)) with ha
  set w : K := ((j / p ^ h : ℕ) : K) with hw
  have hav : a.val = j % p ^ h := by
    rw [ha, ZMod.val_natCast_of_lt (Nat.mod_lt _ (pow_pos hp.out.pos h))]
  have hw1 : ‖w‖ ≤ 1 := by
    rw [hw]
    exact IsUltrametricDist.norm_natCast_le_one K _
  have hzero : ∀ x : ℕ × ℕ, x.2 < x.1 →
      ψ (discCoeff h x.2 (a, x.1)) * c x.2 * w ^ x.1 = 0 := fun x hx => by
    rw [discCoeff_eq_zero_of_lt (x := (a, x.1)) hx, map_zero, zero_mul, zero_mul]
  have hbd : ∀ x : ℕ × ℕ, ‖ψ (discCoeff h x.2 (a, x.1)) * c x.2 * w ^ x.1‖ ≤ ‖c x.2‖ := by
    intro x
    rw [norm_mul, norm_mul, hψ]
    calc ‖discCoeff h x.2 (a, x.1)‖ * ‖c x.2‖ * ‖w ^ x.1‖
        ≤ 1 * ‖c x.2‖ * 1 := by
          refine mul_le_mul (mul_le_mul_of_nonneg_right
            (norm_coeff_discPoly_le _ _ _ (ZMod.val_lt _) _) (norm_nonneg _)) ?_
            (norm_nonneg _) (by positivity)
          rw [norm_pow]
          exact pow_le_one₀ (norm_nonneg _) hw1
      _ = ‖c x.2‖ := by ring
  have hsum : Summable fun x : ℕ × ℕ => ψ (discCoeff h x.2 (a, x.1)) * c x.2 * w ^ x.1 := by
    refine TateFredholm.summable_of_tendsto_cofinite (Metric.tendsto_nhds.mpr fun ε hε => ?_)
    rw [Filter.eventually_cofinite]
    have hc : {n : ℕ | ε ≤ ‖c n‖}.Finite := by
      have h1 : Tendsto (fun n => ‖c n‖) cofinite (𝓝 0) := by
        simpa using (cSpace.tendsto_cofinite c).norm
      simpa [not_lt] using Filter.eventually_cofinite.mp (h1.eventually_lt_const hε)
    refine Set.Finite.subset (hc.biUnion fun n _ => (Set.finite_Iic n).prod
      (Set.finite_singleton n)) fun x hx => ?_
    rw [Set.mem_ofPred_eq, not_lt, dist_zero_right] at hx
    have hx2 : x.1 ≤ x.2 := by
      by_contra hcon
      rw [hzero x (by omega), norm_zero] at hx
      exact absurd (lt_of_lt_of_le hε hx) (lt_irrefl _)
    exact Set.mem_biUnion (hx.trans (hbd x)) ⟨hx2, rfl⟩
  have hstep : ∀ k : ℕ,
      PowerSeries.coeff k (PowerSeries.mk fun k => colmezToDisc ψ hψ h c (a, k)) * w ^ k
        = ∑' n, ψ (discCoeff h n (a, k)) * c n * w ^ k := by
    intro k
    rw [PowerSeries.coeff_mk, colmezToDisc_apply, tsum_mul_right]
  have hcomm : ∑' (n : ℕ) (k : ℕ), ψ (discCoeff h n (a, k)) * c n * w ^ k
      = ∑' (k : ℕ) (n : ℕ), ψ (discCoeff h n (a, k)) * c n * w ^ k :=
    Summable.tsum_comm (f := fun k n => ψ (discCoeff h n (a, k)) * c n * w ^ k) hsum
  rw [tsum_congr hstep, ← hcomm]
  refine tsum_congr fun n => ?_
  rw [tsum_eq_sum (s := Finset.range (n + 1)) fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    exact hzero (k, n) (by omega)]
  have hjval : ((j % p ^ h : ℕ) : ℚ_[p]) + (p : ℚ_[p]) ^ h * (((j / p ^ h : ℕ)) : ℚ_[p])
      = ((j : ℕ) : ℚ_[p]) := by
    rw [← Nat.cast_pow, ← Nat.cast_mul, ← Nat.cast_add]
    norm_cast
    rw [Nat.mul_comm, Nat.add_comm]
    exact div_mul_add_mod (p ^ h) j
  have hval : (discPoly (p := p) h n a.val).eval (((j / p ^ h : ℕ)) : ℚ_[p])
      = (((n / p ^ h)! * j.choose n : ℕ) : ℚ_[p]) := by
    rw [discPoly_eval, hav, hjval, colmezPoly_eval_natCast]
  calc ∑ k ∈ Finset.range (n + 1), ψ (discCoeff h n (a, k)) * c n * w ^ k
      = c n * ψ (∑ k ∈ Finset.range (n + 1),
          (discPoly (p := p) h n a.val).coeff k * (((j / p ^ h : ℕ)) : ℚ_[p]) ^ k) := by
        rw [map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [map_mul, map_pow, map_natCast, ← hw, discCoeff]
        ring
    _ = c n * ψ ((discPoly (p := p) h n a.val).eval (((j / p ^ h : ℕ)) : ℚ_[p])) := by
        rw [← Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (natDegree_discPoly_le _ _ _))]
    _ = c n * (((n / p ^ h)! * j.choose n : ℕ) : K) := by rw [hval, map_natCast]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The `K`-valued form of `fwdDiff_iter_choose_zero`. -/
private theorem fwdDiff_iter_choose_zero_cast (m n : ℕ) :
    Δ_[1]^[m] (fun j : ℕ => ((j.choose n : ℕ) : K)) 0 = if m = n then 1 else 0 := by
  have hz := map_fwdDiff_iter (Int.castAddHom K) (fun j : ℕ => (j.choose n : ℤ)) 1 m 0
  rw [fwdDiff_iter_choose_zero] at hz
  simpa using hz

/-- **Mahler coefficients of a disc-model function are the forward differences of its values at
`ℕ`-points** (the level-`h` `fwdDiff_iter_evalAt_natCast`; `fwdDiff_iter_choose_zero`). -/

theorem discToMahler_apply_eq_fwdDiff (f : c(ZMod (p ^ h) × ℕ, K)) (m : ℕ) :
    discToMahler ψ hψ h f m = Δ_[1]^[m] (fun j : ℕ => discEval ψ h f (j : ℤ_[p])) 0 := by
  classical
  obtain ⟨c, rfl⟩ := surjective_colmezToDisc ψ hψ h f
  have hsummable : ∀ i : ℕ, Summable fun n => c n * (((n / p ^ h)! * i.choose n : ℕ) : K) := by
    intro i
    have htend : Tendsto (fun n => ‖c n‖) cofinite (𝓝 0) := by
      simpa using (cSpace.tendsto_cofinite c).norm
    refine TateFredholm.summable_of_tendsto_cofinite (squeeze_zero_norm (fun n => ?_) htend)
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K _)
  rw [discToMahler_colmezToDisc, fwdDiff_iter_eq_sum_shift]
  have hval : ∀ k : ℕ,
      discEval ψ h (colmezToDisc ψ hψ h c) (((0 + k • (1 : ℕ) : ℕ)) : ℤ_[p])
        = ∑' n, c n * (((n / p ^ h)! * k.choose n : ℕ) : K) := by
    intro k
    rw [show (0 + k • (1 : ℕ) : ℕ) = k from by simp]
    exact discEval_colmezToDisc_natCast ψ hψ h c k
  have hkey : ∀ k ∈ Finset.range (m + 1),
      ((-1 : ℤ) ^ (m - k) * (m.choose k) : ℤ) •
          discEval ψ h (colmezToDisc ψ hψ h c) (((0 + k • (1 : ℕ) : ℕ)) : ℤ_[p])
        = ∑' n, ((((-1 : ℤ) ^ (m - k) * (m.choose k) : ℤ)) : K)
            * (c n * (((n / p ^ h)! * k.choose n : ℕ) : K)) := by
    intro k _
    rw [hval k, zsmul_eq_mul, ← tsum_mul_left]
  rw [Finset.sum_congr rfl hkey,
    ← Summable.tsum_finsetSum fun k _ => (hsummable k).mul_left
      ((((-1 : ℤ) ^ (m - k) * (m.choose k) : ℤ)) : K)]
  have hinner : ∀ n : ℕ, ∑ k ∈ Finset.range (m + 1),
      ((((-1 : ℤ) ^ (m - k) * (m.choose k) : ℤ)) : K)
        * (c n * (((n / p ^ h)! * k.choose n : ℕ) : K))
      = c n * (((n / p ^ h)! : ℕ) : K) * (if m = n then 1 else 0) := by
    intro n
    rw [← fwdDiff_iter_choose_zero_cast (K := K) m n, fwdDiff_iter_eq_sum_shift, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [zsmul_eq_mul, show (0 + k • (1 : ℕ) : ℕ) = k from by simp]
    push_cast
    ring
  rw [tsum_congr hinner,
    tsum_eq_single m fun n hn => by rw [if_neg (Ne.symm hn), mul_zero], if_pos rfl, mul_one]
  ring

end Evaluation

end LWX

end
