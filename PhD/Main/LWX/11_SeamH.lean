/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«10_DiscForms»
import PhD.Main.LWX.«07_Seam»
import PhD.Main.TateFredholm.«08_BlockMap»

/-!
# [LWX, Proposition 2.17] at every analyticity level — SKELETON

> "Proposition 2.17.  The characteristic power series of `U_p` acting on `S^{D,†,m}_{[−]}` is
> `det(I_∞ − X·P)`, where `P` is the matrix of `U_p` with respect to the orthonormal basis
> `⌊n/(q⁻¹pᵐ)⌋!·(z choose n)` of Colmez."

The `m = 1` case is `PhD/Main/LWX/07_Seam.lean`.  This file does every `m = h + 1`, so that the seam
covers the whole boundary annulus `p⁻¹ < ‖T₀‖ < 1` rather than only the sub-annulus
`‖T₀‖² < p⁻¹` where the weight is `1`-locally analytic.

The proof is the `m = 1` proof with the disc model in place of the Tate algebra:

* the Colmez basis of the disc model (`AmiceBasis.colmezDiscEquiv`, Amice's theorem at level `h`)
  turns the disc model into `c(ℕ, K)`, and `diag(⌊n/pʰ⌋!)` turns Colmez coordinates into Mahler
  coefficients (`AmiceBasis.discToMahler`);
* the disc action of a certificate matrix is [LWX, (2.3.2)] pointwise
  (`DiscModel.discEval_discSlash`), so on Mahler coefficients it is the integral entry stream
  `P(δ)` specialised at `T₀` (`discToMahler_comp_discSlash`, from `entry_eq_fwdDiff`);
* hence `diag(⌊n/pʰ⌋!)` intertwines the Colmez-basis matrix `P′` of `U_p` with `P(T₀)`, and
  `det(I∞ − X P′) = det(I∞ − X P(T₀))` (`charPowerSeries_eq_of_diag_intertwine`), while
  `det(1 − X[UηU]) = det(I∞ − X P′)` (`charPowerSeries_conj` along the Colmez basis).

Two corollaries the `m = 1` seam could not state: the characteristic series is **independent of
the analyticity level** ([Bu04, Lemma 4]; [LWX, Def 2.13]), and **every** halo point is covered
at some level (`exists_level_specCharSeries_eq_heckeCharPowerSeries`).

## Main declarations

* `LWX.entry_eq_fwdDiff`, `LWX.discToMahler_comp_discSlash` — the seam for one matrix.
* `LWX.discToMahlerBlock`, `LWX.discToMahlerBlock_comp_discHeckeBlockOp`,
  `LWX.diagFactorialHBlock_comp_colmezConj` — blockwise.
* **`LWX.specCharSeries_ofCerts_eq_discHeckeCharPowerSeries`** — [LWX, Prop 2.17] at level `m`.
* `LWX.discHeckeCharPowerSeries_eq_of_levels` — [Bu04, Lemma 4]: independence of `m`.
* `LWX.exists_level_specCharSeries_eq_heckeCharPowerSeries` — coverage of the halo annulus.
-/

open Filter Topology TateFredholm QMF QMF.Weight AbstractHeckeOperatorSlash

open scoped Nat TateFredholm Pointwise fwdDiff

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

section OneMatrix

/-- Taking the `T^r`-coefficient of a halo-ring element, as an additive map. -/
private def haloCoeffHom (r : ℤ) : HaloInt p →+ ℤ_[p] where
  toFun f := f r
  map_zero' := rfl
  map_add' _ _ := rfl

variable (ψ : ℚ_[p] →+* K) (T₀ : K) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)

/-- **The integral entry stream as a forward difference** ([LWX, Prop 3.4]): the `(m, n)` entry of
the matrix of (2.3.2) in the Mahler basis is `Δ̃^m` of `[cz+d]·(möb z choose n)` at `0`.  (The
`m = 1` seam used the monomial form `fwdDiff_iter_cfunSlash_pow`; the disc model needs the
binomial form, since the Colmez basis is built from binomials.) -/
theorem entry_eq_fwdDiff (hp2 : p ≠ 2) (δ : LocalMat p) (m n : ℕ) :
    entry ω δ m n
      = Δ_[1]^[m] (fun z : ℤ_[p] => univChar ω (δ.denUnit z)
          * HaloInt.const (Ring.choose (δ.mobiusFun z) n)) 0 := by
  refine DFunLike.ext _ _ fun r => ?_
  have hcomm : Δ_[1]^[m] (fun z : ℤ_[p] => (univChar ω (δ.denUnit z)
      * HaloInt.const (Ring.choose (δ.mobiusFun z) n) : HaloInt p) r) 0
      = (Δ_[1]^[m] (fun z : ℤ_[p] => univChar ω (δ.denUnit z)
          * HaloInt.const (Ring.choose (δ.mobiusFun z) n)) 0) r :=
    map_fwdDiff_iter (haloCoeffHom r)
      (fun z : ℤ_[p] => univChar ω (δ.denUnit z)
        * HaloInt.const (Ring.choose (δ.mobiusFun z) n)) 1 m 0
  rw [coeff_entry, ← hcomm]
  rcases le_or_gt 0 r with hr | hr
  · rw [show (fun z : ℤ_[p] => (univChar ω (δ.denUnit z)
        * HaloInt.const (Ring.choose (δ.mobiusFun z) n) : HaloInt p) r)
        = fun z : ℤ_[p] => (ω (Units.map (PadicInt.toZMod (p := p)).toMonoidHom δ.d) : ℤ_[p])
            * (Ring.choose (δ.mobiusFun z) n * Ring.choose (δ.gFun z) r.toNat) from
        funext fun z => by rw [coeff_univChar_mul_const hp2 ω δ n z r, if_pos hr],
      entryCoeff, dif_pos hr]
    exact (map_fwdDiff_iter
      (AddMonoidHom.mulLeft
        ((ω (Units.map (PadicInt.toZMod (p := p)).toMonoidHom δ.d) : ℤ_[p])))
      (fun z : ℤ_[p] => Ring.choose (δ.mobiusFun z) n * Ring.choose (δ.gFun z) r.toNat)
      1 m 0).symm
  · rw [show (fun z : ℤ_[p] => (univChar ω (δ.denUnit z)
        * HaloInt.const (Ring.choose (δ.mobiusFun z) n) : HaloInt p) r)
        = fun _ : ℤ_[p] => (0 : ℤ_[p]) from
        funext fun z => by
          rw [coeff_univChar_mul_const hp2 ω δ n z r, if_neg (not_le.mpr hr)],
      entryCoeff, dif_neg (not_le.mpr hr)]
    simp [fwdDiff_iter_eq_sum_shift]

omit [CharZero K] in
/-- The specialised entry stream as a forward difference of `K`-valued functions
(`HaloInt.specializeHom` commutes with `Δ̃^m`). -/
theorem specialize_entry_eq_fwdDiff (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (δ : LocalMat p) (m n : ℕ) :
    HaloInt.specialize (intHom ψ) T₀ (entry ω δ m n)
      = Δ_[1]^[m] (fun j : ℕ => HaloInt.specialize (intHom ψ) T₀
            (univChar ω (δ.denUnit (j : ℤ_[p])))
          * intHom ψ (Ring.choose (δ.mobiusFun (j : ℤ_[p])) n)) 0 := by
  have hpt : (fun j : ℕ => HaloInt.specialize (intHom ψ) T₀ (univChar ω (δ.denUnit (j : ℤ_[p])))
        * intHom ψ (Ring.choose (δ.mobiusFun (j : ℤ_[p])) n))
      = fun j : ℕ => (HaloInt.specializeHom (intHom ψ) (norm_intHom ψ hψ) h0 h1).toAddMonoidHom
          (univChar ω (δ.denUnit (j : ℤ_[p]))
            * HaloInt.const (Ring.choose (δ.mobiusFun (j : ℤ_[p])) n)) :=
    funext fun j => by
      show _ = HaloInt.specialize (intHom ψ) T₀ (univChar ω (δ.denUnit (j : ℤ_[p]))
        * HaloInt.const (Ring.choose (δ.mobiusFun (j : ℤ_[p])) n))
      rw [HaloInt.specialize_mul (intHom ψ) (norm_intHom ψ hψ) h0 h1, HaloInt.specialize_const]
  rw [hpt, map_fwdDiff_iter, fwdDiff_iter_comp_natCast (fun z : ℤ_[p] =>
    univChar ω (δ.denUnit z) * HaloInt.const (Ring.choose (δ.mobiusFun z) n)),
    ← entry_eq_fwdDiff ω hp2 δ m n]
  rfl

variable (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h : ℕ)

/-- The value of the disc model of the `n`-th Colmez basis vector at a natural number:
`g_n(j) = ⌊n/pʰ⌋!·C(j, n)` (`discEval_colmezToDisc_natCast` at `single n 1`). -/
theorem discEval_colmezToDisc_single (z : ℤ_[p]) (n : ℕ) :
    discEval ψ h (colmezToDisc ψ hψ h (cSpace.single n (1 : K))) z
      = (((n / p ^ h)! : ℕ) : K) * intHom ψ (Ring.choose z n) := by
  classical
  -- the Colmez polynomial evaluated at a `p`-adic integer
  have hpoly : ∀ y : ℤ_[p], (colmezPoly (p := p) h n).eval ((y : ℤ_[p]) : ℚ_[p])
      = (((n / p ^ h)! : ℕ) : ℚ_[p]) * ((Ring.choose y n : ℤ_[p]) : ℚ_[p]) := by
    have hc1 : Continuous fun y : ℤ_[p] =>
        (colmezPoly (p := p) h n).eval ((y : ℤ_[p]) : ℚ_[p]) :=
      (colmezPoly (p := p) h n).continuous.comp continuous_subtype_val
    have hc2 : Continuous fun y : ℤ_[p] =>
        (((n / p ^ h)! : ℕ) : ℚ_[p]) * ((Ring.choose y n : ℤ_[p]) : ℚ_[p]) :=
      continuous_const.mul (continuous_subtype_val.comp (PadicInt.continuous_choose n))
    refine fun y => congrFun (PadicInt.denseRange_natCast.equalizer hc1 hc2
      (funext fun j : ℕ => ?_)) y
    show (colmezPoly (p := p) h n).eval (((j : ℤ_[p]) : ℚ_[p]))
      = (((n / p ^ h)! : ℕ) : ℚ_[p]) * ((Ring.choose ((j : ℕ) : ℤ_[p]) n : ℤ_[p]) : ℚ_[p])
    rw [show (((j : ℕ) : ℤ_[p]) : ℚ_[p]) = ((j : ℕ) : ℚ_[p]) from by push_cast; ring,
      colmezPoly_eval_natCast, Ring.choose_natCast]
    push_cast
    ring
  -- the disc coordinates of the `n`-th Colmez vector
  have haval : (((z.appr h : ℕ) : ZMod (p ^ h))).val = z.appr h :=
    val_toZModPow h z
  have hcoeff : ∀ k : ℕ, (colmezToDisc ψ hψ h (cSpace.single n (1 : K)))
      (((z.appr h : ℕ) : ZMod (p ^ h)), k)
      = ψ ((discPoly (p := p) h n (z.appr h)).coeff k) := by
    intro k
    rw [colmezToDisc_apply, tsum_eq_single n fun m hm => by
      rw [cSpace.single_apply_of_ne hm, mul_zero]]
    rw [cSpace.single_apply_self, mul_one, discCoeff, haval]
  have hdeg : (discPoly (p := p) h n (z.appr h)).natDegree < n + 1 :=
    lt_of_le_of_lt (natDegree_discPoly_le h n _) (by omega)
  rw [discEval, evalAt, tsum_eq_sum (s := Finset.range (n + 1)) fun k hk => by
    rw [Finset.mem_range, not_lt] at hk
    rw [PowerSeries.coeff_mk, hcoeff, Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_lt_of_le hdeg (by omega)), map_zero, zero_mul]]
  have hsum : ∑ k ∈ Finset.range (n + 1),
        PowerSeries.coeff k (PowerSeries.mk fun k => colmezToDisc ψ hψ h
          (cSpace.single n (1 : K)) (((z.appr h : ℕ) : ZMod (p ^ h)), k))
          * intHom ψ (discCoord h z) ^ k
      = ψ ((discPoly (p := p) h n (z.appr h)).eval ((discCoord h z : ℤ_[p]) : ℚ_[p])) := by
    rw [Polynomial.eval_eq_sum_range' hdeg, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_mk, hcoeff, map_mul, map_pow]
    rfl
  rw [hsum, discPoly_eval,
    show ((z.appr h : ℕ) : ℚ_[p]) + (p : ℚ_[p]) ^ h * ((discCoord h z : ℤ_[p]) : ℚ_[p])
      = ((z : ℤ_[p]) : ℚ_[p]) from by
      have hz := congrArg (fun t : ℤ_[p] => (t : ℚ_[p])) (appr_add_pow_mul_discCoord h z)
      push_cast at hz
      exact hz,
    hpoly z, map_mul, map_natCast]
  rfl

/-- **The seam identity for one matrix** at analyticity level `h + 1`: the disc-model-to-Mahler
map intertwines the disc action of `ψ(δ)` at the level-`h` halo weight with the specialised
integral entry stream `P(δ)(T₀)`.

Proof: both sides are continuous linear, so it suffices to check on the Colmez basis
(`colmezDiscEquiv` is an isomorphism).  On `colmezToDisc (single n 1)` the left side is, by
`discToMahler_apply_eq_fwdDiff` and `discEval_discSlash`,
`Δ^m (j ↦ [c j + d](T₀)·⌊n/pʰ⌋!·ψ(möb δ j choose n)) 0 = ⌊n/pʰ⌋!·P_{m,n}(δ)(T₀)`
(`specialize_entry_eq_fwdDiff`), and the right side is
`P(δ)(T₀)` applied to `⌊n/pʰ⌋!·e_n` (`discToMahler_colmezToDisc`). -/
theorem discToMahler_comp_discSlash (hp2 : p ≠ 2) (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)
    (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) (δ : M1 p) :
    (discToMahler ψ hψ h).comp
        (discSlash h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) δ)
      = (specEntryOp hp2 ψ hψ h0 h1 ω (M1.toLocalMat δ)).comp (discToMahler ψ hψ h) := by
  have hcancel : ∀ A B : c(ZMod (p ^ h) × ℕ, K) →L[K] c(ℕ, K),
      A.comp ((colmezDiscEquiv ψ hψ h : c(ℕ, K) →L[K] c(ZMod (p ^ h) × ℕ, K)))
        = B.comp ((colmezDiscEquiv ψ hψ h : c(ℕ, K) →L[K] c(ZMod (p ^ h) × ℕ, K))) → A = B := by
    intro A B hAB
    refine ContinuousLinearMap.ext fun x => ?_
    have hx : ((colmezDiscEquiv ψ hψ h : c(ℕ, K) →L[K] c(ZMod (p ^ h) × ℕ, K)))
        ((colmezDiscEquiv ψ hψ h).symm x) = x :=
      (colmezDiscEquiv ψ hψ h).apply_symm_apply x
    calc A x = (A.comp ((colmezDiscEquiv ψ hψ h : c(ℕ, K) →L[K] c(ZMod (p ^ h) × ℕ, K))))
          ((colmezDiscEquiv ψ hψ h).symm x) := by
          rw [ContinuousLinearMap.comp_apply, hx]
      _ = (B.comp ((colmezDiscEquiv ψ hψ h : c(ℕ, K) →L[K] c(ZMod (p ^ h) × ℕ, K))))
          ((colmezDiscEquiv ψ hψ h).symm x) := by rw [hAB]
      _ = B x := by rw [ContinuousLinearMap.comp_apply, hx]
  refine hcancel _ _ (ext_matrixCoeff fun m n => ?_)
  show discToMahler ψ hψ h (discSlash h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) δ
      (colmezToDisc ψ hψ h (cSpace.single n (1 : K)))) m
    = specEntryOp hp2 ψ hψ h0 h1 ω (M1.toLocalMat δ)
      (discToMahler ψ hψ h (colmezToDisc ψ hψ h (cSpace.single n (1 : K)))) m
  -- the left-hand side, through the forward-difference formula
  have hfun : (fun j : ℕ => discEval ψ h (discSlash h ψ
        (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) δ
          (colmezToDisc ψ hψ h (cSpace.single n (1 : K)))) (j : ℤ_[p]))
      = fun j : ℕ => (((n / p ^ h)! : ℕ) : K)
          * (HaloInt.specialize (intHom ψ) T₀
              (univChar ω ((M1.toLocalMat δ).denUnit (j : ℤ_[p])))
            * intHom ψ (Ring.choose ((M1.toLocalMat δ).mobiusFun (j : ℤ_[p])) n)) := by
    funext j
    rw [discEval_discSlash h ψ T₀ ω hp2 hψ h0 h1 hT δ _ (j : ℤ_[p]),
      discEval_colmezToDisc_single ψ hψ h ((M1.toLocalMat δ).mobiusFun (j : ℤ_[p])) n]
    ring
  have hpull : Δ_[1]^[m] (fun j : ℕ => (((n / p ^ h)! : ℕ) : K)
        * (HaloInt.specialize (intHom ψ) T₀
            (univChar ω ((M1.toLocalMat δ).denUnit (j : ℤ_[p])))
          * intHom ψ (Ring.choose ((M1.toLocalMat δ).mobiusFun (j : ℤ_[p])) n))) 0
      = (((n / p ^ h)! : ℕ) : K) * Δ_[1]^[m] (fun j : ℕ =>
          HaloInt.specialize (intHom ψ) T₀
              (univChar ω ((M1.toLocalMat δ).denUnit (j : ℤ_[p])))
            * intHom ψ (Ring.choose ((M1.toLocalMat δ).mobiusFun (j : ℤ_[p])) n)) 0 :=
    map_fwdDiff_iter (AddMonoidHom.mulLeft (((n / p ^ h)! : ℕ) : K)) _ 1 m 0
  rw [discToMahler_apply_eq_fwdDiff, hfun, hpull,
    ← specialize_entry_eq_fwdDiff ψ T₀ ω hp2 hψ h0 h1 (M1.toLocalMat δ) m n]
  -- the right-hand side
  have hL : discToMahler ψ hψ h (colmezToDisc ψ hψ h (cSpace.single n (1 : K)))
      = (((n / p ^ h)! : ℕ) : K) • cSpace.single n (1 : K) := by
    refine DFunLike.ext _ _ fun k => ?_
    rw [discToMahler_colmezToDisc]
    show _ = (((n / p ^ h)! : ℕ) : K) * cSpace.single n (1 : K) k
    by_cases hk : k = n
    · subst hk
      rw [cSpace.single_apply_self]
    · rw [cSpace.single_apply_of_ne hk, mul_zero, mul_zero]
  rw [hL, map_smul]
  show _ = (((n / p ^ h)! : ℕ) : K)
    * specEntryOp hp2 ψ hψ h0 h1 ω (M1.toLocalMat δ) (cSpace.single n (1 : K)) m
  rw [show specEntryOp hp2 ψ hψ h0 h1 ω (M1.toLocalMat δ) (cSpace.single n (1 : K)) m
      = matrixCoeff (specEntryOp hp2 ψ hψ h0 h1 ω (M1.toLocalMat δ)) m n from rfl,
    matrixCoeff_specEntryOp]

end OneMatrix

section Blockwise

variable (ψ : ℚ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (T₀ : K) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (h : ℕ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The blockwise disc-model-to-Mahler map `c(ι × (ℤ/pʰ × ℕ), K) →L c(ι × ℕ, K)`. -/
def discToMahlerBlock : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × ℕ, K) :=
  blockMap (discToMahler ψ hψ h)

/-- The blockwise `diag(⌊n/pʰ⌋!)`. -/
def diagFactorialHBlock : c(ι × ℕ, K) →L[K] c(ι × ℕ, K) :=
  blockDiag (diagFactorialH (p := p) h)

/-- The blockwise Colmez basis change of the disc model. -/
def colmezDiscEquivBlock : c(ι × ℕ, K) ≃L[K] c(ι × (ZMod (p ^ h) × ℕ), K) :=
  blockMapEquiv (colmezDiscEquiv ψ hψ h)

omit hp [CharZero K] in
@[simp] theorem matrixCoeff_diagFactorialHBlock (a b : ι × ℕ) :
    matrixCoeff (diagFactorialHBlock (p := p) (K := K) (ι := ι) h) a b
      = if a = b then (((a.2 / p ^ h)! : ℕ) : K) else 0 := by
  obtain ⟨i, m⟩ := a
  obtain ⟨j, n⟩ := b
  rw [diagFactorialHBlock, matrixCoeff_blockDiag, matrixCoeff_diagFactorialH]
  by_cases hij : i = j
  · subst hij
    by_cases hmn : m = n
    · subst hmn
      simp
    · simp [hmn]
  · simp [hij]

omit hp [CharZero K] in
theorem matrixCoeff_diagFactorialHBlock_comp (v : c(ι × ℕ, K) →L[K] c(ι × ℕ, K)) (a b : ι × ℕ) :
    matrixCoeff ((diagFactorialHBlock (p := p) (K := K) (ι := ι) h).comp v) a b
      = (((a.2 / p ^ h)! : ℕ) : K) * matrixCoeff v a b := by
  rw [matrixCoeff_comp, tsum_eq_single a fun c hc => by
    rw [matrixCoeff_diagFactorialHBlock, if_neg (Ne.symm hc), mul_zero],
    matrixCoeff_diagFactorialHBlock, if_pos rfl, mul_comm]

omit hp [CharZero K] in
theorem matrixCoeff_comp_diagFactorialHBlock (v : c(ι × ℕ, K) →L[K] c(ι × ℕ, K)) (a b : ι × ℕ) :
    matrixCoeff (v.comp (diagFactorialHBlock (p := p) (K := K) (ι := ι) h)) a b
      = matrixCoeff v a b * (((b.2 / p ^ h)! : ℕ) : K) := by
  rw [matrixCoeff_comp, tsum_eq_single b fun c hc => by
    rw [matrixCoeff_diagFactorialHBlock, if_neg hc, zero_mul],
    matrixCoeff_diagFactorialHBlock, if_pos rfl, mul_comm]

omit [CharZero K] in
/-- `discToMahlerBlock = diagFactorialHBlock ∘ colmezDiscEquivBlock⁻¹` (blockwise
`discToMahler`, `blockMap_comp`, `blockMap_eq_blockDiag`). -/
theorem discToMahlerBlock_eq :
    (discToMahlerBlock (K := K) (ι := ι) ψ hψ h)
      = (diagFactorialHBlock (p := p) (K := K) (ι := ι) h).comp
          ((colmezDiscEquivBlock (K := K) (ι := ι) ψ hψ h).symm :
            c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × ℕ, K)) := by
  unfold discToMahlerBlock diagFactorialHBlock colmezDiscEquivBlock
  rw [coe_blockMapEquiv_symm, ← blockMap_eq_blockDiag, blockMap_comp, discToMahler]

variable {G : Type*} [Group G] {Γ : Subgroup G} (θ : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])
  (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θ)
variable (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θ) (idx : ι → Fin p → ι)
  (u : ι → Fin p → U)

/-- **The seam identity blockwise**: the disc-model-to-Mahler map intertwines the disc-model block
operator of `[UηU]` at the level-`h` halo weight with the specialised integral `U_p` of the
certificate datum (`discToMahler_comp_discSlash` summed over the certificates with target `j`,
`blockMap_comp_blockOp`, `blockOp_comp_blockMap`). -/
theorem discToMahlerBlock_comp_discHeckeBlockOp (hp2 : p ≠ 2) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape) :
    (discToMahlerBlock (K := K) (ι := ι) ψ hψ h).comp
        (discHeckeBlockOp θ h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) U hU vRep hvΔ idx u)
      = (specOp hp2 ψ hψ h0 h1 ω (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape)).comp
          (discToMahlerBlock (K := K) (ι := ι) ψ hψ h) := by
  unfold discToMahlerBlock discHeckeBlockOp specOp
  rw [blockMap_comp_blockOp, blockOp_comp_blockMap]
  congr 1
  funext i j
  unfold discHeckeBlock
  simp only [UpDatum.ofCerts_mat, UpDatum.ofCerts_tgt]
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [ContinuousLinearMap.comp_apply, sum_apply, map_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hd := DFunLike.congr_fun (discToMahler_comp_discSlash ψ T₀ ω hψ h hp2 h0 h1 hT
    (certM1 θ U hU vRep hvΔ u i t)) x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply] at hd
  exact hd

/-- **The Colmez-basis matrix `P′` of `U_p`** is diagonally intertwined with `P(T₀)`:
`diag(⌊n/pʰ⌋!)·P′ = P(T₀)·diag(⌊n/pʰ⌋!)`. -/
theorem diagFactorialHBlock_comp_colmezConj (hp2 : p ≠ 2) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape) :
    (diagFactorialHBlock (p := p) (K := K) (ι := ι) h).comp
        ((((colmezDiscEquivBlock (K := K) (ι := ι) ψ hψ h).symm :
            c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × ℕ, K)).comp
          (discHeckeBlockOp θ h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) U hU vRep hvΔ
            idx u)).comp
          (colmezDiscEquivBlock (K := K) (ι := ι) ψ hψ h :
            c(ι × ℕ, K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K)))
      = (specOp hp2 ψ hψ h0 h1 ω (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape)).comp
          (diagFactorialHBlock (p := p) (K := K) (ι := ι) h) := by
  have hd := discToMahlerBlock_comp_discHeckeBlockOp ψ hψ T₀ ω h θ U hU vRep hvΔ idx u
    hp2 h0 h1 hT hshape
  rw [discToMahlerBlock_eq] at hd
  have hΨ : ((colmezDiscEquivBlock (K := K) (ι := ι) ψ hψ h).symm :
        c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × ℕ, K)).comp
      ((colmezDiscEquivBlock (K := K) (ι := ι) ψ hψ h) :
        c(ι × ℕ, K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K))
        = ContinuousLinearMap.id K c(ι × ℕ, K) :=
    ContinuousLinearMap.ext fun x =>
      (colmezDiscEquivBlock (K := K) (ι := ι) ψ hψ h).symm_apply_apply x
  rw [← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc, hd,
    ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc, hΨ,
    ContinuousLinearMap.comp_id]

/-- **`U_p` is compactoid at the level-`h` halo weight** ([Buzzard, Lemma 12.2] on the disc
model): every certificate matrix has the `U_p`-shape, so `isCompactoid_discHeckeBlockOp` applies
at `σ = max ρ_h p⁻¹ < 1`. -/
theorem isCompactoid_discHeckeBlockOp_haloWeightH (hp2 : p ≠ 2) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape) :
    IsCompactoid (discHeckeBlockOp θ h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) U hU vRep hvΔ
      idx u) :=
  isCompactoid_discHeckeBlockOp θ h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) U hU vRep hvΔ
    idx u (haloRhoH_nonneg h T₀) (max_lt (haloRhoH_lt_one h T₀ hT) inv_lt_one_p) hshape

/-- **[LWX, Proposition 2.17] at analyticity level `m = h + 1`**, on the whole halo
`p⁻¹ < ‖T₀‖ < 1` at which the weight is `m`-locally analytic (`‖T'_h‖² < p⁻¹`): the specialised
integral characteristic series `Char(P)(T₀)` of the certificate datum is the Fredholm determinant
`det(1 − X·[UηU])` of `U_p` on `S^{D,†,m}` at the halo weight.

Proof: `det(1 − X[UηU]) = det(1 − XP′)` (`charPowerSeries_conj` along `colmezDiscEquivBlock`,
compactoid by `isCompactoid_discHeckeBlockOp_haloWeightH`) `= det(1 − XP(T₀))`
(`charPowerSeries_eq_of_diag_intertwine` with `diagFactorialHBlock_comp_colmezConj`)
`= Char(P)(T₀)` (`charPowerSeries_specOp`). -/
theorem specCharSeries_ofCerts_eq_discHeckeCharPowerSeries (hp2 : p ≠ 2)
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape) :
    specCharSeries (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape) ω (intHom ψ) T₀
      = discHeckeCharPowerSeries θ h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) U hU vRep
          hvΔ idx u := by
  have hconj := charPowerSeries_conj (colmezDiscEquivBlock (K := K) (ι := ι) ψ hψ h).symm
    (discHeckeBlockOp θ h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) U hU vRep hvΔ idx u)
    (isCompactoid_discHeckeBlockOp_haloWeightH ψ hψ T₀ ω h θ U hU vRep hvΔ idx u
      hp2 h0 h1 hT hshape)
  rw [ContinuousLinearEquiv.symm_symm] at hconj
  have hE := diagFactorialHBlock_comp_colmezConj ψ hψ T₀ ω h θ U hU vRep hvΔ idx u
    hp2 h0 h1 hT hshape
  have hdiag := charPowerSeries_eq_of_diag_intertwine
    (d := fun a : ι × ℕ => (((a.2 / p ^ h)! : ℕ) : K))
    (fun a => isUnit_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)))
    (fun a b => by
      have hh := congrArg (fun T => matrixCoeff T a b) hE
      rwa [matrixCoeff_diagFactorialHBlock_comp, matrixCoeff_comp_diagFactorialHBlock] at hh)
  rw [← charPowerSeries_specOp hp2 ψ hψ h0 h1 ω, ← hdiag, hconj]
  rfl

end Blockwise

section Corollaries

variable (ψ : ℚ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (T₀ : K) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {G : Type*} [Group G] {Γ : Subgroup G} (θ : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])
  (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θ)
variable (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θ) (idx : ι → Fin p → ι)
  (u : ι → Fin p → U)

/-- **[Bu04, Lemma 4]; [LWX, Definition 2.13]**: "the characteristic power series of `U_p` acting
on `S^{D,†,m}` … is independent of `m`" — both levels compute the same `Char(P)(T₀)`. -/
theorem discHeckeCharPowerSeries_eq_of_levels (hp2 : p ≠ 2) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ < 1) {h h' : ℕ} (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hT' : ‖TH p h' T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape) :
    discHeckeCharPowerSeries θ h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) U hU vRep hvΔ
        idx u
      = discHeckeCharPowerSeries θ h' ψ (haloWeightH h' ψ T₀ ω hp2 hψ h0 h1 hT') U hU
          vRep hvΔ idx u := by
  rw [← specCharSeries_ofCerts_eq_discHeckeCharPowerSeries ψ hψ T₀ ω h θ U hU vRep hvΔ idx u
      hp2 h0 h1 hT hshape,
    ← specCharSeries_ofCerts_eq_discHeckeCharPowerSeries ψ hψ T₀ ω h' θ U hU vRep hvΔ idx u
      hp2 h0 h1 hT' hshape]

/-- **Coverage of the halo annulus** ([LWX, §2.7]: "for `m₀` large enough … `W_{m₀}`"): at *every*
halo point `p⁻¹ < ‖T₀‖ < 1` there is an analyticity level at which the seam identity holds
(`exists_sq_norm_pow_prime_pow_sub_one_lt`). -/
theorem exists_level_specCharSeries_eq_heckeCharPowerSeries (hp2 : p ≠ 2)
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape) :
    ∃ (h : ℕ) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹),
      specCharSeries (UpDatum.ofCerts θ U hU vRep hvΔ idx u hshape) ω (intHom ψ) T₀
        = discHeckeCharPowerSeries θ h ψ (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT) U hU
            vRep hvΔ idx u := by
  have hpK : ‖((p : ℕ) : K)‖ < 1 := by
    rw [norm_natCast_p ψ hψ]
    exact inv_lt_one_p
  obtain ⟨h, hT⟩ := exists_sq_norm_pow_prime_pow_sub_one_lt (K := K) hpK h1
  exact ⟨h, hT, specCharSeries_ofCerts_eq_discHeckeCharPowerSeries ψ hψ T₀ ω h θ U hU vRep
    hvΔ idx u hp2 h0 h1 hT hshape⟩

/-- **The `m = 1` seam is the case `h = 0`**: at a point of the sub-annulus the disc model at
level `0` is the Tate algebra and the two readings agree
(`Seam.specCharSeries_ofCerts_eq_heckeCharPowerSeries`). -/
theorem discHeckeCharPowerSeries_zero_eq_heckeCharPowerSeries (hp2 : p ≠ 2)
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hT : ‖TH p 0 T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θ U hU vRep hvΔ u i t)).IsUpShape) :
    discHeckeCharPowerSeries θ 0 ψ
        (haloWeightH 0 ψ T₀ ω hp2 hψ h0 (norm_lt_one_of_sq_lt h1) hT) U hU vRep hvΔ idx u
      = heckeCharPowerSeries (thetaK ψ θ) (haloWeight ψ T₀ ω hp2 hψ h0 h1) U
          (subset_levelMonoidOf_thetaK ψ θ U hU) 1 vRep
          (fun t => mem_levelMonoidOf_thetaK ψ θ (hvΔ t)) idx u := by
  rw [← specCharSeries_ofCerts_eq_discHeckeCharPowerSeries ψ hψ T₀ ω 0 θ U hU vRep hvΔ idx u
      hp2 h0 (norm_lt_one_of_sq_lt h1) hT hshape,
    specCharSeries_ofCerts_eq_heckeCharPowerSeries ψ T₀ ω θ U hU vRep hvΔ idx u
      hp2 hψ h0 h1 hshape]

end Corollaries

end LWX

end
