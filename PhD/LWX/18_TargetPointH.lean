/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.«17_ClassicalPointH»

/-!
# The theta target of a classical point of conductor `p^{h+1}`

`23_ConductorSlopes.lean` reads the classical `U_p`-slopes at a classical point of conductor
`p^{h+1}` off the full Fredholm determinant; for that it needs the complement of the classical
subspace to have slopes `≥ k+1` (`le_unitSlope_compl`, general in `h`), which is the small-slope
argument through the theta intertwining with the target weight `(−k−2, ψ)`.  So the target
datum of `16_TargetPoint.lean` is needed at level `h`: this file is `16_TargetPoint.lean` with the
level-`1` root-of-unity input replaced by `17_ClassicalPointH.lean`'s.

* The level-`h` halo weight at `weightPoint p (−k−2) ζ` has the target shape
  `autFactor · L^{k+2} = C(κ(d)·d^{k+2})` (the halo exponent is `−(k+2)`,
  `haloExponentH_weightPoint`; the binomial series with exponent `−n` is
  `mk_choose_neg_natCast_mul_pow`).
* **AG-ζ at level `h`**: the target-shape constants at the target point equal the classical
  datum's constants — the binomial series at the two points differ by `exp(p(2k+2)·ψℓ)`
  (`oneAddPow_weightPoint_mul_padicExp_prime_pow`) and the residue characters by `ω₀^{2k+2}`;
  hence `targetData_classicalPointH`.

Step III proper (the degree formula, `16_ThetaExact.lean`, `17_DegreeFormula.lean`) is **not**
generalised: [LWX, Thm 1.5]'s second half uses the complement bound only.  Nothing here depends
on Jacquet–Langlands.
-/

open Filter Topology TateFredholm QMF QMF.Weight
open scoped Nat

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

omit [CompleteSpace K] [CharZero K] in
/-- `0 < p⁻¹` (level-`h` copy of `16_TargetPoint.lean`'s private helper). -/
private theorem inv_p_posG : (0 : ℝ) < (p : ℝ)⁻¹ := by
  have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  positivity

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `‖p·x‖ ≤ p⁻¹` for `‖x‖ ≤ 1`. -/
private theorem norm_p_mul_le_invG (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x : K} (hx : ‖x‖ ≤ 1) :
    ‖((p : ℕ) : K) * x‖ ≤ (p : ℝ)⁻¹ := by
  rw [norm_mul, hpK]
  exact mul_le_of_le_one_right (inv_p_posG (p := p)).le hx

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `‖p·x‖² < ‖p‖` for `‖x‖ ≤ 1`: the exponential's disc contains `p·x`. -/
private theorem norm_p_mul_sq_ltG (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x : K} (hx : ‖x‖ ≤ 1) :
    ‖((p : ℕ) : K) * x‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
  have h0 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_p_posG (p := p)
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_p (p := p)
  have hw := norm_p_mul_le_invG hpK hx
  calc ‖((p : ℕ) : K) * x‖ ^ 2 ≤ ((p : ℝ)⁻¹) ^ 2 := by gcongr
    _ < (p : ℝ)⁻¹ := by nlinarith
    _ = ‖((p : ℕ) : K)‖ := hpK.symm

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- A product of two elements of the unit ball has norm at most one. -/
private theorem norm_mul_le_oneG {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ hx (norm_nonneg y) hy

/-! ### The level-`h` halo weight at the target point has the target shape -/

variable (ψ : ℚ_[p] →+* K) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)

/-- **The automorphy factor of the level-`h` halo weight at the target point** satisfies
`autFactor · L^{k+2} = C(κ(d)·d^{k+2})`: `autFactor_haloWeightH` with the halo exponent
`−(k+2)` (`haloExponentH_weightPoint`) and `mk_choose_neg_natCast_mul_pow`. -/
theorem autFactor_haloWeightH_weightPoint_neg_prime_pow (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    {ζ : K} (h : ℕ) (hζ : ζ ^ p ^ h = 1) (k : ℕ)
    (h0 : (p : ℝ)⁻¹ < ‖weightPoint p (-(k + 2 : ℤ)) ζ‖)
    (h1 : ‖weightPoint p (-(k + 2 : ℤ)) ζ‖ < 1)
    (hT : ‖TH p h (weightPoint p (-(k + 2 : ℤ)) ζ)‖ ^ 2 < (p : ℝ)⁻¹) (g : M1Kh h ψ) :
    (haloWeightH h ψ (weightPoint p (-(k + 2 : ℤ)) ζ) ω hp2 hψ h0 h1 hT).toWeightSeries.autFactor
          g.1 * linX g.1 ^ (k + 2)
      = PowerSeries.C (haloCharFunH h ψ (weightPoint p (-(k + 2 : ℤ)) ζ) ω (g.1 1 1)
          * (g.1 1 1) ^ (k + 2)) := by
  have hd0 : g.1 1 1 ≠ 0 :=
    (levelBounds_M1Kh h ψ (weightPoint p (-(k + 2 : ℤ)) ζ) hψ hT).d_ne_zero g.2
  have hlin : linX g.1
      = PowerSeries.C (g.1 1 1)
        * (1 + PowerSeries.C (g.1 1 0 / g.1 1 1) * PowerSeries.X) := by
    rw [linX, mul_add, mul_one, ← mul_assoc, ← map_mul,
      show g.1 1 1 * (g.1 1 0 / g.1 1 1) = g.1 1 0 from by field_simp]
  have hcast : ((-(k + 2 : ℤ) : ℤ) : K) = -(((k + 2 : ℕ)) : K) := by push_cast; ring
  rw [autFactor_haloWeightH h ψ (weightPoint p (-(k + 2 : ℤ)) ζ) ω hp2 hψ h0 h1 hT g,
    haloExponentH_weightPoint hp2 hζ (norm_natCast_p ψ hψ) (-(k + 2 : ℤ)), hcast, hlin,
    mul_pow, ← map_pow, map_mul]
  linear_combination (PowerSeries.C (haloCharFunH h ψ (weightPoint p (-(k + 2 : ℤ)) ζ) ω (g.1 1 1))
      * PowerSeries.C (g.1 1 1 ^ (k + 2)))
    * mk_choose_neg_natCast_mul_pow (k + 2) (g.1 1 0 / g.1 1 1)

variable {G : Type*} [Group G] {Γ : Subgroup G} (θG : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)
  (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θG) (uu : ι → Fin p → U)

omit [Fintype ι] [DecidableEq ι] in
/-- **The target shape of the level-`h` halo weight at the target point**, with the constants
`κ(d)·d^{k+2}` at the lower-right entry `d` of the disc conjugate. -/
theorem isClassicalShape'_haloWeightH_weightPoint_neg_prime_pow (hp2 : p ≠ 2)
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K} (h : ℕ) (hζ : ζ ^ p ^ h = 1) (k : ℕ)
    (h0 : (p : ℝ)⁻¹ < ‖weightPoint p (-(k + 2 : ℤ)) ζ‖)
    (h1 : ‖weightPoint p (-(k + 2 : ℤ)) ζ‖ < 1)
    (hT : ‖TH p h (weightPoint p (-(k + 2 : ℤ)) ζ)‖ ^ 2 < (p : ℝ)⁻¹) :
    IsClassicalShape' θG h ψ U hU vRep hvΔ uu
      (haloWeightH h ψ (weightPoint p (-(k + 2 : ℤ)) ζ) ω hp2 hψ h0 h1 hT) k
      fun i t a => haloCharFunH h ψ (weightPoint p (-(k + 2 : ℤ)) ζ) ω
          (certConj θG h ψ U hU vRep hvΔ uu i t a 1 1)
        * (certConj θG h ψ U hU vRep hvΔ uu i t a 1 1) ^ (k + 2) :=
  fun i t a => autFactor_haloWeightH_weightPoint_neg_prime_pow ψ ω hp2 hψ h hζ k h0 h1 hT
    (discConjK h (certM1 θG U hU vRep hvΔ uu i t) a ψ)

/-! ### AG-ζ at level `h`: the nebentypus constants of the source and the target agree -/

/-- **The binomial series at two weight points differ by an exponential**:
`(1+T_s)^{ψ y}·exp(p(t−s)·ψ y) = (1+T_t)^{ψ y}` for every `y ∈ ℤ_p` — both sides are continuous
in `y` and agree on `ℕ` (`oneAddPow_weightPoint_mul_padicExp` with the level-`h` norm bound
`norm_weightPoint_lt_one_prime_pow`). -/
theorem oneAddPow_weightPoint_mul_padicExp_prime_pow (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    {ζ : K} {h : ℕ} (hh : 0 < h) (hζ : IsPrimitiveRoot ζ (p ^ h))
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s t : ℤ) (y : ℤ_[p]) :
    oneAddPow (weightPoint p s ζ) (intHom ψ y)
        * PadicExpLog.padicExp (((p : ℕ) : K) * ((t - s : ℤ) : K) * intHom ψ y)
      = oneAddPow (weightPoint p t ζ) (intHom ψ y) := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by rw [hpK]; exact inv_lt_one_p (p := p)
  have hdisc : ∀ x : K, ‖x‖ ≤ 1 → ‖((p : ℕ) : K) * x‖ ^ 2 < ‖((p : ℕ) : K)‖ :=
    fun _ hx => norm_p_mul_sq_ltG hpK hx
  have hs : ‖((s : ℤ) : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one (R := K) s
  have ht : ‖((t : ℤ) : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one (R := K) t
  have hc : ‖((p : ℕ) : K) * ((t - s : ℤ) : K)‖ ≤ (p : ℝ)⁻¹ :=
    norm_p_mul_le_invG hpK (IsUltrametricDist.norm_intCast_le_one (R := K) _)
  refine congrFun (PadicInt.denseRange_natCast.equalizer
    ((continuous_oneAddPow_intHom ψ hψ (norm_weightPoint_lt_one_prime_pow hp2 hh hζ hpK s)).mul
      (continuous_padicExp_mul_intHom ψ hp2 hψ hc))
    (continuous_oneAddPow_intHom ψ hψ (norm_weightPoint_lt_one_prime_pow hp2 hh hζ hpK t))
    (funext fun n => ?_)) y
  have hn : ‖((n : ℕ) : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K n
  have hpow : ∀ v : K, ‖v‖ ≤ 1 → PadicExpLog.padicExp (((p : ℕ) : K) * v) ^ n
      = PadicExpLog.padicExp (((p : ℕ) : K) * (((n : ℕ) : K) * v)) := fun v hv => by
    rw [← PadicExpLog.padicExp_natCast_mul h3 hp2 (hdisc v hv) n]
    congr 1
    ring
  simp only [Function.comp_apply, Pi.mul_apply, map_natCast]
  rw [oneAddPow_natCast, oneAddPow_natCast]
  simp only [weightPoint, show ∀ x : K, (1 : K) + (x - 1) = x from fun x => by ring]
  rw [mul_pow, mul_pow, mul_assoc]
  congr 1
  rw [hpow _ hs, hpow _ ht,
    show ((p : ℕ) : K) * ((t - s : ℤ) : K) * ((n : ℕ) : K)
      = ((p : ℕ) : K) * ((((t : ℤ) : K) - ((s : ℤ) : K)) * ((n : ℕ) : K)) from by push_cast; ring,
    ← PadicExpLog.padicExp_add h3 hp2 (hdisc _ (norm_mul_le_oneG hn hs))
      (hdisc _ (norm_mul_le_oneG (by
        calc ‖((t : ℤ) : K) - ((s : ℤ) : K)‖ = ‖((t - s : ℤ) : K)‖ := by push_cast; ring_nf
          _ ≤ 1 := IsUltrametricDist.norm_intCast_le_one (R := K) _) hn))]
  congr 1
  ring

/-- **The specialised universal characters at the source and the target agree up to the
classical factors** at conductor `p^{h+1}`:
`[a]_{T₁}(ω·ω₀^{−2k−2})·(ψa)^{k+2} = [a]_{T₀}(ω)·(ψa)^{−k}` (`specialize_univChar_targetChar`
with the level-`h` inputs). -/
theorem specialize_univChar_targetChar_prime_pow (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K}
    {h : ℕ} (hh : 0 < h) (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹)
    (k : ℕ) (a : ℤ_[p]ˣ) :
    HaloInt.specialize (intHom ψ) (weightPoint p (-(k + 2 : ℤ)) ζ) (univChar (targetChar p ω k) a)
        * intHom ψ (a : ℤ_[p]) ^ (k + 2)
      = HaloInt.specialize (intHom ψ) (classicalPoint p k ζ) (univChar ω a)
        * (intHom ψ (a : ℤ_[p]))⁻¹ ^ k := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by rw [hpK]; exact inv_lt_one_p (p := p)
  set r : (ZMod p)ˣ := Units.map (PadicInt.toZMod (p := p)).toMonoidHom a with hr
  set x : K := intHom ψ ((teichRes r : ℤ_[p]ˣ) : ℤ_[p]) with hx
  set L : K := intHom ψ (logQuot a) with hL
  set e : K := PadicExpLog.padicExp (((p : ℕ) : K) * L) with he
  have hLle : ‖L‖ ≤ 1 := by rw [hL, norm_intHom ψ hψ]; exact PadicInt.norm_le_one _
  have hx0 : x ≠ 0 := ((teichRes r).isUnit.map (intHom ψ)).ne_zero
  have he0 : e ≠ 0 := by
    have hn1 : ‖e‖ = 1 :=
      norm_eq_one_of_norm_sub_le (p := p) norm_one
        ((PadicExpLog.norm_padicExp_sub_one_le h3 hp2 (norm_p_mul_sq_ltG hpK hLle)).trans
          (norm_p_mul_le_invG hpK hLle))
    exact norm_ne_zero_iff.1 (by rw [hn1]; exact one_ne_zero)
  have ha : intHom ψ (a : ℤ_[p]) = x * e := by
    rw [hx, he, hL, ← intHom_oneUnitPart_eq_padicExp ψ hp2 hψ a, ← map_mul,
      ← coe_eq_teichRes_mul_oneUnitPart a]
  have hchar : intHom ψ (((targetChar p ω k) r : ℤ_[p]ˣ) : ℤ_[p])
      = intHom ψ ((ω r : ℤ_[p]ˣ) : ℤ_[p]) * (x ^ (2 * k + 2))⁻¹ := by
    rw [targetChar_apply, Units.val_mul, map_mul, map_units_inv, Units.val_pow_eq_pow_val,
      map_pow, hx]
  have hbin : oneAddPow (classicalPoint p k ζ) L
      = oneAddPow (weightPoint p (-(k + 2 : ℤ)) ζ) L * e ^ (2 * k + 2) := by
    have h20 := oneAddPow_weightPoint_mul_padicExp_prime_pow ψ hp2 hψ hh hζ hpK
      (-(k + 2 : ℤ)) (k : ℤ) (logQuot a)
    rw [weightPoint_natCast] at h20
    rw [← h20, he, ← PadicExpLog.padicExp_natCast_mul h3 hp2
      (norm_p_mul_sq_ltG hpK hLle) (2 * k + 2)]
    congr 2
    push_cast
    ring
  rw [specialize_univChar (intHom ψ) (norm_intHom ψ hψ)
      (inv_lt_norm_weightPoint_prime_pow hp2 hh hζ hpK _)
      (norm_weightPoint_lt_one_prime_pow hp2 hh hζ hpK _) (targetChar p ω k) a,
    specialize_univChar (intHom ψ) (norm_intHom ψ hψ)
      (inv_lt_norm_classicalPoint_prime_pow hp2 hh hζ hpK k)
      (norm_classicalPoint_lt_one_prime_pow hp2 hh hζ hpK k) ω a,
    hchar, hbin, ha]
  simp only [mul_pow, inv_pow, mul_inv]
  field_simp [hx0, he0]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- **AG-ζ at level `h`**: the target-shape constants at the target point are the classical
datum's constants (`certConj_apply_one_one`, `haloCharFunH_psi` at both points,
`specialize_univChar_targetChar_prime_pow`). -/
theorem targetConst_eq_classicalDataH_u (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K} {h : ℕ}
    (hh : 0 < h) (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ)
    (i : ι) (t : Fin p) (a : ZMod (p ^ h)) :
    haloCharFunH h ψ (weightPoint p (-(k + 2 : ℤ)) ζ) (targetChar p ω k)
          (certConj θG h ψ U hU vRep hvΔ uu i t a 1 1)
        * (certConj θG h ψ U hU vRep hvΔ uu i t a 1 1) ^ (k + 2)
      = (classicalDataH ψ ω θG U hU vRep hvΔ uu hp2 hψ hh hζ hpK k).u i t a := by
  show haloCharFunH h ψ (weightPoint p (-(k + 2 : ℤ)) ζ) (targetChar p ω k)
        (certConj θG h ψ U hU vRep hvΔ uu i t a 1 1)
      * (certConj θG h ψ U hU vRep hvΔ uu i t a 1 1) ^ (k + 2)
    = haloCharFunH h ψ (classicalPoint p k ζ) ω (certConj θG h ψ U hU vRep hvΔ uu i t a 1 1)
      * (certConj θG h ψ U hU vRep hvΔ uu i t a 1 1)⁻¹ ^ k
  rw [certConj_apply_one_one,
    haloCharFunH_psi h ψ (weightPoint p (-(k + 2 : ℤ)) ζ) (targetChar p ω k) hp2 hψ
      (inv_lt_norm_weightPoint_prime_pow hp2 hh hζ hpK _)
      (norm_weightPoint_lt_one_prime_pow hp2 hh hζ hpK _)
      (norm_TH_weightPoint_sq_lt hp2 hζ.pow_eq_one hpK _) _,
    haloCharFunH_psi h ψ (classicalPoint p k ζ) ω hp2 hψ
      (inv_lt_norm_classicalPoint_prime_pow hp2 hh hζ hpK k)
      (norm_classicalPoint_lt_one_prime_pow hp2 hh hζ hpK k)
      (norm_TH_classicalPoint_sq_lt hp2 hζ.pow_eq_one hpK k) _]
  exact specialize_univChar_targetChar_prime_pow ψ ω hp2 hψ hh hζ hpK k _

/-! ### The target datum at level `h` -/

section TargetDataH

variable {θG ψ U hU vRep hvΔ uu} {h : ℕ}

/-- **The theta target of a level-`h` classical datum**: a halo point `T₁` at level `h` of the
weight `(−k−2, ψ)` whose level-`h` halo weight has the target shape with the datum's
nebentypus constants.  `TargetData` is the case `h = 1`. -/
structure TargetDataH {hp2 : p ≠ 2} {hψ : ∀ x, ‖ψ x‖ = ‖x‖} {ω : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ : K}
    {k : ℕ} (c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (ω₁ : (ZMod p)ˣ →* ℤ_[p]ˣ) (T₁ : K) where
  /-- The halo annulus, lower bound. -/
  h0 : (p : ℝ)⁻¹ < ‖T₁‖
  /-- The halo annulus, upper bound. -/
  h1 : ‖T₁‖ < 1
  /-- The level-`h` analyticity condition. -/
  hT : ‖TH p h T₁‖ ^ 2 < (p : ℝ)⁻¹
  /-- The target shape, with the source's constants. -/
  shape : IsClassicalShape' θG h ψ U hU vRep hvΔ uu (haloWeightH h ψ T₁ ω₁ hp2 hψ h0 h1 hT) k c.u

namespace TargetDataH

variable {hp2 : p ≠ 2} {hψ : ∀ x, ‖ψ x‖ = ‖x‖} {ω ω₁ : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₁ : K} {k : ℕ}
  {c : ClassicalDataH θG h ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k}

/-- The level-`h` halo weight of the target. -/
def weight (d : TargetDataH c ω₁ T₁) :
    AnalyticWeight (haloUnitsH h ψ) (M1Kh h ψ) (haloRhoH p h T₁) :=
  haloWeightH h ψ T₁ ω₁ hp2 hψ d.h0 d.h1 d.hT

end TargetDataH

end TargetDataH

omit [Fintype ι] [DecidableEq ι] in
/-- **The theta target of the classical datum at a classical point of conductor `p^{h+1}`**:
the halo point `T_{(−k−2,ψ)}` with the nebentypus `ω·ω₀^{−2k−2}`. -/
theorem targetData_classicalPointH (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K} {h : ℕ}
    (hh : 0 < h) (hζ : IsPrimitiveRoot ζ (p ^ h)) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    TargetDataH (classicalDataH ψ ω θG U hU vRep hvΔ uu hp2 hψ hh hζ hpK k) (targetChar p ω k)
      (weightPoint p (-(k + 2 : ℤ)) ζ) where
  h0 := inv_lt_norm_weightPoint_prime_pow hp2 hh hζ hpK _
  h1 := norm_weightPoint_lt_one_prime_pow hp2 hh hζ hpK _
  hT := norm_TH_weightPoint_sq_lt hp2 hζ.pow_eq_one hpK _
  shape := by
    have hu : (fun (i : ι) (t : Fin p) (a : ZMod (p ^ h)) =>
          haloCharFunH h ψ (weightPoint p (-(k + 2 : ℤ)) ζ) (targetChar p ω k)
              (certConj θG h ψ U hU vRep hvΔ uu i t a 1 1)
            * (certConj θG h ψ U hU vRep hvΔ uu i t a 1 1) ^ (k + 2))
        = (classicalDataH ψ ω θG U hU vRep hvΔ uu hp2 hψ hh hζ hpK k).u :=
      funext fun i => funext fun t => funext fun a =>
        targetConst_eq_classicalDataH_u ψ ω θG U hU vRep hvΔ uu hp2 hψ hh hζ hpK k i t a
    rw [← hu]
    exact isClassicalShape'_haloWeightH_weightPoint_neg_prime_pow ψ (targetChar p ω k) θG U hU
      vRep hvΔ uu hp2 hψ h hζ.pow_eq_one k _ _ _

end LWX

end
