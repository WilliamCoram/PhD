/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«15_ClassicalPoint»
import PhD.Main.LWX.«15_StepThree»

/-!
# The theta target of a classical point

[LWX, §3.23 Step III] applies the theta sequence at the classical weight `χ_k = (k, ψ)` and
reads off the target weight `(−k−2, ψ)`; its restriction to `Δ = 𝔽_p^×` is `ω·ω₀^{−2k−2}`
("`n⁺_{k+1} − n_{k+1} = r_ord(ψ|_Δ · ω₀^{−k−2}) = r_ord(ωω₀^{−2k−2})`", `lwx.txt:2070–2076`).
`15_StepThree.lean` packages what Step III needs of the target as `TargetData`: a halo point `T₁`
of the weight `(−k−2, ψ)` whose halo weight has the *target shape* `autFactor · L^{k+2} = C u`
with the **same** nebentypus constants `u` as the classical datum.  This file constructs it at
the classical points of `15_ClassicalPoint.lean`.

* `weightPoint p s ζ = ζ·exp(p s) − 1` is the `T`-coordinate of the weight `(s, ψ)` for `s ∈ ℤ`
  (`ψ(exp p) = ζ`, [LWX, §3.23]: "the corresponding `T`-coordinates `T_{χ_k}`"); at `s = k` it
  is `classicalPoint p k ζ`, and the target point is `s = −(k+2)`.  The halo conditions and the
  level-`1` halo exponent `s_1 = s` are proved once for every `s`.
* The binomial series with exponent `−n` is the inverse of `(1 + xz)^n`
  (`mk_choose_neg_natCast_mul_pow`, Vandermonde `Ring.add_choose_eq`), so the automorphy
  factor at the target point satisfies `autFactor · L^{k+2} = C(κ(d)·d^{k+2})`.
* **AG-ζ**: the constants agree.  With `a = ω₀(ā)·⟨a⟩` and `ψ⟨a⟩ = exp(p·ψ ℓ⟨a⟩)`, the
  binomial series at the two points differ by `exp(p(2k+2)·ψ ℓ)` — an identity of continuous
  functions of `ℓ ∈ ℤ_p` checked on `ℕ` (`PadicInt.denseRange_natCast`) — and the residue
  characters differ by `ω₀^{2k+2}`.  Hence `targetChar ω k = ω·ω₀^{−2k−2}`.
* The shift `(k, ω) ↦ (k + 1, ωω₀²)` of [LWX, Cor 1.4] on the characters:
  `targetChar (ωω₀²) (k + 1) = targetChar ω k`, and the identities in `ω₀^{2m}` it is iterated with.

No Jacquet–Langlands input; see `.mathlib-quality/lwx-stepone/JL-AUDIT.md`.
-/

open Filter Topology TateFredholm QMF QMF.Weight
open scoped Nat

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

/-! ### The Teichmüller character and the target nebentypus -/

variable (p) in
/-- **The Teichmüller character** `ω₀ : 𝔽_p^× → ℤ_p^×` ([LWX, Notation 2.1]), `teichRes` as a
monoid homomorphism. -/
def teichChar : (ZMod p)ˣ →* ℤ_[p]ˣ where
  toFun := teichRes
  map_one' := teichRes_one
  map_mul' := teichRes_mul

@[simp] theorem teichChar_apply (r : (ZMod p)ˣ) : teichChar p r = teichRes r := rfl

/-- `ω₀(ā) = ωT(a)`: the Teichmüller character of the residue of a unit is its Teichmüller
lift. -/
theorem teichChar_unitsMap_toZMod (a : ℤ_[p]ˣ) :
    teichChar p (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) = teichmuller a :=
  teichRes_toZMod a

variable (p) in
/-- **The target nebentypus** `ω·ω₀^{−2k−2}` of the theta target `(−k−2, ψ)` of the classical
weight `(k, ψ)` with `ψ|_Δ = ω·ω₀^{−k}` ([LWX, §3.23 Step III], `lwx.txt:2070–2076`). -/
def targetChar (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) : (ZMod p)ˣ →* ℤ_[p]ˣ :=
  ω * (teichChar p ^ (2 * k + 2))⁻¹

theorem targetChar_apply (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) (r : (ZMod p)ˣ) :
    targetChar p ω k r = ω r * (teichRes r ^ (2 * k + 2))⁻¹ := by
  rw [targetChar, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, teichChar_apply]

/-! ### The shift `(k, ω) ↦ (k + 1, ωω₀²)` on the characters ([LWX, Cor 1.4]) -/

/-- `ω·ω₀^{2·0} = ω`. -/
theorem mul_teichChar_pow_zero (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) : ω * teichChar p ^ (2 * 0) = ω := by
  refine MonoidHom.ext fun r => ?_
  rw [MonoidHom.mul_apply, MonoidHom.pow_apply, Nat.mul_zero, pow_zero, mul_one]

/-- `ω·ω₀^{2(m+1)} = (ω·ω₀^{2m})·ω₀²`. -/
theorem mul_teichChar_pow_succ (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (m : ℕ) :
    ω * teichChar p ^ (2 * (m + 1)) = ω * teichChar p ^ (2 * m) * teichChar p ^ 2 := by
  refine MonoidHom.ext fun r => ?_
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.pow_apply,
    MonoidHom.pow_apply, MonoidHom.pow_apply, mul_assoc, ← pow_add, mul_add, mul_one]

/-- `ω·ω₀^{−2·0} = ω`. -/
theorem mul_inv_teichChar_pow_zero (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    ω * (teichChar p ^ (2 * 0))⁻¹ = ω := by
  refine MonoidHom.ext fun r => ?_
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, Nat.mul_zero, pow_zero,
    inv_one, mul_one]

/-- `ωω₀²·ω₀^{−2(n+1)} = ω·ω₀^{−2n}` ([LWX, Cor 1.4], `lwx.txt:164–166`). -/
theorem mul_teichChar_sq_mul_inv_teichChar_pow_succ (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    ω * teichChar p ^ 2 * (teichChar p ^ (2 * (n + 1)))⁻¹ = ω * (teichChar p ^ (2 * n))⁻¹ := by
  refine MonoidHom.ext fun r => ?_
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply,
    MonoidHom.inv_apply, MonoidHom.pow_apply, MonoidHom.pow_apply, MonoidHom.pow_apply,
    show 2 * (n + 1) = 2 + 2 * n by ring, pow_add (teichChar p r) 2 (2 * n), mul_inv, mul_assoc,
    mul_inv_cancel_left]

/-- The target nebentypus `ωω₀^{−2k−2}` of weight `k` is `ωω₀^{−2(k+1)}`
([LWX, §3.23 Step III], `lwx.txt:2079–2097`: the second term of `deg X_{(k,k+1),ω}` at `k + 1`). -/
theorem targetChar_eq_mul_inv_teichChar_pow (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    targetChar p ω k = ω * (teichChar p ^ (2 * (k + 1)))⁻¹ :=
  rfl

/-- The target nebentypus of `(ωω₀², k+1)` is that of `(ω, k)`:
`ωω₀²·ω₀^{−2(k+1)−2} = ωω₀^{−2k−2}` ([LWX, Cor 1.4], `lwx.txt:164–166`). -/
theorem targetChar_mul_teichChar_sq_succ (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    targetChar p (ω * teichChar p ^ 2) (k + 1) = targetChar p ω k := by
  refine MonoidHom.ext fun r => ?_
  rw [targetChar_apply, targetChar_apply, MonoidHom.mul_apply, MonoidHom.pow_apply, teichChar_apply,
    show 2 * (k + 1) + 2 = 2 + (2 * k + 2) by ring, pow_add (teichRes r) 2 (2 * k + 2), mul_inv,
    mul_assoc, mul_inv_cancel_left]

/-! ### The `T`-coordinate of the weight `(s, ψ)` -/

variable (p) in
/-- **The halo point of the weight `(s, ψ)`**, `s ∈ ℤ`: `T_{(s,ψ)} = ζ·exp(p s) − 1` with
`ζ = ψ(exp p)` ([LWX, §3.23], `lwx.txt:1794–1798`; `classicalPoint` is the case `s = k ≥ 0`). -/
def weightPoint (s : ℤ) (ζ : K) : K :=
  ζ * PadicExpLog.padicExp (((p : ℕ) : K) * (s : K)) - 1

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- At a natural exponent the weight point is the classical point. -/
theorem weightPoint_natCast (k : ℕ) (ζ : K) : weightPoint p (k : ℤ) ζ = classicalPoint p k ζ := by
  rw [weightPoint, classicalPoint, Int.cast_natCast]


omit [CompleteSpace K] [CharZero K] in
/-- `p⁻¹ < 1`, `0 < p⁻¹`, and `‖p‖ = p⁻¹`: the three inequalities every norm computation at a
weight point uses. -/
private theorem inv_p_pos : (0 : ℝ) < (p : ℝ)⁻¹ := by
  have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  positivity

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- A `p`-adically small element lies in the exponential's disc: `‖w‖ ≤ p⁻¹` gives
`‖w‖² < ‖p‖`. -/
private theorem norm_sq_lt_of_le_inv (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {w : K}
    (hw : ‖w‖ ≤ (p : ℝ)⁻¹) : ‖w‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
  have h0 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_p_pos (p := p)
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_p (p := p)
  calc ‖w‖ ^ 2 ≤ ((p : ℝ)⁻¹) ^ 2 := by gcongr
    _ < (p : ℝ)⁻¹ := by nlinarith
    _ = ‖((p : ℕ) : K)‖ := hpK.symm

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `‖p·x‖ ≤ p⁻¹` for `‖x‖ ≤ 1`. -/
private theorem norm_p_mul_le_inv (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x : K} (hx : ‖x‖ ≤ 1) :
    ‖((p : ℕ) : K) * x‖ ≤ (p : ℝ)⁻¹ := by
  rw [norm_mul, hpK]
  exact mul_le_of_le_one_right (inv_p_pos (p := p)).le hx

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `‖p·x‖² < ‖p‖` for `‖x‖ ≤ 1`: the exponential's disc contains `p·x`. -/
private theorem norm_p_mul_sq_lt (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x : K} (hx : ‖x‖ ≤ 1) :
    ‖((p : ℕ) : K) * x‖ ^ 2 < ‖((p : ℕ) : K)‖ :=
  norm_sq_lt_of_le_inv hpK (norm_p_mul_le_inv hpK hx)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- A product of two elements of the unit ball has norm at most one. -/
private theorem norm_mul_le_one {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x * y‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ hx (norm_nonneg y) hy

/-- `‖exp(p·x) − 1‖ ≤ p⁻¹` for `‖x‖ ≤ 1`. -/
private theorem norm_padicExp_p_mul_sub_one_le (hp2 : p ≠ 2)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) {x : K} (hx : ‖x‖ ≤ 1) :
    ‖PadicExpLog.padicExp (((p : ℕ) : K) * x) - 1‖ ≤ (p : ℝ)⁻¹ :=
  (PadicExpLog.norm_padicExp_sub_one_le (by rw [hpK]; exact inv_lt_one_p (p := p)) hp2
    (norm_p_mul_sq_lt hpK hx)).trans (norm_p_mul_le_inv hpK hx)

/-- `‖T_{(s,ψ)}‖ = ‖ζ − 1‖`: the factor `exp(ps)` is a `1`-unit closer to `1` than `ζ`. -/
theorem norm_weightPoint (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    ‖weightPoint p s ζ‖ = ‖ζ - 1‖ := by
  have hs : ‖((s : ℤ) : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one (R := K) s
  have hE1 : ‖PadicExpLog.padicExp (((p : ℕ) : K) * ((s : ℤ) : K)) - 1‖ ≤ (p : ℝ)⁻¹ :=
    norm_padicExp_p_mul_sub_one_le hp2 hpK hs
  have hEn : ‖PadicExpLog.padicExp (((p : ℕ) : K) * ((s : ℤ) : K))‖ = 1 :=
    norm_eq_one_of_norm_sub_le (p := p) norm_one hE1
  have hgt : (p : ℝ)⁻¹ < ‖ζ - 1‖ := inv_lt_norm_sub_one_of_isPrimitiveRoot hp2 hζ hpK
  have hsplit : weightPoint p s ζ
      = (ζ - 1) * PadicExpLog.padicExp (((p : ℕ) : K) * ((s : ℤ) : K))
        + (PadicExpLog.padicExp (((p : ℕ) : K) * ((s : ℤ) : K)) - 1) := by
    rw [weightPoint]; ring
  have hne : ‖(ζ - 1) * PadicExpLog.padicExp (((p : ℕ) : K) * ((s : ℤ) : K))‖
      ≠ ‖PadicExpLog.padicExp (((p : ℕ) : K) * ((s : ℤ) : K)) - 1‖ := by
    rw [norm_mul, hEn, mul_one]
    exact fun hcon => absurd (hcon ▸ hE1) (not_le.2 hgt)
  rw [hsplit, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_mul, hEn, mul_one,
    max_eq_left (hE1.trans hgt.le)]

/-- The classical norm condition at every weight point: `‖T_{(s,ψ)}‖^{p−1} = ‖p‖`. -/
theorem norm_weightPoint_pow (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    ‖weightPoint p s ζ‖ ^ (p - 1) = ‖((p : ℕ) : K)‖ := by
  rw [norm_weightPoint hp2 hζ hpK s]
  exact norm_sub_one_pow_of_isPrimitiveRoot hζ (by rw [hpK]; exact inv_lt_one_p (p := p))

/-- The weight point lies in the halo annulus: `p⁻¹ < ‖T_{(s,ψ)}‖`. -/
theorem inv_lt_norm_weightPoint (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    (p : ℝ)⁻¹ < ‖weightPoint p s ζ‖ := by
  rw [norm_weightPoint hp2 hζ hpK s]
  exact inv_lt_norm_sub_one_of_isPrimitiveRoot hp2 hζ hpK

/-- The weight point lies in the halo annulus: `‖T_{(s,ψ)}‖ < 1`. -/
theorem norm_weightPoint_lt_one (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    ‖weightPoint p s ζ‖ < 1 := by
  rw [norm_weightPoint hp2 hζ hpK s]
  exact norm_sub_one_lt_one_of_isPrimitiveRoot hζ (by rw [hpK]; exact inv_lt_one_p (p := p))

/-- At level `1` the wild part disappears: `(1 + T_{(s,ψ)})^p − 1 = exp(p²s) − 1`. -/
theorem TH_one_weightPoint (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    TH p 1 (weightPoint p s ζ) = PadicExpLog.padicExp (((p : ℕ) : K) ^ 2 * (s : K)) - 1 := by
  have hs : ‖((s : ℤ) : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one (R := K) s
  rw [TH, weightPoint, show ∀ x : K, (1 : K) + (x - 1) = x from fun x => by ring,
    pow_one, mul_pow, hζ.pow_eq_one, one_mul,
    ← PadicExpLog.padicExp_natCast_mul (by rw [hpK]; exact inv_lt_one_p (p := p)) hp2
      (norm_p_mul_sq_lt hpK hs) p]
  congr 2
  ring

/-- The level-`1` analyticity condition at the weight point. -/
theorem norm_TH_one_weightPoint_sq_lt (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    ‖TH p 1 (weightPoint p s ζ)‖ ^ 2 < (p : ℝ)⁻¹ := by
  have h0 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_p_pos (p := p)
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_p (p := p)
  have hs : ‖((s : ℤ) : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one (R := K) s
  have hx : ‖((p : ℕ) : K) * ((s : ℤ) : K)‖ ≤ 1 :=
    (norm_p_mul_le_inv hpK hs).trans (inv_lt_one_p (p := p)).le
  have hle : ‖TH p 1 (weightPoint p s ζ)‖ ≤ (p : ℝ)⁻¹ := by
    rw [TH_one_weightPoint hp2 hζ hpK s,
      show ((p : ℕ) : K) ^ 2 * ((s : ℤ) : K) = ((p : ℕ) : K) * (((p : ℕ) : K) * ((s : ℤ) : K))
        from by ring]
    exact norm_padicExp_p_mul_sub_one_le hp2 hpK hx
  calc ‖TH p 1 (weightPoint p s ζ)‖ ^ 2 ≤ ((p : ℝ)⁻¹) ^ 2 := by gcongr
    _ < (p : ℝ)⁻¹ := by nlinarith

/-- **The level-`1` halo exponent at the weight point is `s`**: `s_1 = log(exp(p²s))/p² = s`. -/
theorem haloExponentH_one_weightPoint (hp2 : p ≠ 2) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s : ℤ) :
    haloExponentH p 1 (weightPoint p s ζ) = (s : K) := by
  have h0 : ((p : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hp.out.pos.ne'
  have hs : ‖((s : ℤ) : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one (R := K) s
  have hx : ‖((p : ℕ) : K) * ((s : ℤ) : K)‖ ≤ 1 :=
    (norm_p_mul_le_inv hpK hs).trans (inv_lt_one_p (p := p)).le
  have hdisc : ‖((p : ℕ) : K) ^ 2 * ((s : ℤ) : K)‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
    rw [show ((p : ℕ) : K) ^ 2 * ((s : ℤ) : K) = ((p : ℕ) : K) * (((p : ℕ) : K) * ((s : ℤ) : K))
      from by ring]
    exact norm_p_mul_sq_lt hpK hx
  rw [haloExponentH, TH_one_weightPoint hp2 hζ hpK s,
    show ∀ x : K, (1 : K) + (x - 1) = x from fun x => by ring,
    PadicExpLog.padicLog_padicExp (by rw [hpK]; exact inv_lt_one_p (p := p)) hp2 hdisc]
  field_simp
  ring

/-! ### The binomial series with a negative integer exponent -/

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **Vandermonde for the binomial series**: `(1+xz)^a · (1+xz)^b = (1+xz)^{a+b}` as formal
series in `z` (`Ring.add_choose_eq`). -/
theorem mk_choose_mul_mk_choose (a b x : K) :
    PowerSeries.mk (fun m => Ring.choose a m * x ^ m)
        * PowerSeries.mk (fun m => Ring.choose b m * x ^ m)
      = PowerSeries.mk (fun m => Ring.choose (a + b) m * x ^ m) := by
  refine PowerSeries.ext fun m => ?_
  rw [PowerSeries.coeff_mul, PowerSeries.coeff_mk, Ring.add_choose_eq m (Commute.all a b),
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, ← Finset.mem_antidiagonal.1 hij, pow_add]
  ring

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The binomial series with exponent `0` is `1` (`Ring.choose_zero_ite`). -/
theorem mk_choose_zero (x : K) :
    PowerSeries.mk (fun m => Ring.choose (0 : K) m * x ^ m) = 1 := by
  refine PowerSeries.ext fun m => ?_
  rw [PowerSeries.coeff_mk, Ring.choose_zero_ite K, PowerSeries.coeff_one]
  split_ifs with hm
  · rw [hm, pow_zero, mul_one]
  · rw [zero_mul]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **The binomial series with exponent `−n` inverts `(1 + xz)^n`**:
`mk_choose_mul_mk_choose` at `(−n) + n = 0`, `mk_choose_zero`, `mk_choose_natCast_mul_pow`. -/
theorem mk_choose_neg_natCast_mul_pow (n : ℕ) (x : K) :
    PowerSeries.mk (fun m => Ring.choose (-(n : K)) m * x ^ m)
        * (1 + PowerSeries.C x * PowerSeries.X) ^ n = 1 := by
  rw [← mk_choose_natCast_mul_pow n x, mk_choose_mul_mk_choose, neg_add_cancel, mk_choose_zero]

/-! ### The halo weight at the target point has the target shape -/

variable (ψ : ℚ_[p] →+* K) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)

/-- **The automorphy factor of the halo weight at the target point** satisfies
`autFactor · L^{k+2} = C(κ(d)·d^{k+2})`: `autFactor_haloWeightH` with the halo exponent
`−(k+2)` (`haloExponentH_one_weightPoint`) and `mk_choose_neg_natCast_mul_pow`. -/
theorem autFactor_haloWeightH_weightPoint_neg (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (k : ℕ)
    (h0 : (p : ℝ)⁻¹ < ‖weightPoint p (-(k + 2 : ℤ)) ζ‖)
    (h1 : ‖weightPoint p (-(k + 2 : ℤ)) ζ‖ < 1)
    (hT : ‖TH p 1 (weightPoint p (-(k + 2 : ℤ)) ζ)‖ ^ 2 < (p : ℝ)⁻¹) (g : M1Kh 1 ψ) :
    (haloWeightH 1 ψ (weightPoint p (-(k + 2 : ℤ)) ζ) ω hp2 hψ h0 h1 hT).toWeightSeries.autFactor
          g.1 * linX g.1 ^ (k + 2)
      = PowerSeries.C (haloCharFunH 1 ψ (weightPoint p (-(k + 2 : ℤ)) ζ) ω (g.1 1 1)
          * (g.1 1 1) ^ (k + 2)) := by
  have hd0 : g.1 1 1 ≠ 0 :=
    (levelBounds_M1Kh 1 ψ (weightPoint p (-(k + 2 : ℤ)) ζ) hψ hT).d_ne_zero g.2
  have hlin : linX g.1
      = PowerSeries.C (g.1 1 1)
        * (1 + PowerSeries.C (g.1 1 0 / g.1 1 1) * PowerSeries.X) := by
    rw [linX, mul_add, mul_one, ← mul_assoc, ← map_mul,
      show g.1 1 1 * (g.1 1 0 / g.1 1 1) = g.1 1 0 from by field_simp]
  have hcast : ((-(k + 2 : ℤ) : ℤ) : K) = -(((k + 2 : ℕ)) : K) := by push_cast; ring
  rw [autFactor_haloWeightH 1 ψ (weightPoint p (-(k + 2 : ℤ)) ζ) ω hp2 hψ h0 h1 hT g,
    haloExponentH_one_weightPoint hp2 hζ (norm_natCast_p ψ hψ) (-(k + 2 : ℤ)), hcast, hlin,
    mul_pow, ← map_pow, map_mul]
  linear_combination (PowerSeries.C (haloCharFunH 1 ψ (weightPoint p (-(k + 2 : ℤ)) ζ) ω (g.1 1 1))
      * PowerSeries.C (g.1 1 1 ^ (k + 2)))
    * mk_choose_neg_natCast_mul_pow (k + 2) (g.1 1 0 / g.1 1 1)

variable {G : Type*} [Group G] {Γ : Subgroup G} (θG : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)
  (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θG) (uu : ι → Fin p → U)

omit [Fintype ι] [DecidableEq ι] in
/-- **The target shape of the halo weight at the target point**, with the constants
`κ(d)·d^{k+2}` at the lower-right entry `d` of the disc conjugate. -/
theorem isClassicalShape'_haloWeightH_weightPoint_neg (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    {ζ : K} (hζ : IsPrimitiveRoot ζ p) (k : ℕ)
    (h0 : (p : ℝ)⁻¹ < ‖weightPoint p (-(k + 2 : ℤ)) ζ‖)
    (h1 : ‖weightPoint p (-(k + 2 : ℤ)) ζ‖ < 1)
    (hT : ‖TH p 1 (weightPoint p (-(k + 2 : ℤ)) ζ)‖ ^ 2 < (p : ℝ)⁻¹) :
    IsClassicalShape' θG 1 ψ U hU vRep hvΔ uu
      (haloWeightH 1 ψ (weightPoint p (-(k + 2 : ℤ)) ζ) ω hp2 hψ h0 h1 hT) k
      fun i t a => haloCharFunH 1 ψ (weightPoint p (-(k + 2 : ℤ)) ζ) ω
          (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1)
        * (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1) ^ (k + 2) :=
  fun i t a => autFactor_haloWeightH_weightPoint_neg ψ ω hp2 hψ hζ k h0 h1 hT
    (discConjK 1 (certM1 θG U hU vRep hvΔ uu i t) a ψ)

/-! ### AG-ζ: the nebentypus constants of the source and the target agree -/

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] [Fintype ι] [DecidableEq ι] in
/-- **The lower-right entry of a disc conjugate is `ψ` of a `p`-adic unit**: the `d`-entry of
its `LocalMat` record. -/
theorem certConj_apply_one_one (h : ℕ) (i : ι) (t : Fin p) (a : ZMod (p ^ h)) :
    certConj θG h ψ U hU vRep hvΔ uu i t a 1 1
      = intHom ψ ((M1.toLocalMat (discConj h (certM1 θG U hU vRep hvΔ uu i t) a)).d : ℤ_[p]) := by
  rw [certConj, coe_discConjK, RingHom.mapMatrix_apply, Matrix.map_apply, intHom_apply,
    M1.coe_toLocalMat_d]

/-- **The Teichmüller decomposition** `a = ω₀(ā)·⟨a⟩` of a unit ([LWX, Notation 2.1]). -/
theorem coe_eq_teichRes_mul_oneUnitPart (a : ℤ_[p]ˣ) :
    (a : ℤ_[p]) = (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p])
      * oneUnitPart a := by
  rw [teichRes_toZMod, oneUnitPart, ← Units.val_mul, mul_comm a (teichmuller a)⁻¹,
    mul_inv_cancel_left]

/-- **`exp` is continuous on the disc**: `‖exp w − exp w'‖ ≤ ‖w − w'‖` there
(`padicExp_add`, `norm_padicExp_sub_one_le`), so `y ↦ exp(c·ψ y)` is continuous on `ℤ_p` for
`‖c‖ ≤ p⁻¹`. -/
theorem continuous_padicExp_mul_intHom (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {c : K}
    (hc : ‖c‖ ≤ (p : ℝ)⁻¹) :
    Continuous fun y : ℤ_[p] => PadicExpLog.padicExp (c * intHom ψ y) := by
  have hpK := norm_natCast_p ψ hψ
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by rw [hpK]; exact inv_lt_one_p (p := p)
  have hle : ∀ y : ℤ_[p], ‖c * intHom ψ y‖ ≤ (p : ℝ)⁻¹ := fun y => by
    calc ‖c * intHom ψ y‖ = ‖c‖ * ‖y‖ := by rw [norm_mul, norm_intHom ψ hψ]
      _ ≤ ‖c‖ * 1 := by gcongr; exact PadicInt.norm_le_one y
      _ = ‖c‖ := mul_one _
      _ ≤ (p : ℝ)⁻¹ := hc
  have hdisc : ∀ y : ℤ_[p], ‖c * intHom ψ y‖ ^ 2 < ‖((p : ℕ) : K)‖ := fun y =>
    norm_sq_lt_of_le_inv hpK (hle y)
  refine (LipschitzWith.of_dist_le_mul (K := ⟨‖c‖, norm_nonneg c⟩) fun y y' => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm]
  have hEn : ‖PadicExpLog.padicExp (c * intHom ψ y')‖ = 1 :=
    norm_eq_one_of_norm_sub_le (p := p) norm_one
      ((PadicExpLog.norm_padicExp_sub_one_le h3 hp2 (hdisc y')).trans (hle y'))
  have hdiff : PadicExpLog.padicExp (c * intHom ψ y) - PadicExpLog.padicExp (c * intHom ψ y')
      = PadicExpLog.padicExp (c * intHom ψ y')
        * (PadicExpLog.padicExp (c * intHom ψ (y - y')) - 1) := by
    rw [mul_sub, mul_one, ← PadicExpLog.padicExp_add h3 hp2 (hdisc y') (hdisc (y - y'))]
    congr 2
    rw [map_sub]
    ring
  rw [hdiff, norm_mul, hEn, one_mul]
  calc ‖PadicExpLog.padicExp (c * intHom ψ (y - y')) - 1‖ ≤ ‖c * intHom ψ (y - y')‖ :=
        PadicExpLog.norm_padicExp_sub_one_le h3 hp2 (hdisc _)
    _ = ‖c‖ * ‖y - y'‖ := by rw [norm_mul, norm_intHom ψ hψ]

/-- **The one-unit part is the exponential of the normalised logarithm**:
`ψ⟨a⟩ = exp(p·ψ ℓ⟨a⟩)` (`coe_logQuot`, `map_padicLog`, `padicExp_padicLog`). -/
theorem intHom_oneUnitPart_eq_padicExp (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (a : ℤ_[p]ˣ) :
    intHom ψ (oneUnitPart a)
      = PadicExpLog.padicExp (((p : ℕ) : K) * intHom ψ (logQuot a)) := by
  have hpK := norm_natCast_p ψ hψ
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by rw [hpK]; exact inv_lt_one_p (p := p)
  have hpne : ((p : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 hp.out.pos.ne'
  have hu : ‖oneUnitPart a - 1‖ ≤ (p : ℝ)⁻¹ := norm_oneUnitPart_sub_one_le a
  have hyQ : ‖((oneUnitPart a : ℤ_[p]) : ℚ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ := by
    rw [show ((oneUnitPart a : ℤ_[p]) : ℚ_[p]) - 1 = ((oneUnitPart a - 1 : ℤ_[p]) : ℚ_[p]) from by
      push_cast; ring, ← PadicInt.norm_def]
    exact hu
  have hK : ‖intHom ψ (oneUnitPart a) - 1‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
    refine norm_sq_lt_of_le_inv hpK ?_
    rw [show intHom ψ (oneUnitPart a) - 1 = intHom ψ (oneUnitPart a - 1) from by
      rw [map_sub, map_one], norm_intHom ψ hψ]
    exact hu
  rw [← PadicExpLog.padicExp_padicLog h3 hp2 hK]
  congr 1
  rw [intHom_apply (ψ := ψ) (x := logQuot a), coe_logQuot hp2]
  simp only [qlog]
  rw [map_div₀, map_natCast, mul_comm ((p : ℕ) : K), div_mul_cancel₀ _ hpne,
    map_padicLog ψ hp2 hψ hyQ]
  rfl

/-- **The binomial series at two weight points differ by an exponential**:
`(1+T_s)^{ψ y}·exp(p(t−s)·ψ y) = (1+T_t)^{ψ y}` for every `y ∈ ℤ_p` — both sides are continuous
in `y` and agree on `ℕ` (`oneAddPow_natCast`, `padicExp_natCast_mul`, `padicExp_add`;
`PadicInt.denseRange_natCast`). -/
theorem oneAddPow_weightPoint_mul_padicExp (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (s t : ℤ) (y : ℤ_[p]) :
    oneAddPow (weightPoint p s ζ) (intHom ψ y)
        * PadicExpLog.padicExp (((p : ℕ) : K) * ((t - s : ℤ) : K) * intHom ψ y)
      = oneAddPow (weightPoint p t ζ) (intHom ψ y) := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by rw [hpK]; exact inv_lt_one_p (p := p)
  have hdisc : ∀ x : K, ‖x‖ ≤ 1 → ‖((p : ℕ) : K) * x‖ ^ 2 < ‖((p : ℕ) : K)‖ :=
    fun _ hx => norm_p_mul_sq_lt hpK hx
  have hs : ‖((s : ℤ) : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one (R := K) s
  have ht : ‖((t : ℤ) : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one (R := K) t
  have hc : ‖((p : ℕ) : K) * ((t - s : ℤ) : K)‖ ≤ (p : ℝ)⁻¹ :=
    norm_p_mul_le_inv hpK (IsUltrametricDist.norm_intCast_le_one (R := K) _)
  refine congrFun (PadicInt.denseRange_natCast.equalizer
    ((continuous_oneAddPow_intHom ψ hψ (norm_weightPoint_lt_one hp2 hζ hpK s)).mul
      (continuous_padicExp_mul_intHom ψ hp2 hψ hc))
    (continuous_oneAddPow_intHom ψ hψ (norm_weightPoint_lt_one hp2 hζ hpK t))
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
    ← PadicExpLog.padicExp_add h3 hp2 (hdisc _ (norm_mul_le_one hn hs))
      (hdisc _ (norm_mul_le_one (by
        calc ‖((t : ℤ) : K) - ((s : ℤ) : K)‖ = ‖((t - s : ℤ) : K)‖ := by push_cast; ring_nf
          _ ≤ 1 := IsUltrametricDist.norm_intCast_le_one (R := K) _) hn))]
  congr 1
  ring

/-- **The specialised universal characters at the source and the target agree up to the
classical factors**: `[a]_{T₁}(ω·ω₀^{−2k−2})·(ψa)^{k+2} = [a]_{T₀}(ω)·(ψa)^{−k}`
(`specialize_univChar` at both points, `coe_eq_teichRes_mul_oneUnitPart`,
`intHom_oneUnitPart_eq_padicExp`, `oneAddPow_weightPoint_mul_padicExp`). -/
theorem specialize_univChar_targetChar (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) (a : ℤ_[p]ˣ) :
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
        ((PadicExpLog.norm_padicExp_sub_one_le h3 hp2 (norm_p_mul_sq_lt hpK hLle)).trans
          (norm_p_mul_le_inv hpK hLle))
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
    have h20 := oneAddPow_weightPoint_mul_padicExp ψ hp2 hψ hζ hpK (-(k + 2 : ℤ)) (k : ℤ)
      (logQuot a)
    rw [weightPoint_natCast] at h20
    rw [← h20, he, ← PadicExpLog.padicExp_natCast_mul h3 hp2
      (norm_p_mul_sq_lt hpK hLle) (2 * k + 2)]
    congr 2
    push_cast
    ring
  rw [specialize_univChar (intHom ψ) (norm_intHom ψ hψ)
      (inv_lt_norm_weightPoint hp2 hζ hpK _) (norm_weightPoint_lt_one hp2 hζ hpK _)
      (targetChar p ω k) a,
    specialize_univChar (intHom ψ) (norm_intHom ψ hψ)
      (inv_lt_norm_classicalPoint hp2 hζ hpK k) (norm_classicalPoint_lt_one hp2 hζ hpK k) ω a,
    hchar, hbin, ha]
  simp only [mul_pow, inv_pow, mul_inv]
  field_simp [hx0, he0]
  ring

/-- **AG-ζ**: the target-shape constants at the target point are the classical datum's
constants (`certConj_apply_one_one`, `haloCharFunH_psi` at both points,
`specialize_univChar_targetChar`). -/
theorem targetConst_eq_classicalData_u (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) (i : ι) (t : Fin p)
    (a : ZMod (p ^ 1)) :
    haloCharFunH 1 ψ (weightPoint p (-(k + 2 : ℤ)) ζ) (targetChar p ω k)
          (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1)
        * (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1) ^ (k + 2)
      = (classicalData ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ hpK k).u i t a := by
  show haloCharFunH 1 ψ (weightPoint p (-(k + 2 : ℤ)) ζ) (targetChar p ω k)
        (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1)
      * (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1) ^ (k + 2)
    = haloCharFunH 1 ψ (classicalPoint p k ζ) ω (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1)
      * (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1)⁻¹ ^ k
  rw [certConj_apply_one_one,
    haloCharFunH_psi 1 ψ (weightPoint p (-(k + 2 : ℤ)) ζ) (targetChar p ω k) hp2 hψ
      (inv_lt_norm_weightPoint hp2 hζ hpK _) (norm_weightPoint_lt_one hp2 hζ hpK _)
      (norm_TH_one_weightPoint_sq_lt hp2 hζ hpK _) _,
    haloCharFunH_psi 1 ψ (classicalPoint p k ζ) ω hp2 hψ
      (inv_lt_norm_classicalPoint hp2 hζ hpK k) (norm_classicalPoint_lt_one hp2 hζ hpK k)
      (norm_TH_one_classicalPoint_sq_lt hp2 hζ hpK k) _]
  exact specialize_univChar_targetChar ψ ω hp2 hψ hζ hpK k _

/-! ### The target datum -/

/-- **The theta target of the classical datum at a classical point**: the halo point
`T_{(−k−2,ψ)}` with the nebentypus `ω·ω₀^{−2k−2}`, everything `15_StepThree.lean`'s Step III asks
of it assembled. -/
theorem targetData_classicalPoint (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hpK : ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹) (k : ℕ) :
    TargetData (classicalData ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ hpK k) (targetChar p ω k)
      (weightPoint p (-(k + 2 : ℤ)) ζ) where
  h0 := inv_lt_norm_weightPoint hp2 hζ hpK _
  h1 := norm_weightPoint_lt_one hp2 hζ hpK _
  hT := norm_TH_one_weightPoint_sq_lt hp2 hζ hpK _
  shape := by
    have hu : (fun (i : ι) (t : Fin p) (a : ZMod (p ^ 1)) =>
          haloCharFunH 1 ψ (weightPoint p (-(k + 2 : ℤ)) ζ) (targetChar p ω k)
              (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1)
            * (certConj θG 1 ψ U hU vRep hvΔ uu i t a 1 1) ^ (k + 2))
        = (classicalData ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ hpK k).u :=
      funext fun i => funext fun t => funext fun a =>
        targetConst_eq_classicalData_u ψ ω θG U hU vRep hvΔ uu hp2 hψ hζ hpK k i t a
    rw [← hu]
    exact isClassicalShape'_haloWeightH_weightPoint_neg ψ (targetChar p ω k) θG U hU vRep hvΔ uu
      hp2 hψ hζ k (inv_lt_norm_weightPoint hp2 hζ hpK _) (norm_weightPoint_lt_one hp2 hζ hpK _)
      (norm_TH_one_weightPoint_sq_lt hp2 hζ hpK _)

end LWX

end
