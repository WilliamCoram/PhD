/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.«07_PowSubOne»

/-!
# The halo weight at analyticity level `h` — SKELETON

[LWX, §2.1]: a character `χ` with `v(T_χ) > q/(pᵐ(p−1))` "is `m`-locally analytic: … for
`a ∈ ℤ_p^×` and `x ∈ 1 + pᵐℤ_p` (`q = p` odd), `χ(a·x) = χ(a)·χ(exp(pᵐ))^{(log x)/pᵐ}`".  With
`h = m − 1`, `T'_h := χ(exp(p^{h+1})) − 1 = (1+T₀)^{pʰ} − 1` and the level-`h` exponent
`s_h := log(1 + T'_h)/p^{h+1}`, the character on the `p^{-(h+1)}`-disc about a `ℤ_p`-unit `a` is
`x ↦ [a](T₀)·exp(s_h·log(x/a))`, a rigid-analytic function of `x` whose Taylor coefficients decay
like `(‖T'_h‖·√p)^m` (`norm_choose_haloExponentH_mul_pow_le`, the level-`h` form of
[LWX, Prop 3.14]'s estimate).  Packaged as an `AnalyticWeight` at the level `M1Kh h ψ` — the
`ψ`-image of the matrices with `p^{h+1} ∣ c` (the conjugates `t_{a'}⁻¹·δ·t_a` of the level `M₁` by
the disc maps `t_a(w) = a + pʰw`, `09_DiscModel.lean`) — on the level-`h` halo units
`ψ(ℤ_p^×)·(1 + p^{h+1}𝒪_K)`, of radius `haloRhoH p h T₀ = max(p^{−(h+1)}, ‖T'_h‖)·√p`.

The construction mirrors `06_HaloWeight.lean` (`h = 0`) step for step; the two are related by the
**binomial power identity** `oneAddPow_pow_mul` (`07_PowSubOne.lean`): on a `1`-unit
`u ∈ 1 + p^{h+1}ℤ_p` the universal character specialises to
`(1+T₀)^{log u/p} = (1+T'_h)^{log u/p^{h+1}} = exp(s_h·log u)` (`specialize_univChar_eq_padicExp`).

## Main declarations

* `LWX.Mh`, `LWX.M1Kh`, `LWX.haloUnitsH`, `LWX.repLift` — the level, the units, the residues.
* `LWX.TH`, `LWX.haloExponentH`, `LWX.specialize_univChar_eq_padicExp`, `LWX.haloCharFunH`,
  `LWX.haloCharFunH_psi`, `LWX.haloCharH`.
* `LWX.haloRhoH`, `LWX.levelBounds_M1Kh`, `LWX.haloColH`, `LWX.norm_coeff_haloColH_le`,
  `LWX.evalAt_haloColH`, **`LWX.haloWeightH`**, `LWX.evalAt_autFactor_haloWeightH`.
-/

open Filter Topology TateFredholm QMF

open scoped Nat

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

section Level

variable (p) in
/-- **The level-`h` monoid** `M_h`: integral matrices with `p^{h+1} ∣ c`, `d` a unit and nonzero
determinant (`M_0 = M₁`, [LWX, (2.3.3)]).  The disc conjugates `t_{a'}⁻¹·δ·t_a` of `δ ∈ M₁` lie in
`M_h` (`09_DiscModel.lean`). -/
def Mh (h : ℕ) : Submonoid (Matrix (Fin 2) (Fin 2) ℚ_[p]) where
  carrier :=
    {g | (∀ i j, ‖g i j‖ ≤ 1) ∧ ‖g 1 0‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) ∧ ‖g 1 1‖ = 1 ∧ g.det ≠ 0}
  mul_mem' := by
    rintro g k ⟨hg1, hg2, hg3, hg4⟩ ⟨hk1, hk2, hk3, hk4⟩
    have hpinv1 : ((p : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)
    have hpow1 : ((p : ℝ))⁻¹ ^ (h + 1) ≤ 1 := pow_le_one₀ (by positivity) hpinv1
    have hpowlt : ((p : ℝ))⁻¹ ^ (h + 1) < 1 := by
      refine pow_lt_one₀ (by positivity) ?_ (by omega)
      exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)
    have hmul : ∀ {x y : ℚ_[p]} {cx cy : ℝ}, ‖x‖ ≤ cx → ‖y‖ ≤ cy → 0 ≤ cy →
        ‖x * y‖ ≤ cx * cy := fun hx hy hcy =>
      (norm_mul_le _ _).trans (mul_le_mul hx hy (norm_nonneg _) ((norm_nonneg _).trans hx))
    refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
    · rw [Matrix.mul_apply, Fin.sum_univ_two]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · simpa using hmul (hg1 i 0) (hk1 0 j) zero_le_one
      · simpa using hmul (hg1 i 1) (hk1 1 j) zero_le_one
    · rw [Matrix.mul_apply, Fin.sum_univ_two]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · calc ‖g 1 0 * k 0 0‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) * 1 := hmul hg2 (hk1 0 0) zero_le_one
          _ = (p : ℝ)⁻¹ ^ (h + 1) := mul_one _
      · calc ‖g 1 1 * k 1 0‖ ≤ 1 * (p : ℝ)⁻¹ ^ (h + 1) :=
            hmul (hg1 1 1) hk2 (by positivity)
          _ = (p : ℝ)⁻¹ ^ (h + 1) := one_mul _
    · rw [Matrix.mul_apply, Fin.sum_univ_two]
      have hsmall : ‖g 1 0 * k 0 1‖ < 1 := by
        calc ‖g 1 0 * k 0 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) * 1 := hmul hg2 (hk1 0 1) zero_le_one
          _ = (p : ℝ)⁻¹ ^ (h + 1) := mul_one _
          _ < 1 := hpowlt
      have hbig : ‖g 1 1 * k 1 1‖ = 1 := by rw [norm_mul, hg3, hk3, mul_one]
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
        (by rw [hbig]; exact hsmall.ne), hbig, max_eq_right hsmall.le]
    · rw [Matrix.det_mul]
      exact mul_ne_zero hg4 hk4
  one_mem' := by
    refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
    · fin_cases i <;> fin_cases j <;> simp
    · simp
    · simp
    · simp

theorem mem_Mh_iff {h : ℕ} {g : Matrix (Fin 2) (Fin 2) ℚ_[p]} :
    g ∈ Mh p h ↔
      (∀ i j, ‖g i j‖ ≤ 1) ∧ ‖g 1 0‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) ∧ ‖g 1 1‖ = 1 ∧ g.det ≠ 0 :=
  Iff.rfl

/-- `M_h ⊆ M₁`. -/
theorem Mh_le_M1 (h : ℕ) : Mh p h ≤ M1 p := by
  rintro g ⟨hg1, hg2, hg3, hg4⟩
  refine ⟨hg1, ?_, hg3, hg4⟩
  refine hg2.trans ?_
  calc (p : ℝ)⁻¹ ^ (h + 1) ≤ (p : ℝ)⁻¹ ^ 1 :=
      pow_le_pow_of_le_one (by positivity)
        (inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)) (by omega)
    _ = (p : ℝ)⁻¹ := pow_one _

/-- `M_0 = M₁`. -/
theorem Mh_zero : Mh p 0 = M1 p := by
  ext g
  show ((∀ i j, ‖g i j‖ ≤ 1) ∧ ‖g 1 0‖ ≤ (p : ℝ)⁻¹ ^ (0 + 1) ∧ ‖g 1 1‖ = 1 ∧ g.det ≠ 0) ↔ _
  rw [zero_add, pow_one]
  rfl

variable (h : ℕ) (ψ : ℚ_[p] →+* K)

/-- **The level at height `h`**: the image of `M_h` in the `K`-matrices. -/
def M1Kh : Submonoid (Matrix (Fin 2) (Fin 2) K) :=
  (Mh p h).map (RingHom.mapMatrix ψ).toMonoidHom

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem mem_M1Kh_iff {g : Matrix (Fin 2) (Fin 2) K} :
    g ∈ M1Kh h ψ ↔ ∃ δ ∈ Mh p h, (RingHom.mapMatrix ψ) δ = g :=
  Submonoid.mem_map

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem M1Kh_le_M1K : M1Kh h ψ ≤ M1K ψ := by
  rintro g ⟨δ, hδ, rfl⟩
  exact ⟨δ, Mh_le_M1 h hδ, rfl⟩

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem norm_apply_le_one_of_mem_M1Kh (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ M1Kh h ψ) (i j : Fin 2) : ‖g i j‖ ≤ 1 := by
  obtain ⟨δ, hδ, rfl⟩ := hg
  rw [mapMatrix_toMonoidHom_apply, hψ]
  exact hδ.1 i j

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem norm_apply_one_zero_le_of_mem_M1Kh (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    {g : Matrix (Fin 2) (Fin 2) K} (hg : g ∈ M1Kh h ψ) : ‖g 1 0‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) := by
  obtain ⟨δ, hδ, rfl⟩ := hg
  rw [mapMatrix_toMonoidHom_apply, hψ]
  exact hδ.2.1

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem norm_apply_one_one_of_mem_M1Kh (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ M1Kh h ψ) : ‖g 1 1‖ = 1 := by
  obtain ⟨δ, hδ, rfl⟩ := hg
  rw [mapMatrix_toMonoidHom_apply, hψ]
  exact hδ.2.2.1

end Level

section Units

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `(p⁻¹)^{h+1} ≤ p⁻¹`. -/
theorem pow_le_inv_p (h : ℕ) : (p : ℝ)⁻¹ ^ (h + 1) ≤ (p : ℝ)⁻¹ := by
  calc (p : ℝ)⁻¹ ^ (h + 1) ≤ (p : ℝ)⁻¹ ^ 1 :=
      pow_le_pow_of_le_one (by positivity)
        (inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)) (by omega)
    _ = (p : ℝ)⁻¹ := pow_one _

variable (h : ℕ) (ψ : ℚ_[p] →+* K)

/-- **The level-`h` halo units** `ψ(ℤ_p^×)·(1 + p^{h+1}𝒪_K)`: units of `K` within `p^{−(h+1)}`
of a `ℤ_p`-unit — the domain of the level-`h` character, containing every value `cz + d`
(`‖c‖ ≤ p^{−(h+1)}`, `d ∈ ψ(ℤ_p^×)`, `‖z‖ ≤ 1`) of the level `M1Kh`. -/
def haloUnitsH : Subgroup Kˣ where
  carrier := {x | ∃ a : ℤ_[p]ˣ, ‖ψ ((a : ℤ_[p]) : ℚ_[p])‖ = 1 ∧
    ‖(x : K) - ψ ((a : ℤ_[p]) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ ^ (h + 1)}
  one_mem' := ⟨1, by simp, by simp⟩
  mul_mem' := by
    rintro x y ⟨a, ha1, ha⟩ ⟨b, hb1, hb⟩
    have hx1 : ‖(x : K)‖ = 1 := norm_eq_one_of_norm_sub_le ha1 (ha.trans (pow_le_inv_p h))
    refine ⟨a * b, ?_, ?_⟩
    · rw [Units.val_mul, PadicInt.coe_mul, map_mul, norm_mul, ha1, hb1, one_mul]
    · rw [Units.val_mul x y, Units.val_mul a b, PadicInt.coe_mul, map_mul]
      calc ‖(x : K) * y - ψ ((a : ℤ_[p]) : ℚ_[p]) * ψ ((b : ℤ_[p]) : ℚ_[p])‖
          = ‖(x : K) * ((y : K) - ψ ((b : ℤ_[p]) : ℚ_[p]))
              + ((x : K) - ψ ((a : ℤ_[p]) : ℚ_[p])) * ψ ((b : ℤ_[p]) : ℚ_[p])‖ := by
            congr 1
            ring
        _ ≤ max ‖(x : K) * ((y : K) - ψ ((b : ℤ_[p]) : ℚ_[p]))‖
              ‖((x : K) - ψ ((a : ℤ_[p]) : ℚ_[p])) * ψ ((b : ℤ_[p]) : ℚ_[p])‖ :=
            IsUltrametricDist.norm_add_le_max _ _
        _ ≤ (p : ℝ)⁻¹ ^ (h + 1) := max_le (by rw [norm_mul, hx1, one_mul]; exact hb)
            (by rw [norm_mul, hb1, mul_one]; exact ha)
  inv_mem' := by
    rintro x ⟨a, ha1, ha⟩
    have hx1 : ‖(x : K)‖ = 1 := norm_eq_one_of_norm_sub_le ha1 (ha.trans (pow_le_inv_p h))
    have hab : ψ ((a : ℤ_[p]) : ℚ_[p]) * ψ (((a⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = 1 := by
      rw [← map_mul, ← PadicInt.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        PadicInt.coe_one, map_one]
    have hinv1 : ‖ψ (((a⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])‖ = 1 := by
      have hn := congrArg norm hab
      rwa [norm_mul, ha1, one_mul, norm_one] at hn
    refine ⟨a⁻¹, hinv1, ?_⟩
    have hxx : ((x⁻¹ : Kˣ) : K) * (x : K) = 1 := Units.inv_mul x
    have hkey : ((x⁻¹ : Kˣ) : K) - ψ (((a⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])
        = ((x⁻¹ : Kˣ) : K) * (ψ ((a : ℤ_[p]) : ℚ_[p]) - x)
          * ψ (((a⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) := by
      linear_combination (-((x⁻¹ : Kˣ) : K)) * hab + ψ (((a⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) * hxx
    rw [hkey, norm_mul, norm_mul, hinv1, mul_one, Units.val_inv_eq_inv_val, norm_inv, hx1,
      inv_one, one_mul, norm_sub_rev]
    exact ha

omit [CompleteSpace K] [CharZero K] in
theorem mem_haloUnitsH_iff {x : Kˣ} :
    x ∈ haloUnitsH h ψ ↔ ∃ a : ℤ_[p]ˣ, ‖ψ ((a : ℤ_[p]) : ℚ_[p])‖ = 1 ∧
      ‖(x : K) - ψ ((a : ℤ_[p]) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) :=
  Iff.rfl

omit [CompleteSpace K] [CharZero K] in
/-- The level-`h` halo units lie in the halo units. -/
theorem haloUnitsH_le_haloUnits : haloUnitsH h ψ ≤ haloUnits ψ := by
  rintro x ⟨a, ha1, ha⟩
  exact ⟨a, ha1, ha.trans (pow_le_inv_p h)⟩

/-- The natural representative of a unit residue class modulo `p^{h+1}` is a `p`-adic unit. -/
theorem isUnit_natCast_val_pow (r : (ZMod (p ^ (h + 1)))ˣ) :
    IsUnit ((((r : ZMod (p ^ (h + 1))).val : ℕ)) : ℤ_[p]) := by
  have hcop : Nat.Coprime ((r : ZMod (p ^ (h + 1))).val) (p ^ (h + 1)) := by
    rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
    exact r.isUnit
  by_contra hcon
  have h0 : PadicInt.toZMod ((((r : ZMod (p ^ (h + 1))).val : ℕ)) : ℤ_[p]) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
    exact mem_nonunits_iff.mpr hcon
  rw [map_natCast] at h0
  replace h0 := (ZMod.natCast_eq_zero_iff _ p).mp h0
  have hdvd : p ∣ Nat.gcd ((r : ZMod (p ^ (h + 1))).val) (p ^ (h + 1)) :=
    Nat.dvd_gcd h0 (dvd_pow_self p (by omega))
  rw [hcop] at hdvd
  have := hp.out.one_lt
  have hp1 : p = 1 := Nat.eq_one_of_dvd_one hdvd
  omega

/-- **The representatives of the residue classes modulo `p^{h+1}`**: the natural lifts. -/
def repLift (r : (ZMod (p ^ (h + 1)))ˣ) : ℤ_[p]ˣ := (isUnit_natCast_val_pow h r).unit

theorem coe_repLift (r : (ZMod (p ^ (h + 1)))ˣ) :
    (repLift h r : ℤ_[p]) = (((r : ZMod (p ^ (h + 1))).val : ℕ) : ℤ_[p]) :=
  (isUnit_natCast_val_pow h r).unit_spec

/-- The lift reduces to the residue class it lifts. -/
theorem toZModPow_repLift (r : (ZMod (p ^ (h + 1)))ˣ) :
    PadicInt.toZModPow (h + 1) (repLift h r : ℤ_[p]) = r := by
  rw [coe_repLift, map_natCast, ZMod.natCast_zmod_val]

theorem repLift_injective : Function.Injective (repLift (p := p) h) := fun r r' hrr => by
  have hz := congrArg (fun u : ℤ_[p]ˣ => PadicInt.toZModPow (h + 1) (u : ℤ_[p])) hrr
  rw [toZModPow_repLift, toZModPow_repLift] at hz
  exact Units.ext hz

/-- Every unit is within `p^{−(h+1)}` of the lift of its residue class (`ker_toZModPow`). -/
theorem norm_sub_repLift_le (a : ℤ_[p]ˣ) :
    ‖(a : ℤ_[p]) - (repLift h (Units.map (PadicInt.toZModPow (p := p) (h + 1)).toMonoidHom a)
      : ℤ_[p])‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) := by
  have hker : ((a : ℤ_[p]) - (repLift h
      (Units.map (PadicInt.toZModPow (p := p) (h + 1)).toMonoidHom a) : ℤ_[p]))
      ∈ Ideal.span {(p : ℤ_[p]) ^ (h + 1)} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, toZModPow_repLift, sub_eq_zero]
    rfl
  have hnorm := (PadicInt.norm_le_pow_iff_mem_span_pow _ (h + 1)).mpr hker
  rw [show ((p : ℝ) ^ (-((h + 1 : ℕ) : ℤ))) = (p : ℝ)⁻¹ ^ (h + 1) from by
    rw [zpow_neg, zpow_natCast, inv_pow]] at hnorm
  exact hnorm

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem norm_intHom_repLift (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (r : (ZMod (p ^ (h + 1)))ˣ) :
    ‖intHom ψ (repLift h r : ℤ_[p])‖ = 1 := by
  rw [norm_intHom ψ hψ]
  exact PadicInt.norm_units _

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Lifts of distinct residue classes are at distance `> p^{−(h+1)}` in `K`. -/
theorem repLift_eq_of_norm_sub_le (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {r r' : (ZMod (p ^ (h + 1)))ˣ}
    (hrr : ‖intHom ψ (repLift h r : ℤ_[p]) - intHom ψ (repLift h r' : ℤ_[p])‖
      ≤ (p : ℝ)⁻¹ ^ (h + 1)) : r = r' := by
  rw [← map_sub, norm_intHom ψ hψ] at hrr
  have hspan : ((repLift h r : ℤ_[p]) - (repLift h r' : ℤ_[p]))
      ∈ Ideal.span {(p : ℤ_[p]) ^ (h + 1)} := by
    refine (PadicInt.norm_le_pow_iff_mem_span_pow _ (h + 1)).mp ?_
    rw [show ((p : ℝ) ^ (-((h + 1 : ℕ) : ℤ))) = (p : ℝ)⁻¹ ^ (h + 1) from by
      rw [zpow_neg, zpow_natCast, inv_pow]]
    exact hrr
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, toZModPow_repLift,
    toZModPow_repLift, sub_eq_zero] at hspan
  exact Units.ext hspan

omit [CompleteSpace K] [CharZero K] in
/-- A level-`h` halo unit is within `p^{−(h+1)}` of the lift of a unique residue class. -/
theorem exists_unique_repLift_of_mem_haloUnitsH (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {x : Kˣ}
    (hx : x ∈ haloUnitsH h ψ) :
    ∃! r : (ZMod (p ^ (h + 1)))ˣ,
      ‖(x : K) - intHom ψ (repLift h r : ℤ_[p])‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) := by
  obtain ⟨a, -, ha⟩ := hx
  have hex : ‖(x : K) - intHom ψ
      (repLift h (Units.map (PadicInt.toZModPow (p := p) (h + 1)).toMonoidHom a) : ℤ_[p])‖
      ≤ (p : ℝ)⁻¹ ^ (h + 1) := by
    calc ‖(x : K) - intHom ψ
          (repLift h (Units.map (PadicInt.toZModPow (p := p) (h + 1)).toMonoidHom a) : ℤ_[p])‖
        = ‖((x : K) - intHom ψ (a : ℤ_[p])) + intHom ψ ((a : ℤ_[p])
            - (repLift h (Units.map (PadicInt.toZModPow (p := p) (h + 1)).toMonoidHom a)
              : ℤ_[p]))‖ := by
          rw [map_sub, sub_add_sub_cancel]
      _ ≤ max ‖(x : K) - intHom ψ (a : ℤ_[p])‖ ‖intHom ψ ((a : ℤ_[p])
            - (repLift h (Units.map (PadicInt.toZModPow (p := p) (h + 1)).toMonoidHom a)
              : ℤ_[p]))‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ (p : ℝ)⁻¹ ^ (h + 1) :=
          max_le ha (by rw [norm_intHom ψ hψ]; exact norm_sub_repLift_le h a)
  refine ⟨_, hex, fun r hr => repLift_eq_of_norm_sub_le h ψ hψ ?_⟩
  calc ‖intHom ψ (repLift h r : ℤ_[p]) - intHom ψ
        (repLift h (Units.map (PadicInt.toZModPow (p := p) (h + 1)).toMonoidHom a) : ℤ_[p])‖
      = ‖((x : K) - intHom ψ (repLift h
            (Units.map (PadicInt.toZModPow (p := p) (h + 1)).toMonoidHom a) : ℤ_[p]))
          - ((x : K) - intHom ψ (repLift h r : ℤ_[p]))‖ := by rw [sub_sub_sub_cancel_left]
    _ ≤ max ‖(x : K) - intHom ψ (repLift h
            (Units.map (PadicInt.toZModPow (p := p) (h + 1)).toMonoidHom a) : ℤ_[p])‖
          ‖(x : K) - intHom ψ (repLift h r : ℤ_[p])‖ := norm_sub_le_max_norm _ _
    _ ≤ (p : ℝ)⁻¹ ^ (h + 1) := max_le hex hr

end Units

section Character

variable (p) in
/-- `T'_h = (1 + T₀)^{pʰ} − 1`: the halo coordinate of `χ(exp(p^{h+1}))`. -/
def TH (h : ℕ) (T₀ : K) : K := (1 + T₀) ^ p ^ h - 1

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
@[simp] theorem TH_zero (T₀ : K) : TH p 0 T₀ = T₀ := by
  rw [TH, pow_zero, pow_one, add_sub_cancel_left]

variable (p) in
/-- **The level-`h` halo exponent** `s_h = log(1 + T'_h)/p^{h+1}`: `exp(s_h·log x)` is
`(1+T'_h)^{log x/p^{h+1}}`. -/
def haloExponentH (h : ℕ) (T₀ : K) : K :=
  PadicExpLog.padicLog (1 + TH p h T₀) / ((p : ℕ) : K) ^ (h + 1)

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem haloExponentH_zero (T₀ : K) : haloExponentH p 0 T₀ = haloExponent (p := p) T₀ := by
  rw [haloExponentH, TH_zero, pow_one, haloExponent]

variable (h : ℕ) (ψ : ℚ_[p] →+* K) (T₀ : K) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)

/-- `‖s_h‖ = p^{h+1}·‖T'_h‖` on the disc `‖T'_h‖² < p⁻¹` (`norm_padicLog_eq`). -/
theorem norm_haloExponentH (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) :
    ‖haloExponentH p h T₀‖ = (p : ℝ) ^ (h + 1) * ‖TH p h T₀‖ := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by
    rw [norm_natCast_p ψ hψ]
    exact inv_lt_one_p
  have hu : ‖(1 + TH p h T₀) - 1‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
    rw [add_sub_cancel_left, norm_natCast_p ψ hψ]
    exact hT
  rw [haloExponentH, norm_div, PadicExpLog.norm_padicLog_eq h3 hp2 hu, add_sub_cancel_left,
    norm_pow, norm_natCast_p ψ hψ, inv_pow, div_inv_eq_mul, mul_comm]

/-- `‖s_h·log x‖ ≤ ‖T'_h‖` for `‖x − 1‖ ≤ p^{−(h+1)}`. -/
theorem norm_haloExponentH_mul_padicLog_le (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) {x : K} (hx : ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1)) :
    ‖haloExponentH p h T₀ * PadicExpLog.padicLog x‖ ≤ ‖TH p h T₀‖ := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by
    rw [norm_natCast_p ψ hψ]
    exact inv_lt_one_p
  have hp0 : ((p : ℝ)) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hxd : ‖x - 1‖ ^ 2 < ‖((p : ℕ) : K)‖ :=
    sq_norm_lt_norm_p_of_le ψ hψ (hx.trans (pow_le_inv_p h))
  rw [norm_mul, norm_haloExponentH h ψ T₀ hp2 hψ hT, PadicExpLog.norm_padicLog_eq h3 hp2 hxd]
  calc (p : ℝ) ^ (h + 1) * ‖TH p h T₀‖ * ‖x - 1‖
      ≤ (p : ℝ) ^ (h + 1) * ‖TH p h T₀‖ * (p : ℝ)⁻¹ ^ (h + 1) :=
        mul_le_mul_of_nonneg_left hx (by positivity)
    _ = ‖TH p h T₀‖ := by
        rw [mul_right_comm, ← mul_pow, mul_inv_cancel₀ hp0, one_pow, one_mul]

/-- `s_h·log x` lies in the convergence disc of `exp`. -/
theorem sq_norm_haloExponentH_mul_padicLog_lt (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) {x : K} (hx : ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1)) :
    ‖haloExponentH p h T₀ * PadicExpLog.padicLog x‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
  rw [norm_natCast_p ψ hψ]
  exact lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _)
    (norm_haloExponentH_mul_padicLog_le h ψ T₀ hp2 hψ hT hx) 2) hT

theorem norm_padicExp_haloExponentH_mul_padicLog (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) {x : K} (hx : ‖x - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1)) :
    ‖PadicExpLog.padicExp (haloExponentH p h T₀ * PadicExpLog.padicLog x)‖ = 1 := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by
    rw [norm_natCast_p ψ hψ]
    exact inv_lt_one_p
  refine PadicExpLog.norm_eq_one_of_norm_sub_one_lt_one ?_
  refine (PadicExpLog.norm_padicExp_sub_one_le h3 hp2
    (sq_norm_haloExponentH_mul_padicLog_lt h ψ T₀ hp2 hψ hT hx)).trans_lt ?_
  exact (norm_haloExponentH_mul_padicLog_le h ψ T₀ hp2 hψ hT hx).trans_lt
    (norm_lt_one_of_sq_lt hT)

/-- A `1`-unit modulo `p` has trivial residue. -/
theorem unitsMap_toZMod_eq_one_of_norm_sub_one_le {u : ℤ_[p]ˣ}
    (hu : ‖(u : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹) :
    Units.map (PadicInt.toZMod (p := p)).toMonoidHom u = 1 := by
  rw [norm_le_inv_iff_toZMod_eq_zero, map_sub, map_one, sub_eq_zero] at hu
  exact Units.ext hu

/-- The Teichmüller representative of a `1`-unit is `1`. -/
theorem teichmuller_eq_one_of_norm_sub_one_le {u : ℤ_[p]ˣ}
    (hu : ‖(u : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹) : teichmuller u = 1 := by
  rw [← teichRes_toZMod, unitsMap_toZMod_eq_one_of_norm_sub_one_le hu, teichRes_one]

/-- On a `1`-unit, `ℓ⟨u⟩ = log u/p`. -/
theorem coe_logQuot_of_norm_sub_one_le {u : ℤ_[p]ˣ} (hu : ‖(u : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹) :
    (logQuot u : ℚ_[p]) = PadicExpLog.padicLog ((u : ℤ_[p]) : ℚ_[p]) / (p : ℚ_[p]) := by
  show qlog (oneUnitPart u) / (p : ℚ_[p]) = _
  rw [oneUnitPart, teichmuller_eq_one_of_norm_sub_one_le hu, inv_one, mul_one, qlog]

/-- On a `1`-unit modulo `p^{h+1}`, `ℓ⟨u⟩ = pʰ·v` with `v = log u/p^{h+1} ∈ ℤ_p`
(`norm_padicLog_eq`). -/
theorem exists_pow_mul_eq_logQuot (hp2 : p ≠ 2) {u : ℤ_[p]ˣ}
    (hu : ‖(u : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1)) :
    ∃ v : ℤ_[p], logQuot u = (p : ℤ_[p]) ^ h * v ∧
      (v : ℚ_[p]) = PadicExpLog.padicLog ((u : ℤ_[p]) : ℚ_[p]) / (p : ℚ_[p]) ^ (h + 1) := by
  have hp3 : ‖((p : ℕ) : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p]
    exact inv_lt_one_p
  have hpne : ((p : ℚ_[p])) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hsub : ‖((u : ℤ_[p]) : ℚ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) := by
    rw [show ((u : ℤ_[p]) : ℚ_[p]) - 1 = (((u : ℤ_[p]) - 1 : ℤ_[p]) : ℚ_[p]) from by
      push_cast; ring]
    exact hu
  have hpinv0 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
  have hlog : ‖PadicExpLog.padicLog ((u : ℤ_[p]) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) := by
    rw [PadicExpLog.norm_padicLog_eq hp3 hp2 (by
      rw [Padic.norm_p]
      calc ‖((u : ℤ_[p]) : ℚ_[p]) - 1‖ ^ 2 ≤ ((p : ℝ)⁻¹ ^ (h + 1)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hsub 2
        _ = (p : ℝ)⁻¹ ^ (2 * (h + 1)) := by rw [← pow_mul, Nat.mul_comm]
        _ < (p : ℝ)⁻¹ ^ 1 := pow_lt_pow_right_of_lt_one₀ hpinv0 inv_lt_one_p (by omega)
        _ = (p : ℝ)⁻¹ := pow_one _)]
    exact hsub
  refine ⟨⟨PadicExpLog.padicLog ((u : ℤ_[p]) : ℚ_[p]) / (p : ℚ_[p]) ^ (h + 1), ?_⟩, ?_, rfl⟩
  · rw [norm_div, norm_pow, Padic.norm_p, div_le_one (by positivity)]
    exact hlog
  · refine Subtype.ext ?_
    show (logQuot u : ℚ_[p])
      = ((p : ℚ_[p])) ^ h * (PadicExpLog.padicLog ((u : ℤ_[p]) : ℚ_[p]) / (p : ℚ_[p]) ^ (h + 1))
    rw [coe_logQuot_of_norm_sub_one_le (hu.trans (pow_le_inv_p h))]
    field_simp
    ring

/-- **The `m`-analytic extension formula** ([LWX, §2.1]: "`χ(a·x) = χ(a)·χ(exp(pᵐ))^{(log x)/pᵐ}`",
the `a = 1` case): on a `1`-unit `u` modulo `p^{h+1}` the specialised universal character is
`exp(s_h·log ψ(u))` — `specialize_univChar`, the residue and Teichmüller parts are trivial,
`ℓ⟨u⟩ = pʰ·v`, the binomial power identity `oneAddPow_pow_mul`, and the binomial theorem
`hasSum_choose_mul_pow` at `T'_h`. -/
theorem specialize_univChar_eq_padicExp (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) {u : ℤ_[p]ˣ}
    (hu : ‖(u : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1)) :
    HaloInt.specialize (intHom ψ) T₀ (univChar ω u)
      = PadicExpLog.padicExp (haloExponentH p h T₀
          * PadicExpLog.padicLog (intHom ψ (u : ℤ_[p]))) := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by
    rw [norm_natCast_p ψ hψ]
    exact inv_lt_one_p
  have hTK : ‖TH p h T₀‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
    rw [norm_natCast_p ψ hψ]
    exact hT
  obtain ⟨v, hv1, hv2⟩ := exists_pow_mul_eq_logQuot h hp2 hu
  have hsub : ‖((u : ℤ_[p]) : ℚ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ := by
    rw [show ((u : ℤ_[p]) : ℚ_[p]) - 1 = (((u : ℤ_[p]) - 1 : ℤ_[p]) : ℚ_[p]) from by
      push_cast; ring]
    exact hu.trans (pow_le_inv_p h)
  have hvval : intHom ψ v
      = PadicExpLog.padicLog (intHom ψ (u : ℤ_[p])) / ((p : ℕ) : K) ^ (h + 1) := by
    show ψ ((v : ℚ_[p])) = _
    rw [hv2, map_div₀, map_pow, map_natCast, map_padicLog ψ hp2 hψ hsub]
    rfl
  have hsum := PadicExpLog.hasSum_choose_mul_pow h3 hp2 (c := ‖TH p h T₀‖) hTK
    (e := intHom ψ v) (x := TH p h T₀) le_rfl
    (by
      refine mul_le_of_le_one_left (norm_nonneg _) ?_
      rw [norm_intHom ψ hψ]
      exact PadicInt.norm_le_one _)
  rw [specialize_univChar (intHom ψ) (norm_intHom ψ hψ) h0 h1 ω u,
    unitsMap_toZMod_eq_one_of_norm_sub_one_le (hu.trans (pow_le_inv_p h)), map_one,
    Units.val_one, map_one, one_mul, hv1, oneAddPow_pow_mul ψ hψ h1 h v]
  show oneAddPow (TH p h T₀) (intHom ψ v) = _
  rw [oneAddPow, hsum.tsum_eq, hvval, haloExponentH]
  congr 1
  ring

/-- **The level-`h` halo character function** on `K`:
`x ↦ [r](T₀)·exp(s_h·log(x/ψ(r)))`, `r` the residue class with `‖x − ψ(r)‖ ≤ p^{−(h+1)}`
(a finite sum with at most one nonzero term; `0` off the level-`h` halo units). -/
def haloCharFunH (x : K) : K :=
  ∑ r : (ZMod (p ^ (h + 1)))ˣ,
    if ‖x - intHom ψ (repLift h r : ℤ_[p])‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) then
      HaloInt.specialize (intHom ψ) T₀ (univChar ω (repLift h r))
        * PadicExpLog.padicExp (haloExponentH p h T₀
            * PadicExpLog.padicLog (x * (intHom ψ (repLift h r : ℤ_[p]))⁻¹))
    else 0

omit [CompleteSpace K] [CharZero K] in
theorem haloCharFunH_of_norm_sub_le (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {x : K}
    {r : (ZMod (p ^ (h + 1)))ˣ}
    (hx : ‖x - intHom ψ (repLift h r : ℤ_[p])‖ ≤ (p : ℝ)⁻¹ ^ (h + 1)) :
    haloCharFunH h ψ T₀ ω x
      = HaloInt.specialize (intHom ψ) T₀ (univChar ω (repLift h r))
        * PadicExpLog.padicExp (haloExponentH p h T₀
            * PadicExpLog.padicLog (x * (intHom ψ (repLift h r : ℤ_[p]))⁻¹)) := by
  unfold haloCharFunH
  rw [Finset.sum_eq_single r ?_ (fun h' => absurd (Finset.mem_univ r) h'), if_pos hx]
  intro r' _ hr'
  refine if_neg fun h' => hr' (repLift_eq_of_norm_sub_le h ψ hψ ?_)
  calc ‖intHom ψ (repLift h r' : ℤ_[p]) - intHom ψ (repLift h r : ℤ_[p])‖
      = ‖(x - intHom ψ (repLift h r : ℤ_[p])) - (x - intHom ψ (repLift h r' : ℤ_[p]))‖ := by
        rw [sub_sub_sub_cancel_left]
    _ ≤ max ‖x - intHom ψ (repLift h r : ℤ_[p])‖ ‖x - intHom ψ (repLift h r' : ℤ_[p])‖ :=
        norm_sub_le_max_norm _ _
    _ ≤ (p : ℝ)⁻¹ ^ (h + 1) := max_le hx h'

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `‖x·t⁻¹ − 1‖ ≤ ε` whenever `‖x − t‖ ≤ ε` and `t` is a unit — the level-`h` form of
`norm_mul_inv_sub_one_le`. -/
theorem norm_mul_inv_sub_one_le' {x t : K} {ε : ℝ} (ht : ‖t‖ = 1) (hx : ‖x - t‖ ≤ ε) :
    ‖x * t⁻¹ - 1‖ ≤ ε := by
  have ht0 : t ≠ 0 := by
    intro hc
    rw [hc, norm_zero] at ht
    exact zero_ne_one ht
  rw [show x * t⁻¹ - 1 = (x - t) * t⁻¹ from by field_simp, norm_mul, norm_inv, ht, inv_one,
    mul_one]
  exact hx

/-- `repLift` of the identity residue is `1`. -/
theorem repLift_one : repLift (p := p) h 1 = 1 := by
  haveI : Fact (1 < p ^ (h + 1)) := ⟨Nat.one_lt_pow (by omega) hp.out.one_lt⟩
  refine Units.ext ?_
  rw [coe_repLift, Units.val_one, ZMod.val_one]
  norm_num

omit [CompleteSpace K] in
theorem haloCharFunH_one (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) :
    haloCharFunH h ψ T₀ ω 1 = 1 := by
  rw [haloCharFunH_of_norm_sub_le h ψ T₀ ω hψ (r := 1) (by
    rw [repLift_one]
    simp), repLift_one, univChar_one hp2,
    show HaloInt.specialize (intHom ψ) T₀ 1 = 1 from HaloInt.specialize_one _ _]
  simp

omit [CompleteSpace K] [CharZero K] in
/-- The `1`-units modulo `p⁻¹` are closed under multiplication. -/
theorem norm_mul_sub_one_le {u v : K} {ε : ℝ} (hε : ε ≤ (p : ℝ)⁻¹) (hu : ‖u - 1‖ ≤ ε)
    (hv : ‖v - 1‖ ≤ ε) : ‖u * v - 1‖ ≤ ε := by
  have hu1 : ‖u‖ = 1 := norm_eq_one_of_norm_sub_le norm_one (hu.trans hε)
  rw [show u * v - 1 = u * (v - 1) + (u - 1) from by ring]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ hu)
  rw [norm_mul, hu1, one_mul]
  exact hv

/-- The residue of a unit `w` congruent to `1` modulo `p^{h+1}` bounds `‖w − 1‖`. -/
theorem norm_sub_one_le_of_toZModPow_eq_one {w : ℤ_[p]ˣ}
    (hw : PadicInt.toZModPow (h + 1) (w : ℤ_[p]) = 1) :
    ‖(w : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) := by
  have hker : ((w : ℤ_[p]) - 1) ∈ Ideal.span {(p : ℤ_[p]) ^ (h + 1)} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_one, hw, sub_self]
  have hnorm := (PadicInt.norm_le_pow_iff_mem_span_pow _ (h + 1)).mpr hker
  rwa [show ((p : ℝ) ^ (-((h + 1 : ℕ) : ℤ))) = (p : ℝ)⁻¹ ^ (h + 1) from by
    rw [zpow_neg, zpow_natCast, inv_pow]] at hnorm

/-- **Multiplicativity** on the level-`h` halo units (`univChar_mul`, `padicLog_mul`,
`padicExp_add`). -/
theorem haloCharFunH_mul (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) {x y : Kˣ} (hx : x ∈ haloUnitsH h ψ)
    (hy : y ∈ haloUnitsH h ψ) :
    haloCharFunH h ψ T₀ ω ((x : K) * y) = haloCharFunH h ψ T₀ ω x * haloCharFunH h ψ T₀ ω y := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by
    rw [norm_natCast_p ψ hψ]
    exact inv_lt_one_p
  obtain ⟨r, hr, -⟩ := exists_unique_repLift_of_mem_haloUnitsH h ψ hψ hx
  obtain ⟨r', hr', -⟩ := exists_unique_repLift_of_mem_haloUnitsH h ψ hψ hy
  have hτ : ∀ t : (ZMod (p ^ (h + 1)))ˣ, ‖intHom ψ (repLift h t : ℤ_[p])‖ = 1 :=
    norm_intHom_repLift h ψ hψ
  have hx1 : ‖(x : K)‖ = 1 :=
    norm_eq_one_of_norm_sub_le (hτ r) (hr.trans (pow_le_inv_p h))
  -- the correction unit `w = lift r · lift r' · lift (r r')⁻¹`, congruent to `1`
  have hmapLift : ∀ t : (ZMod (p ^ (h + 1)))ˣ,
      Units.map (PadicInt.toZModPow (p := p) (h + 1)).toMonoidHom (repLift h t) = t :=
    fun t => Units.ext (toZModPow_repLift h t)
  have hwres : PadicInt.toZModPow (h + 1)
      ((repLift h r * repLift h r' * (repLift h (r * r'))⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
    have hmap : Units.map (PadicInt.toZModPow (p := p) (h + 1)).toMonoidHom
        (repLift h r * repLift h r' * (repLift h (r * r'))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_inv, hmapLift, hmapLift, hmapLift, mul_inv_cancel]
    exact congrArg Units.val hmap
  have hwnorm := norm_sub_one_le_of_toZModPow_eq_one h hwres
  have hwK : ‖intHom ψ ((repLift h r * repLift h r' * (repLift h (r * r'))⁻¹ : ℤ_[p]ˣ) : ℤ_[p])
      - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) := by
    rw [show (1 : K) = intHom ψ 1 from (map_one _).symm, ← map_sub, norm_intHom ψ hψ]
    exact hwnorm
  set W : ℤ_[p]ˣ := repLift h r * repLift h r' * (repLift h (r * r'))⁻¹ with hWdef
  have hcunit : ∀ t : (ZMod (p ^ (h + 1)))ˣ, intHom ψ (repLift h t : ℤ_[p]) ≠ 0 := by
    intro t hc
    have := hτ t
    rw [hc, norm_zero] at this
    exact zero_ne_one this
  have hWK : intHom ψ (W : ℤ_[p])
      = intHom ψ (repLift h r : ℤ_[p]) * intHom ψ (repLift h r' : ℤ_[p])
        * (intHom ψ (repLift h (r * r') : ℤ_[p]))⁻¹ := by
    rw [hWdef, Units.val_mul, Units.val_mul, map_mul, map_mul,
      map_units_inv (intHom ψ) (repLift h (r * r'))]
  -- the three `1`-units
  have hu1 : ‖(x : K) * (intHom ψ (repLift h r : ℤ_[p]))⁻¹ - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) :=
    norm_mul_inv_sub_one_le' (hτ r) hr
  have hu2 : ‖(y : K) * (intHom ψ (repLift h r' : ℤ_[p]))⁻¹ - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) :=
    norm_mul_inv_sub_one_le' (hτ r') hr'
  have hu3 : ‖intHom ψ (W : ℤ_[p]) - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) := hwK
  have hu12 : ‖(x : K) * (intHom ψ (repLift h r : ℤ_[p]))⁻¹
      * ((y : K) * (intHom ψ (repLift h r' : ℤ_[p]))⁻¹) - 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) :=
    norm_mul_sub_one_le (pow_le_inv_p h) hu1 hu2
  -- `xy` lies in the residue disc of `r·r'`
  have hxy : ‖((x : K) * y) - intHom ψ (repLift h (r * r') : ℤ_[p])‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) := by
    have hprod : (x : K) * y - intHom ψ (repLift h (r * r') : ℤ_[p])
        = (x : K) * ((y : K) - intHom ψ (repLift h r' : ℤ_[p]))
          + (((x : K) - intHom ψ (repLift h r : ℤ_[p]))
              * intHom ψ (repLift h r' : ℤ_[p])
            + intHom ψ (repLift h (r * r') : ℤ_[p])
                * (intHom ψ (W : ℤ_[p]) - 1)) := by
      rw [hWK]
      field_simp
      ring
    rw [hprod]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul, hx1, one_mul]
      exact hr'
    · refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
      · rw [norm_mul, hτ, mul_one]
        exact hr
      · rw [norm_mul, hτ, one_mul]
        exact hwK
  -- the character values multiply up to the correction `exp(s·log ψW)`
  have hA : HaloInt.specialize (intHom ψ) T₀ (univChar ω (repLift h r))
      * HaloInt.specialize (intHom ψ) T₀ (univChar ω (repLift h r'))
      = HaloInt.specialize (intHom ψ) T₀ (univChar ω (repLift h (r * r')))
        * PadicExpLog.padicExp (haloExponentH p h T₀
            * PadicExpLog.padicLog (intHom ψ (W : ℤ_[p]))) := by
    rw [← specialize_univChar_eq_padicExp h ψ T₀ ω hp2 hψ h0 h1 hT hwnorm,
      ← HaloInt.specialize_mul (intHom ψ) (norm_intHom ψ hψ) h0 h1,
      ← HaloInt.specialize_mul (intHom ψ) (norm_intHom ψ hψ) h0 h1, ← univChar_mul hp2,
      ← univChar_mul hp2]
    congr 2
    rw [hWdef, mul_comm (repLift h r * repLift h r') (repLift h (r * r'))⁻¹, ← mul_assoc,
      mul_inv_cancel, one_mul]
  have hexp : PadicExpLog.padicExp (haloExponentH p h T₀
        * PadicExpLog.padicLog (intHom ψ (W : ℤ_[p])))
      * (PadicExpLog.padicExp (haloExponentH p h T₀ * PadicExpLog.padicLog
            ((x : K) * (intHom ψ (repLift h r : ℤ_[p]))⁻¹))
        * PadicExpLog.padicExp (haloExponentH p h T₀ * PadicExpLog.padicLog
            ((y : K) * (intHom ψ (repLift h r' : ℤ_[p]))⁻¹)))
      = PadicExpLog.padicExp (haloExponentH p h T₀ * PadicExpLog.padicLog
          ((x : K) * (y : K) * (intHom ψ (repLift h (r * r') : ℤ_[p]))⁻¹)) := by
    rw [← PadicExpLog.padicExp_add h3 hp2
        (sq_norm_haloExponentH_mul_padicLog_lt h ψ T₀ hp2 hψ hT hu1)
        (sq_norm_haloExponentH_mul_padicLog_lt h ψ T₀ hp2 hψ hT hu2), ← mul_add,
      ← PadicExpLog.padicLog_mul h3 hp2
        (sq_norm_lt_norm_p_of_le ψ hψ (hu1.trans (pow_le_inv_p h)))
        (sq_norm_lt_norm_p_of_le ψ hψ (hu2.trans (pow_le_inv_p h))),
      ← PadicExpLog.padicExp_add h3 hp2
        (sq_norm_haloExponentH_mul_padicLog_lt h ψ T₀ hp2 hψ hT hu3)
        (sq_norm_haloExponentH_mul_padicLog_lt h ψ T₀ hp2 hψ hT hu12), ← mul_add,
      ← PadicExpLog.padicLog_mul h3 hp2
        (sq_norm_lt_norm_p_of_le ψ hψ (hu3.trans (pow_le_inv_p h)))
        (sq_norm_lt_norm_p_of_le ψ hψ (hu12.trans (pow_le_inv_p h)))]
    congr 2
    rw [hWK]
    field_simp
  rw [haloCharFunH_of_norm_sub_le h ψ T₀ ω hψ hxy, haloCharFunH_of_norm_sub_le h ψ T₀ ω hψ hr,
    haloCharFunH_of_norm_sub_le h ψ T₀ ω hψ hr',
    show HaloInt.specialize (intHom ψ) T₀ (univChar ω (repLift h r))
        * PadicExpLog.padicExp (haloExponentH p h T₀ * PadicExpLog.padicLog
            ((x : K) * (intHom ψ (repLift h r : ℤ_[p]))⁻¹))
      * (HaloInt.specialize (intHom ψ) T₀ (univChar ω (repLift h r'))
        * PadicExpLog.padicExp (haloExponentH p h T₀ * PadicExpLog.padicLog
            ((y : K) * (intHom ψ (repLift h r' : ℤ_[p]))⁻¹)))
      = (HaloInt.specialize (intHom ψ) T₀ (univChar ω (repLift h r))
          * HaloInt.specialize (intHom ψ) T₀ (univChar ω (repLift h r')))
        * (PadicExpLog.padicExp (haloExponentH p h T₀ * PadicExpLog.padicLog
              ((x : K) * (intHom ψ (repLift h r : ℤ_[p]))⁻¹))
          * PadicExpLog.padicExp (haloExponentH p h T₀ * PadicExpLog.padicLog
              ((y : K) * (intHom ψ (repLift h r' : ℤ_[p]))⁻¹))) from by ring, hA,
    mul_assoc _ (PadicExpLog.padicExp (haloExponentH p h T₀
      * PadicExpLog.padicLog (intHom ψ (W : ℤ_[p])))) _, hexp]

omit [CharZero K] in
/-- The specialised universal character takes unit values (it is a unit of the halo ring). -/
theorem norm_specialize_univChar (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ < 1) (a : ℤ_[p]ˣ) :
    ‖HaloInt.specialize (intHom ψ) T₀ (univChar ω a)‖ = 1 := by
  have hle : ∀ b : ℤ_[p]ˣ, ‖HaloInt.specialize (intHom ψ) T₀ (univChar ω b)‖ ≤ 1 := by
    intro b
    have hb := HaloInt.norm_specialize_le (intHom ψ) (norm_intHom ψ hψ) h0 h1 (k := 0)
      (f := univChar ω b) (by
        rw [Nat.cast_zero, neg_zero, zpow_zero]
        exact HaloInt.norm_le_one _)
    rwa [pow_zero] at hb
  have hprod : HaloInt.specialize (intHom ψ) T₀ (univChar ω a)
      * HaloInt.specialize (intHom ψ) T₀ (univChar ω a⁻¹) = 1 := by
    rw [← HaloInt.specialize_mul (intHom ψ) (norm_intHom ψ hψ) h0 h1, ← univChar_mul hp2,
      mul_inv_cancel, univChar_one hp2]
    exact HaloInt.specialize_one _ _
  have hn := congrArg norm hprod
  rw [norm_mul, norm_one] at hn
  refine le_antisymm (hle a) ?_
  nlinarith [hle a⁻¹, norm_nonneg (HaloInt.specialize (intHom ψ) T₀ (univChar ω a)),
    norm_nonneg (HaloInt.specialize (intHom ψ) T₀ (univChar ω a⁻¹))]

theorem norm_haloCharFunH (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) {x : Kˣ} (hx : x ∈ haloUnitsH h ψ) :
    ‖haloCharFunH h ψ T₀ ω x‖ = 1 := by
  obtain ⟨r, hr, -⟩ := exists_unique_repLift_of_mem_haloUnitsH h ψ hψ hx
  rw [haloCharFunH_of_norm_sub_le h ψ T₀ ω hψ hr, norm_mul,
    norm_specialize_univChar ψ T₀ ω hp2 hψ h0 h1, one_mul]
  refine norm_padicExp_haloExponentH_mul_padicLog h ψ T₀ hp2 hψ hT ?_
  exact norm_mul_inv_sub_one_le' (norm_intHom_repLift h ψ hψ r) hr

/-- **The character is the specialised universal character on `ψ(ℤ_p^×)`**:
`κ_{T₀,h}(ψ a) = [a](T₀)` (`a = repLift r · u` with `u` a `1`-unit modulo `p^{h+1}`,
`univChar_mul`, `specialize_univChar_eq_padicExp`). -/
theorem haloCharFunH_psi (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) :
    haloCharFunH h ψ T₀ ω (intHom ψ (a : ℤ_[p]))
      = HaloInt.specialize (intHom ψ) T₀ (univChar ω a) := by
  set r : (ZMod (p ^ (h + 1)))ˣ :=
    Units.map (PadicInt.toZModPow (p := p) (h + 1)).toMonoidHom a with hrdef
  have hr : ‖intHom ψ (a : ℤ_[p]) - intHom ψ (repLift h r : ℤ_[p])‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) := by
    rw [← map_sub, norm_intHom ψ hψ]
    exact norm_sub_repLift_le h a
  have hmapLift : Units.map (PadicInt.toZModPow (p := p) (h + 1)).toMonoidHom (repLift h r) = r :=
    Units.ext (toZModPow_repLift h r)
  set u : ℤ_[p]ˣ := a * (repLift h r)⁻¹ with hudef
  have hures : PadicInt.toZModPow (h + 1) ((u : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
    have hmap : Units.map (PadicInt.toZModPow (p := p) (h + 1)).toMonoidHom u = 1 := by
      rw [hudef, map_mul, map_inv, hmapLift, ← hrdef, mul_inv_cancel]
    exact congrArg Units.val hmap
  have hUK : intHom ψ ((u : ℤ_[p]ˣ) : ℤ_[p])
      = intHom ψ (a : ℤ_[p]) * (intHom ψ (repLift h r : ℤ_[p]))⁻¹ := by
    rw [hudef, Units.val_mul, map_mul, map_units_inv (intHom ψ) (repLift h r)]
  rw [haloCharFunH_of_norm_sub_le h ψ T₀ ω hψ hr, ← hUK,
    ← specialize_univChar_eq_padicExp h ψ T₀ ω hp2 hψ h0 h1 hT
      (norm_sub_one_le_of_toZModPow_eq_one h hures),
    ← HaloInt.specialize_mul (intHom ψ) (norm_intHom ψ hψ) h0 h1, ← univChar_mul hp2]
  congr 2
  rw [hudef, mul_comm (a : ℤ_[p]ˣ) (repLift h r)⁻¹, ← mul_assoc, mul_inv_cancel, one_mul]

/-- **The level-`h` halo weight's character** on the level-`h` halo units: `x ↦ x²·κ_{T₀,h}(x)`. -/
def haloCharH (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)
    (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) : haloUnitsH h ψ →* Kˣ where
  toFun x := Units.mk0 (((x : Kˣ) : K) ^ 2 * haloCharFunH h ψ T₀ ω ((x : Kˣ) : K))
    (mul_ne_zero (pow_ne_zero 2 (Units.ne_zero _)) fun hc => by
      have hn := norm_haloCharFunH h ψ T₀ ω hp2 hψ h0 h1 hT x.2
      rw [hc, norm_zero] at hn
      exact zero_ne_one hn)
  map_one' := Units.ext (by simp [haloCharFunH_one h ψ T₀ ω hp2 hψ])
  map_mul' x y := by
    have hmul := haloCharFunH_mul h ψ T₀ ω hp2 hψ h0 h1 hT x.2 y.2
    refine Units.ext ?_
    simp only [Units.val_mk0, Units.val_mul, Subgroup.coe_mul, hmul, mul_pow]
    ring

theorem coe_haloCharH_apply (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) (x : haloUnitsH h ψ) :
    (haloCharH h ψ T₀ ω hp2 hψ h0 h1 hT x : K)
      = ((x : Kˣ) : K) ^ 2 * haloCharFunH h ψ T₀ ω ((x : Kˣ) : K) :=
  rfl

end Character

section LevelBounds

variable (p) in
/-- The decay radius of the level-`h` halo weight: `ρ_h = max(p^{−(h+1)}, ‖T'_h‖)·√p`. -/
def haloRhoH (h : ℕ) (T₀ : K) : ℝ := max ((p : ℝ)⁻¹ ^ (h + 1)) ‖TH p h T₀‖ * Real.sqrt p

variable (h : ℕ) (ψ : ℚ_[p] →+* K) (T₀ : K)

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem haloRhoH_nonneg : 0 ≤ haloRhoH p h T₀ :=
  mul_nonneg (le_max_of_le_right (norm_nonneg _)) (Real.sqrt_nonneg _)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The expansion radius `max(p^{−(h+1)}, ‖T'_h‖)` lies in the convergence disc of `exp`. -/
theorem sq_max_lt_inv_p (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) :
    max ((p : ℝ)⁻¹ ^ (h + 1)) ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹ := by
  have hpinv0 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
  rcases max_cases ((p : ℝ)⁻¹ ^ (h + 1)) ‖TH p h T₀‖ with ⟨he, -⟩ | ⟨he, -⟩
  · rw [he, ← pow_mul]
    calc (p : ℝ)⁻¹ ^ ((h + 1) * 2) < (p : ℝ)⁻¹ ^ 1 :=
          pow_lt_pow_right_of_lt_one₀ hpinv0 inv_lt_one_p (by omega)
      _ = (p : ℝ)⁻¹ := pow_one _
  · rw [he]
    exact hT

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `ρ_h < 1` on the disc `‖T'_h‖² < p⁻¹` (and `p^{−2(h+1)}·p < 1`). -/
theorem haloRhoH_lt_one (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) : haloRhoH p h T₀ < 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  refine lt_of_pow_lt_pow_left₀ 2 zero_le_one ?_
  rw [one_pow, haloRhoH, mul_pow, Real.sq_sqrt hp0.le]
  calc max ((p : ℝ)⁻¹ ^ (h + 1)) ‖TH p h T₀‖ ^ 2 * (p : ℝ) < (p : ℝ)⁻¹ * (p : ℝ) :=
        mul_lt_mul_of_pos_right (sq_max_lt_inv_p h T₀ hT) hp0
    _ = 1 := inv_mul_cancel₀ hp0.ne'

/-- `1 ≤ √p`. -/
theorem one_le_sqrt_p : 1 ≤ Real.sqrt (p : ℝ) := by
  rw [← Real.sqrt_one]
  exact Real.sqrt_le_sqrt (by exact_mod_cast hp.out.one_le)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `max(p^{−(h+1)}, ‖T'_h‖) ≤ ρ_h`. -/
theorem max_le_haloRhoH : max ((p : ℝ)⁻¹ ^ (h + 1)) ‖TH p h T₀‖ ≤ haloRhoH p h T₀ := by
  calc max ((p : ℝ)⁻¹ ^ (h + 1)) ‖TH p h T₀‖
      = max ((p : ℝ)⁻¹ ^ (h + 1)) ‖TH p h T₀‖ * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left one_le_sqrt_p (le_max_of_le_right (norm_nonneg _))

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem inv_pow_le_haloRhoH : (p : ℝ)⁻¹ ^ (h + 1) ≤ haloRhoH p h T₀ :=
  (le_max_left _ _).trans (max_le_haloRhoH h T₀)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem norm_TH_le_haloRhoH : ‖TH p h T₀‖ ≤ haloRhoH p h T₀ :=
  (le_max_right _ _).trans (max_le_haloRhoH h T₀)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The level bounds of `M1Kh` at the radius `ρ_h`. -/
theorem levelBounds_M1Kh (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) :
    LevelBounds (M1Kh h ψ) (haloRhoH p h T₀) where
  rho_nonneg := haloRhoH_nonneg h T₀
  rho_lt_one := haloRhoH_lt_one h T₀ hT
  integral hg i j := norm_apply_le_one_of_mem_M1Kh h ψ hψ hg i j
  c_le hg := (norm_apply_one_zero_le_of_mem_M1Kh h ψ hψ hg).trans (inv_pow_le_haloRhoH h T₀)
  d_unit hg := norm_apply_one_one_of_mem_M1Kh h ψ hψ hg

omit [CompleteSpace K] [CharZero K] in
/-- The values `cz + d` of the level lie in the level-`h` halo units. -/
theorem mem_haloUnitsH_of_mem_M1Kh (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ M1Kh h ψ) {z : K} (hz : ‖z‖ ≤ 1) (hu : IsUnit (g 1 0 * z + g 1 1)) :
    hu.unit ∈ haloUnitsH h ψ := by
  obtain ⟨δ, hδ, rfl⟩ := hg
  obtain ⟨d, hd⟩ : ∃ d : ℤ_[p], (d : ℚ_[p]) = δ 1 1 := ⟨⟨δ 1 1, hδ.1 1 1⟩, rfl⟩
  have hdu : IsUnit d := PadicInt.isUnit_iff.mpr (by rw [PadicInt.norm_def, hd]; exact hδ.2.2.1)
  refine ⟨hdu.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec, hd, hψ]
    exact hδ.2.2.1
  · rw [IsUnit.unit_spec, IsUnit.unit_spec, hd, mapMatrix_toMonoidHom_apply,
      mapMatrix_toMonoidHom_apply, add_sub_cancel_right, norm_mul, hψ]
    calc ‖δ 1 0‖ * ‖z‖ ≤ ‖δ 1 0‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ ≤ (p : ℝ)⁻¹ ^ (h + 1) := by rw [mul_one]; exact hδ.2.1

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The `1`-units `1 + wz`, `‖w‖ ≤ p^{−(h+1)}`, `‖z‖ ≤ 1`, of the level. -/
theorem norm_div_mul_le_of_mem_M1Kh (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ M1Kh h ψ) {z : K} (hz : ‖z‖ ≤ 1) : ‖g 1 0 / g 1 1 * z‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) := by
  rw [norm_mul, norm_div, norm_apply_one_one_of_mem_M1Kh h ψ hψ hg, div_one]
  exact (mul_le_of_le_one_right (norm_nonneg _) hz).trans
    (norm_apply_one_zero_le_of_mem_M1Kh h ψ hψ hg)

end LevelBounds

section Expansion

variable (h : ℕ) (ψ : ℚ_[p] →+* K) (T₀ : K) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)

/-- **Row decay of the binomial coefficients** at level `h`:
`‖C(s_h, m)·w^m‖ ≤ (p^{h+1}‖T'_h‖·p^{−(h+1)})^m·p^{(m−1)/(p−1)} ≤ (‖T'_h‖·√p)^m` for
`‖w‖ ≤ p^{−(h+1)}` (the level-`h` form of [LWX, Prop 3.14]'s estimate; `sq_norm_factorial_ge`). -/
theorem norm_choose_haloExponentH_mul_pow_le (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) {w : K} (hw : ‖w‖ ≤ (p : ℝ)⁻¹ ^ (h + 1)) (m : ℕ) :
    ‖Ring.choose (haloExponentH p h T₀) m * w ^ m‖ ≤ haloRhoH p h T₀ ^ m := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by
    rw [norm_natCast_p ψ hψ]
    exact inv_lt_one_p
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hsq : Real.sqrt (‖((p : ℕ) : K)‖⁻¹) = Real.sqrt (p : ℝ) := by
    rw [norm_natCast_p ψ hψ, inv_inv]
  have hmax : max ‖w‖ (‖haloExponentH p h T₀‖ * ‖w‖)
      ≤ max ((p : ℝ)⁻¹ ^ (h + 1)) ‖TH p h T₀‖ := by
    refine max_le (hw.trans (le_max_left _ _)) (le_max_of_le_right ?_)
    rw [norm_haloExponentH h ψ T₀ hp2 hψ hT]
    calc (p : ℝ) ^ (h + 1) * ‖TH p h T₀‖ * ‖w‖
        ≤ (p : ℝ) ^ (h + 1) * ‖TH p h T₀‖ * (p : ℝ)⁻¹ ^ (h + 1) :=
          mul_le_mul_of_nonneg_left hw (by positivity)
      _ = ‖TH p h T₀‖ := by
          rw [mul_right_comm, ← mul_pow, mul_inv_cancel₀ hp0.ne', one_pow, one_mul]
  calc ‖Ring.choose (haloExponentH p h T₀) m * w ^ m‖
      ≤ max ‖w‖ (‖haloExponentH p h T₀‖ * ‖w‖) ^ m * ‖((m ! : ℕ) : K)‖⁻¹ :=
        PadicExpLog.norm_choose_mul_pow_le _ _ m
    _ ≤ max ((p : ℝ)⁻¹ ^ (h + 1)) ‖TH p h T₀‖ ^ m * Real.sqrt (p : ℝ) ^ m := by
        refine mul_le_mul (pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg w)) hmax m) ?_
          (by positivity) (by positivity)
        refine (PadicExpLog.norm_factorial_inv_le h3 hp2 hm.ne').trans ?_
        rw [hsq]
        exact pow_le_pow_right₀ one_le_sqrt_p (Nat.sub_le m 1)
    _ = haloRhoH p h T₀ ^ m := by rw [haloRhoH, mul_pow]

/-- **The column of the level-`h` halo weight**: the expansion of `(cz+d)²·κ_{T₀,h}(cz + d)`
in `z`, `(cz+d)²·κ_{T₀,h}(d)·∑_m C(s_h, m)(c/d)^m z^m`. -/
def haloColH (c d : K) : PowerSeries K :=
  (PowerSeries.C d + PowerSeries.C c * PowerSeries.X) ^ 2
    * PowerSeries.C (haloCharFunH h ψ T₀ ω d)
    * PowerSeries.mk fun m => Ring.choose (haloExponentH p h T₀) m * (c / d) ^ m

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The coefficients `d, c, 0, 0, …` of `cz + d` on the level are bounded by `ρ_h^n`. -/
theorem norm_coeff_linXH_le (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ M1Kh h ψ) (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.C (g 1 1) + PowerSeries.C (g 1 0) * PowerSeries.X)‖
      ≤ haloRhoH p h T₀ ^ n := by
  rw [map_add, PowerSeries.coeff_C, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
  rcases n with _ | _ | n
  · rw [if_pos rfl, if_neg (by omega), mul_zero, add_zero, pow_zero,
      norm_apply_one_one_of_mem_M1Kh h ψ hψ hg]
  · rw [if_neg (by omega), if_pos (by omega), mul_one, zero_add, pow_one]
    exact (norm_apply_one_zero_le_of_mem_M1Kh h ψ hψ hg).trans (inv_pow_le_haloRhoH h T₀)
  · rw [if_neg (by omega), if_neg (by omega), mul_zero, add_zero, norm_zero]
    exact pow_nonneg (haloRhoH_nonneg h T₀) _

/-- Row decay `‖coeff_m‖ ≤ ρ_h^m` on the level (multiplying by `(cz+d)²` keeps the bound since
`p^{−(h+1)} ≤ ρ_h`). -/
theorem norm_coeff_haloColH_le (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ M1Kh h ψ) (m : ℕ) :
    ‖PowerSeries.coeff m (haloColH h ψ T₀ ω (g 1 0) (g 1 1))‖ ≤ haloRhoH p h T₀ ^ m := by
  have hρ0 := haloRhoH_nonneg (p := p) h T₀
  have hd0 : g 1 1 ≠ 0 := (levelBounds_M1Kh h ψ T₀ hψ hT).d_ne_zero hg
  have hu0 : IsUnit (g 1 0 * 0 + g 1 1) := by
    rw [mul_zero, zero_add]
    exact hd0.isUnit
  have hχ : ‖haloCharFunH h ψ T₀ ω (g 1 1)‖ = 1 := by
    have hn := norm_haloCharFunH h ψ T₀ ω hp2 hψ h0 h1 hT
      (mem_haloUnitsH_of_mem_M1Kh h ψ hψ hg (z := 0)
        (by rw [norm_zero]; exact zero_le_one) hu0)
    rwa [IsUnit.unit_spec, mul_zero, zero_add] at hn
  have hw : ‖g 1 0 / g 1 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) := by
    rw [norm_div, norm_apply_one_one_of_mem_M1Kh h ψ hψ hg, div_one]
    exact norm_apply_one_zero_le_of_mem_M1Kh h ψ hψ hg
  have hlin := norm_coeff_linXH_le h ψ T₀ hψ hg
  have hlin2 : ∀ n, ‖PowerSeries.coeff n
      ((PowerSeries.C (g 1 1) + PowerSeries.C (g 1 0) * PowerSeries.X) ^ 2)‖
        ≤ haloRhoH p h T₀ ^ n := fun n => by
    rw [sq]
    exact norm_coeff_mul_le hρ0 hlin hlin n
  have hC : ∀ n, ‖PowerSeries.coeff n (PowerSeries.C (haloCharFunH h ψ T₀ ω (g 1 1)))‖
      ≤ haloRhoH p h T₀ ^ n := fun n => by
    rw [PowerSeries.coeff_C]
    split_ifs with hn
    · rw [hn, pow_zero, hχ]
    · rw [norm_zero]
      exact pow_nonneg hρ0 _
  have hmk : ∀ n, ‖PowerSeries.coeff n (PowerSeries.mk fun m =>
      Ring.choose (haloExponentH p h T₀) m * (g 1 0 / g 1 1) ^ m)‖
        ≤ haloRhoH p h T₀ ^ n := fun n => by
    rw [PowerSeries.coeff_mk]
    exact norm_choose_haloExponentH_mul_pow_le h ψ T₀ hp2 hψ hT hw n
  unfold haloColH
  exact norm_coeff_mul_le hρ0 (norm_coeff_mul_le hρ0 hlin2 hC) hmk m

/-- **The binomial theorem at `s_h`**: `∑_m C(s_h, m)(wz)^m = exp(s_h·log(1 + wz))` on
`‖w‖ ≤ p^{−(h+1)}`, `‖z‖ ≤ 1` (`hasSum_choose_mul_pow`), which is `κ_{T₀,h}(1 + wz)`. -/
theorem evalAt_mk_choose_haloExponentH (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) {w : K}
    (hw : ‖w‖ ≤ (p : ℝ)⁻¹ ^ (h + 1)) {z : K} (hz : ‖z‖ ≤ 1) :
    evalAt (PowerSeries.mk fun m => Ring.choose (haloExponentH p h T₀) m * w ^ m) z
      = haloCharFunH h ψ T₀ ω (1 + w * z) := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by
    rw [norm_natCast_p ψ hψ]
    exact inv_lt_one_p
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hc : max ((p : ℝ)⁻¹ ^ (h + 1)) ‖TH p h T₀‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
    rw [norm_natCast_p ψ hψ]
    exact sq_max_lt_inv_p h T₀ hT
  have hwz : ‖w * z‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hz).trans hw
  have hex : ‖haloExponentH p h T₀‖ * ‖w * z‖
      ≤ max ((p : ℝ)⁻¹ ^ (h + 1)) ‖TH p h T₀‖ := by
    refine le_max_of_le_right ?_
    rw [norm_haloExponentH h ψ T₀ hp2 hψ hT]
    calc (p : ℝ) ^ (h + 1) * ‖TH p h T₀‖ * ‖w * z‖
        ≤ (p : ℝ) ^ (h + 1) * ‖TH p h T₀‖ * (p : ℝ)⁻¹ ^ (h + 1) :=
          mul_le_mul_of_nonneg_left hwz (by positivity)
      _ = ‖TH p h T₀‖ := by
          rw [mul_right_comm, ← mul_pow, mul_inv_cancel₀ hp0, one_pow, one_mul]
  have hterm : ∀ n, PowerSeries.coeff n (PowerSeries.mk fun m =>
      Ring.choose (haloExponentH p h T₀) m * w ^ m) * z ^ n
        = Ring.choose (haloExponentH p h T₀) n * (w * z) ^ n := fun n => by
    rw [PowerSeries.coeff_mk, mul_pow, mul_assoc]
  have hone : ‖(1 + w * z)
      - intHom ψ (repLift h (1 : (ZMod (p ^ (h + 1)))ˣ) : ℤ_[p])‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) := by
    rw [repLift_one, Units.val_one, map_one, add_sub_cancel_left]
    exact hwz
  unfold evalAt
  simp_rw [hterm]
  rw [(PadicExpLog.hasSum_choose_mul_pow h3 hp2 hc (hwz.trans (le_max_left _ _)) hex).tsum_eq,
    haloCharFunH_of_norm_sub_le h ψ T₀ ω hψ hone]
  simp only [repLift_one, univChar_one hp2, HaloInt.specialize_one, Units.val_one, map_one,
    inv_one, mul_one, one_mul]

theorem haloCharFunH_mul_one_add (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ M1Kh h ψ) {z : K} (hz : ‖z‖ ≤ 1) :
    haloCharFunH h ψ T₀ ω (g 1 1) * haloCharFunH h ψ T₀ ω (1 + g 1 0 / g 1 1 * z)
      = haloCharFunH h ψ T₀ ω (g 1 0 * z + g 1 1) := by
  have hd0 : g 1 1 ≠ 0 := (levelBounds_M1Kh h ψ T₀ hψ hT).d_ne_zero hg
  have hwz := norm_div_mul_le_of_mem_M1Kh h ψ hψ hg hz
  have h1u : 1 + g 1 0 / g 1 1 * z ≠ 0 := by
    intro hc
    have hn := norm_eq_one_of_norm_sub_le (y := (1 : K)) norm_one
      (by rw [add_sub_cancel_left]; exact hwz.trans (pow_le_inv_p h))
    rw [hc, norm_zero] at hn
    exact zero_ne_one hn
  have hu0 : IsUnit (g 1 0 * 0 + g 1 1) := by
    rw [mul_zero, zero_add]
    exact hd0.isUnit
  have hd : Units.mk0 (g 1 1) hd0 ∈ haloUnitsH h ψ := by
    obtain ⟨a, ha1, ha⟩ := mem_haloUnitsH_of_mem_M1Kh h ψ hψ hg (z := 0)
      (by rw [norm_zero]; exact zero_le_one) hu0
    rw [IsUnit.unit_spec, mul_zero, zero_add] at ha
    exact ⟨a, ha1, ha⟩
  have hone : Units.mk0 (1 + g 1 0 / g 1 1 * z) h1u ∈ haloUnitsH h ψ := by
    refine ⟨1, by simp, ?_⟩
    rw [Units.val_mk0, Units.val_one, PadicInt.coe_one, map_one, add_sub_cancel_left]
    exact hwz
  have hmul := haloCharFunH_mul h ψ T₀ ω hp2 hψ h0 h1 hT hd hone
  rw [Units.val_mk0, Units.val_mk0] at hmul
  rw [← hmul]
  congr 1
  rw [mul_add, mul_one, div_eq_mul_inv, mul_right_comm (g 1 0) (g 1 1)⁻¹ z,
    mul_left_comm (g 1 1) (g 1 0 * z) (g 1 1)⁻¹, mul_inv_cancel₀ hd0, mul_one, add_comm]

/-- **Evaluation of the column**: `haloColH(c, d)(z) = (cz+d)²·κ_{T₀,h}(cz + d)` on the closed
unit ball. -/
theorem evalAt_haloColH (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ M1Kh h ψ) {z : K} (hz : ‖z‖ ≤ 1) :
    evalAt (haloColH h ψ T₀ ω (g 1 0) (g 1 1)) z
      = (g 1 0 * z + g 1 1) ^ 2 * haloCharFunH h ψ T₀ ω (g 1 0 * z + g 1 1) := by
  have hw : ‖g 1 0 / g 1 1‖ ≤ (p : ℝ)⁻¹ ^ (h + 1) := by
    rw [norm_div, norm_apply_one_one_of_mem_M1Kh h ψ hψ hg, div_one]
    exact norm_apply_one_zero_le_of_mem_M1Kh h ψ hψ hg
  have hmk : PowerSeries.AbsSummable (PowerSeries.mk fun m =>
      Ring.choose (haloExponentH p h T₀) m * (g 1 0 / g 1 1) ^ m) := by
    unfold PowerSeries.AbsSummable
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (summable_geometric_of_lt_one (haloRhoH_nonneg h T₀) (haloRhoH_lt_one h T₀ hT))
    rw [PowerSeries.coeff_mk]
    exact norm_choose_haloExponentH_mul_pow_le h ψ T₀ hp2 hψ hT hw n
  change evalAt (linX g ^ 2 * PowerSeries.C (haloCharFunH h ψ T₀ ω (g 1 1))
    * PowerSeries.mk fun m => Ring.choose (haloExponentH p h T₀) m * (g 1 0 / g 1 1) ^ m) z
    = _
  rw [evalAt_mul (PowerSeries.absSummable_mul
      (PowerSeries.absSummable_pow (WeightSeries.absSummable_linX g) 2)
      (PowerSeries.absSummable_C _)) hmk hz,
    evalAt_mul (PowerSeries.absSummable_pow (WeightSeries.absSummable_linX g) 2)
      (PowerSeries.absSummable_C _) hz,
    evalAt_pow (WeightSeries.absSummable_linX g) hz, evalAt_linX g hz, evalAt_C,
    evalAt_mk_choose_haloExponentH h ψ T₀ ω hp2 hψ hT hw hz, mul_assoc,
    haloCharFunH_mul_one_add h ψ T₀ ω hp2 hψ h0 h1 hT hg hz]

/-- **The expansion datum of the level-`h` halo weight** ([Jacobs, Def 1.27] for
`κ = (·)²·κ_{T₀,h}`). -/
def haloExpansionH (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) :
    ExpansionData (M1Kh h ψ) (haloRhoH p h T₀) (haloUnitsH h ψ)
      (haloCharH h ψ T₀ ω hp2 hψ h0 h1 hT) where
  bounds := levelBounds_M1Kh h ψ T₀ hψ hT
  col := haloColH h ψ T₀ ω
  rowDecay hg m := norm_coeff_haloColH_le h ψ T₀ ω hp2 hψ h0 h1 hT hg m
  mem_level hg z hz hu := mem_haloUnitsH_of_mem_M1Kh h ψ hψ hg hz hu
  eval hg z hz hu := by
    rw [coe_haloCharH_apply]
    exact evalAt_haloColH h ψ T₀ ω hp2 hψ h0 h1 hT hg hz

/-- **The halo weight at level `h`** `κ_{T₀,h}` (normalised) as an `AnalyticWeight` on the
level-`h` halo units, at the level `M1Kh`, radius `ρ_h` — the weight at which the disc model
`DiscForms` is [LWX]'s `S^{D,†,m}_{[−]_{T₀}}`, `m = h + 1`. -/
def haloWeightH (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)
    (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) :
    AnalyticWeight (haloUnitsH h ψ) (M1Kh h ψ) (haloRhoH p h T₀) :=
  ⟨haloCharH h ψ T₀ ω hp2 hψ h0 h1 hT, haloExpansionH h ψ T₀ ω hp2 hψ h0 h1 hT⟩

/-- The automorphy factor of the level-`h` halo weight, as a series:
`col·(cz+d)^{−2} = κ_{T₀,h}(d)·∑_m C(s_h, m)(c/d)^m z^m`. -/
theorem autFactor_haloWeightH (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) (g : M1Kh h ψ) :
    (haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT).toWeightSeries.autFactor g.1
      = PowerSeries.C (haloCharFunH h ψ T₀ ω (g.1 1 1))
        * PowerSeries.mk fun m => Ring.choose (haloExponentH p h T₀) m
            * (g.1 1 0 / g.1 1 1) ^ m := by
  have hd0 : g.1 1 1 ≠ 0 := (levelBounds_M1Kh h ψ T₀ hψ hT).d_ne_zero g.2
  have hinv : linX g.1 * (linX g.1)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_linX]; exact hd0)
  have key : ∀ A B : PowerSeries K, linX g.1 ^ 2 * A * B * ((linX g.1)⁻¹) ^ 2 = A * B := by
    intro A B
    rw [show linX g.1 ^ 2 * A * B * ((linX g.1)⁻¹) ^ 2 = A * B * (linX g.1 * (linX g.1)⁻¹) ^ 2
      by ring, hinv, one_pow, mul_one]
  exact key _ _

/-- **The automorphy factor evaluates to `κ_{T₀,h}(cz + d)`** on the closed unit ball. -/
theorem evalAt_autFactor_haloWeightH (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹) (g : M1Kh h ψ)
    {z : K} (hz : ‖z‖ ≤ 1) :
    evalAt ((haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT).toWeightSeries.autFactor g.1) z
      = haloCharFunH h ψ T₀ ω (g.1 1 0 * z + g.1 1 1) := by
  have hB := levelBounds_M1Kh h ψ T₀ hψ hT
  have hd0 : g.1 1 1 ≠ 0 := hB.d_ne_zero g.2
  have hlt : ‖g.1 1 0‖ < ‖g.1 1 1‖ := by
    rw [hB.d_unit g.2]
    exact (hB.c_le g.2).trans_lt (haloRhoH_lt_one h T₀ hT)
  have hne : g.1 1 0 * z + g.1 1 1 ≠ 0 := by
    intro hc
    have hn := norm_eq_one_of_norm_sub_le (hB.d_unit g.2) (x := g.1 1 0 * z + g.1 1 1) (by
      rw [add_sub_cancel_right, norm_mul]
      exact ((mul_le_of_le_one_right (norm_nonneg _) hz).trans
        (norm_apply_one_zero_le_of_mem_M1Kh h ψ hψ g.2)).trans (pow_le_inv_p h))
    rw [hc, norm_zero] at hn
    exact zero_ne_one hn
  change evalAt ((haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT).toWeightSeries.col (g.1 1 0) (g.1 1 1)
    * ((linX g.1)⁻¹) ^ 2) z = _
  rw [evalAt_mul ((haloWeightH h ψ T₀ ω hp2 hψ h0 h1 hT).toWeightSeries.absSummable g.2)
      (PowerSeries.absSummable_pow (WeightSeries.absSummable_linX_inv hd0 hlt) 2) hz,
    evalAt_pow (WeightSeries.absSummable_linX_inv hd0 hlt) hz, evalAt_linX_inv hd0 hlt hz]
  change evalAt (haloColH h ψ T₀ ω (g.1 1 0) (g.1 1 1)) z * _ = _
  rw [evalAt_haloColH h ψ T₀ ω hp2 hψ h0 h1 hT g.2 hz, mul_right_comm, ← mul_pow,
    mul_inv_cancel₀ hne, one_pow, one_mul]

end Expansion

end LWX

end
