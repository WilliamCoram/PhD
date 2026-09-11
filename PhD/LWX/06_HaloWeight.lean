/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.«01_Binomial»
import PhD.LWX.«05_Specialize»

/-!
# The halo weight `κ_{T₀}` as an analytic weight

The specialization of the universal character `[−] : ℤ_p^× → Λ^×` ([LWX, Notation 2.1]) at a
point `T₀` of the halo annulus is the character `κ_{T₀}(x) = ω(x̄)·(1+T₀)^{ℓ⟨x⟩}`,
`ℓ⟨x⟩ = log⟨x⟩/p`, i.e. `κ_{T₀}(x) = ω(x̄)·exp(s·log⟨x⟩)` with the **halo exponent**
`s = log(1+T₀)/p`.  The general-weight layer `PhD/QMF/Weight/` needs a weight as an
`AnalyticWeight UK S ρ`: a character on a subgroup `UK ≤ Kˣ` together with the expansion of
`κ(cz + d)` as a power series in `z` on the closed unit ball of `K` with decay `ρ^m`.  Here:

* `UK = haloUnits ψ = ψ(ℤ_p^×)·(1 + p𝒪_K)` — the units of `K` within `p⁻¹` of a `ℤ_p`-unit
  (the values `cz + d`, `z ∈ 𝒪_K`, of the level below);
* `S = M1K ψ` — the image of [LWX, (2.3.3)]'s monoid `M₁` in the `K`-matrices;
* the character is `x ↦ x²·κ_{T₀}(x)` — [LWX]'s `χ = κ_{T₀}` times the `(cz+d)²`
  normalisation of [Jacobs, Def 1.27], so that the automorphy factor `κ(cz+d)/(cz+d)²` of
  `QMF.Weight.kappaSlash` is exactly [LWX, (2.3.2)]'s `χ(cz + d)`;
* the column is `(cz+d)²·κ_{T₀}(d)·∑_m C(s, m)(c/d)^m z^m` — `κ_{T₀}(1 + wz) = (1 + wz)^s`
  expanded by the binomial theorem `PhD/LWX/01_Binomial.lean` — with decay
  `ρ = ‖T₀‖·√p`, valid on the **sub-annulus `p⁻¹ < ‖T₀‖`, `‖T₀‖² < p⁻¹`** (`v(T₀) > 1/2`),
  where `κ_{T₀}` is `1`-analytic.  ([LWX, §2.7] only records the crude radius
  `W^{≤ p^{−1/p^{m₀−4}}}` for `m₀`-analyticity — "the radius here is not optimal"; the
  `m = 1` sub-annulus is what the Tate-algebra model of `PhD/QMF/Weight/` can express.)

## Main declarations

* `LWX.haloUnits`, `LWX.haloCharFun`, `LWX.haloChar` — the domain and the character.
* `LWX.haloCharFun_psi` — on `ψ(ℤ_p^×)` the character is the specialized universal character.
* `LWX.M1K`, `LWX.levelBounds_M1K` — the level.
* `LWX.haloCol`, `LWX.haloExpansion`, **`LWX.haloWeight`** — the analytic weight.
* `LWX.evalAt_autFactor_haloWeight` — the automorphy factor evaluates to `κ_{T₀}(cz + d)`.
-/

open Filter Topology TateFredholm QMF

open scoped Nat

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The integral coefficient map `ℤ_p → K` underlying `ψ : ℚ_p → K`. -/
def intHom (ψ : ℚ_[p] →+* K) : ℤ_[p] →+* K := ψ.comp PadicInt.Coe.ringHom

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
@[simp] theorem intHom_apply (ψ : ℚ_[p] →+* K) (x : ℤ_[p]) : intHom ψ x = ψ (x : ℚ_[p]) :=
  rfl

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `intHom ψ` is isometric when `ψ` is. -/
theorem norm_intHom (ψ : ℚ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (x : ℤ_[p]) :
    ‖intHom ψ x‖ = ‖x‖ := by
  rw [intHom_apply, hψ, PadicInt.norm_def]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `‖p‖ = p⁻¹` in `K` under an isometric `ψ`. -/
theorem norm_natCast_p (ψ : ℚ_[p] →+* K) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) :
    ‖((p : ℕ) : K)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast ψ, hψ, Padic.norm_p]

/-- `p⁻¹ < 1` in `ℝ`. -/
theorem inv_lt_one_p : (p : ℝ)⁻¹ < 1 :=
  inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.out.one_lt)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The sub-annulus condition `‖T₀‖² < p⁻¹` implies the halo condition `‖T₀‖ < 1`. -/
theorem norm_lt_one_of_sq_lt {T₀ : K} (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) : ‖T₀‖ < 1 :=
  lt_of_pow_lt_pow_left₀ 2 zero_le_one (by rw [one_pow]; exact h1.trans (inv_lt_one_p (p := p)))

omit [CompleteSpace K] [CharZero K] in
/-- The ultrametric inequality for differences. -/
theorem norm_sub_le_max_norm (a b : K) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  rw [sub_eq_add_neg, ← norm_neg b]
  exact IsUltrametricDist.norm_add_le_max a (-b)

omit [CompleteSpace K] [CharZero K] in
/-- An element within `p⁻¹` of a norm-one element has norm one. -/
theorem norm_eq_one_of_norm_sub_le {x y : K} (hy : ‖y‖ = 1) (h : ‖x - y‖ ≤ (p : ℝ)⁻¹) :
    ‖x‖ = 1 := by
  have hlt : ‖x - y‖ < 1 := h.trans_lt (inv_lt_one_p (p := p))
  calc ‖x‖ = ‖(x - y) + y‖ := by rw [sub_add_cancel]
    _ = max ‖x - y‖ ‖y‖ :=
        IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hy]; exact hlt.ne)
    _ = 1 := by rw [hy, max_eq_right hlt.le]

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `x/t` is a `1`-unit when `x` is within `p⁻¹` of the norm-one element `t`. -/
theorem norm_mul_inv_sub_one_le {x t : K} (ht : ‖t‖ = 1) (h : ‖x - t‖ ≤ (p : ℝ)⁻¹) :
    ‖x * t⁻¹ - 1‖ ≤ (p : ℝ)⁻¹ := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [norm_zero] at ht
    exact zero_ne_one ht
  have hkey : x * t⁻¹ - 1 = (x - t) * t⁻¹ := by rw [sub_mul, mul_inv_cancel₀ ht0]
  rw [hkey, norm_mul, norm_inv, ht, inv_one, mul_one]
  exact h

section Teichmuller

/-- In `ℤ_p`, `‖x‖ ≤ p⁻¹` iff `x` reduces to `0` modulo `p`. -/
theorem norm_le_inv_iff_toZMod_eq_zero (x : ℤ_[p]) :
    ‖x‖ ≤ (p : ℝ)⁻¹ ↔ PadicInt.toZMod x = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits,
    ← zpow_neg_one, PadicInt.norm_le_pow_iff_norm_lt_pow_add_one, neg_add_cancel, zpow_zero]

/-- The natural-number lift `r.val` of a residue class is a `p`-adic unit. -/
theorem isUnit_natCast_val (r : (ZMod p)ˣ) : IsUnit ((((r : ZMod p).val : ℕ)) : ℤ_[p]) := by
  by_contra h
  have h0 : PadicInt.toZMod ((((r : ZMod p).val : ℕ)) : ℤ_[p]) = 0 := by
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal]
    exact mem_nonunits_iff.mpr h
  rw [map_natCast, ZMod.natCast_zmod_val] at h0
  exact r.ne_zero h0

/-- The Teichmüller lift of a residue class `r ∈ 𝔽_p^×`. -/
def teichRes (r : (ZMod p)ˣ) : ℤ_[p]ˣ := teichmuller (isUnit_natCast_val r).unit

/-- The residue of the natural-number lift of `r` is `r`. -/
theorem toZMod_natCast_val (r : (ZMod p)ˣ) :
    PadicInt.toZMod (((r : ZMod p).val : ℕ) : ℤ_[p]) = r := by
  rw [map_natCast, ZMod.natCast_zmod_val]

/-- Teichmüller lifts preserve residues (`norm_mul_teichmuller_inv_sub_one_le`). -/
theorem unitsMap_toZMod_teichmuller (x : ℤ_[p]ˣ) :
    Units.map (PadicInt.toZMod (p := p)).toMonoidHom (teichmuller x)
      = Units.map (PadicInt.toZMod (p := p)).toMonoidHom x := by
  have h := norm_mul_teichmuller_inv_sub_one_le x
  rw [norm_le_inv_iff_toZMod_eq_zero, map_sub, map_one, sub_eq_zero] at h
  have h' : Units.map (PadicInt.toZMod (p := p)).toMonoidHom (x * (teichmuller x)⁻¹) = 1 :=
    Units.ext h
  rwa [map_mul, map_inv, mul_inv_eq_one, eq_comm] at h'

/-- The residue of `teichRes r` is `r`. -/
theorem toZMod_teichRes (r : (ZMod p)ˣ) :
    Units.map (PadicInt.toZMod (p := p)).toMonoidHom (teichRes r) = r := by
  rw [teichRes, unitsMap_toZMod_teichmuller]
  refine Units.ext ?_
  change PadicInt.toZMod ((isUnit_natCast_val r).unit : ℤ_[p]) = r
  rw [IsUnit.unit_spec, toZMod_natCast_val]

/-- `teichRes` of the residue of a unit is its Teichmüller lift. -/
theorem teichRes_toZMod (a : ℤ_[p]ˣ) :
    teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) = teichmuller a := by
  refine teichmuller_eq_of_norm_sub_le ?_
  rw [norm_le_inv_iff_toZMod_eq_zero, map_sub, IsUnit.unit_spec, toZMod_natCast_val, sub_eq_zero]
  rfl

/-- Every unit is within `p⁻¹` of the Teichmüller lift of its residue. -/
theorem norm_sub_teichRes_le (a : ℤ_[p]ˣ) :
    ‖(a : ℤ_[p]) - (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p])‖
      ≤ (p : ℝ)⁻¹ := by
  rw [teichRes_toZMod, norm_le_inv_iff_toZMod_eq_zero, map_sub, sub_eq_zero]
  exact (congrArg Units.val (unitsMap_toZMod_teichmuller a)).symm

/-- `teichRes` is multiplicative (`teichmuller_mul` and local constancy). -/
theorem teichRes_mul (r r' : (ZMod p)ˣ) : teichRes (r * r') = teichRes r * teichRes r' := by
  unfold teichRes
  rw [← teichmuller_mul]
  refine teichmuller_eq_of_norm_sub_le ?_
  rw [norm_le_inv_iff_toZMod_eq_zero, map_sub, sub_eq_zero]
  simp only [IsUnit.unit_spec, Units.val_mul, map_mul, map_natCast, ZMod.natCast_zmod_val]

/-- Distinct residues have Teichmüller lifts at distance `1`. -/
theorem teichRes_injective : Function.Injective (teichRes (p := p)) :=
  Function.LeftInverse.injective (g := Units.map (PadicInt.toZMod (p := p)).toMonoidHom)
    toZMod_teichRes

/-- `teichRes 1 = 1`. -/
theorem teichRes_one : teichRes (1 : (ZMod p)ˣ) = 1 := by
  have h := teichRes_mul (1 : (ZMod p)ˣ) 1
  rw [mul_one] at h
  exact mul_left_cancel (a := teichRes (1 : (ZMod p)ˣ)) (by rw [mul_one]; exact h.symm)

end Teichmuller

section Units

variable (ψ : ℚ_[p] →+* K)

omit [CompleteSpace K] [CharZero K] in
/-- **The halo units** `ψ(ℤ_p^×)·(1 + p𝒪_K)`: units of `K` within `p⁻¹` of a `ℤ_p`-unit —
the domain of the halo character, containing every value `cz + d` (`‖c‖ ≤ p⁻¹`,
`d ∈ ψ(ℤ_p^×)`, `‖z‖ ≤ 1`) of the level.  (The clause `‖ψ a‖ = 1` is automatic for an isometric
`ψ`; it is carried so that the subgroup laws need no hypothesis on `ψ`.) -/
def haloUnits : Subgroup Kˣ where
  carrier := {x | ∃ a : ℤ_[p]ˣ, ‖ψ ((a : ℤ_[p]) : ℚ_[p])‖ = 1 ∧
    ‖(x : K) - ψ ((a : ℤ_[p]) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹}
  one_mem' := ⟨1, by simp, by simp⟩
  mul_mem' := by
    rintro x y ⟨a, ha1, ha⟩ ⟨b, hb1, hb⟩
    have hx1 : ‖(x : K)‖ = 1 := norm_eq_one_of_norm_sub_le ha1 ha
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
        _ ≤ (p : ℝ)⁻¹ := max_le (by rw [norm_mul, hx1, one_mul]; exact hb)
            (by rw [norm_mul, hb1, mul_one]; exact ha)
  inv_mem' := by
    rintro x ⟨a, ha1, ha⟩
    have hx1 : ‖(x : K)‖ = 1 := norm_eq_one_of_norm_sub_le ha1 ha
    have hab : ψ ((a : ℤ_[p]) : ℚ_[p]) * ψ (((a⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p]) = 1 := by
      rw [← map_mul, ← PadicInt.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        PadicInt.coe_one, map_one]
    have hinv1 : ‖ψ (((a⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) : ℚ_[p])‖ = 1 := by
      have := congrArg norm hab
      rwa [norm_mul, ha1, one_mul, norm_one] at this
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
/-- Membership in the halo units, unfolded. -/
theorem mem_haloUnits_iff {x : Kˣ} :
    x ∈ haloUnits ψ ↔ ∃ a : ℤ_[p]ˣ, ‖ψ ((a : ℤ_[p]) : ℚ_[p])‖ = 1 ∧
      ‖(x : K) - ψ ((a : ℤ_[p]) : ℚ_[p])‖ ≤ (p : ℝ)⁻¹ :=
  Iff.rfl

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The images of the Teichmüller lifts have norm one. -/
theorem norm_intHom_teichRes (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (r : (ZMod p)ˣ) :
    ‖intHom ψ (teichRes r : ℤ_[p])‖ = 1 := by
  rw [norm_intHom ψ hψ]
  exact PadicInt.norm_units _

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Teichmüller lifts of distinct residues are at distance `1` in `K`. -/
theorem teichRes_eq_of_norm_sub_le (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {r r' : (ZMod p)ˣ}
    (h : ‖intHom ψ (teichRes r : ℤ_[p]) - intHom ψ (teichRes r' : ℤ_[p])‖ ≤ (p : ℝ)⁻¹) :
    r = r' := by
  rw [← map_sub, norm_intHom ψ hψ, norm_le_inv_iff_toZMod_eq_zero, map_sub, sub_eq_zero] at h
  rw [← toZMod_teichRes r, ← toZMod_teichRes r']
  exact Units.ext h

omit [CompleteSpace K] [CharZero K] in
/-- A halo unit is within `p⁻¹` of the Teichmüller lift of a unique residue class. -/
theorem exists_unique_teichRes_of_mem_haloUnits (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {x : Kˣ}
    (hx : x ∈ haloUnits ψ) :
    ∃! r : (ZMod p)ˣ, ‖(x : K) - intHom ψ (teichRes r : ℤ_[p])‖ ≤ (p : ℝ)⁻¹ := by
  obtain ⟨a, -, ha⟩ := hx
  have hex : ‖(x : K) - intHom ψ
      (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    calc ‖(x : K) - intHom ψ
          (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p])‖
        = ‖((x : K) - intHom ψ (a : ℤ_[p])) + intHom ψ ((a : ℤ_[p])
            - (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p]))‖ := by
          rw [map_sub, sub_add_sub_cancel]
      _ ≤ max ‖(x : K) - intHom ψ (a : ℤ_[p])‖ ‖intHom ψ ((a : ℤ_[p])
            - (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p]))‖ :=
          IsUltrametricDist.norm_add_le_max _ _
      _ ≤ (p : ℝ)⁻¹ := max_le ha (by rw [norm_intHom ψ hψ]; exact norm_sub_teichRes_le a)
  refine ⟨_, hex, fun r hr => teichRes_eq_of_norm_sub_le ψ hψ ?_⟩
  calc ‖intHom ψ (teichRes r : ℤ_[p]) - intHom ψ
        (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p])‖
      = ‖((x : K) - intHom ψ
            (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p]))
          - ((x : K) - intHom ψ (teichRes r : ℤ_[p]))‖ := by
        rw [sub_sub_sub_cancel_left]
    _ ≤ max ‖(x : K) - intHom ψ
            (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p])‖
          ‖(x : K) - intHom ψ (teichRes r : ℤ_[p])‖ := norm_sub_le_max_norm _ _
    _ ≤ (p : ℝ)⁻¹ := max_le hex hr

end Units

section Character

variable (ψ : ℚ_[p] →+* K) (T₀ : K) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)

/-- **The halo exponent** `s = log(1 + T₀)/p`: `(1+T₀)^{log x/p} = x^s`. -/
def haloExponent : K := PadicExpLog.padicLog (1 + T₀) / ((p : ℕ) : K)

/-- `‖s‖ = p·‖T₀‖` on the sub-annulus (`norm_padicLog_eq`). -/
theorem norm_haloExponent (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) :
    ‖haloExponent (p := p) T₀‖ = p * ‖T₀‖ := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by
    rw [norm_natCast_p ψ hψ]
    exact inv_lt_one_p
  have hu : ‖(1 + T₀) - 1‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
    rw [add_sub_cancel_left, norm_natCast_p ψ hψ]
    exact h1
  rw [haloExponent, norm_div, PadicExpLog.norm_padicLog_eq h3 hp2 hu, add_sub_cancel_left,
    norm_natCast_p ψ hψ, div_inv_eq_mul, mul_comm]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `‖w‖ ≤ p⁻¹` puts `w` on the joint disc `‖w‖² < ‖p‖` of `exp` and `log`. -/
theorem sq_norm_lt_norm_p_of_le (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {w : K} (hw : ‖w‖ ≤ (p : ℝ)⁻¹) :
    ‖w‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
  rw [norm_natCast_p ψ hψ]
  have hp0 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp.out.pos)
  calc ‖w‖ ^ 2 ≤ ((p : ℝ)⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
    _ < (p : ℝ)⁻¹ := by
        rw [sq]
        exact mul_lt_of_lt_one_left hp0 inv_lt_one_p

/-- `‖s·log u‖ ≤ ‖T₀‖` for a `1`-unit `u` (`‖s‖ = p‖T₀‖`, `‖log u‖ = ‖u − 1‖ ≤ p⁻¹`). -/
theorem norm_haloExponent_mul_padicLog_le (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) {u : K} (hu : ‖u - 1‖ ≤ (p : ℝ)⁻¹) :
    ‖haloExponent (p := p) T₀ * PadicExpLog.padicLog u‖ ≤ ‖T₀‖ := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by
    rw [norm_natCast_p ψ hψ]
    exact inv_lt_one_p
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  rw [norm_mul, norm_haloExponent ψ T₀ hp2 hψ h1,
    PadicExpLog.norm_padicLog_eq h3 hp2 (sq_norm_lt_norm_p_of_le ψ hψ hu)]
  calc (p : ℝ) * ‖T₀‖ * ‖u - 1‖ ≤ (p : ℝ) * ‖T₀‖ * (p : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_left hu (by positivity)
    _ = ‖T₀‖ := by rw [mul_right_comm, mul_inv_cancel₀ hp0, one_mul]

/-- `s·log u` lies on the joint disc of `exp` and `log` for a `1`-unit `u`. -/
theorem sq_norm_haloExponent_mul_padicLog_lt (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) {u : K} (hu : ‖u - 1‖ ≤ (p : ℝ)⁻¹) :
    ‖haloExponent (p := p) T₀ * PadicExpLog.padicLog u‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
  rw [norm_natCast_p ψ hψ]
  exact lt_of_le_of_lt (pow_le_pow_left₀ (norm_nonneg _)
    (norm_haloExponent_mul_padicLog_le ψ T₀ hp2 hψ h1 hu) 2) h1

/-- `‖exp(s·log u)‖ = 1` for a `1`-unit `u`. -/
theorem norm_padicExp_haloExponent_mul_padicLog (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) {u : K} (hu : ‖u - 1‖ ≤ (p : ℝ)⁻¹) :
    ‖PadicExpLog.padicExp (haloExponent (p := p) T₀ * PadicExpLog.padicLog u)‖ = 1 := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by
    rw [norm_natCast_p ψ hψ]
    exact inv_lt_one_p
  refine PadicExpLog.norm_eq_one_of_norm_sub_one_lt_one ?_
  refine (PadicExpLog.norm_padicExp_sub_one_le h3 hp2
    (sq_norm_haloExponent_mul_padicLog_lt ψ T₀ hp2 hψ h1 hu)).trans_lt ?_
  exact (norm_haloExponent_mul_padicLog_le ψ T₀ hp2 hψ h1 hu).trans_lt (norm_lt_one_of_sq_lt h1)

/-- **[LWX]'s character `χ = κ_{T₀}`** as a total function on `K`:
`x ↦ ψ(ω(r))·exp(s·log(x/ψ(τ(r))))`, `r` the residue class with `‖x − ψ(τ(r))‖ ≤ p⁻¹`
(a finite sum with at most one nonzero term; `0` off the halo units). -/
def haloCharFun (x : K) : K :=
  ∑ r : (ZMod p)ˣ,
    if ‖x - intHom ψ (teichRes r : ℤ_[p])‖ ≤ (p : ℝ)⁻¹ then
      intHom ψ (ω r : ℤ_[p])
        * PadicExpLog.padicExp (haloExponent (p := p) T₀
            * PadicExpLog.padicLog (x * (intHom ψ (teichRes r : ℤ_[p]))⁻¹))
    else 0

omit [CompleteSpace K] [CharZero K] in
/-- The value of `haloCharFun` on the residue disc of `r`. -/
theorem haloCharFun_of_norm_sub_le (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {x : K} {r : (ZMod p)ˣ}
    (h : ‖x - intHom ψ (teichRes r : ℤ_[p])‖ ≤ (p : ℝ)⁻¹) :
    haloCharFun ψ T₀ ω x
      = intHom ψ (ω r : ℤ_[p])
        * PadicExpLog.padicExp (haloExponent (p := p) T₀
            * PadicExpLog.padicLog (x * (intHom ψ (teichRes r : ℤ_[p]))⁻¹)) := by
  unfold haloCharFun
  rw [Finset.sum_eq_single r ?_ (fun h' => absurd (Finset.mem_univ r) h'), if_pos h]
  intro r' _ hr'
  refine if_neg fun h' => hr' (teichRes_eq_of_norm_sub_le ψ hψ ?_)
  calc ‖intHom ψ (teichRes r' : ℤ_[p]) - intHom ψ (teichRes r : ℤ_[p])‖
      = ‖(x - intHom ψ (teichRes r : ℤ_[p])) - (x - intHom ψ (teichRes r' : ℤ_[p]))‖ := by
        rw [sub_sub_sub_cancel_left]
    _ ≤ max ‖x - intHom ψ (teichRes r : ℤ_[p])‖ ‖x - intHom ψ (teichRes r' : ℤ_[p])‖ :=
        norm_sub_le_max_norm _ _
    _ ≤ (p : ℝ)⁻¹ := max_le h h'

omit [CompleteSpace K] in
/-- `κ_{T₀}(1) = 1`. -/
theorem haloCharFun_one (hψ : ∀ x, ‖ψ x‖ = ‖x‖) : haloCharFun ψ T₀ ω 1 = 1 := by
  rw [haloCharFun_of_norm_sub_le ψ T₀ ω hψ (r := 1) (by simp [teichRes_one])]
  simp [teichRes_one]

/-- **Multiplicativity** on the halo units (`teichRes_mul`, `padicLog_mul`, `padicExp_add`
on the joint disc `‖T₀‖² < p⁻¹`). -/
theorem haloCharFun_mul (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (_h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) {x y : Kˣ} (hx : x ∈ haloUnits ψ) (hy : y ∈ haloUnits ψ) :
    haloCharFun ψ T₀ ω ((x * y : Kˣ) : K) = haloCharFun ψ T₀ ω x * haloCharFun ψ T₀ ω y := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by
    rw [norm_natCast_p ψ hψ]
    exact inv_lt_one_p
  obtain ⟨r, hr, -⟩ := exists_unique_teichRes_of_mem_haloUnits ψ hψ hx
  obtain ⟨r', hr', -⟩ := exists_unique_teichRes_of_mem_haloUnits ψ hψ hy
  have hτ := norm_intHom_teichRes ψ hψ
  have hx1 : ‖(x : K)‖ = 1 := norm_eq_one_of_norm_sub_le (hτ r) hr
  have hrr' : ‖((x * y : Kˣ) : K) - intHom ψ (teichRes (r * r') : ℤ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [teichRes_mul, Units.val_mul (teichRes r) (teichRes r'), map_mul, Units.val_mul x y]
    calc ‖(x : K) * y - intHom ψ (teichRes r : ℤ_[p]) * intHom ψ (teichRes r' : ℤ_[p])‖
        = ‖(x : K) * ((y : K) - intHom ψ (teichRes r' : ℤ_[p]))
            + ((x : K) - intHom ψ (teichRes r : ℤ_[p])) * intHom ψ (teichRes r' : ℤ_[p])‖ := by
          congr 1
          ring
      _ ≤ max ‖(x : K) * ((y : K) - intHom ψ (teichRes r' : ℤ_[p]))‖
            ‖((x : K) - intHom ψ (teichRes r : ℤ_[p])) * intHom ψ (teichRes r' : ℤ_[p])‖ :=
          IsUltrametricDist.norm_add_le_max _ _
      _ ≤ (p : ℝ)⁻¹ := max_le (by rw [norm_mul, hx1, one_mul]; exact hr')
          (by rw [norm_mul, hτ, mul_one]; exact hr)
  have hu := norm_mul_inv_sub_one_le (hτ r) hr
  have hv := norm_mul_inv_sub_one_le (hτ r') hr'
  have hsplit : (x : K) * y
      * (intHom ψ (teichRes r : ℤ_[p]) * intHom ψ (teichRes r' : ℤ_[p]))⁻¹
      = ((x : K) * (intHom ψ (teichRes r : ℤ_[p]))⁻¹)
        * ((y : K) * (intHom ψ (teichRes r' : ℤ_[p]))⁻¹) := by
    rw [mul_inv]
    ring
  rw [haloCharFun_of_norm_sub_le ψ T₀ ω hψ hrr', haloCharFun_of_norm_sub_le ψ T₀ ω hψ hr,
    haloCharFun_of_norm_sub_le ψ T₀ ω hψ hr', map_mul ω, Units.val_mul (ω r) (ω r'),
    map_mul (intHom ψ), teichRes_mul, Units.val_mul (teichRes r) (teichRes r'),
    map_mul (intHom ψ), Units.val_mul x y, hsplit,
    PadicExpLog.padicLog_mul h3 hp2 (sq_norm_lt_norm_p_of_le ψ hψ hu)
      (sq_norm_lt_norm_p_of_le ψ hψ hv),
    mul_add, PadicExpLog.padicExp_add h3 hp2
      (sq_norm_haloExponent_mul_padicLog_lt ψ T₀ hp2 hψ h1 hu)
      (sq_norm_haloExponent_mul_padicLog_lt ψ T₀ hp2 hψ h1 hv)]
  ring

/-- The character has norm `1` on every residue disc. -/
theorem norm_haloCharFun_of_norm_sub_le (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) {x : K} {r : (ZMod p)ˣ}
    (hr : ‖x - intHom ψ (teichRes r : ℤ_[p])‖ ≤ (p : ℝ)⁻¹) :
    ‖haloCharFun ψ T₀ ω x‖ = 1 := by
  rw [haloCharFun_of_norm_sub_le ψ T₀ ω hψ hr, norm_mul, norm_intHom ψ hψ, PadicInt.norm_units,
    one_mul]
  exact norm_padicExp_haloExponent_mul_padicLog ψ T₀ hp2 hψ h1
    (norm_mul_inv_sub_one_le (norm_intHom_teichRes ψ hψ r) hr)

/-- The character takes values of norm `1` on the halo units. -/
theorem norm_haloCharFun (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (_h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) {x : Kˣ} (hx : x ∈ haloUnits ψ) :
    ‖haloCharFun ψ T₀ ω x‖ = 1 := by
  obtain ⟨r, hr, -⟩ := exists_unique_teichRes_of_mem_haloUnits ψ hψ hx
  exact norm_haloCharFun_of_norm_sub_le ψ T₀ ω hp2 hψ h1 hr

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- An isometric `ψ` commutes with the `p`-adic logarithm on the `p⁻¹`-disc about `1`. -/
theorem map_padicLog (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {y : ℚ_[p]}
    (hy : ‖y - 1‖ ≤ (p : ℝ)⁻¹) :
    ψ (PadicExpLog.padicLog y) = PadicExpLog.padicLog (ψ y) := by
  have hcont : Continuous ψ :=
    AddMonoidHomClass.continuous_of_bound ψ 1 fun x => by rw [hψ, one_mul]
  have h3 : ‖((p : ℕ) : ℚ_[p])‖ < 1 := by
    rw [Padic.norm_p]
    exact inv_lt_one_p
  have hy2 : ‖y - 1‖ ^ 2 ≤ ‖((p : ℕ) : ℚ_[p])‖ := by
    rw [Padic.norm_p]
    calc ‖y - 1‖ ^ 2 ≤ ((p : ℝ)⁻¹) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hy 2
      _ ≤ (p : ℝ)⁻¹ := by
          rw [sq]
          exact mul_le_of_le_one_left (by positivity) inv_lt_one_p.le
  unfold PadicExpLog.padicLog
  rw [map_neg, ← ((PadicExpLog.summable_padicLog_term h3 hp2 hy2).hasSum.map ψ hcont).tsum_eq]
  congr 1
  refine tsum_congr fun n => ?_
  simp only [Function.comp_apply, map_div₀, map_pow, map_sub, map_one, map_add, map_natCast]

/-- **The character is the specialized universal character on `ψ(ℤ_p^×)`**:
`κ_{T₀}(ψ a) = [a](T₀)` (`specialize_univChar`, `ψ` commutes with `log`, and the binomial
theorem `(1+T₀)^{ψ(ℓ⟨a⟩)} = exp(ψ(ℓ⟨a⟩)·log(1+T₀))`). -/
theorem haloCharFun_psi (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) (a : ℤ_[p]ˣ) :
    haloCharFun ψ T₀ ω (intHom ψ (a : ℤ_[p]))
      = HaloInt.specialize (intHom ψ) T₀ (univChar ω a) := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by
    rw [norm_natCast_p ψ hψ]
    exact inv_lt_one_p
  have hr : ‖intHom ψ (a : ℤ_[p]) - intHom ψ
      (teichRes (Units.map (PadicInt.toZMod (p := p)).toMonoidHom a) : ℤ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [← map_sub, norm_intHom ψ hψ]
    exact norm_sub_teichRes_le a
  have hc : ‖T₀‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
    rw [norm_natCast_p ψ hψ]
    exact h1
  have hu1 : ‖intHom ψ (logQuot a)‖ ≤ 1 := by
    rw [norm_intHom ψ hψ]
    exact PadicInt.norm_le_one _
  have hlog : intHom ψ (logQuot a)
      = PadicExpLog.padicLog (intHom ψ (oneUnitPart a)) / ((p : ℕ) : K) := by
    rw [intHom_apply, coe_logQuot hp2, qlog, map_div₀, map_natCast, map_padicLog ψ hp2 hψ ?_]
    · rfl
    · rw [← PadicInt.coe_one, ← PadicInt.coe_sub, ← PadicInt.norm_def]
      exact norm_oneUnitPart_sub_one_le a
  have hunit : intHom ψ (a : ℤ_[p]) * (intHom ψ (teichmuller a : ℤ_[p]))⁻¹
      = intHom ψ (oneUnitPart a) := by
    rw [oneUnitPart, Units.val_mul, map_mul, map_units_inv]
  rw [haloCharFun_of_norm_sub_le ψ T₀ ω hψ hr,
    specialize_univChar (intHom ψ) (norm_intHom ψ hψ) h0 (norm_lt_one_of_sq_lt h1) ω a]
  congr 1
  rw [oneAddPow, (PadicExpLog.hasSum_choose_mul_pow h3 hp2 hc le_rfl
    (mul_le_of_le_one_left (norm_nonneg _) hu1)).tsum_eq]
  congr 1
  rw [teichRes_toZMod, hunit, hlog, haloExponent]
  ring

/-- **The halo weight's character** on the halo units: `x ↦ x²·κ_{T₀}(x)` — [LWX]'s `χ`
times the `(cz+d)²` normalisation of [Jacobs, Def 1.27]. -/
def haloChar (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) : haloUnits ψ →* Kˣ where
  toFun x := Units.mk0 (((x : Kˣ) : K) ^ 2 * haloCharFun ψ T₀ ω ((x : Kˣ) : K))
    (mul_ne_zero (pow_ne_zero 2 (Units.ne_zero _)) fun h => by
      have := norm_haloCharFun ψ T₀ ω hp2 hψ h0 h1 x.2
      rw [h, norm_zero] at this
      exact zero_ne_one this)
  map_one' := Units.ext (by simp [haloCharFun_one ψ T₀ ω hψ])
  map_mul' x y := by
    have hmul := haloCharFun_mul ψ T₀ ω hp2 hψ h0 h1 x.2 y.2
    rw [Units.val_mul] at hmul
    refine Units.ext ?_
    simp only [Units.val_mk0, Units.val_mul, Subgroup.coe_mul, hmul, mul_pow]
    ring

/-- The value of the halo weight's character. -/
theorem coe_haloChar_apply (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) (x : haloUnits ψ) :
    (haloChar ψ T₀ ω hp2 hψ h0 h1 x : K)
      = ((x : Kˣ) : K) ^ 2 * haloCharFun ψ T₀ ω ((x : Kˣ) : K) :=
  rfl

end Character

section Level

variable (ψ : ℚ_[p] →+* K) (T₀ : K)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **The level**: the image of [LWX, (2.3.3)]'s monoid `M₁` in the `K`-matrices. -/
def M1K : Submonoid (Matrix (Fin 2) (Fin 2) K) :=
  (M1 p).map (RingHom.mapMatrix ψ).toMonoidHom

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Membership in the level, unfolded. -/
theorem mem_M1K_iff {g : Matrix (Fin 2) (Fin 2) K} :
    g ∈ M1K ψ ↔ ∃ δ ∈ M1 p, (RingHom.mapMatrix ψ) δ = g :=
  Submonoid.mem_map

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- Entries of the image of a matrix under `ψ`. -/
theorem mapMatrix_toMonoidHom_apply (δ : Matrix (Fin 2) (Fin 2) ℚ_[p]) (i j : Fin 2) :
    ((RingHom.mapMatrix ψ).toMonoidHom δ) i j = ψ (δ i j) :=
  rfl

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The lower-left entry of a member of the level has norm `≤ p⁻¹`. -/
theorem norm_apply_one_zero_le_of_mem_M1K (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ M1K ψ) : ‖g 1 0‖ ≤ (p : ℝ)⁻¹ := by
  obtain ⟨δ, hδ, rfl⟩ := hg
  rw [mapMatrix_toMonoidHom_apply, hψ]
  exact hδ.2.1

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The lower-right entry of a member of the level has norm `1`. -/
theorem norm_apply_one_one_of_mem_M1K (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ M1K ψ) : ‖g 1 1‖ = 1 := by
  obtain ⟨δ, hδ, rfl⟩ := hg
  rw [mapMatrix_toMonoidHom_apply, hψ]
  exact hδ.2.2.1

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The decay radius of the halo weight: `ρ = ‖T₀‖·√p` (`< 1` iff `‖T₀‖² < p⁻¹`). -/
def haloRho : ℝ := ‖T₀‖ * Real.sqrt p

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `0 ≤ ρ`. -/
theorem haloRho_nonneg : 0 ≤ haloRho (p := p) T₀ :=
  mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `ρ < 1` on the sub-annulus `‖T₀‖² < p⁻¹`. -/
theorem haloRho_lt_one (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) : haloRho (p := p) T₀ < 1 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  refine lt_of_pow_lt_pow_left₀ 2 zero_le_one ?_
  rw [one_pow, haloRho, mul_pow, Real.sq_sqrt hp0.le]
  calc ‖T₀‖ ^ 2 * (p : ℝ) < (p : ℝ)⁻¹ * (p : ℝ) := mul_lt_mul_of_pos_right h1 hp0
    _ = 1 := inv_mul_cancel₀ hp0.ne'

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `p⁻¹ ≤ ρ` on the halo `p⁻¹ < ‖T₀‖` (`√p ≥ 1`). -/
theorem inv_le_haloRho (h0 : (p : ℝ)⁻¹ < ‖T₀‖) : (p : ℝ)⁻¹ ≤ haloRho (p := p) T₀ := by
  have h1p : 1 ≤ Real.sqrt (p : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hp.out.one_le)
  calc (p : ℝ)⁻¹ ≤ ‖T₀‖ := h0.le
    _ = ‖T₀‖ * 1 := (mul_one _).symm
    _ ≤ ‖T₀‖ * Real.sqrt (p : ℝ) := mul_le_mul_of_nonneg_left h1p (norm_nonneg _)

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The level bounds of `M1K` at the radius `ρ`: integral entries, `‖c‖ ≤ p⁻¹ ≤ ρ`, `d` a
unit. -/
theorem levelBounds_M1K (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) : LevelBounds (M1K ψ) (haloRho (p := p) T₀) where
  rho_nonneg := haloRho_nonneg T₀
  rho_lt_one := haloRho_lt_one T₀ h1
  integral := by
    rintro g ⟨δ, hδ, rfl⟩ i j
    rw [mapMatrix_toMonoidHom_apply, hψ]
    exact hδ.1 i j
  c_le hg := (norm_apply_one_zero_le_of_mem_M1K ψ hψ hg).trans (inv_le_haloRho T₀ h0)
  d_unit hg := norm_apply_one_one_of_mem_M1K ψ hψ hg

omit [CompleteSpace K] [CharZero K] in
/-- The values `cz + d` of the level lie in the halo units. -/
theorem mem_haloUnits_of_mem_M1K (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ M1K ψ) {z : K} (hz : ‖z‖ ≤ 1) (hu : IsUnit (g 1 0 * z + g 1 1)) :
    hu.unit ∈ haloUnits ψ := by
  obtain ⟨δ, hδ, rfl⟩ := hg
  obtain ⟨d, hd⟩ : ∃ d : ℤ_[p], (d : ℚ_[p]) = δ 1 1 := ⟨⟨δ 1 1, hδ.1 1 1⟩, rfl⟩
  have hdu : IsUnit d := PadicInt.isUnit_iff.mpr (by rw [PadicInt.norm_def, hd]; exact hδ.2.2.1)
  refine ⟨hdu.unit, ?_, ?_⟩
  · rw [IsUnit.unit_spec, hd, hψ]
    exact hδ.2.2.1
  · rw [IsUnit.unit_spec, IsUnit.unit_spec, hd, mapMatrix_toMonoidHom_apply,
      mapMatrix_toMonoidHom_apply, add_sub_cancel_right, norm_mul, hψ]
    calc ‖δ 1 0‖ * ‖z‖ ≤ ‖δ 1 0‖ * 1 := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ ≤ (p : ℝ)⁻¹ := by rw [mul_one]; exact hδ.2.1

end Level

section Expansion

variable (ψ : ℚ_[p] →+* K) (T₀ : K) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)

omit [CompleteSpace K] [CharZero K] in
/-- Geometric coefficient bounds are stable under products of power series (ultrametric). -/
theorem norm_coeff_mul_le {f g : PowerSeries K} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hf : ∀ m, ‖PowerSeries.coeff m f‖ ≤ ρ ^ m) (hg : ∀ m, ‖PowerSeries.coeff m g‖ ≤ ρ ^ m)
    (m : ℕ) : ‖PowerSeries.coeff m (f * g)‖ ≤ ρ ^ m := by
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  rw [norm_mul, ← hij, pow_add]
  exact mul_le_mul (hf _) (hg _) (norm_nonneg _) (by positivity)

/-- **The halo binomial coefficients decay like `ρ^m`**: `‖C(s, m)·w^m‖ ≤ (‖T₀‖√p)^m` for
`‖w‖ ≤ p⁻¹` (`‖C(s,m)‖ ≤ ‖s‖^m‖m!‖⁻¹`, `‖s‖‖w‖ ≤ ‖T₀‖`, `‖m!‖⁻¹ ≤ √p^{m−1}`). -/
theorem norm_choose_haloExponent_mul_pow_le (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) {w : K} (hw : ‖w‖ ≤ (p : ℝ)⁻¹)
    (m : ℕ) :
    ‖Ring.choose (haloExponent (p := p) T₀) m * w ^ m‖ ≤ haloRho (p := p) T₀ ^ m := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by
    rw [norm_natCast_p ψ hψ]
    exact inv_lt_one_p
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  have hsq : Real.sqrt (‖((p : ℕ) : K)‖⁻¹) = Real.sqrt (p : ℝ) := by
    rw [norm_natCast_p ψ hψ, inv_inv]
  have h1q : 1 ≤ Real.sqrt (p : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hp.out.one_le)
  have hmax : max ‖w‖ (‖haloExponent (p := p) T₀‖ * ‖w‖) ≤ ‖T₀‖ := by
    refine max_le (hw.trans h0.le) ?_
    rw [norm_haloExponent ψ T₀ hp2 hψ h1]
    calc (p : ℝ) * ‖T₀‖ * ‖w‖ ≤ (p : ℝ) * ‖T₀‖ * (p : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hw (by positivity)
      _ = ‖T₀‖ := by rw [mul_right_comm, mul_inv_cancel₀ hp0.ne', one_mul]
  calc ‖Ring.choose (haloExponent (p := p) T₀) m * w ^ m‖
      ≤ max ‖w‖ (‖haloExponent (p := p) T₀‖ * ‖w‖) ^ m * ‖((m ! : ℕ) : K)‖⁻¹ :=
        PadicExpLog.norm_choose_mul_pow_le _ _ m
    _ ≤ ‖T₀‖ ^ m * Real.sqrt (p : ℝ) ^ m := by
        refine mul_le_mul (pow_le_pow_left₀ (le_max_of_le_left (norm_nonneg w)) hmax m) ?_
          (by positivity) (by positivity)
        refine (PadicExpLog.norm_factorial_inv_le h3 hp2 hm.ne').trans ?_
        rw [hsq]
        exact pow_le_pow_right₀ h1q (Nat.sub_le m 1)
    _ = haloRho (p := p) T₀ ^ m := by rw [haloRho, mul_pow]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The coefficients `d, c, 0, 0, …` of `cz + d` on the level are bounded by `ρ^n`. -/
theorem norm_coeff_linX_le (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    {g : Matrix (Fin 2) (Fin 2) K} (hg : g ∈ M1K ψ) (n : ℕ) :
    ‖PowerSeries.coeff n (PowerSeries.C (g 1 1) + PowerSeries.C (g 1 0) * PowerSeries.X)‖
      ≤ haloRho (p := p) T₀ ^ n := by
  rw [map_add, PowerSeries.coeff_C, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
  rcases n with _ | _ | n
  · rw [if_pos rfl, if_neg (by omega), mul_zero, add_zero, pow_zero,
      norm_apply_one_one_of_mem_M1K ψ hψ hg]
  · rw [if_neg (by omega), if_pos (by omega), mul_one, zero_add, pow_one]
    exact (norm_apply_one_zero_le_of_mem_M1K ψ hψ hg).trans (inv_le_haloRho T₀ h0)
  · rw [if_neg (by omega), if_neg (by omega), mul_zero, add_zero, norm_zero]
    exact pow_nonneg (haloRho_nonneg T₀) _

/-- **The column of the halo weight**: the expansion of `(cz+d)²·κ_{T₀}(cz + d)` in `z`,
`(cz+d)²·κ_{T₀}(d)·∑_m C(s, m)(c/d)^m z^m` (`κ_{T₀}(cz+d) = κ_{T₀}(d)·(1 + (c/d)z)^s`). -/
def haloCol (c d : K) : PowerSeries K :=
  (PowerSeries.C d + PowerSeries.C c * PowerSeries.X) ^ 2
    * PowerSeries.C (haloCharFun ψ T₀ ω d)
    * PowerSeries.mk fun m => Ring.choose (haloExponent (p := p) T₀) m * (c / d) ^ m

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The `1`-units `1 + wz`, `‖w‖ ≤ p⁻¹`, `‖z‖ ≤ 1`, of the level. -/
theorem norm_div_mul_le_of_mem_M1K (hψ : ∀ x, ‖ψ x‖ = ‖x‖) {g : Matrix (Fin 2) (Fin 2) K}
    (hg : g ∈ M1K ψ) {z : K} (hz : ‖z‖ ≤ 1) : ‖g 1 0 / g 1 1 * z‖ ≤ (p : ℝ)⁻¹ := by
  rw [norm_mul, norm_div, norm_apply_one_one_of_mem_M1K ψ hψ hg, div_one]
  exact (mul_le_of_le_one_right (norm_nonneg _) hz).trans
    (norm_apply_one_zero_le_of_mem_M1K ψ hψ hg)

/-- **Row decay** `‖coeff_m‖ ≤ ρ^m` on the level: `‖C(s, m)(c/d)^m‖ ≤ (p‖T₀‖)^m·p^{(m−1)/2}·p^{−m}
≤ (‖T₀‖√p)^m`, and multiplying by `(cz+d)²` (coefficients `d², 2cd, c²`) keeps the bound
since `p⁻¹ ≤ ρ`. -/
theorem norm_coeff_haloCol_le (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) {g : Matrix (Fin 2) (Fin 2) K} (hg : g ∈ M1K ψ) (m : ℕ) :
    ‖PowerSeries.coeff m (haloCol ψ T₀ ω (g 1 0) (g 1 1))‖ ≤ haloRho (p := p) T₀ ^ m := by
  have hρ0 := haloRho_nonneg (p := p) T₀
  have hd0 : g 1 1 ≠ 0 := (levelBounds_M1K ψ T₀ hψ h0 h1).d_ne_zero hg
  have hu0 : IsUnit (g 1 0 * 0 + g 1 1) := by
    rw [mul_zero, zero_add]
    exact hd0.isUnit
  obtain ⟨r, hr, -⟩ := exists_unique_teichRes_of_mem_haloUnits ψ hψ
    (mem_haloUnits_of_mem_M1K ψ hψ hg (z := 0) (by rw [norm_zero]; exact zero_le_one) hu0)
  rw [IsUnit.unit_spec, mul_zero, zero_add] at hr
  have hχ : ‖haloCharFun ψ T₀ ω (g 1 1)‖ = 1 :=
    norm_haloCharFun_of_norm_sub_le ψ T₀ ω hp2 hψ h1 hr
  have hw : ‖g 1 0 / g 1 1‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_div, norm_apply_one_one_of_mem_M1K ψ hψ hg, div_one]
    exact norm_apply_one_zero_le_of_mem_M1K ψ hψ hg
  have hlin := norm_coeff_linX_le ψ T₀ hψ h0 hg
  have hlin2 : ∀ n, ‖PowerSeries.coeff n
      ((PowerSeries.C (g 1 1) + PowerSeries.C (g 1 0) * PowerSeries.X) ^ 2)‖
        ≤ haloRho (p := p) T₀ ^ n := fun n => by
    rw [sq]
    exact norm_coeff_mul_le hρ0 hlin hlin n
  have hC : ∀ n, ‖PowerSeries.coeff n (PowerSeries.C (haloCharFun ψ T₀ ω (g 1 1)))‖
      ≤ haloRho (p := p) T₀ ^ n := fun n => by
    rw [PowerSeries.coeff_C]
    split_ifs with hn
    · rw [hn, pow_zero, hχ]
    · rw [norm_zero]
      exact pow_nonneg hρ0 _
  have hmk : ∀ n, ‖PowerSeries.coeff n (PowerSeries.mk fun m =>
      Ring.choose (haloExponent (p := p) T₀) m * (g 1 0 / g 1 1) ^ m)‖
        ≤ haloRho (p := p) T₀ ^ n := fun n => by
    rw [PowerSeries.coeff_mk]
    exact norm_choose_haloExponent_mul_pow_le ψ T₀ hp2 hψ h0 h1 hw n
  unfold haloCol
  exact norm_coeff_mul_le hρ0 (norm_coeff_mul_le hρ0 hlin2 hC) hmk m

/-- **Evaluation of the binomial column**: `∑_m C(s, m)(wz)^m = κ_{T₀}(1 + wz)` for
`‖w‖ ≤ p⁻¹`, `‖z‖ ≤ 1` (the binomial theorem `hasSum_choose_mul_pow` and the residue disc of
`1`). -/
theorem evalAt_mk_choose_haloExponent (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) {w : K} (hw : ‖w‖ ≤ (p : ℝ)⁻¹) {z : K}
    (hz : ‖z‖ ≤ 1) :
    evalAt (PowerSeries.mk fun m => Ring.choose (haloExponent (p := p) T₀) m * w ^ m) z
      = haloCharFun ψ T₀ ω (1 + w * z) := by
  have h3 : ‖((p : ℕ) : K)‖ < 1 := by
    rw [norm_natCast_p ψ hψ]
    exact inv_lt_one_p
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hc : ‖T₀‖ ^ 2 < ‖((p : ℕ) : K)‖ := by
    rw [norm_natCast_p ψ hψ]
    exact h1
  have hwz : ‖w * z‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) hz).trans hw
  have hex : ‖haloExponent (p := p) T₀‖ * ‖w * z‖ ≤ ‖T₀‖ := by
    rw [norm_haloExponent ψ T₀ hp2 hψ h1]
    calc (p : ℝ) * ‖T₀‖ * ‖w * z‖ ≤ (p : ℝ) * ‖T₀‖ * (p : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left hwz (by positivity)
      _ = ‖T₀‖ := by rw [mul_right_comm, mul_inv_cancel₀ hp0, one_mul]
  have hterm : ∀ n, PowerSeries.coeff n (PowerSeries.mk fun m =>
      Ring.choose (haloExponent (p := p) T₀) m * w ^ m) * z ^ n
        = Ring.choose (haloExponent (p := p) T₀) n * (w * z) ^ n := fun n => by
    rw [PowerSeries.coeff_mk, mul_pow, mul_assoc]
  have hone : ‖(1 + w * z) - intHom ψ (teichRes (1 : (ZMod p)ˣ) : ℤ_[p])‖ ≤ (p : ℝ)⁻¹ := by
    rw [teichRes_one, Units.val_one, map_one, add_sub_cancel_left]
    exact hwz
  unfold evalAt
  simp_rw [hterm]
  rw [(PadicExpLog.hasSum_choose_mul_pow h3 hp2 hc (hwz.trans h0.le) hex).tsum_eq,
    haloCharFun_of_norm_sub_le ψ T₀ ω hψ hone]
  simp only [teichRes_one, map_one, Units.val_one, inv_one, mul_one, one_mul]

/-- `κ_{T₀}(d)·κ_{T₀}(1 + (c/d)z) = κ_{T₀}(cz + d)` on the level. -/
theorem haloCharFun_mul_one_add (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) {g : Matrix (Fin 2) (Fin 2) K} (hg : g ∈ M1K ψ) {z : K}
    (hz : ‖z‖ ≤ 1) :
    haloCharFun ψ T₀ ω (g 1 1) * haloCharFun ψ T₀ ω (1 + g 1 0 / g 1 1 * z)
      = haloCharFun ψ T₀ ω (g 1 0 * z + g 1 1) := by
  have hd0 : g 1 1 ≠ 0 := (levelBounds_M1K ψ T₀ hψ h0 h1).d_ne_zero hg
  have hwz := norm_div_mul_le_of_mem_M1K ψ hψ hg hz
  have h1u : 1 + g 1 0 / g 1 1 * z ≠ 0 := by
    intro h
    have := norm_eq_one_of_norm_sub_le (y := (1 : K)) norm_one
      (by rw [add_sub_cancel_left]; exact hwz)
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hu0 : IsUnit (g 1 0 * 0 + g 1 1) := by
    rw [mul_zero, zero_add]
    exact hd0.isUnit
  have hd : Units.mk0 (g 1 1) hd0 ∈ haloUnits ψ := by
    obtain ⟨a, ha1, ha⟩ := mem_haloUnits_of_mem_M1K ψ hψ hg (z := 0)
      (by rw [norm_zero]; exact zero_le_one) hu0
    rw [IsUnit.unit_spec, mul_zero, zero_add] at ha
    exact ⟨a, ha1, ha⟩
  have hone : Units.mk0 (1 + g 1 0 / g 1 1 * z) h1u ∈ haloUnits ψ := by
    refine ⟨1, by simp, ?_⟩
    rw [Units.val_mk0, Units.val_one, PadicInt.coe_one, map_one, add_sub_cancel_left]
    exact hwz
  have hmul := haloCharFun_mul ψ T₀ ω hp2 hψ h0 h1 hd hone
  rw [Units.val_mul, Units.val_mk0, Units.val_mk0] at hmul
  rw [← hmul]
  congr 1
  rw [mul_add, mul_one, div_eq_mul_inv, mul_right_comm (g 1 0) (g 1 1)⁻¹ z,
    mul_left_comm (g 1 1) (g 1 0 * z) (g 1 1)⁻¹, mul_inv_cancel₀ hd0, mul_one, add_comm]

/-- **Evaluation of the column**: `haloCol(c, d)(z) = (cz+d)²·κ_{T₀}(cz + d)` on the closed
unit ball (the binomial theorem `∑ C(s,m)(wz)^m = exp(s·log(1 + wz))`, `w = c/d`, and
multiplicativity `κ_{T₀}(d)·κ_{T₀}(1 + wz) = κ_{T₀}(cz + d)`). -/
theorem evalAt_haloCol (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) {g : Matrix (Fin 2) (Fin 2) K} (hg : g ∈ M1K ψ) {z : K}
    (hz : ‖z‖ ≤ 1) :
    evalAt (haloCol ψ T₀ ω (g 1 0) (g 1 1)) z
      = (g 1 0 * z + g 1 1) ^ 2 * haloCharFun ψ T₀ ω (g 1 0 * z + g 1 1) := by
  have hw : ‖g 1 0 / g 1 1‖ ≤ (p : ℝ)⁻¹ := by
    rw [norm_div, norm_apply_one_one_of_mem_M1K ψ hψ hg, div_one]
    exact norm_apply_one_zero_le_of_mem_M1K ψ hψ hg
  have hmk : PowerSeries.AbsSummable (PowerSeries.mk fun m =>
      Ring.choose (haloExponent (p := p) T₀) m * (g 1 0 / g 1 1) ^ m) := by
    unfold PowerSeries.AbsSummable
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (summable_geometric_of_lt_one (haloRho_nonneg T₀) (haloRho_lt_one T₀ h1))
    rw [PowerSeries.coeff_mk]
    exact norm_choose_haloExponent_mul_pow_le ψ T₀ hp2 hψ h0 h1 hw n
  change evalAt (linX g ^ 2 * PowerSeries.C (haloCharFun ψ T₀ ω (g 1 1))
    * PowerSeries.mk fun m => Ring.choose (haloExponent (p := p) T₀) m * (g 1 0 / g 1 1) ^ m) z
    = _
  rw [evalAt_mul (PowerSeries.absSummable_mul
      (PowerSeries.absSummable_pow (WeightSeries.absSummable_linX g) 2)
      (PowerSeries.absSummable_C _)) hmk hz,
    evalAt_mul (PowerSeries.absSummable_pow (WeightSeries.absSummable_linX g) 2)
      (PowerSeries.absSummable_C _) hz,
    evalAt_pow (WeightSeries.absSummable_linX g) hz, evalAt_linX g hz, evalAt_C,
    evalAt_mk_choose_haloExponent ψ T₀ ω hp2 hψ h0 h1 hw hz, mul_assoc,
    haloCharFun_mul_one_add ψ T₀ ω hp2 hψ h0 h1 hg hz]

/-- **The expansion datum of the halo weight** ([Jacobs, Def 1.27] for `κ = (·)²·κ_{T₀}`). -/
def haloExpansion (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) :
    ExpansionData (M1K ψ) (haloRho (p := p) T₀) (haloUnits ψ) (haloChar ψ T₀ ω hp2 hψ h0 h1) where
  bounds := levelBounds_M1K ψ T₀ hψ h0 h1
  col := haloCol ψ T₀ ω
  rowDecay hg m := norm_coeff_haloCol_le ψ T₀ ω hp2 hψ h0 h1 hg m
  mem_level hg z hz hu := mem_haloUnits_of_mem_M1K ψ hψ hg hz hu
  eval hg z hz hu := by
    rw [coe_haloChar_apply]
    exact evalAt_haloCol ψ T₀ ω hp2 hψ h0 h1 hg hz

/-- **The halo weight** `κ_{T₀}` (normalised) as an `AnalyticWeight` on the halo units, at
the level `M1K`, radius `‖T₀‖·√p` — the weight at which `QMF.Weight.Forms` is
[LWX]'s `S^{D,†,1}_{[−]_{T₀}}`. -/
def haloWeight (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) :
    AnalyticWeight (haloUnits ψ) (M1K ψ) (haloRho (p := p) T₀) :=
  ⟨haloChar ψ T₀ ω hp2 hψ h0 h1, haloExpansion ψ T₀ ω hp2 hψ h0 h1⟩

/-- **The automorphy factor of the halo weight** is [LWX, (2.3.2)]'s `χ(cz + d)`, as a series:
`col·(cz+d)^{−2} = κ_{T₀}(d)·∑_m C(s, m)(c/d)^m z^m`. -/
theorem autFactor_haloWeight (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (h0 : (p : ℝ)⁻¹ < ‖T₀‖)
    (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) (g : M1K ψ) :
    (haloWeight ψ T₀ ω hp2 hψ h0 h1).toWeightSeries.autFactor g.1
      = PowerSeries.C (haloCharFun ψ T₀ ω (g.1 1 1))
        * PowerSeries.mk fun m => Ring.choose (haloExponent (p := p) T₀) m
            * (g.1 1 0 / g.1 1 1) ^ m := by
  have hd0 : g.1 1 1 ≠ 0 := (levelBounds_M1K ψ T₀ hψ h0 h1).d_ne_zero g.2
  have hinv : linX g.1 * (linX g.1)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_linX]; exact hd0)
  have key : ∀ A B : PowerSeries K, linX g.1 ^ 2 * A * B * ((linX g.1)⁻¹) ^ 2 = A * B := by
    intro A B
    rw [show linX g.1 ^ 2 * A * B * ((linX g.1)⁻¹) ^ 2 = A * B * (linX g.1 * (linX g.1)⁻¹) ^ 2
      by ring, hinv, one_pow, mul_one]
  exact key _ _

/-- **The automorphy factor evaluates to `κ_{T₀}(cz + d)`** on the closed unit ball. -/
theorem evalAt_autFactor_haloWeight (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹) (g : M1K ψ) {z : K} (hz : ‖z‖ ≤ 1) :
    evalAt ((haloWeight ψ T₀ ω hp2 hψ h0 h1).toWeightSeries.autFactor g.1) z
      = haloCharFun ψ T₀ ω (g.1 1 0 * z + g.1 1 1) := by
  have hB := levelBounds_M1K ψ T₀ hψ h0 h1
  have hd0 : g.1 1 1 ≠ 0 := hB.d_ne_zero g.2
  have hlt : ‖g.1 1 0‖ < ‖g.1 1 1‖ := by
    rw [hB.d_unit g.2]
    exact (hB.c_le g.2).trans_lt (haloRho_lt_one T₀ h1)
  have hne : g.1 1 0 * z + g.1 1 1 ≠ 0 := by
    intro h
    have := norm_eq_one_of_norm_sub_le (hB.d_unit g.2) (x := g.1 1 0 * z + g.1 1 1) (by
      rw [add_sub_cancel_right, norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) hz).trans
        (norm_apply_one_zero_le_of_mem_M1K ψ hψ g.2))
    rw [h, norm_zero] at this
    exact zero_ne_one this
  change evalAt ((haloWeight ψ T₀ ω hp2 hψ h0 h1).toWeightSeries.col (g.1 1 0) (g.1 1 1)
    * ((linX g.1)⁻¹) ^ 2) z = _
  rw [evalAt_mul ((haloWeight ψ T₀ ω hp2 hψ h0 h1).toWeightSeries.absSummable g.2)
      (PowerSeries.absSummable_pow (WeightSeries.absSummable_linX_inv hd0 hlt) 2) hz,
    evalAt_pow (WeightSeries.absSummable_linX_inv hd0 hlt) hz, evalAt_linX_inv hd0 hlt hz]
  change evalAt (haloCol ψ T₀ ω (g.1 1 0) (g.1 1 1)) z * _ = _
  rw [evalAt_haloCol ψ T₀ ω hp2 hψ h0 h1 g.2 hz, mul_right_comm, ← mul_pow,
    mul_inv_cancel₀ hne, one_pow, one_mul]

end Expansion

end LWX

end
