/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.SeamH
import PhD.LWX.Quaternionic

/-!
# `S^{D,†,m}` and [LWX, Prop 2.17] for a definite quaternion algebra over `ℚ` — SKELETON

[LWX, §2.4–2.7] for `D/ℚ` split at `p`, at every analyticity level `m = h + 1`.  Unlike the
`m = 1` seam (`PhD/LWX/Quaternionic.lean`), the disc model is built directly on the **integral**
component map `thetaInt : (D ⊗ 𝔸_f)ˣ →* M₂(ℚ_p)` — the disc action of `PhD/LWX/DiscModel.lean`
takes `M₁`-matrices over `ℚ_p`, so no comparison with `K_p`-matrices is needed on the level side;
the field `K_p` enters only through the coefficients `ψ = E : ℚ_p ≃ K_p`.

The upshot is the spectral reading of [LWX, Def 2.13] at **every** point of the boundary annulus
`p⁻¹ < ‖T₀‖ < 1`: the zeros of the integral characteristic series `Char(P)(T₀)` are exactly the
reciprocal `U_p`-eigenvalues on `S^{D,†,m}_{[−]_{T₀}}(U)` for any (equivalently, some) level `m`
at which the halo character is `m`-locally analytic.

## Main declarations

* `LWX.DiscFormsQ`, `LWX.discHeckeUpQ` — `S^{D,†,m}` for `D/ℚ` and its `U_p`.
* **`LWX.specCharSeries_ofCerts_eq_discHeckeCharPowerSeriesQ`** — [LWX, Prop 2.17] for `D/ℚ` at
  level `m`.
* **`LWX.evalT_specCharSeries_eq_zero_iff_disc`** — the spectral reading at a halo point.
* `LWX.exists_level_evalT_specCharSeries_eq_zero_iff` — the spectral reading at *every* halo
  point.
-/

open IsDedekindDomain NumberField QMF QMF.Weight AbstractHeckeOperatorSlash TateFredholm

open scoped Pointwise TateFredholm

noncomputable section

namespace LWX

variable (p : ℕ) [hp : Fact p.Prime]

section Quaternion

variable (D : Type*) [Ring D] [Algebra ℚ D] [RigidificationAt ℚ D (padicPlace p)]
variable (h : ℕ) (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {T₀ : Kp p}
  (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹)
variable (U : Subgroup (Dfx ℚ D)) (hU : (U : Set (Dfx ℚ D)) ⊆ levelM1 (p := p) (thetaInt p D))

/-- **`S^{D,†,m}_{[−]_{T₀}}(U)` for `D/ℚ`** ([LWX, §2.4], `m = h + 1`), at the level-`h` halo
weight. -/
abbrev DiscFormsQ :
    Submodule (Kp p) (AutomorphicFunction (Dfx ℚ D) (globalUnits ℚ D)
      c(ZMod (p ^ h) × ℕ, Kp p)) :=
  DiscForms (Γ := globalUnits ℚ D) (thetaInt p D) h (padicComparison p)
    (haloWeightH h (padicComparison p) T₀ ω hp2 (norm_padicComparison p) h0 h1 hT) U hU

/-- **`U_p` on `S^{D,†,m}` for `D/ℚ`** ([LWX, (2.5.1)]). -/
def discHeckeUpQ
    (hfin : (((Quotient.mk'' : Dfx ℚ D → RightCosets U) ''
          (({etaAdelic' ℚ D (padicPlace p) ((p : ℕ) : Kp p) (natCast_p_ne_zero p)} :
            Set (Dfx ℚ D)) * (U : Set (Dfx ℚ D)))) : Set (RightCosets U)).Finite) :
    DiscFormsQ p D h hp2 ω h0 h1 hT U hU →ₗ[Kp p] DiscFormsQ p D h hp2 ω h0 h1 hT U hU :=
  discHeckeOperator (Γ := globalUnits ℚ D) (thetaInt p D) h (padicComparison p) _ U hU
    (etaAdelic'_mem_levelM1 p D) hfin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **[LWX, Proposition 2.17] for `D/ℚ` at analyticity level `m = h + 1`**: the specialised
integral characteristic series of the certificate datum of `U_p` is the Fredholm determinant of
`U_p` on `S^{D,†,m}_{[−]_{T₀}}(U)`. -/
theorem specCharSeries_ofCerts_eq_discHeckeCharPowerSeriesQ
    (vRep : Fin p → Dfx ℚ D) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) (thetaInt p D))
    (idx : ι → Fin p → ι) (u : ι → Fin p → U)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 (thetaInt p D) U hU vRep hvΔ u i t)).IsUpShape) :
    specCharSeries (UpDatum.ofCerts (thetaInt p D) U hU vRep hvΔ idx u hshape) ω
        (intHom (padicComparison p)) T₀
      = discHeckeCharPowerSeries (thetaInt p D) h (padicComparison p)
          (haloWeightH h (padicComparison p) T₀ ω hp2 (norm_padicComparison p) h0 h1 hT) U hU
          vRep hvΔ idx u :=
  specCharSeries_ofCerts_eq_discHeckeCharPowerSeries (padicComparison p)
    (norm_padicComparison p) T₀ ω h (thetaInt p D) U hU vRep hvΔ idx u hp2 h0 h1 hT hshape

/-- **The spectral reading of [LWX, Def 2.13] at a halo point, at analyticity level `m = h + 1`**
(neat level): for `a ≠ 0`, `Char(P)(T₀)(a) = 0` iff `a⁻¹` is a `U_p`-eigenvalue on
`S^{D,†,m}_{[−]_{T₀}}(U)`. -/
theorem evalT_specCharSeries_eq_zero_iff_disc
    (hfin : (((Quotient.mk'' : Dfx ℚ D → RightCosets U) ''
          (({etaAdelic' ℚ D (padicPlace p) ((p : ℕ) : Kp p) (natCast_p_ne_zero p)} :
            Set (Dfx ℚ D)) * (U : Set (Dfx ℚ D)))) : Set (RightCosets U)).Finite)
    (c : ι → Dfx ℚ D)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) :
        DoubleCoset.Quotient ((globalUnits ℚ D : Subgroup (Dfx ℚ D)) : Set (Dfx ℚ D))
          (U : Set (Dfx ℚ D)))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash (globalUnits ℚ D) U (c i) = ⊥)
    (vRep : Fin p → Dfx ℚ D) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) (thetaInt p D))
    (hv : Set.BijOn (Quotient.mk'' : Dfx ℚ D → RightCosets U) (Set.range vRep)
      (((Quotient.mk'' : Dfx ℚ D → RightCosets U) ''
        (({etaAdelic' ℚ D (padicPlace p) ((p : ℕ) : Kp p) (natCast_p_ne_zero p)} :
          Set (Dfx ℚ D)) * (U : Set (Dfx ℚ D)))) : Set (RightCosets U)))
    (hvinj : Function.Injective vRep)
    (idx : ι → Fin p → ι) (d : ι → Fin p → Dfx ℚ D) (hd : ∀ i t, d i t ∈ globalUnits ℚ D)
    (u : ι → Fin p → U)
    (hfact : ∀ i t, c i * (vRep t)⁻¹ = d i t * c (idx i t) * (u i t : Dfx ℚ D))
    {a : Kp p} (ha0 : a ≠ 0) :
    PowerSeries.evalT a
        (specCharSeries (UpDatum.ofCerts (thetaInt p D) U hU vRep hvΔ idx u
            (isUpShape_certM1 (thetaInt p D) U hU vRep hvΔ u (etaAdelic'_mem_levelM1 p D)
              (norm_thetaInt_etaAdelic'_zero_zero p D) hv)) ω
          (intHom (padicComparison p)) T₀) = 0 ↔
      ∃ φ : DiscFormsQ p D h hp2 ω h0 h1 hT U hU,
        φ ≠ 0 ∧ discHeckeUpQ p D h hp2 ω h0 h1 hT U hU hfin φ = a⁻¹ • φ := by
  rw [specCharSeries_ofCerts_eq_discHeckeCharPowerSeriesQ p D h hp2 ω h0 h1 hT U hU vRep hvΔ
    idx u (isUpShape_certM1 (thetaInt p D) U hU vRep hvΔ u (etaAdelic'_mem_levelM1 p D)
      (norm_thetaInt_etaAdelic'_zero_zero p D) hv)]
  exact evalT_discHeckeCharPowerSeries_eq_zero_iff (thetaInt p D) h (padicComparison p)
    (haloWeightH h (padicComparison p) T₀ ω hp2 (norm_padicComparison p) h0 h1 hT) U hU
    vRep hvΔ idx u (haloRhoH_nonneg h T₀)
    (max_lt (haloRhoH_lt_one h T₀ hT) inv_lt_one_p)
    (isUpShape_certM1 (thetaInt p D) U hU vRep hvΔ u (etaAdelic'_mem_levelM1 p D)
      (norm_thetaInt_etaAdelic'_zero_zero p D) hv)
    c hc hstab (etaAdelic'_mem_levelM1 p D) hfin hv hvinj d hd hfact ha0

end Quaternion

section EveryPoint

variable (D : Type*) [Ring D] [Algebra ℚ D] [RigidificationAt ℚ D (padicPlace p)]
variable (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {T₀ : Kp p}
  (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1)
variable (U : Subgroup (Dfx ℚ D)) (hU : (U : Set (Dfx ℚ D)) ⊆ levelM1 (p := p) (thetaInt p D))
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The spectral reading at *every* point of the boundary annulus** — the statement the `m = 1`
seam could not reach ([LWX, §2.7]: the halo character is `m`-locally analytic for `m` large
enough; `exists_sq_norm_pow_prime_pow_sub_one_lt`).  For every halo point `p⁻¹ < ‖T₀‖ < 1` there
is an analyticity level `m = h + 1` at which the zeros of `Char(P)(T₀)` are exactly the
reciprocal `U_p`-eigenvalues on `S^{D,†,m}_{[−]_{T₀}}(U)`. -/
theorem exists_level_evalT_specCharSeries_eq_zero_iff
    (hfin : (((Quotient.mk'' : Dfx ℚ D → RightCosets U) ''
          (({etaAdelic' ℚ D (padicPlace p) ((p : ℕ) : Kp p) (natCast_p_ne_zero p)} :
            Set (Dfx ℚ D)) * (U : Set (Dfx ℚ D)))) : Set (RightCosets U)).Finite)
    (c : ι → Dfx ℚ D)
    (hc : Function.Bijective
      (fun i => (Quotient.mk'' (c i) :
        DoubleCoset.Quotient ((globalUnits ℚ D : Subgroup (Dfx ℚ D)) : Set (Dfx ℚ D))
          (U : Set (Dfx ℚ D)))))
    (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash (globalUnits ℚ D) U (c i) = ⊥)
    (vRep : Fin p → Dfx ℚ D) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) (thetaInt p D))
    (hv : Set.BijOn (Quotient.mk'' : Dfx ℚ D → RightCosets U) (Set.range vRep)
      (((Quotient.mk'' : Dfx ℚ D → RightCosets U) ''
        (({etaAdelic' ℚ D (padicPlace p) ((p : ℕ) : Kp p) (natCast_p_ne_zero p)} :
          Set (Dfx ℚ D)) * (U : Set (Dfx ℚ D)))) : Set (RightCosets U)))
    (hvinj : Function.Injective vRep)
    (idx : ι → Fin p → ι) (d : ι → Fin p → Dfx ℚ D) (hd : ∀ i t, d i t ∈ globalUnits ℚ D)
    (u : ι → Fin p → U)
    (hfact : ∀ i t, c i * (vRep t)⁻¹ = d i t * c (idx i t) * (u i t : Dfx ℚ D))
    {a : Kp p} (ha0 : a ≠ 0) :
    ∃ (h : ℕ) (hT : ‖TH p h T₀‖ ^ 2 < (p : ℝ)⁻¹),
      (PowerSeries.evalT a
          (specCharSeries (UpDatum.ofCerts (thetaInt p D) U hU vRep hvΔ idx u
              (isUpShape_certM1 (thetaInt p D) U hU vRep hvΔ u (etaAdelic'_mem_levelM1 p D)
                (norm_thetaInt_etaAdelic'_zero_zero p D) hv)) ω
            (intHom (padicComparison p)) T₀) = 0 ↔
        ∃ φ : DiscFormsQ p D h hp2 ω h0 h1 hT U hU,
          φ ≠ 0 ∧ discHeckeUpQ p D h hp2 ω h0 h1 hT U hU hfin φ = a⁻¹ • φ) := by
  have hpK : ‖((p : ℕ) : Kp p)‖ < 1 := by
    rw [norm_natCast_p (padicComparison p) (norm_padicComparison p)]
    exact inv_lt_one_p
  obtain ⟨h, hT⟩ := exists_sq_norm_pow_prime_pow_sub_one_lt (K := Kp p) hpK h1
  exact ⟨h, hT, evalT_specCharSeries_eq_zero_iff_disc p D h hp2 ω h0 h1 hT U hU hfin c hc hstab
    vRep hvΔ hv hvinj idx d hd u hfact ha0⟩

end EveryPoint

end LWX

end
