/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.LWX.«07_Seam»
import PhD.QMF.Weight.«07_Quaternionic»
import PhD.ForMathlib.NumberTheory.Padics.AdicCompletionEquiv

/-!
# The integral model for a definite quaternion algebra over `ℚ`

[LWX, §2.4]: "We fix a definite quaternion algebra `D` over `ℚ` which splits at `p`, and we
fix an isomorphism `D ⊗ ℚ_p ≃ M₂(ℚ_p)` … We fix the tame level structure `K^p` …"; [LWX, §2.5]:
`U_p` is the double coset `Iw_q (p 0; 0 1) Iw_q = ∐_j Iw_q v_j`, `v_j = (p 0; jq 1)`.

The general-weight layer's quaternionic instantiation (`PhD/QMF/Weight/07_Quaternionic.lean`)
works over a number field `F` at a place `v` with `K = F_v = v.adicCompletion F`; the integral
model of `PhD/LWX/04_IntegralModel.lean` needs `ℤ_p`-entries, i.e. `θ` valued in `M₂(ℚ_p)`.  At
`F = ℚ`, `v = (p)`, mathlib's comparison `Padic.adicCompletionEquiv : ℚ_[p] ≃A[ℚ] ℚ_v` (an
isometry, `PhD/ForMathlib/…/AdicCompletionEquiv.lean`) transports one to the other: with
`ψ = E : ℚ_p → K_p` and `θ = E⁻¹ ∘ toMatrix ℚ D v`, the `K`-side map `thetaK ψ θ` of
`PhD/LWX/07_Seam.lean` is literally `toMatrix ℚ D v`, so `IntForms θ … U` is [LWX]'s `S^D_int` at
the tame level `U` and the seam theorem lands on Buzzard's `S^D_κ(U) = FormsQ ℚ D v κ U`.

## Main declarations

* `LWX.padicPlace`, `LWX.Kp`, `LWX.padicComparison` — the place `(p)`, its completion, and the
  isometric comparison `ℚ_[p] →+* K_p`.
* `LWX.thetaInt`, `LWX.thetaK_thetaInt` — the integral component map and its `K`-side reading.
* `LWX.IntFormsQ`, `LWX.intHeckeUpQ` — `S^D_int` and its `U_p` for `D/ℚ`.
* **`LWX.specCharSeries_ofCerts_eq_heckeCharPowerSeriesQ`** — [LWX, Prop 2.17] for `D/ℚ`.
* **`LWX.evalT_specCharSeries_eq_zero_iff`** — the spectral reading ([LWX, Def 2.13] at a
  point): at a neat level, the zeros of `Char(P)(T₀)` are the reciprocal `U_p`-eigenvalues on
  `S^D_{κ_{T₀}}(U)`.
-/

open IsDedekindDomain NumberField QMF QMF.Weight AbstractHeckeOperatorSlash TateFredholm

open scoped Pointwise TateFredholm

noncomputable section

namespace LWX

variable (p : ℕ) [hp : Fact p.Prime]

/-- The place `(p)` of `ℚ`. -/
def padicPlace : HeightOneSpectrum (RingOfIntegers ℚ) :=
  (Rat.HeightOneSpectrum.primesEquiv (R := RingOfIntegers ℚ)).symm ⟨p, hp.out⟩

/-- The completion of `ℚ` at `(p)`. -/
abbrev Kp : Type := (padicPlace p).adicCompletion ℚ

attribute [local instance 2000] IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion in
instance : CharZero (Kp p) := charZero_of_injective_algebraMap (algebraMap ℚ (Kp p)).injective

/-- The comparison ring homomorphism `ℚ_[p] →+* K_p` (mathlib's `Padic.adicCompletionEquiv`). -/
def padicComparison : ℚ_[p] →+* Kp p :=
  RingHomClass.toRingHom (Padic.adicCompletionEquiv (RingOfIntegers ℚ) ⟨p, hp.out⟩)

/-- The inverse comparison `K_p →+* ℚ_[p]`. -/
def padicComparisonSymm : Kp p →+* ℚ_[p] :=
  RingHomClass.toRingHom (Padic.adicCompletionEquiv (RingOfIntegers ℚ) ⟨p, hp.out⟩).symm

/-- The inverse comparison is a left inverse of the comparison. -/
theorem padicComparisonSymm_comp :
    (padicComparisonSymm p).comp (padicComparison p) = RingHom.id ℚ_[p] :=
  RingHom.ext fun x =>
    (Padic.adicCompletionEquiv (RingOfIntegers ℚ) ⟨p, hp.out⟩).symm_apply_apply x

/-- The inverse comparison is a right inverse of the comparison. -/
theorem padicComparison_comp :
    (padicComparison p).comp (padicComparisonSymm p) = RingHom.id (Kp p) :=
  RingHom.ext fun x =>
    (Padic.adicCompletionEquiv (RingOfIntegers ℚ) ⟨p, hp.out⟩).apply_symm_apply x

/-- **The comparison is an isometry** (`Padic.norm_adicCompletionEquiv`). -/
theorem norm_padicComparison (y : ℚ_[p]) : ‖padicComparison p y‖ = ‖y‖ :=
  Padic.norm_adicCompletionEquiv ⟨p, hp.out⟩ y

/-- `‖p‖ = p⁻¹` in `K_p`. -/
theorem norm_natCast_p_Kp : ‖((p : ℕ) : Kp p)‖ = (p : ℝ)⁻¹ := by
  rw [show ((p : ℕ) : Kp p) = padicComparison p ((p : ℕ) : ℚ_[p]) from (map_natCast _ _).symm,
    norm_padicComparison, Padic.norm_p]

/-- `p` is a nonzero integral element of `K_p`. -/
theorem valued_natCast_p_le_one : Valued.v ((p : ℕ) : Kp p) ≤ 1 := by
  rw [← Valued.toNormedField.norm_le_one_iff, norm_natCast_p_Kp]
  exact inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)

theorem natCast_p_ne_zero : ((p : ℕ) : Kp p) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero

section Quaternion

variable (D : Type*) [Ring D] [Algebra ℚ D] [RigidificationAt ℚ D (padicPlace p)]

/-- **The integral component map** `(D ⊗ 𝔸_f)ˣ →* M₂(ℚ_p)`: the `v`-component through the
rigidification, read back in `ℚ_p` by the comparison. -/
def thetaInt : Dfx ℚ D →* Matrix (Fin 2) (Fin 2) ℚ_[p] :=
  (RingHom.mapMatrix (padicComparisonSymm p)).toMonoidHom.comp (toMatrix ℚ D (padicPlace p))

/-- The `K`-side reading of the integral component map is the rigidification's `toMatrix`. -/
theorem thetaK_thetaInt :
    thetaK (padicComparison p) (thetaInt p D) = toMatrix ℚ D (padicPlace p) :=
  MonoidHom.ext fun _ => Matrix.ext fun _ _ =>
    (Padic.adicCompletionEquiv (RingOfIntegers ℚ) ⟨p, hp.out⟩).apply_symm_apply _

/-- **`S^D_int` for `D/ℚ`** ([LWX, §2.7]) at the tame level `U` (an open compact subgroup with
`θ(U) ⊆ M₁`, i.e. `U = K^p·Iw_p`). -/
abbrev IntFormsQ (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (U : Subgroup (Dfx ℚ D))
    (hU : (U : Set (Dfx ℚ D)) ⊆ levelM1 (p := p) (thetaInt p D)) :=
  IntForms (Γ := globalUnits ℚ D) (thetaInt p D) hp2 ω U hU

/-- The level condition on the `K`-side: `U` has wild level `≥ M1K`. -/
theorem subset_levelMonoidOf_toMatrix (U : Subgroup (Dfx ℚ D))
    (hU : (U : Set (Dfx ℚ D)) ⊆ levelM1 (p := p) (thetaInt p D)) :
    (U : Set (Dfx ℚ D))
      ⊆ levelMonoidOf (toMatrix ℚ D (padicPlace p)) (M1K (padicComparison p)) := by
  rw [← thetaK_thetaInt]
  exact subset_levelMonoidOf_thetaK _ _ U hU

/-- The integral matrix of `η` is `(p 0; 0 1)`. -/
theorem thetaInt_etaAdelic' :
    thetaInt p D (etaAdelic' ℚ D (padicPlace p) ((p : ℕ) : Kp p) (natCast_p_ne_zero p))
      = !![(p : ℚ_[p]), 0; 0, 1] := by
  have h := toMatrix_etaAdelic' ℚ D (padicPlace p)
    ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    (by decide) ((p : ℕ) : Kp p) (valued_natCast_p_le_one p) (natCast_p_ne_zero p)
  change (RingHom.mapMatrix (padicComparisonSymm p)) (toMatrix ℚ D (padicPlace p) _) = _
  rw [h]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Sigma0'.eta]

/-- [LWX, §2.5]'s `η = (p 0; 0 1)` lies in the integral level monoid. -/
theorem etaAdelic'_mem_levelM1 :
    etaAdelic' ℚ D (padicPlace p) ((p : ℕ) : Kp p) (natCast_p_ne_zero p)
      ∈ levelM1 (p := p) (thetaInt p D) := by
  change thetaInt p D _ ∈ M1 p
  rw [thetaInt_etaAdelic']
  have hp1 : ((p : ℝ))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp.out.one_le)
  refine ⟨fun i j => ?_, ?_, ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [Padic.norm_p, hp1]
  · simp
  · simp
  · simp [Matrix.det_fin_two_of, hp.out.ne_zero]

/-- `‖η₀₀‖ = ‖p‖ ≤ p⁻¹` — the shape input of `isUpShape_certM1`. -/
theorem norm_thetaInt_etaAdelic'_zero_zero :
    ‖thetaInt p D (etaAdelic' ℚ D (padicPlace p) ((p : ℕ) : Kp p) (natCast_p_ne_zero p)) 0 0‖
      ≤ (p : ℝ)⁻¹ := by
  rw [thetaInt_etaAdelic']
  simp [Padic.norm_p]

/-- **`U_p` on `S^D_int` for `D/ℚ`** ([LWX, (2.5.1)]). -/
def intHeckeUpQ (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (U : Subgroup (Dfx ℚ D))
    (hU : (U : Set (Dfx ℚ D)) ⊆ levelM1 (p := p) (thetaInt p D))
    (h : (((Quotient.mk'' : Dfx ℚ D → RightCosets U) ''
          (({etaAdelic' ℚ D (padicPlace p) ((p : ℕ) : Kp p) (natCast_p_ne_zero p)} :
            Set (Dfx ℚ D)) * (U : Set (Dfx ℚ D)))) : Set (RightCosets U)).Finite) :
    IntFormsQ p D hp2 ω U hU →ₗ[HaloInt p] IntFormsQ p D hp2 ω U hU :=
  intHeckeOperator (thetaInt p D) U hU hp2 ω (etaAdelic'_mem_levelM1 p D) h

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **[LWX, Proposition 2.17] for `D/ℚ`** (at `m = 1`, on the sub-annulus): the specialised
integral characteristic series of the certificate datum of `U_p` is the Fredholm determinant of
`U_p` on Buzzard's `S^D_κ(U)` at the halo weight. -/
theorem specCharSeries_ofCerts_eq_heckeCharPowerSeriesQ (hp2 : p ≠ 2)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {T₀ : Kp p} (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (U : Subgroup (Dfx ℚ D)) (hU : (U : Set (Dfx ℚ D)) ⊆ levelM1 (p := p) (thetaInt p D))
    (vRep : Fin p → Dfx ℚ D) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) (thetaInt p D))
    (idx : ι → Fin p → ι) (u : ι → Fin p → U)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 (thetaInt p D) U hU vRep hvΔ u i t)).IsUpShape) :
    specCharSeries (UpDatum.ofCerts (thetaInt p D) U hU vRep hvΔ idx u hshape) ω
        (intHom (padicComparison p)) T₀
      = heckeCharPowerSeries (toMatrix ℚ D (padicPlace p))
          (haloWeight (padicComparison p) T₀ ω hp2 (norm_padicComparison p) h0 h1) U
          (subset_levelMonoidOf_toMatrix p D U hU) 1 vRep
          (fun t => by
            have := mem_levelMonoidOf_thetaK (padicComparison p) (thetaInt p D) (hvΔ t)
            rwa [thetaK_thetaInt] at this) idx u := by
  have key : ∀ (θ' : Dfx ℚ D →* Matrix (Fin 2) (Fin 2) (Kp p))
      (hθ : θ' = toMatrix ℚ D (padicPlace p))
      (hU' : (U : Set (Dfx ℚ D)) ⊆ levelMonoidOf θ' (M1K (padicComparison p)))
      (hvΔ' : ∀ t, vRep t ∈ levelMonoidOf θ' (M1K (padicComparison p))),
      heckeCharPowerSeries θ'
          (haloWeight (padicComparison p) T₀ ω hp2 (norm_padicComparison p) h0 h1) U hU' 1 vRep
          hvΔ' idx u
        = heckeCharPowerSeries (toMatrix ℚ D (padicPlace p))
          (haloWeight (padicComparison p) T₀ ω hp2 (norm_padicComparison p) h0 h1) U
          (subset_levelMonoidOf_toMatrix p D U hU) 1 vRep
          (fun t => by
            have := mem_levelMonoidOf_thetaK (padicComparison p) (thetaInt p D) (hvΔ t)
            rwa [thetaK_thetaInt] at this) idx u := by
    intro θ' hθ hU' hvΔ'
    subst hθ
    rfl
  exact (specCharSeries_ofCerts_eq_heckeCharPowerSeries (padicComparison p) T₀ ω (thetaInt p D) U
    hU vRep hvΔ idx u hp2 (norm_padicComparison p) h0 h1 hshape).trans
    (key _ (thetaK_thetaInt p D) _ _)

/-- **The spectral reading of [LWX, Def 2.13] at a halo point** (`m = 1`, neat level): for
`a ≠ 0`, `Char(P)(T₀)(a) = 0` iff `a⁻¹` is a `U_p`-eigenvalue on `S^D_{κ_{T₀}}(U)`
(`QMF.Weight.evalT_heckeCharPowerSeries_eq_zero_iff` through
`specCharSeries_ofCerts_eq_heckeCharPowerSeriesQ`, with `σ = ρ`). -/
theorem evalT_specCharSeries_eq_zero_iff (hp2 : p ≠ 2) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) {T₀ : Kp p}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ ^ 2 < (p : ℝ)⁻¹)
    (U : Subgroup (Dfx ℚ D)) (hU : (U : Set (Dfx ℚ D)) ⊆ levelM1 (p := p) (thetaInt p D))
    (h : (((Quotient.mk'' : Dfx ℚ D → RightCosets U) ''
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
      ∃ φ : FormsQ ℚ D (padicPlace p)
          (haloWeight (padicComparison p) T₀ ω hp2 (norm_padicComparison p) h0 h1) U
          (subset_levelMonoidOf_toMatrix p D U hU),
        φ ≠ 0 ∧
          heckeUpiQ ℚ D (padicPlace p)
              (haloWeight (padicComparison p) T₀ ω hp2 (norm_padicComparison p) h0 h1) U
              (subset_levelMonoidOf_toMatrix p D U hU) ((p : ℕ) : Kp p) (natCast_p_ne_zero p)
              (by
                have := mem_levelMonoidOf_thetaK (padicComparison p) (thetaInt p D)
                  (etaAdelic'_mem_levelM1 p D)
                rwa [thetaK_thetaInt] at this) h φ
            = a⁻¹ • φ := by
  rw [specCharSeries_ofCerts_eq_heckeCharPowerSeriesQ p D hp2 ω h0 h1 U hU vRep hvΔ idx u]
  have hstab' : ∀ i (w : Dfx ℚ D)
      (hw : w ∈ AutomorphicFunction.stabilizerAtSlash (globalUnits ℚ D) U (c i)) (x : c(ℕ, Kp p)),
      (1 : M1K (padicComparison p) →* (Kp p)ˣ)
          ⟨toMatrix ℚ D (padicPlace p) w, subset_levelMonoidOf_toMatrix p D U hU hw.1⟩
        • (haloWeight (padicComparison p) T₀ ω hp2 (norm_padicComparison p) h0 h1).kappaSlash
          ⟨toMatrix ℚ D (padicPlace p) w, subset_levelMonoidOf_toMatrix p D U hU hw.1⟩ x = x := by
    intro i w hw x
    have hw1 : w = 1 := Subgroup.mem_bot.mp (hstab i ▸ hw)
    subst hw1
    rw [show (⟨toMatrix ℚ D (padicPlace p) 1, subset_levelMonoidOf_toMatrix p D U hU hw.1⟩ :
        M1K (padicComparison p)) = 1 from Subtype.ext (map_one _), map_one,
      AnalyticWeight.kappaSlash_one, one_smul]
    rfl
  have hdet : ‖(toMatrix ℚ D (padicPlace p)
      (etaAdelic' ℚ D (padicPlace p) ((p : ℕ) : Kp p) (natCast_p_ne_zero p))).det‖
        ≤ haloRho (p := p) T₀ := by
    rw [norm_det_toMatrix_etaAdelic' ℚ D (padicPlace p) _ (valued_natCast_p_le_one p)
      (natCast_p_ne_zero p), norm_natCast_p_Kp]
    exact inv_le_haloRho T₀ h0
  exact QMF.Weight.evalT_heckeCharPowerSeries_eq_zero_iff (toMatrix ℚ D (padicPlace p)) _ U _ 1 c
    hc hstab' _ h vRep _ hv hvinj idx d hd u hfact le_rfl (haloRho_lt_one T₀ h1) hdet ha0

end Quaternion

end LWX

end
