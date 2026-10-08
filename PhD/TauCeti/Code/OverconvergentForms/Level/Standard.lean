/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.OverconvergentForms.Adelic.IntegralAdeles
import PhD.TauCeti.Code.OverconvergentForms.Level.Local

/-!
# The standard levels `U₀(𝔫)` and `U₁(𝔫)`

A level is cut out of `U₀(1)` by conditions on finitely many components: for places `w k` with
rigidifications and subgroups `H k ⊆ GL₂(F_{w k})`, `standardLevel` is
`U₀(1) ∩ ⋂_k θ_{w k}⁻¹(H k)`, compact open as soon as every `H k` is open. `U₀(𝔫)` and `U₁(𝔫)`, for
`𝔫 = ∏_k (w k)^{t k}`, are the cases `H k = Iw`, `Iw₁`; `U₁(𝔫)` is normal in `U₀(𝔫)` and the
quotient is `∏_k (𝒪_{w k} / 𝔭^{t k})^×` through the lower-right entries.

[Buz07, §9, p. 69]: "If `𝔫` is an ideal of `𝒪_F` which is coprime to `disc(D)` then we define
`U₀(𝔫)` (resp. `U₁(𝔫)`) in the usual way as being matrices in `(𝒪_D ⊗ ℤ̂)^×` which are congruent to
`((∗ ∗), (0 ∗))` (resp. `((∗ ∗), (0 1))`) mod `𝔫`."

## Main definitions

* `AdelicAlgebra.levelAt`, `AdelicAlgebra.standardLevel`.
* `AdelicAlgebra.levelThreshold`: the value `v(ϖ)^t ∈ ℤᵐ⁰`.
* `AdelicAlgebra.U0Level`, `AdelicAlgebra.U1Level`.
* `AdelicAlgebra.lowerRightResidueLevel`: `g ↦ d(θ_{w k}(g)) mod 𝔭^{t k}`.

## Main results

* `AdelicAlgebra.isOpen_levelAt`, `AdelicAlgebra.unitAt_mem_levelAt_iff`,
  `AdelicAlgebra.unitAt_mem_levelAt_of_ne`.
* `AdelicAlgebra.isCompact_standardLevel`, `AdelicAlgebra.isOpen_standardLevel`, and the
  `U₀(𝔫)`, `U₁(𝔫)` cases `AdelicAlgebra.isCompact_U0Level`, `AdelicAlgebra.isOpen_U1Level`, ….
* `AdelicAlgebra.U1Level_normal`, `AdelicAlgebra.iInf_ker_lowerRightResidueLevel`,
  `AdelicAlgebra.lowerRightResidueLevel_surjective`: `U₀(𝔫) / U₁(𝔫) ≃ ∏_k (𝒪_{w k}/𝔭^{t k})^×`.

Roadmap: §0.3.1. Tau Ceti home: `TauCeti/NumberTheory/AdelicAlgebra/StandardLevel.lean`.
-/

open scoped TensorProduct Classical WithZero
open IsDedekindDomain NumberField LocalLevel

noncomputable section

namespace AdelicAlgebra

open scoped RightAlgebra

variable {F : Type*} [Field F] [NumberField F] {D : Type*} [Ring D] [Algebra F D]
variable {ι : Type*} [Fintype ι] (b : Module.Basis ι F D) (hb : IsOrderBasis b)

/-- The value `v(ϖ)^t` of the `t`-th power of a uniformiser, in `ℤᵐ⁰`. -/
def levelThreshold (t : ℕ) : ℤᵐ⁰ := WithZero.exp (-(t : ℤ))

/-- `v(ϖ)^t < 1` for `t ≥ 1`. -/
theorem levelThreshold_lt_one {t : ℕ} (ht : 1 ≤ t) : levelThreshold t < 1 := by
  rw [levelThreshold, ← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

theorem levelThreshold_ne_zero (t : ℕ) : levelThreshold t ≠ 0 :=
  WithZero.exp_ne_zero

private theorem levelThreshold_anti {t t' : ℕ} (h : t ≤ t') :
    levelThreshold t' ≤ levelThreshold t := by
  rw [levelThreshold, levelThreshold, WithZero.exp_le_exp]
  omega

/-- `v(ϖ)^t` is the threshold, for a uniformiser `ϖ`. -/
theorem valued_pow_eq_levelThreshold (v : HeightOneSpectrum (𝓞 F)) {ϖ : v.adicCompletion F}
    (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (t : ℕ) : Valued.v ϖ ^ t = levelThreshold t := by
  rw [hϖ, levelThreshold, ← WithZero.exp_nsmul, nsmul_eq_mul, mul_neg, mul_one]

private theorem exists_ne_zero_valued_le_levelThreshold (v : HeightOneSpectrum (𝓞 F)) (t : ℕ) :
    ∃ x : v.adicCompletion F, x ≠ 0 ∧ Valued.v x ≤ levelThreshold t := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) :=
    (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) π).trans hπ
  refine ⟨(π : v.adicCompletion F) ^ t, pow_ne_zero _ fun h => ?_, ?_⟩
  · rw [h, map_zero] at hv
    exact WithZero.exp_ne_zero hv.symm
  · exact ((map_pow _ _ _).trans (valued_pow_eq_levelThreshold v hv t)).le

section LevelAt

variable (F D) (v : HeightOneSpectrum (𝓞 F)) [RigidificationAt F D v]

/-- The subgroup of `D_f^×` cut out by a condition on the `v`-component. -/
def levelAt (H : Subgroup (GL (Fin 2) (v.adicCompletion F))) : Subgroup (Dfx F D) :=
  H.comap (toGL F D v)

variable {F D v}

theorem mem_levelAt_iff {H : Subgroup (GL (Fin 2) (v.adicCompletion F))} {g : Dfx F D} :
    g ∈ levelAt F D v H ↔ toGL F D v g ∈ H :=
  Iff.rfl

/-- A condition by an open subgroup at `v` cuts out an open subgroup. -/
theorem isOpen_levelAt {H : Subgroup (GL (Fin 2) (v.adicCompletion F))}
    (hH : IsOpen (H : Set (GL (Fin 2) (v.adicCompletion F)))) :
    IsOpen (levelAt F D v H : Set (Dfx F D)) :=
  hH.preimage (continuous_toGL F D v)

/-- `ι_v(m)` satisfies the condition at `v` exactly when `m` does. -/
theorem unitAt_mem_levelAt_iff {H : Subgroup (GL (Fin 2) (v.adicCompletion F))}
    {m : GL (Fin 2) (v.adicCompletion F)} : unitAt F D v m ∈ levelAt F D v H ↔ m ∈ H := by
  rw [mem_levelAt_iff, toGL_unitAt]

/-- `ι_w(m)` satisfies every condition at `v ≠ w`. -/
theorem unitAt_mem_levelAt_of_ne {w : HeightOneSpectrum (𝓞 F)} [RigidificationAt F D w]
    (hw : w ≠ v) (H : Subgroup (GL (Fin 2) (v.adicCompletion F)))
    (m : GL (Fin 2) (w.adicCompletion F)) : unitAt F D w m ∈ levelAt F D v H := by
  rw [mem_levelAt_iff, toGL_unitAt_of_ne w hw.symm m]
  exact one_mem H

end LevelAt

section Standard

variable {κ : Type*} [Finite κ] (w : κ → HeightOneSpectrum (𝓞 F))
  [∀ k, RigidificationAt F D (w k)]

/-- **A standard level**: `U₀(1)` cut down by conditions at the places `w k`. -/
def standardLevel (H : ∀ k, Subgroup (GL (Fin 2) ((w k).adicCompletion F))) :
    Subgroup (Dfx F D) :=
  U0 b hb ⊓ ⨅ k, levelAt F D (w k) (H k)

/-- **`U₀(𝔫)`** for `𝔫 = ∏_k (w k)^{t k}`. -/
def U0Level (t : κ → ℕ) : Subgroup (Dfx F D) :=
  standardLevel b hb w fun k ↦ iwahori ((w k).adicCompletion F) (levelThreshold (t k))

/-- **`U₁(𝔫)`** for `𝔫 = ∏_k (w k)^{t k}`. -/
def U1Level (t : κ → ℕ) : Subgroup (Dfx F D) :=
  standardLevel b hb w fun k ↦ iwahoriOne ((w k).adicCompletion F) (levelThreshold (t k))

variable {b hb w}

omit [Fintype ι] [Finite κ] in
/-- A standard level lies in `U₀(1)`. -/
theorem standardLevel_le_U0 (H : ∀ k, Subgroup (GL (Fin 2) ((w k).adicCompletion F))) :
    standardLevel b hb w H ≤ U0 b hb :=
  inf_le_left

/-- **A standard level is open.** -/
theorem isOpen_standardLevel
    {H : ∀ k, Subgroup (GL (Fin 2) ((w k).adicCompletion F))}
    (hH : ∀ k, IsOpen (H k : Set (GL (Fin 2) ((w k).adicCompletion F)))) :
    IsOpen (standardLevel b hb w H : Set (Dfx F D)) := by
  rw [standardLevel, Subgroup.coe_inf, Subgroup.coe_iInf]
  exact isOpen_U0.inter (isOpen_iInter_of_finite fun k => isOpen_levelAt (hH k))

/-- **A standard level is compact**: a closed subgroup of `U₀(1)`. -/
theorem isCompact_standardLevel
    {H : ∀ k, Subgroup (GL (Fin 2) ((w k).adicCompletion F))}
    (hH : ∀ k, IsOpen (H k : Set (GL (Fin 2) ((w k).adicCompletion F)))) :
    IsCompact (standardLevel b hb w H : Set (Dfx F D)) :=
  haveI : Module.Finite F D := Module.Finite.of_basis b
  (isCompact_U0 (b := b) (hb := hb)).of_isClosed_subset
    ((standardLevel b hb w H).isClosed_of_isOpen (isOpen_standardLevel hH))
    (standardLevel_le_U0 H)

/-- `U₀(𝔫)` is open. -/
theorem isOpen_U0Level (t : κ → ℕ) :
    IsOpen (U0Level b hb w t : Set (Dfx F D)) :=
  isOpen_standardLevel fun k =>
    isOpen_iwahori (exists_ne_zero_valued_le_levelThreshold (w k) (t k))

/-- `U₀(𝔫)` is compact. -/
theorem isCompact_U0Level (t : κ → ℕ) :
    IsCompact (U0Level b hb w t : Set (Dfx F D)) :=
  isCompact_standardLevel fun k =>
    isOpen_iwahori (exists_ne_zero_valued_le_levelThreshold (w k) (t k))

/-- `U₁(𝔫)` is open. -/
theorem isOpen_U1Level (t : κ → ℕ) :
    IsOpen (U1Level b hb w t : Set (Dfx F D)) :=
  isOpen_standardLevel fun k =>
    isOpen_iwahoriOne (exists_ne_zero_valued_le_levelThreshold (w k) (t k))

/-- `U₁(𝔫)` is compact. -/
theorem isCompact_U1Level (t : κ → ℕ) :
    IsCompact (U1Level b hb w t : Set (Dfx F D)) :=
  isCompact_standardLevel fun k =>
    isOpen_iwahoriOne (exists_ne_zero_valued_le_levelThreshold (w k) (t k))

omit [Fintype ι] [Finite κ] in
/-- `U₁(𝔫) ⊆ U₀(𝔫)`. -/
theorem U1Level_le_U0Level (t : κ → ℕ) : U1Level b hb w t ≤ U0Level b hb w t :=
  inf_le_inf_left _ (iInf_mono fun _ => Subgroup.comap_mono (iwahoriOne_le_iwahori _))

omit [Fintype ι] [Finite κ] in
/-- The levels shrink as the exponents grow: `U₀(𝔫) ∩ U₀(𝔭^{t'}) ⊆ U₀(𝔫) ∩ U₀(𝔭^t)`. -/
theorem U0Level_anti {t t' : κ → ℕ} (h : t ≤ t') : U0Level b hb w t' ≤ U0Level b hb w t :=
  inf_le_inf_left _ (iInf_mono fun k =>
    Subgroup.comap_mono (iwahori_mono (levelThreshold_anti (h k))))

omit [Fintype ι] [Finite κ] in
/-- **`U₁(𝔫)` is normal in `U₀(𝔫)`.** -/
theorem U1Level_normal (t : κ → ℕ) :
    ((U1Level b hb w t).subgroupOf (U0Level b hb w t)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  refine ⟨(Subgroup.mem_inf.mp (g * n * g⁻¹).2).1, Subgroup.mem_iInf.mpr fun k => ?_⟩
  have hg : toGL F D (w k) (g : Dfx F D) ∈
      iwahori ((w k).adicCompletion F) (levelThreshold (t k)) :=
    Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp g.2).2 k
  have hn' : toGL F D (w k) (n : Dfx F D) ∈
      iwahoriOne ((w k).adicCompletion F) (levelThreshold (t k)) :=
    Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp hn).2 k
  have hconj := (iwahoriOne_normal (K := (w k).adicCompletion F) (levelThreshold (t k))).conj_mem
    ⟨_, iwahoriOne_le_iwahori _ hn'⟩ hn' ⟨_, hg⟩
  rw [mem_levelAt_iff, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul,
    map_inv]
  exact hconj

variable (b hb w)

/-- **The lower-right residue at `w k`**: `g ↦ d(θ_{w k}(g)) mod 𝔭^{t k}` on `U₀(𝔫)`. -/
def lowerRightResidueLevel (t : κ → ℕ) (k : κ) :
    U0Level b hb w t →*
      ((Valued.v : Valuation ((w k).adicCompletion F) ℤᵐ⁰).integer ⧸
        ballIdeal ((w k).adicCompletion F) (levelThreshold (t k)))ˣ :=
  (lowerRightResidue ((w k).adicCompletion F) (levelThreshold (t k))).comp
    { toFun := fun g ↦ ⟨toGL F D (w k) (g : Dfx F D),
        Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp g.2).2 k⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun _ _ => Subtype.ext (map_mul _ _ _) }

variable {b hb w}

private theorem toGL_eq_one_of_toLocalUnits_eq_one {v : HeightOneSpectrum (𝓞 F)}
    [RigidificationAt F D v] {g : Dfx F D} (h : toLocalUnits F D v g = 1) :
    toGL F D v g = 1 := by
  rw [show toGL F D v g = Units.map
      (RigidificationAt.equiv (F := F) (D := D) (v := v)).toAlgHom.toMonoidHom
        (toLocalUnits F D v g) from rfl, h, map_one]

omit [Fintype ι] [Finite κ] in
/-- **`U₀(𝔫) / U₁(𝔫)`**: the kernel of the residues is `U₁(𝔫)`. -/
theorem iInf_ker_lowerRightResidueLevel (t : κ → ℕ) :
    ⨅ k, (lowerRightResidueLevel b hb w t k).ker =
      (U1Level b hb w t).subgroupOf (U0Level b hb w t) := by
  ext g
  have hk : ∀ k, lowerRightResidueLevel b hb w t k g = 1 ↔
      toGL F D (w k) (g : Dfx F D) ∈
        iwahoriOne ((w k).adicCompletion F) (levelThreshold (t k)) := fun k => by
    have h := SetLike.ext_iff.mp
      (ker_lowerRightResidue (K := (w k).adicCompletion F) (levelThreshold (t k)))
      ⟨toGL F D (w k) (g : Dfx F D), Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp g.2).2 k⟩
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf] at h
    exact h
  simp only [Subgroup.mem_iInf, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  exact ⟨fun h => ⟨(Subgroup.mem_inf.mp g.2).1, Subgroup.mem_iInf.mpr fun k => (hk k).mp (h k)⟩,
    fun h k => (hk k).mpr (Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp h).2 k)⟩

omit [Fintype ι] in
/-- **`U₀(𝔫) / U₁(𝔫) ≃ ∏_k (𝒪_{w k} / 𝔭^{t k})^×`**: the residues are jointly surjective, through
the commuting elements `ι_{w k}(diag(1, d_k))`. -/
theorem lowerRightResidueLevel_surjective (hw : Function.Injective w)
    (hint : ∀ k, RigidificationAt.IsIntegral b hb (w k)) {t : κ → ℕ} (ht : ∀ k, 1 ≤ t k) :
    Function.Surjective fun (g : U0Level b hb w t) (k : κ) ↦
      lowerRightResidueLevel b hb w t k g := by
  haveI := Fintype.ofFinite κ
  intro u
  choose m hm using fun k => lowerRightResidue_surjective (K := (w k).adicCompletion F)
    (levelThreshold_lt_one (ht k)) (u k)
  have hmU : ∀ k, unitAt F D (w k) (m k : GL (Fin 2) ((w k).adicCompletion F)) ∈ U0 b hb :=
    fun k => (unitAt_mem_U0_iff (w k) (hint k)).mpr
      ((mem_integralGL_iff _).mpr ⟨(m k).2.1, (m k).2.2.1⟩)
  have key : ∀ s : Finset κ, ∃ g : Dfx F D, g ∈ U0 b hb ∧
      (∀ k ∈ s, toGL F D (w k) g = m k) ∧ (∀ k ∉ s, toLocalUnits F D (w k) g = 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_mem _, fun k hk => absurd hk (Finset.notMem_empty k),
        fun _ _ => map_one _⟩
    | insert k s hks ih =>
      obtain ⟨g, hgU, hgin, hgout⟩ := ih
      refine ⟨unitAt F D (w k) (m k) * g, mul_mem (hmU k) hgU, fun j hj => ?_, fun j hj => ?_⟩
      · rcases Finset.mem_insert.mp hj with rfl | hj
        · rw [map_mul, toGL_unitAt, toGL_eq_one_of_toLocalUnits_eq_one (hgout _ hks), mul_one]
        · have hjk : w j ≠ w k := hw.ne (ne_of_mem_of_not_mem hj hks)
          rw [map_mul, toGL_unitAt_of_ne (w k) hjk, hgin j hj, one_mul]
      · have hjk : w j ≠ w k := hw.ne fun h => hj (Finset.mem_insert.mpr (Or.inl h))
        rw [map_mul, hgout j fun h => hj (Finset.mem_insert_of_mem h), mul_one]
        exact toLocalUnits_localIncl_of_ne (w k) hjk _
  obtain ⟨g, hgU, hgin, -⟩ := key Finset.univ
  refine ⟨⟨g, Subgroup.mem_inf.mpr ⟨hgU, Subgroup.mem_iInf.mpr fun k => ?_⟩⟩, funext fun k => ?_⟩
  · rw [mem_levelAt_iff, hgin k (Finset.mem_univ k)]
    exact (m k).2
  · rw [← hm k]
    show lowerRightResidue ((w k).adicCompletion F) (levelThreshold (t k)) _ =
      lowerRightResidue ((w k).adicCompletion F) (levelThreshold (t k)) (m k)
    exact congrArg (lowerRightResidue ((w k).adicCompletion F) (levelThreshold (t k)))
      (Subtype.ext (hgin k (Finset.mem_univ k)))

end Standard

end AdelicAlgebra
