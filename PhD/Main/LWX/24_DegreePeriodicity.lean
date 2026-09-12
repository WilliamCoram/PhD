/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«23_ConductorSlopes»

/-!
# The degrees at every classical weight, and [LWX, Corollary 1.4]

[LWX, Theorem 1.3] evaluates the degrees of the components `X_{n,ω}` and `X_{(n,n+1),ω}` of the
spectral curve near the boundary of weight space in terms of ordinary dimensions
(`lwx.txt:148–160`):

  `deg X_{n,ω} = r_ord(ω⁻¹ω₀^{2n−2}) + r_ord(ωω₀^{−2n})` (`n ≥ 1`),
  `deg X_{(n,n+1),ω} = qt − r_ord(ω⁻¹ω₀^{2n}) − r_ord(ωω₀^{−2n})` (`n ≥ 0`), which is `> 0`,

and [LWX, Corollary 1.4] (`lwx.txt:164–169`) reads off the shift symmetry
`deg X_{I,ω} = deg X_{I+1,ωω₀²}` for `I = (0,1), 1, (1,2), 2, …`, hence the periodicity of
`deg X_{I,ω}` modulo `ϕ(q)/2` in `I`.  At the coefficient level (`degX`, `degXint` of
`15_StepThree.lean`) the integer-point formula `degX_succ_of_atkinLehnerData` and the first
open-interval formula `degXint_zero` are proved one weight at a time, granted the Atkin–Lehner data
at that weight.  Here they are proved **at every weight at once**, granted the family of data
`AtkinLehnerFamily` (one section, a Hecke character at every classical weight of conductor `p²`),
the remaining open-interval degrees `deg X_{(n,n+1),ω}`, `n ≥ 1`, are computed from the two gaps
of the unit band at consecutive vertices, positivity follows from `r_ord ≤ t` and `p ≥ 3`, and
Corollary 1.4 is the algebra of the characters `ω⁻¹ω₀^{2n}`, `ωω₀^{−2n}` under `ω ↦ ωω₀²`,
`n ↦ n + 1`, iterated with `ω₀^{p−1} = 1`.  Those character identities live with the characters
(`16_TargetPoint.lean`, `17_NebChar.lean`, `22_AtkinLehnerFamily.lean`) and `r_ord ≤ t` with `ordDim`
(`ordDim_le_card`, `07_Degrees.lean`).  No Jacquet–Langlands input.
-/

open Filter Topology TateFredholm QMF QMF.Weight AbstractHeckeOperatorSlash
open scoped Nat TateFredholm Pointwise

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### The degrees at every classical weight, from the family of Atkin–Lehner data -/

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]
variable {G : Type*} [Group G] {Γ : Subgroup G} (θG : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])
variable (ψ : ℚ_[p] →+* K)
variable (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG) (idx : ι → Fin p → ι)
  (uu : ι → Fin p → U)

section Family

variable {ζ : K} (F : AtkinLehnerFamily θG ψ U Γ ζ)
variable (hfin : (((Quotient.mk'' : G → RightCosets U) ''
      (({upEltF θG ψ U F} : Set G) * (U : Set G))) : Set (RightCosets U)).Finite)
  (hv : Set.BijOn (Quotient.mk'' : G → RightCosets U) (Set.range (vRepF θG ψ U F))
      (((Quotient.mk'' : G → RightCosets U) ''
        (({upEltF θG ψ U F} : Set G) * (U : Set G))) : Set (RightCosets U)))
  (hvinj : Function.Injective (vRepF θG ψ U F))
  (c : ι → G)
  (hc : Function.Bijective
    (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient (Γ : Set G) (U : Set G))))
  (hstab : ∀ i, AutomorphicFunction.stabilizerAtSlash Γ U (c i) = ⊥)
  (d : ι → Fin p → G) (hd : ∀ i t, d i t ∈ Γ)
  (hfact : ∀ i t, c i * (vRepF θG ψ U F t)⁻¹ = d i t * c (idx i t) * (uu i t : G))
  (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F)
    uu i t)).IsUpShape)
  (hdet : ∀ i t, (certM1 θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) uu i t :
    Matrix (Fin 2) (Fin 2) ℚ_[p]).det = p)

include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **The left gap at every weight** ([LWX, §3.23 Step III], `lwx.txt:2025–2047`:
`n_{k+1} − n⁻_{k+1} = r_ord(ω⁻¹ω₀^{2k})`), granted the family of Atkin–Lehner data. -/
theorem touchX_sub_leftIndex_eq_ordDim_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    touchX p (Fintype.card ι) (k + 1)
        - leftIndex (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
            hshape) ω (k + 1)
      = ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (partnerChar p ω k) :=
  touchX_sub_leftIndex_eq_ordDim idx hp2 hψ hshape hdet
    (classicalData ψ ω θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) uu hp2 hψ hζ
      (norm_natCast_p ψ hψ) k)
    (classicalData ψ (partnerChar p ω k) θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) uu
      hp2 hψ hζ.inv (norm_natCast_p ψ hψ) k)
    (targetData_classicalPoint ψ ω θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) uu hp2
      hψ hζ (norm_natCast_p ψ hψ) k)
    (targetData_classicalPoint ψ (partnerChar p ω k) θG U hU (vRepF θG ψ U F)
      (vRepF_mem_levelM1 θG ψ U F) uu hp2 hψ hζ.inv (norm_natCast_p ψ hψ) k)
    (atkinLehnerHypothesis_of_atkinLehnerData θG ψ U hU k ω hp2 hψ hζ (norm_natCast_p ψ hψ)
      (AtkinLehnerFamily.toData θG ψ U F ω k) hfin hv hvinj c hc hstab idx uu d hd hfact)

include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **The right gap at every weight** ([LWX, §3.23 Step III], `lwx.txt:2048–2078`:
`n⁺_{k+1} − n_{k+1} = r_ord(ωω₀^{−2k−2})`), granted the family of Atkin–Lehner data (H2 is
`isThetaExact_classicalData`). -/
theorem rightIndex_sub_touchX_eq_ordDim_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    rightIndex (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) ω (k + 1)
        - touchX p (Fintype.card ι) (k + 1)
      = ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (targetChar p ω k) :=
  rightIndex_sub_touchX_eq_ordDim idx hp2 hψ hshape hdet
    (classicalData ψ ω θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) uu hp2 hψ hζ
      (norm_natCast_p ψ hψ) k)
    (classicalData ψ (partnerChar p ω k) θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) uu
      hp2 hψ hζ.inv (norm_natCast_p ψ hψ) k)
    (targetData_classicalPoint ψ ω θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) uu hp2
      hψ hζ (norm_natCast_p ψ hψ) k)
    (atkinLehnerHypothesis_of_atkinLehnerData θG ψ U hU k ω hp2 hψ hζ (norm_natCast_p ψ hψ)
      (AtkinLehnerFamily.toData θG ψ U F ω k) hfin hv hvinj c hc hstab idx uu d hd hfact)
    (isThetaExact_classicalData idx hshape hdet
      (classicalData ψ ω θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) uu hp2 hψ hζ
        (norm_natCast_p ψ hψ) k)
      (targetData_classicalPoint ψ ω θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) uu
        hp2 hψ hζ (norm_natCast_p ψ hψ) k))

include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, Thm 1.3]: `deg X_{k+1,ω} = r_ord(ω⁻¹ω₀^{2k}) + r_ord(ωω₀^{−2k−2})` at every weight**
(`lwx.txt:151–155`), granted the family of Atkin–Lehner data. -/
theorem degX_succ_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape) ω
        (k + 1)
      = ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (partnerChar p ω k)
        + ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (targetChar p ω k) :=
  degX_succ_of_atkinLehnerData θG ψ U hU k ω hp2 hψ hζ (AtkinLehnerFamily.toData θG ψ U F ω k)
    hfin hv hvinj c hc hstab idx uu d hd hfact hshape hdet

include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, Thm 1.3]: `deg X_{(0,1),ω} = qt − r_ord(ω⁻¹) − r_ord(ω)`** (`lwx.txt:157–159` at
`n = 0`), granted the family of Atkin–Lehner data. -/
theorem degXint_zero_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) :
    degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
        ω 0
      = p * Fintype.card ι
        - ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (partnerChar p ω 0)
        - ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) ω :=
  degXint_zero idx hp2 hψ hshape hdet
    (classicalData ψ ω θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) uu hp2 hψ hζ
      (norm_natCast_p ψ hψ) 0)
    (classicalData ψ (partnerChar p ω 0) θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) uu
      hp2 hψ hζ.inv (norm_natCast_p ψ hψ) 0)
    (targetData_classicalPoint ψ ω θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) uu hp2
      hψ hζ (norm_natCast_p ψ hψ) 0)
    (targetData_classicalPoint ψ (partnerChar p ω 0) θG U hU (vRepF θG ψ U F)
      (vRepF_mem_levelM1 θG ψ U F) uu hp2 hψ hζ.inv (norm_natCast_p ψ hψ) 0)
    (atkinLehnerHypothesis_of_atkinLehnerData θG ψ U hU 0 ω hp2 hψ hζ (norm_natCast_p ψ hψ)
      (AtkinLehnerFamily.toData θG ψ U F ω 0) hfin hv hvinj c hc hstab idx uu d hd hfact)

include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, Thm 1.3]: `deg X_{(k+1,k+2),ω} = qt − r_ord(ω⁻¹ω₀^{2k+2}) − r_ord(ωω₀^{−2k−2})`**
(`lwx.txt:2089–2097`: `n⁻_{k+2} − n⁺_{k+1} = (n_{k+2} − n_{k+1}) − (n_{k+2} − n⁻_{k+2})
− (n⁺_{k+1} − n_{k+1})`), granted the family of Atkin–Lehner data. -/
theorem degXint_succ_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
        ω (k + 1)
      = p * Fintype.card ι
        - ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (partnerChar p ω (k + 1))
        - ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (targetChar p ω k) := by
  have hL := touchX_sub_leftIndex_eq_ordDim_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c
    hc hstab d hd hfact hshape hdet hp2 hψ hζ ω (k + 1)
  have hR := rightIndex_sub_touchX_eq_ordDim_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c
    hc hstab d hd hfact hshape hdet hp2 hψ hζ ω k
  have hb1 := hasUnitBand_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd
    hfact hshape hp2 hψ hζ ω (k + 1)
  have hb2 := hasUnitBand_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd
    hfact hshape hp2 hψ hζ ω (k + 1 + 1)
  have hle := (leftIndex_mem _ ω hb2).2.1
  have hge := (rightIndex_mem _ ω hb1).1
  have hRL := rightIndex_le_leftIndex_succ _ ω hb1 hb2
  have htouch : touchX p (Fintype.card ι) (k + 1 + 1)
      = touchX p (Fintype.card ι) (k + 1) + p * Fintype.card ι := by
    rw [touchX, touchX]
    ring
  rw [degXint]
  generalize p * Fintype.card ι = N at htouch ⊢
  omega

include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, Thm 1.3]: `deg X_{(n,n+1),ω} = qt − r_ord(ω⁻¹ω₀^{2n}) − r_ord(ωω₀^{−2n})` for every
`n ≥ 0`** (`lwx.txt:157–159`), granted the family of Atkin–Lehner data. -/
theorem degXint_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
        ω n
      = p * Fintype.card ι
        - ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (partnerChar p ω n)
        - ordDim (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (ω * (teichChar p ^ (2 * n))⁻¹) := by
  cases n with
  | zero =>
    rw [degXint_zero_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact
      hshape hdet hp2 hψ hζ ω, mul_inv_teichChar_pow_zero]
  | succ k =>
    rw [degXint_succ_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact
      hshape hdet hp2 hψ hζ ω k, targetChar_eq_mul_inv_teichChar_pow]

include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, Thm 1.3]: `deg X_{(n,n+1),ω} > 0` for all `n ≥ 0`** (`lwx.txt:160`): `qt − r − r' ≥
qt − 2t > 0` since `r_ord ≤ t` and `p ≥ 3`. -/
theorem degXint_pos_of_atkinLehnerFamily [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    0 < degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
      hshape) ω n := by
  rw [degXint_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape
    hdet hp2 hψ hζ ω n]
  have h1 := ordDim_le_card (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F)
    idx uu hshape) (partnerChar p ω n)
  have h2 := ordDim_le_card (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F)
    idx uu hshape) (ω * (teichChar p ^ (2 * n))⁻¹)
  have h3 : 3 * Fintype.card ι ≤ p * Fintype.card ι :=
    Nat.mul_le_mul_right _ (by have := hp.out.two_le; omega)
  have h4 := Fintype.card_pos (α := ι)
  generalize p * Fintype.card ι = N at h3 ⊢
  omega

/-! ### [LWX, Corollary 1.4]: the shift `(I, ω) ↦ (I + 1, ωω₀²)` and periodicity -/

include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, Cor 1.4] at the integers** (`lwx.txt:164–166`): `deg X_{k+1,ω} = deg X_{k+2,ωω₀²}`. -/
theorem degX_succ_mul_teichChar_sq [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape) ω
        (k + 1)
      = degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
          (ω * teichChar p ^ 2) (k + 2) := by
  rw [degX_succ_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape
      hdet hp2 hψ hζ ω k, show k + 2 = k + 1 + 1 from rfl,
    degX_succ_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape
      hdet hp2 hψ hζ (ω * teichChar p ^ 2) (k + 1),
    partnerChar_mul_teichChar_sq_succ, targetChar_mul_teichChar_sq_succ]

include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, Cor 1.4] on the open intervals** (`lwx.txt:164–166`):
`deg X_{(n,n+1),ω} = deg X_{(n+1,n+2),ωω₀²}`. -/
theorem degXint_mul_teichChar_sq [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
        ω n
      = degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (ω * teichChar p ^ 2) (n + 1) := by
  rw [degXint_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape
      hdet hp2 hψ hζ ω n,
    degXint_of_atkinLehnerFamily θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape
      hdet hp2 hψ hζ (ω * teichChar p ^ 2) (n + 1),
    partnerChar_mul_teichChar_sq_succ, mul_teichChar_sq_mul_inv_teichChar_pow_succ]

include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- [LWX, Cor 1.4] at the integers, iterated `m` times: `deg X_{k+1,ω} = deg X_{k+1+m,ωω₀^{2m}}`. -/
theorem degX_succ_mul_teichChar_pow [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (m k : ℕ) :
    degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape) ω
        (k + 1)
      = degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
          (ω * teichChar p ^ (2 * m)) (k + 1 + m) := by
  induction m with
  | zero => rw [mul_teichChar_pow_zero, Nat.add_zero]
  | succ m ih =>
    rw [ih, mul_teichChar_pow_succ ω m, show k + 1 + m = k + m + 1 by omega,
      show k + 1 + (m + 1) = k + m + 2 by omega]
    exact degX_succ_mul_teichChar_sq θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape
      hdet hp2 hψ hζ (ω * teichChar p ^ (2 * m)) (k + m)

include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- [LWX, Cor 1.4] on the open intervals, iterated `m` times:
`deg X_{(n,n+1),ω} = deg X_{(n+m,n+m+1),ωω₀^{2m}}`. -/
theorem degXint_mul_teichChar_pow [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (m n : ℕ) :
    degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
        ω n
      = degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) (ω * teichChar p ^ (2 * m)) (n + m) := by
  induction m with
  | zero => rw [mul_teichChar_pow_zero, Nat.add_zero]
  | succ m ih =>
    rw [ih, mul_teichChar_pow_succ ω m, show n + (m + 1) = n + m + 1 by omega]
    exact degXint_mul_teichChar_sq θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape
      hdet hp2 hψ hζ (ω * teichChar p ^ (2 * m)) (n + m)

include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, Cor 1.4]: `deg X_{n,ω}` is periodic modulo `ϕ(q)/2 = (p−1)/2` in `n ≥ 1`**
(`lwx.txt:168–169`): `deg X_{k+1+(p−1)/2,ω} = deg X_{k+1,ω}` ("since `ω₀^{ϕ(q)} = 1`"). -/
theorem degX_succ_add_period [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (k : ℕ) :
    degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape) ω
        (k + 1 + (p - 1) / 2)
      = degX (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
          ω (k + 1) := by
  rw [degX_succ_mul_teichChar_pow θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape hdet
      hp2 hψ hζ ω ((p - 1) / 2) k, mul_teichChar_pow_two_mul_sub_one_div_two hp2]

include hfin hv hvinj c hc hstab d hd hfact hdet in
/-- **[LWX, Cor 1.4]: `deg X_{(n,n+1),ω}` is periodic modulo `ϕ(q)/2 = (p−1)/2` in `n ≥ 0`**
(`lwx.txt:168–169`): `deg X_{(n+(p−1)/2, n+(p−1)/2+1),ω} = deg X_{(n,n+1),ω}`. -/
theorem degXint_add_period [Nonempty ι] [IsAlgClosed K]
    (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (hζ : IsPrimitiveRoot ζ p)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (n : ℕ) :
    degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu hshape)
        ω (n + (p - 1) / 2)
      = degXint (UpDatum.ofCerts θG U hU (vRepF θG ψ U F) (vRepF_mem_levelM1 θG ψ U F) idx uu
          hshape) ω n := by
  rw [degXint_mul_teichChar_pow θG ψ U hU idx uu F hfin hv hvinj c hc hstab d hd hfact hshape hdet
      hp2 hψ hζ ω ((p - 1) / 2) n, mul_teichChar_pow_two_mul_sub_one_div_two hp2]

end Family

end LWX

end
