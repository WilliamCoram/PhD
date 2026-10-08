/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Tate
import PhD.TauCeti.Code.OverconvergentForms.Weight.Expansion

/-!
# Algebraic weights, the nebentypus twist and the scalars

The algebraic characters `u ↦ ∏_i i(u)^{n_i}` of `𝒪_L^×` have expansion data at every level: the
polynomial `∏_i (i(d) + i(c) z_i)^{n_i}` for `n_i ≥ 0`, and the product with the geometric inverse
`(i(d) + i(c) z_i)^{-1} = i(d)^{-1} ∑ (−i(c)/i(d))^m z_i^m` for `n_i < 0`. Buzzard's second
character `v` is a character of `𝒪_L^×` extended to `L^×` by `v(ϖ) = 1` (`extendUnits`). A
finite-order character `ψ` of `𝒪_L^×` factoring through `(𝒪_L / 𝔞_ρ)^×` is *loaded* into any weight
by the twist `col(c, d) ↦ ψ(d̄) col(c, d)`, since `ψ(cz + d) = ψ(d)` on the level; the
classical-shape weights `(nψ, v)` are the algebraic weights so loaded, and Layer 5 is stated for
them. The scalar matrices `u · 1`, `u ∈ 𝒪_L^×`, act by the scalar `n(u) v(u²)`, which forces the
invariants to vanish unless `κ(u, u²) = 1`.

[Buz07, §11, p. 73]: "Define `κ : 𝒪_p^× × 𝒪_p^× → K^×` by `κ(α, β) = ∏_i α_i^{n_i} β_i^{v_i}`.
[…] The map `n : 𝒪_p^× → K^×` defined by `α ↦ ∏_i α_i^{n_i}` extends to a map of rigid spaces
`B^×_r → 𝔾_m` for any `r`, so `r(κ)_j = |π_j|` for all `j ∈ J`." [Buz07, §11, p. 74]: "Choose a
character `ε : Δ → L^×` and let `ε` also denote the induced character of `𝒪_p^×`. Now define
`κ : 𝒪_p^× × 𝒪_p^× → L^×` by `κ(α, β) = ε(α) ∏_i α_i^{n_i} β_i^{v_i}`." [Buz07, §10, p. 71]: "We
extend the map `v : 𝒪_p^× → 𝒪(X)^×` to a group homomorphism `v : F_p^× → 𝒪(X)^×` by defining
`v(π_j) = 1` for all `j ∈ J`."

## Main definitions

* `AutomorphicForm.Embeddings.algChar e n`: the character `u ↦ ∏_i i(u)^{n_i}`.
* `AutomorphicForm.extendUnits ϖ hϖ v₀`: Buzzard's extension `v(ϖ) = 1`.
* `AutomorphicForm.Embeddings.algCol`, `algExpansionData`, `algWeight`.
* `AutomorphicForm.LevelBounds.lowerRightResidue`: the character `γ ↦ d mod 𝔞_ρ` of the level.
* `AutomorphicForm.ExpansionData.twistResidue`, `AnalyticWeight.twistResidue`,
  `Embeddings.classicalShape`.

## Main results

* `AutomorphicForm.AnalyticWeight.kappaSlash_algWeight_monomial`: the action of an algebraic
  weight on monomials.
* `AutomorphicForm.AnalyticWeight.kappaSlash_twistResidue`: the loaded weight acts by the twisted
  action.
* `AutomorphicForm.AnalyticWeight.kappaSlash_smul_one`: the scalars act by `n(u) v(u²)`.

Roadmap: §1.3.1, §1.3.4, §1.3.5. Tau Ceti home:
`TauCeti/NumberTheory/AutomorphicForm/Weight/Algebraic.lean`.
-/

open MvPowerSeries MvPowerSeries.Restricted

namespace AutomorphicForm

variable {L : Type*} [NormedField L] [IsUltrametricDist L]
  {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Buzzard's `v`: extension by `v(ϖ) = 1` -/

omit [IsUltrametricDist L] in
/-- The exponent `k` with `‖x‖ = ‖ϖ‖^k` is unique. -/
private theorem choose_eq_of_norm_eq (ϖ : NormedRing.PseudoUniformizer L)
    (hϖ : ∀ x : L, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖(ϖ : L)‖ ^ k) {x : L} (hx : x ≠ 0) {k : ℤ}
    (hk : ‖x‖ = ‖(ϖ : L)‖ ^ k) : Classical.choose (hϖ x hx) = k :=
  zpow_right_injective₀ ϖ.norm_pos ϖ.norm_lt_one.ne
    ((Classical.choose_spec (hϖ x hx)).symm.trans hk)

omit [IsUltrametricDist L] in
/-- The normalised element `x ϖ^{-k}` has norm one. -/
private theorem norm_mul_inv_zpow_choose (ϖ : NormedRing.PseudoUniformizer L)
    (hϖ : ∀ x : L, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖(ϖ : L)‖ ^ k) (x : Lˣ) :
    ‖(x : L) * ((ϖ.unit ^ (Classical.choose (hϖ x x.ne_zero)))⁻¹ : Lˣ)‖ = 1 := by
  rw [norm_mul, Units.val_inv_eq_inv_val, norm_inv, ϖ.norm_zpow,
    ← Classical.choose_spec (hϖ x x.ne_zero)]
  exact mul_inv_cancel₀ (norm_ne_zero_iff.mpr x.ne_zero)

/-- **Buzzard's extension of `v`**: for a pseudo-uniformiser `ϖ` with `‖L^×‖ = ‖ϖ‖^ℤ`, a character
`v₀` of `𝒪_L^×` extends to `L^×` by `v(ϖ^k u) := v₀(u)`. Source: roadmap §1.2.2; [Buz07, §10, p. 71]
("`v(π_j) = 1`"). -/
noncomputable def extendUnits (ϖ : NormedRing.PseudoUniformizer L)
    (hϖ : ∀ x : L, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖(ϖ : L)‖ ^ k)
    (v₀ : (Subring.unitClosedBall L)ˣ →* Kˣ) : Lˣ →* Kˣ where
  toFun x := v₀ (unitOfNormEqOne ((x : L) * ((ϖ.unit ^ (Classical.choose (hϖ x x.ne_zero)))⁻¹ : Lˣ))
    (norm_mul_inv_zpow_choose ϖ hϖ x))
  map_one' := by
    have hk : Classical.choose (hϖ ((1 : Lˣ) : L) (1 : Lˣ).ne_zero) = 0 :=
      choose_eq_of_norm_eq ϖ hϖ (1 : Lˣ).ne_zero (by rw [Units.val_one, norm_one, zpow_zero])
    refine (congrArg v₀ (Units.ext (Subtype.ext ?_))).trans v₀.map_one
    rw [coe_unitOfNormEqOne, hk]
    simp
  map_mul' x y := by
    have hk : Classical.choose (hϖ ((x * y : Lˣ) : L) (x * y).ne_zero) =
        Classical.choose (hϖ (x : L) x.ne_zero) + Classical.choose (hϖ (y : L) y.ne_zero) :=
      choose_eq_of_norm_eq ϖ hϖ (x * y).ne_zero (by
        rw [Units.val_mul, norm_mul, zpow_add₀ ϖ.norm_pos.ne']
        exact congrArg₂ (· * ·) (Classical.choose_spec (hϖ (x : L) x.ne_zero))
          (Classical.choose_spec (hϖ (y : L) y.ne_zero)))
    refine (congrArg v₀ (Units.ext (Subtype.ext ?_))).trans (v₀.map_mul _ _)
    rw [coe_unitOfNormEqOne, hk, zpow_add, mul_inv]
    simp only [Units.val_mul, Subring.coe_mul, coe_unitOfNormEqOne]
    ring

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem extendUnits_unitsIncl (ϖ : NormedRing.PseudoUniformizer L)
    (hϖ : ∀ x : L, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖(ϖ : L)‖ ^ k) (v₀ : (Subring.unitClosedBall L)ˣ →* Kˣ)
    (u : (Subring.unitClosedBall L)ˣ) : extendUnits ϖ hϖ v₀ (unitsIncl L u) = v₀ u := by
  have hu : ‖((u : Subring.unitClosedBall L) : L)‖ = 1 :=
    NormedRing.isUnit_iff_norm_eq_one.mp u.isUnit
  have hk : Classical.choose (hϖ ((unitsIncl L u : Lˣ) : L) (unitsIncl L u).ne_zero) = 0 :=
    choose_eq_of_norm_eq ϖ hϖ (unitsIncl L u).ne_zero (by rw [coe_unitsIncl, hu, zpow_zero])
  refine congrArg v₀ (Units.ext (Subtype.ext ?_))
  rw [coe_unitOfNormEqOne, hk, zpow_zero, inv_one, Units.val_one, mul_one, coe_unitsIncl]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem extendUnits_unit (ϖ : NormedRing.PseudoUniformizer L)
    (hϖ : ∀ x : L, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖(ϖ : L)‖ ^ k) (v₀ : (Subring.unitClosedBall L)ˣ →* Kˣ) :
    extendUnits ϖ hϖ v₀ ϖ.unit = 1 := by
  have hk : Classical.choose (hϖ (ϖ.unit : L) ϖ.unit.ne_zero) = 1 :=
    choose_eq_of_norm_eq ϖ hϖ ϖ.unit.ne_zero (zpow_one _).symm
  refine (congrArg v₀ (Units.ext (Subtype.ext ?_))).trans v₀.map_one
  rw [coe_unitOfNormEqOne, hk, zpow_one, Units.mul_inv]
  rfl

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem norm_extendUnits (ϖ : NormedRing.PseudoUniformizer L)
    (hϖ : ∀ x : L, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖(ϖ : L)‖ ^ k) (v₀ : (Subring.unitClosedBall L)ˣ →* Kˣ)
    (hv₀ : ∀ u, ‖(v₀ u : K)‖ = 1) (x : Lˣ) : ‖(extendUnits ϖ hϖ v₀ x : K)‖ = 1 :=
  hv₀ _

/-! ### Algebraic weights -/

namespace Embeddings

variable (e : Embeddings L K ι)

/-- **The algebraic character** `u ↦ ∏_i i(u)^{n_i}` of `𝒪_L^×`, `n ∈ ℤ^ι`. Source: roadmap §1.3.1;
[Buz07, §11, p. 73]. -/
noncomputable def algChar (n : ι → ℤ) : (Subring.unitClosedBall L)ˣ →* Kˣ where
  toFun u :=
    ∏ i, (Units.map ((e.emb i).comp (Subring.unitClosedBall L).subtype).toMonoidHom u) ^ n i
  map_one' := by simp
  map_mul' u v := by simp only [map_mul, mul_zpow, Finset.prod_mul_distrib]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem coe_algChar (n : ι → ℤ) (u : (Subring.unitClosedBall L)ˣ) :
    (e.algChar n u : K) = ∏ i, e.emb i (u : Subring.unitClosedBall L) ^ n i := by
  simp [algChar, Units.coe_prod, Units.val_zpow_eq_zpow_val]

omit [IsUltrametricDist K] [CompleteSpace K] in
theorem norm_algChar (n : ι → ℤ) (u : (Subring.unitClosedBall L)ˣ) : ‖(e.algChar n u : K)‖ = 1 := by
  have hu : ‖((u : Subring.unitClosedBall L) : L)‖ = 1 :=
    NormedRing.isUnit_iff_norm_eq_one.mp u.isUnit
  rw [coe_algChar, norm_prod]
  exact Finset.prod_eq_one fun i _ => by rw [norm_zpow, e.norm_emb, hu, one_zpow]

omit [IsUltrametricDist L] [IsUltrametricDist K] [CompleteSpace K] in
/-- The lower row `(c, d)` of a level element, completed by the upper row `(1, 0)`, has level
bounds. -/
private theorem multiBounds_lowerRow {S : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ : ℝ}
    (hb : LevelBounds S ρ) {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) :
    MultiBounds ρ (e.toMulti !![1, 0; g 1 0, g 1 1]) := by
  refine ⟨hb.rho_nonneg, hb.rho_lt_one, fun i j k => ?_, fun i => ?_, fun i => ?_⟩
  · fin_cases j <;> fin_cases k <;> simp [e.norm_emb, hb.integral hg]
  · simpa [e.norm_emb] using hb.c_le hg
  · simpa [e.norm_emb] using hb.d_unit hg

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- `a^{n⁺} (a⁻¹)^{n⁻} = a^n`. -/
private theorem pow_toNat_mul_inv_pow_toNat (a : K) (n : ℤ) :
    a ^ n.toNat * a⁻¹ ^ (-n).toNat = a ^ n := by
  rcases le_total 0 n with hn | hn
  · rw [Int.toNat_eq_zero.mpr (by omega : -n ≤ 0), pow_zero, mul_one, ← zpow_natCast,
      Int.toNat_of_nonneg hn]
  · rw [Int.toNat_eq_zero.mpr hn, pow_zero, one_mul, ← zpow_natCast,
      Int.toNat_of_nonneg (by omega : 0 ≤ -n), inv_zpow', neg_neg]

/-- The expansion `∏_i (i(d) + i(c) z_i)^{n_i}` of the algebraic character, with the negative
exponents realised by the geometric inverse `linInv`. Source: roadmap §1.3.1. -/
noncomputable def algCol (n : ι → ℤ) (c d : L) : Restricted K (1 : ι → ℝ) :=
  ∏ i, lin (e.toMulti !![1, 0; c, d]) i ^ (n i).toNat *
    linInv (e.toMulti !![1, 0; c, d]) i ^ (-n i).toNat

omit [IsUltrametricDist L] [CompleteSpace K] in
/-- For `n ≥ 0` the expansion is the polynomial `∏_i (i(d) + i(c) z_i)^{n_i}`. -/
theorem algCol_natCast (n : ι → ℕ) (c d : L) :
    e.algCol (fun i => (n i : ℤ)) c d = ∏ i, lin (e.toMulti !![1, 0; c, d]) i ^ n i := by
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Int.toNat_natCast, Int.toNat_eq_zero.mpr (neg_nonpos.mpr (Int.natCast_nonneg (n i))),
    pow_zero, mul_one]

/-- **The algebraic weights have expansion data at every level**. Source: roadmap §1.3.1 ("This is
an expansion datum at every level `(SigmaNorm F_𝔭 ρ, ρ)`, `ρ < 1` (Buzzard §11:
`r(κ)_j = |π_j|`)"). -/
noncomputable def algExpansionData {S : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ : ℝ}
    (hb : LevelBounds S ρ) (n : ι → ℤ) : ExpansionData e S ρ (e.algChar n) where
  bounds := hb
  col := e.algCol n
  rowBound_col := by
    intro g hg
    have hM := e.multiBounds_lowerRow hb hg
    exact RowBound.prod hb.rho_nonneg _ fun i _ =>
      ((rowBound_lin hM le_rfl i).pow hb.rho_nonneg _).mul hb.rho_nonneg
        ((rowBound_linInv hM le_rfl i).pow hb.rho_nonneg _)
  evalPoint_col := by
    intro g hg z
    have hM := e.multiBounds_lowerRow hb hg
    rw [coe_algChar]
    simp only [algCol, map_prod, map_mul, map_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    have hlin : e.evalPoint z (lin (e.toMulti !![1, 0; g 1 0, g 1 1]) i) =
        e.emb i (hb.linUnit hg z) :=
      e.evalPoint_lin hb hg z i
    have hinv : e.evalPoint z (linInv (e.toMulti !![1, 0; g 1 0, g 1 1]) i) =
        (e.emb i (hb.linUnit hg z))⁻¹ := by
      rw [← hlin]
      exact eq_inv_of_mul_eq_one_right (by rw [← map_mul, lin_mul_linInv hM i, map_one])
    rw [hlin, hinv]
    exact pow_toNat_mul_inv_pow_toNat _ _

/-- **The algebraic weight** `algWeight (n, v)`: the character `∏ i(u)^{n_i}` with its polynomial
expansion, and a norm-one character `v` (Buzzard's `∏ i(·)^{v_i}` extended by `v(ϖ) = 1` is
`extendUnits ϖ hϖ (e.algChar v)`). Source: roadmap §1.3.1. -/
noncomputable def algWeight {S : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ : ℝ}
    (hb : LevelBounds S ρ) (n : ι → ℤ) (v : Lˣ →* Kˣ) (hv : ∀ x, ‖(v x : K)‖ = 1) :
    AnalyticWeight e S ρ where
  n := e.algChar n
  v := v
  norm_v := hv
  expansion := e.algExpansionData hb n

@[simp] theorem algWeight_n {S : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ : ℝ}
    (hb : LevelBounds S ρ) (n : ι → ℤ) (v : Lˣ →* Kˣ) (hv : ∀ x, ‖(v x : K)‖ = 1) :
    (e.algWeight hb n v hv).n = e.algChar n :=
  rfl

@[simp] theorem algWeight_v {S : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ : ℝ}
    (hb : LevelBounds S ρ) (n : ι → ℤ) (v : Lˣ →* Kˣ) (hv : ∀ x, ‖(v x : K)‖ = 1) :
    (e.algWeight hb n v hv).v = v :=
  rfl

end Embeddings

namespace AnalyticWeight

variable {e : Embeddings L K ι} {S : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ : ℝ}

/-- **The algebraic weight on monomials**: for `r ≤ n`,
`z^r ∣ γ = v(det γ) ∏_i L_i^{n_i − r_i} N_i^{r_i}` — Buzzard's `L_{n,v}` formula. Source: roadmap
§1.3.2; [Buz07, §9, p. 68]. -/
theorem kappaSlash_algWeight_monomial [CharZero K] (hb : LevelBounds S ρ) (n : ι → ℕ)
    (v : Lˣ →* Kˣ) (hv : ∀ x, ‖(v x : K)‖ = 1) (γ : S) (r : ι →₀ ℕ) (hr : ∀ i, r i ≤ n i) :
    (e.algWeight hb (fun i => (n i : ℤ)) v hv).kappaSlash γ (monomial 1 r 1) =
      ((e.algWeight hb (fun i => (n i : ℤ)) v hv).detChar γ : K) •
        ∏ i, lin (e.toMulti γ) i ^ (n i - r i) * num (e.toMulti γ) i ^ r i := by
  have hM : MultiBounds ρ (e.toMulti γ) := e.multiBounds_toMulti hb γ.2
  rw [kappaSlash_monomial, autFactor, smul_mul_assoc]
  congr 1
  show e.algCol (fun i => (n i : ℤ)) _ _ * _ = _
  rw [e.algCol_natCast, Finsupp.prod_fintype _ _ (fun i => pow_zero _), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hlin : lin (e.toMulti !![1, 0; (γ : Matrix (Fin 2) (Fin 2) L) 1 0,
      (γ : Matrix (Fin 2) (Fin 2) L) 1 1]) i = lin (e.toMulti γ) i := rfl
  rw [hlin, mobius]
  conv_lhs => rw [← Nat.sub_add_cancel (hr i)]
  rw [pow_add, mul_pow]
  calc _ = lin (e.toMulti γ) i ^ (n i - r i) * num (e.toMulti γ) i ^ r i *
        (lin (e.toMulti γ) i * linInv (e.toMulti γ) i) ^ r i := by ring
    _ = _ := by rw [lin_mul_linInv hM i, one_pow, mul_one]

end AnalyticWeight

/-! ### Loading a nebentypus -/

namespace LevelBounds

variable {S : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ : ℝ} (hb : LevelBounds S ρ)

/-- The residue of an element of norm one in `(𝒪_L / 𝔞_ρ)^×`, `𝔞_ρ = {x | ‖x‖ ≤ ρ}` (junk `1` off
the unit circle). -/
noncomputable def residueUnit (d : L) :
    (Subring.unitClosedBall L ⧸ NormedRing.closedBallIdeal L ⟨ρ, hb.rho_nonneg⟩)ˣ :=
  if h : ‖d‖ = 1 then
    Units.map (Ideal.Quotient.mk (NormedRing.closedBallIdeal L ⟨ρ, hb.rho_nonneg⟩)).toMonoidHom
      (unitOfNormEqOne d h)
  else 1

/-- On the level, the residue of the lower-right entry is the residue of the unit `d`. -/
theorem residueUnit_of_mem {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S) :
    hb.residueUnit (g 1 1) =
      Units.map (Ideal.Quotient.mk (NormedRing.closedBallIdeal L ⟨ρ, hb.rho_nonneg⟩)).toMonoidHom
        (hb.dUnit hg) :=
  dif_pos (hb.d_unit hg)

/-- **The lower-right residue character** `γ ↦ d mod 𝔞_ρ` of the level: multiplicative because
`(δγ)_{11} = c'b + d'd ≡ d'd mod 𝔞_ρ`. Source: roadmap §1.2.8 ("a nebentypus pulled back through
`d`"), §1.3.4. -/
noncomputable def lowerRightResidue :
    S →* (Subring.unitClosedBall L ⧸ NormedRing.closedBallIdeal L ⟨ρ, hb.rho_nonneg⟩)ˣ where
  toFun g := hb.residueUnit ((g : Matrix (Fin 2) (Fin 2) L) 1 1)
  map_one' := by
    show hb.residueUnit ((1 : Matrix (Fin 2) (Fin 2) L) 1 1) = 1
    have h1 : hb.dUnit S.one_mem = 1 := Units.ext (Subtype.ext (by simp [dUnit]))
    rw [hb.residueUnit_of_mem S.one_mem, h1, map_one]
  map_mul' g h := by
    show hb.residueUnit (((g : Matrix (Fin 2) (Fin 2) L) * h) 1 1) =
      hb.residueUnit ((g : Matrix (Fin 2) (Fin 2) L) 1 1) *
        hb.residueUnit ((h : Matrix (Fin 2) (Fin 2) L) 1 1)
    rw [hb.residueUnit_of_mem (S.mul_mem g.2 h.2), hb.residueUnit_of_mem g.2,
      hb.residueUnit_of_mem h.2, ← map_mul]
    refine Units.ext ?_
    show Ideal.Quotient.mk _ ((hb.dUnit (S.mul_mem g.2 h.2) : (Subring.unitClosedBall L)ˣ) :
        Subring.unitClosedBall L) =
      Ideal.Quotient.mk _ ((hb.dUnit g.2 * hb.dUnit h.2 : (Subring.unitClosedBall L)ˣ) :
        Subring.unitClosedBall L)
    refine Ideal.Quotient.eq.mpr (NormedRing.mem_closedBallIdeal.mpr ?_)
    have hcoe : ((((hb.dUnit (S.mul_mem g.2 h.2) : (Subring.unitClosedBall L)ˣ) :
        Subring.unitClosedBall L) - ((hb.dUnit g.2 * hb.dUnit h.2 : (Subring.unitClosedBall L)ˣ) :
          Subring.unitClosedBall L) : Subring.unitClosedBall L) : L) =
        (g : Matrix (Fin 2) (Fin 2) L) 1 0 * (h : Matrix (Fin 2) (Fin 2) L) 0 1 := by
      simp [dUnit, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hcoe, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hb.integral h.2 0 1)).trans (hb.c_le g.2)

theorem lowerRightResidue_apply (g : S) :
    hb.lowerRightResidue g =
      Units.map (Ideal.Quotient.mk (NormedRing.closedBallIdeal L ⟨ρ, hb.rho_nonneg⟩)).toMonoidHom
        (hb.dUnit g.2) :=
  hb.residueUnit_of_mem g.2

/-- On the level, `cz + d ≡ d mod 𝔞_ρ` for every integral `z`. Source: roadmap §1.3.4 ("because
`ψ(cz + d) = ψ(d)` for `z ∈ 𝒪` and `ϖ^α ∣ c`"). -/
theorem residueUnit_linUnit {g : Matrix (Fin 2) (Fin 2) L} (hg : g ∈ S)
    (z : Subring.unitClosedBall L) :
    Units.map (Ideal.Quotient.mk (NormedRing.closedBallIdeal L ⟨ρ, hb.rho_nonneg⟩)).toMonoidHom
      (hb.linUnit hg z) = hb.residueUnit (g 1 1) := by
  rw [hb.residueUnit_of_mem hg]
  refine Units.ext ?_
  show Ideal.Quotient.mk _ ((hb.linUnit hg z : (Subring.unitClosedBall L)ˣ) :
      Subring.unitClosedBall L) =
    Ideal.Quotient.mk _ ((hb.dUnit hg : (Subring.unitClosedBall L)ˣ) : Subring.unitClosedBall L)
  refine Ideal.Quotient.eq.mpr (NormedRing.mem_closedBallIdeal.mpr ?_)
  have hcoe : ((((hb.linUnit hg z : (Subring.unitClosedBall L)ˣ) : Subring.unitClosedBall L) -
      ((hb.dUnit hg : (Subring.unitClosedBall L)ˣ) : Subring.unitClosedBall L) :
        Subring.unitClosedBall L) : L) = g 1 0 * z := by
    simp [dUnit]
  rw [hcoe, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (Subring.norm_le_one z)).trans (hb.c_le hg)

end LevelBounds

namespace ExpansionData

variable {e : Embeddings L K ι} {S : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ : ℝ}
  {n : (Subring.unitClosedBall L)ˣ →* Kˣ} (E : ExpansionData e S ρ n)

/-- **Loading a character of the residue ring**: `col(c, d) ↦ ψ(d̄) • col(c, d)` is an expansion
datum for `u ↦ n(u) ψ(ū)`. Stated for every `n` with expansion data (the roadmap's `n` algebraic is
the instance `classicalShape`). Source: roadmap §1.3.4; [Buz07, §11, p. 74]. -/
noncomputable def twistResidue
    (ψ : (Subring.unitClosedBall L ⧸ NormedRing.closedBallIdeal L ⟨ρ, E.bounds.rho_nonneg⟩)ˣ →* Kˣ)
    (hψ : ∀ x, ‖(ψ x : K)‖ = 1) :
    ExpansionData e S ρ (n * ψ.comp (Units.map (Ideal.Quotient.mk
      (NormedRing.closedBallIdeal L ⟨ρ, E.bounds.rho_nonneg⟩)).toMonoidHom)) where
  bounds := E.bounds
  col c d := (ψ (E.bounds.residueUnit d) : K) • E.col c d
  rowBound_col hg := (E.rowBound_col hg).smul (hψ _).le
  evalPoint_col := by
    intro g hg z
    show e.evalPoint z ((ψ (E.bounds.residueUnit (g 1 1)) : K) • E.col (g 1 0) (g 1 1)) = _
    rw [map_smul, E.evalPoint_col hg z, smul_eq_mul, MonoidHom.mul_apply, Units.val_mul,
      MonoidHom.comp_apply, E.bounds.residueUnit_linUnit hg z, mul_comm]

theorem twistResidue_col
    (ψ : (Subring.unitClosedBall L ⧸ NormedRing.closedBallIdeal L ⟨ρ, E.bounds.rho_nonneg⟩)ˣ →* Kˣ)
    (hψ : ∀ x, ‖(ψ x : K)‖ = 1) (c d : L) :
    (E.twistResidue ψ hψ).col c d = (ψ (E.bounds.residueUnit d) : K) • E.col c d :=
  rfl

end ExpansionData

namespace AnalyticWeight

variable {e : Embeddings L K ι} {S : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ : ℝ}
  (κ : AnalyticWeight e S ρ)

/-- **The weight loaded with a nebentypus** `ψ`: `(nψ, v)`. Source: roadmap §1.3.4. -/
noncomputable def twistResidue
    (ψ : (Subring.unitClosedBall L ⧸ NormedRing.closedBallIdeal L ⟨ρ, κ.bounds.rho_nonneg⟩)ˣ →* Kˣ)
    (hψ : ∀ x, ‖(ψ x : K)‖ = 1) : AnalyticWeight e S ρ where
  n := _
  v := κ.v
  norm_v := κ.norm_v
  expansion := κ.expansion.twistResidue ψ hψ

/-- The loaded weight acts by the twist of the action by `ψ ∘ (lower-right residue)`. Source:
roadmap §1.2.8, §1.3.4. -/
theorem kappaSlash_twistResidue [CharZero K]
    (ψ : (Subring.unitClosedBall L ⧸ NormedRing.closedBallIdeal L ⟨ρ, κ.bounds.rho_nonneg⟩)ˣ →* Kˣ)
    (hψ : ∀ x, ‖(ψ x : K)‖ = 1) (γ : S) :
    (κ.twistResidue ψ hψ).kappaSlash γ =
      (ψ (κ.bounds.lowerRightResidue γ) : K) • κ.kappaSlash γ := by
  refine ContinuousLinearMap.ext fun f => ?_
  show ((κ.detChar γ : K) • ((ψ (κ.bounds.lowerRightResidue γ) : K) •
      κ.expansion.col ((γ : Matrix (Fin 2) (Fin 2) L) 1 0) ((γ : Matrix (Fin 2) (Fin 2) L) 1 1))) *
        mobiusSubst (e.multiBounds_toMulti κ.expansion.bounds γ.2) f =
    (ψ (κ.bounds.lowerRightResidue γ) : K) • ((κ.detChar γ : K) •
      κ.expansion.col ((γ : Matrix (Fin 2) (Fin 2) L) 1 0) ((γ : Matrix (Fin 2) (Fin 2) L) 1 1) *
        mobiusSubst (e.multiBounds_toMulti κ.expansion.bounds γ.2) f)
  rw [smul_comm, smul_mul_assoc]

end AnalyticWeight

namespace Embeddings

variable (e : Embeddings L K ι) {S : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ : ℝ}

/-- **The classical-shape weights** `(nψ, v)`: an algebraic weight loaded with a nebentypus. Their
automorphy factor is a constant times a polynomial in `cz + d`; Layer 5 is stated for them. Source:
roadmap §1.3.4; [Buz07, §11, p. 74] (`κ(α, β) = ε(α) ∏ α_i^{n_i} β_i^{v_i}`). -/
noncomputable def classicalShape (hb : LevelBounds S ρ) (n : ι → ℤ) (v : Lˣ →* Kˣ)
    (hv : ∀ x, ‖(v x : K)‖ = 1)
    (ψ : (Subring.unitClosedBall L ⧸ NormedRing.closedBallIdeal L ⟨ρ, hb.rho_nonneg⟩)ˣ →* Kˣ)
    (hψ : ∀ x, ‖(ψ x : K)‖ = 1) : AnalyticWeight e S ρ :=
  (e.algWeight hb n v hv).twistResidue ψ hψ

/-- The automorphy factor of a classical-shape weight:
`ψ(d̄) v(det γ) ∏ (i(d) + i(c) z_i)^{n_i}`. -/
theorem autFactor_classicalShape (hb : LevelBounds S ρ) (n : ι → ℤ) (v : Lˣ →* Kˣ)
    (hv : ∀ x, ‖(v x : K)‖ = 1)
    (ψ : (Subring.unitClosedBall L ⧸ NormedRing.closedBallIdeal L ⟨ρ, hb.rho_nonneg⟩)ˣ →* Kˣ)
    (hψ : ∀ x, ‖(ψ x : K)‖ = 1) (γ : S) :
    (e.classicalShape hb n v hv ψ hψ).autFactor γ =
      ((ψ (hb.lowerRightResidue γ) : K) * ((e.algWeight hb n v hv).detChar γ : K)) •
        e.algCol n ((γ : Matrix (Fin 2) (Fin 2) L) 1 0) ((γ : Matrix (Fin 2) (Fin 2) L) 1 1) := by
  show ((e.algWeight hb n v hv).detChar γ : K) • ((ψ (hb.lowerRightResidue γ) : K) •
    e.algCol n ((γ : Matrix (Fin 2) (Fin 2) L) 1 0) ((γ : Matrix (Fin 2) (Fin 2) L) 1 1)) = _
  rw [mul_smul, smul_comm]

end Embeddings

/-! ### The scalars -/

/-- The scalar matrix `u · 1`, `u ∈ 𝒪_L^×`, lies in every `Σ(ρ)`. Source: roadmap §1.3.5. -/
theorem smul_one_mem_sigmaNorm {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1)
    (u : (Subring.unitClosedBall L)ˣ) :
    ((u : Subring.unitClosedBall L) : L) • (1 : Matrix (Fin 2) (Fin 2) L) ∈
      SigmaNorm L ρ hρ0 hρ := by
  have hu : ‖((u : Subring.unitClosedBall L) : L)‖ = 1 :=
    NormedRing.isUnit_iff_norm_eq_one.mp u.isUnit
  have hu0 : ((u : Subring.unitClosedBall L) : L) ≠ 0 := fun h0 => by simp [h0] at hu
  refine ⟨fun i j => ?_, by simpa using hρ0, by simpa using hu, ?_⟩
  · rw [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp [hu]
  · rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact pow_ne_zero _ hu0

namespace AnalyticWeight

variable {e : Embeddings L K ι} {S : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ : ℝ}
  (κ : AnalyticWeight e S ρ)

/-- **The scalars act by `κ(u, u²) = n(u) v(u²)`**. Source: roadmap §1.3.5 ("acts on `A` by the
scalar `n(u) v(u²)`"). -/
theorem kappaSlash_smul_one [CharZero K] (u : (Subring.unitClosedBall L)ˣ)
    (hu : ((u : Subring.unitClosedBall L) : L) • (1 : Matrix (Fin 2) (Fin 2) L) ∈ S)
    (f : Restricted K (1 : ι → ℝ)) :
    κ.kappaSlash ⟨_, hu⟩ f = ((κ.n u : K) * (κ.v (unitsIncl L u ^ 2) : K)) • f := by
  have hM : MultiBounds ρ (e.toMulti (((u : Subring.unitClosedBall L) : L) •
      (1 : Matrix (Fin 2) (Fin 2) L))) := e.multiBounds_toMulti κ.expansion.bounds hu
  -- the Möbius substitution of a scalar matrix is the identity
  have hmob : ∀ i, mobius (e.toMulti (((u : Subring.unitClosedBall L) : L) •
      (1 : Matrix (Fin 2) (Fin 2) L))) i = X K 1 i := fun i => by
    have hlin : lin (e.toMulti (((u : Subring.unitClosedBall L) : L) •
        (1 : Matrix (Fin 2) (Fin 2) L))) i = C 1 (e.emb i (u : Subring.unitClosedBall L)) := by
      simp [lin]
    have hnum : num (e.toMulti (((u : Subring.unitClosedBall L) : L) •
        (1 : Matrix (Fin 2) (Fin 2) L))) i =
          C 1 (e.emb i (u : Subring.unitClosedBall L)) * X K 1 i := by
      simp [num]
    rw [mobius, hnum, ← hlin, mul_comm _ (X K 1 i), mul_assoc, lin_mul_linInv hM i, mul_one]
  have hsub : mobiusSubst hM f = f := by
    have h : mobiusSubst hM = AlgHom.id K _ :=
      algHom_ext_of_continuous (continuous_mobiusSubst hM) continuous_id fun i => by
        rw [mobiusSubst_X, hmob i, AlgHom.id_apply]
    exact DFunLike.congr_fun h f
  -- the expansion at `(0, u)` is the constant `n(u)`
  have hcol : κ.expansion.col ((((u : Subring.unitClosedBall L) : L) •
      (1 : Matrix (Fin 2) (Fin 2) L)) 1 0) ((((u : Subring.unitClosedBall L) : L) •
        (1 : Matrix (Fin 2) (Fin 2) L)) 1 1) = C 1 (κ.n u : K) := by
    refine e.ext_of_forall_evalPoint_eq fun z => ?_
    have hl : κ.expansion.bounds.linUnit hu z = u := Units.ext (Subtype.ext (by simp))
    rw [κ.expansion.evalPoint_col hu z, hl]
    exact (aeval_C_self (e.norm_point_le_one z) _).symm
  have hdet : (κ.detChar ⟨_, hu⟩ : K) = (κ.v (unitsIncl L u ^ 2) : K) := by
    refine congrArg (fun x => ((κ.v x : Kˣ) : K)) (Units.ext ?_)
    simp [sq]
  have hCf : C 1 (κ.n u : K) * f = (κ.n u : K) • f := by
    rw [Algebra.smul_def, algebraMap_apply]
  rw [kappaSlash_apply, hsub, autFactor, hcol, smul_mul_assoc, hCf, smul_smul, hdet, mul_comm]

/-- **The weight condition**: an element fixed by a scalar acting through `κ(u, u²) ≠ 1` is zero;
hence `A^G = 0` unless `κ(γ, γ²) = 1` on `G`. Source: roadmap §1.3.5. -/
theorem eq_zero_of_kappaSlash_eq_self_of_ne_one [CharZero K] (u : (Subring.unitClosedBall L)ˣ)
    (hu : ((u : Subring.unitClosedBall L) : L) • (1 : Matrix (Fin 2) (Fin 2) L) ∈ S)
    (hκ : (κ.n u : K) * (κ.v (unitsIncl L u ^ 2) : K) ≠ 1) {f : Restricted K (1 : ι → ℝ)}
    (hf : κ.kappaSlash ⟨_, hu⟩ f = f) : f = 0 := by
  rw [κ.kappaSlash_smul_one u hu f] at hf
  have hc : (κ.n u : K) * (κ.v (unitsIncl L u ^ 2) : K) - 1 ≠ 0 := sub_ne_zero.mpr hκ
  have h0 : ((κ.n u : K) * (κ.v (unitsIncl L u ^ 2) : K) - 1) • f = 0 := by
    rw [sub_smul, one_smul, hf, sub_self]
  rw [← inv_smul_smul₀ hc f, h0, smul_zero]

end AnalyticWeight

end AutomorphicForm
