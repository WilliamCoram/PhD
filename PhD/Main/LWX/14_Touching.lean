/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«13_AtkinLehnerInst»
import PhD.Main.LWX.«13_SlopesSeam»
import PhD.Main.TateFredholm.«12_RieszColeman»
import PhD.Main.NewtonPolygons.Product
import PhD.Main.QMF.Weight.«06_Algebraic»

/-!
# Step I of [LWX, Theorem 1.3]: the squeeze — SKELETON (tranche 5 of `lwx-theta`)

[LWX, §3.23 Step I] (`lwx.txt:1807–1846`): at a classical weight `χ_k = (k, ψ)` of conductor
`q² = p²`, the Newton polygon of `∑ c_n(T_{χ_k}) Xⁿ` touches the Corollary 3.18 lower bound
polygon at `P_k = (n_{k+1}, λ(n_{k+1}) v(T_{χ_k}))`.  The source's argument:

* [LWX, Prop 3.22] (hypothesis **H1**, `AtkinLehnerHypothesis`): the `U_p`-slopes on
  `S^D_{k+2}(ψ) ⊕ S^D_{k+2}(ψ⁻¹)` sum to `(k+1)²qt` — here read off the determinants of the two
  classical matrices, `det A · det A' = p^{(k+1)·n_{k+1}}`;
* the classical space is a finite `U_p`-stable piece of the overconvergent space, so the Fredholm
  determinant splits off the polynomial factor `det(1 − X·A)` (`charPowerSeries_eq_mul_of_stable`);
* the Newton polygon of a product is the Minkowski sum of the factors' polygons
  (`PhD/Main/NewtonPolygons/Product.lean`), so **the height of the overconvergent polygon at
  `n_{k+1}` is at most `−log‖det A‖`** (`height_le_negLogNorm_det`);
* the lower bound [LWX, Cor 3.18] at `n_{k+1}`, for both `ψ` and `ψ⁻¹`, and the arithmetic
  [LWX, (3.23.1)] `2λ(n_{k+1})·v(T_{χ_k}) = (k+1)·n_{k+1}·v(p)`;
* the squeeze: `λv ≤ h_ψ ≤ S_ψ`, `λv ≤ h_{ψ⁻¹} ≤ S_{ψ⁻¹}`, `S_ψ + S_{ψ⁻¹} = 2λv`, hence
  `h_ψ = λv` — the touching.

**A deliberate weakening of the source's route.**  [LWX] pass through classicality
([LWX, Prop 2.15]) to identify the classical slopes with the *first* `n_{k+1}` overconvergent
slopes, and then use the sum of those.  The squeeze only needs the inequality
`h_ψ ≤ S_ψ` (the first `n_{k+1}` slopes are at most *any* `n_{k+1}` of the slopes), which is the
Minkowski bound and needs no classicality at all.  Classicality is then a consequence of the
touching rather than an input; see `.mathlib-quality/lwx-theta/decomposition.md`, tranche 5.
Nothing here depends on Jacquet–Langlands (`.mathlib-quality/lwx-stepone/JL-AUDIT.md`).

## Main declarations

* `LWX.IsClassicalShape` — a weight whose automorphy factor at every disc conjugate of every
  certificate matrix has the classical shape `u · (cz+d)^k`, with the nebentypus constants `u`.
* `LWX.mem_locPolyDegSubmoduleBlock_discHeckeBlockOp_of_isClassicalShape` — the classical
  subspace is `U_p`-stable at such a weight (directly, without the theta operator).
* `LWX.ClassicalData`, `LWX.ClassicalData.matrix` — the halo point of a classical weight with its
  shape, and the matrix of `U_p` on the classical subspace there.
* `LWX.charPowerSeries_eq_mul_of_stable` — the finite factor `det(1 − X·U_p) = R · det(1 − X·A)`.
* `LWX.height_mul_le_height_right`, `LWX.height_le_negLogNorm_det` — the Minkowski upper bound.
* `LWX.isStepOneTouching_of_atkinLehnerHypothesis` — **Step I**, granted H1.
* `LWX.hasUnitBand_of_atkinLehnerHypothesis` — the hand-off to Step II.
-/

open Filter Topology TateFredholm QMF QMF.Weight AbstractHeckeOperatorSlash
open scoped Nat TateFredholm Pointwise

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

/-! ### General lemmas: polygons of products, and determinants under H1 -/

omit [CompleteSpace K] in
/-- **The Minkowski upper bound**: the polygon of a product lies on or below the polygon of
either factor (the split `i = 0` of `NewtonPolygon₀.minkowskiHeight`). -/
theorem height_mul_le_height_right {f g : PowerSeries K}
    (hf : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c f)
    (hg : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c g) (hf0 : PowerSeries.coeff 0 f = 1)
    (hg0 : PowerSeries.coeff 0 g = 1) (n : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm (f * g)).height n ≤
      (newtonPolygon₀OfPowerSeries negLogNorm g).height n := by
  have hf0' : PowerSeries.coeff 0 f ≠ 0 := by rw [hf0]; exact one_ne_zero
  have hg0' : PowerSeries.coeff 0 g ≠ 0 := by rw [hg0]; exact one_ne_zero
  rw [height_newtonPolygon₀OfPowerSeries_mul hf hg hf0' hg0' n]
  refine le_trans (NewtonPolygon₀.minkowskiHeight_le (Nat.zero_le n)) (le_of_eq ?_)
  rw [Nat.cast_zero, height_zero_newtonPolygon₀OfPowerSeries hf0, zero_add, sub_zero]

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- The polygon lies on or below the point `(n, −log‖coeff n g‖)`. -/
theorem height_le_coeffVal {g : PowerSeries K}
    (hg : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c g)
    (hg0 : PowerSeries.coeff 0 g = 1) (n : ℕ) :
    (newtonPolygon₀OfPowerSeries negLogNorm g).height n ≤
      ((coeffVal g n : WithTop ℝ) : WithBotTop ℝ) := by
  have hg0' : PowerSeries.coeff 0 g ≠ 0 := by rw [hg0]; exact one_ne_zero
  have h := (isEntireNewtonPolygonOf_coeffVal hg hg0').toIsNewtonPolygonOf.height_le n
  rwa [pointHeight_eq_coe] at h

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The top coefficient of `charpolyRev` is `(−1)^N · det`. -/
theorem coeff_charpolyRev_card {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n K) :
    A.charpolyRev.coeff (Fintype.card n) = (-1) ^ Fintype.card n * A.det := by
  have h2 : ((-1 : K)) ^ Fintype.card n * (-1) ^ Fintype.card n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  rw [← Matrix.reverse_charpoly, Polynomial.coeff_reverse, A.charpoly_natDegree_eq_dim,
    Polynomial.revAt_le le_rfl, Nat.sub_self, Matrix.det_eq_sign_charpoly_coeff, ← mul_assoc,
    h2, one_mul]

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **H1 on determinants** ([LWX, Prop 3.22]'s "the total sum of the `U_p`-slopes … is
`(k+1)²q⁻¹pᵐt`"): from `A·B = c·1`, `Q·P = 1` and `A' = P·B·Q`,
`−log‖det A‖ − log‖det A'‖ = card·(−log‖c‖)`. -/
theorem neg_log_norm_det_add_of_mul_eq_smul {n : Type*} [Fintype n] [DecidableEq n]
    {A B A' P Q : Matrix n n K} {c : K} (hc : c ≠ 0) (hAB : A * B = c • (1 : Matrix n n K))
    (hQP : Q * P = 1) (hA' : A' = P * B * Q) :
    -Real.log ‖A.det‖ + -Real.log ‖A'.det‖ = Fintype.card n * (-Real.log ‖c‖) := by
  have hprod : A.det * B.det = c ^ Fintype.card n := Matrix.det_mul_det_of_mul_eq_smul hAB
  have hA0 : A.det ≠ 0 := Matrix.det_ne_zero_of_mul_eq_smul hc hAB
  have hB0 : B.det ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hprod
    exact pow_ne_zero _ hc hprod.symm
  have hQP' : Q.det * P.det = 1 := by rw [← Matrix.det_mul, hQP, Matrix.det_one]
  have hA'B : A'.det = B.det := by
    rw [hA', Matrix.det_mul, Matrix.det_mul]
    calc P.det * B.det * Q.det = B.det * (Q.det * P.det) := by ring
      _ = B.det := by rw [hQP', mul_one]
  have hlog : Real.log ‖A.det‖ + Real.log ‖B.det‖
      = (Fintype.card n : ℝ) * Real.log ‖c‖ := by
    rw [← Real.log_mul (norm_ne_zero_iff.2 hA0) (norm_ne_zero_iff.2 hB0), ← norm_mul, hprod,
      norm_pow, Real.log_pow]
  rw [hA'B]
  linarith

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The determinants under H1 are nonzero. -/
theorem det_ne_zero_of_mul_eq_smul' {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n K} {c : K} (hc : c ≠ 0) (hAB : A * B = c • (1 : Matrix n n K)) :
    A.det ≠ 0 :=
  Matrix.det_ne_zero_of_mul_eq_smul hc hAB

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The Atkin–Lehner partner's determinant is nonzero as well: `det A' = det B`, and
`det A · det B = c^N ≠ 0`. -/
theorem det_ne_zero_of_mul_eq_smul_conj {n : Type*} [Fintype n] [DecidableEq n]
    {A B A' P Q : Matrix n n K} {c : K} (hc : c ≠ 0) (hAB : A * B = c • (1 : Matrix n n K))
    (hQP : Q * P = 1) (hA' : A' = P * B * Q) :
    A'.det ≠ 0 := by
  have hprod : A.det * B.det = c ^ Fintype.card n := Matrix.det_mul_det_of_mul_eq_smul hAB
  have hB0 : B.det ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hprod
    exact pow_ne_zero _ hc hprod.symm
  have hQP' : Q.det * P.det = 1 := by rw [← Matrix.det_mul, hQP, Matrix.det_one]
  have hP0 : P.det ≠ 0 := fun h0 => by rw [h0, mul_zero] at hQP'; exact one_ne_zero hQP'.symm
  have hQ0 : Q.det ≠ 0 := fun h0 => by rw [h0, zero_mul] at hQP'; exact one_ne_zero hQP'.symm
  rw [hA', Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero hP0 hB0) hQ0

variable {G : Type*} [Group G] {Γ : Subgroup G} (θG : G →* Matrix (Fin 2) (Fin 2) ℚ_[p])
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : ℕ) (ψ : ℚ_[p] →+* K) {UK : Subgroup Kˣ} {ρ : ℝ}
variable (U : Subgroup G) (hU : (U : Set G) ⊆ levelM1 (p := p) θG)
  (vRep : Fin p → G) (hvΔ : ∀ t, vRep t ∈ levelM1 (p := p) θG) (idx : ι → Fin p → ι)
  (uu : ι → Fin p → U)

/-! ### The classical shape of a weight -/

/-- The `K`-side disc conjugate `t_{a'}⁻¹·δ·t_a` of the certificate matrix `δ = u_{i,t}·v_t`. -/
def certConj (i : ι) (t : Fin p) (a : ZMod (p ^ h)) : Matrix (Fin 2) (Fin 2) K :=
  ((discConjK h (certM1 θG U hU vRep hvΔ uu i t) a ψ : M1Kh h ψ) : Matrix (Fin 2) (Fin 2) K)

/-- **The classical shape of exponent `k`**: at every disc conjugate of every certificate matrix
the automorphy factor is `u · (cz + d)^k`, i.e. `autFactor · L = C u · L^{k+1}`, with a constant
`u` (the nebentypus at `d`) depending on the block.  This is exactly what `12_Bol.lean`'s
equivariance consumes, and what a classical weight `(k, ψ)` of conductor `p²` has at level
`h ≥ 1`. -/
def IsClassicalShape (κ : AnalyticWeight UK (M1Kh h ψ) ρ) (k : ℕ)
    (u : ι → Fin p → ZMod (p ^ h) → K) : Prop :=
  ∀ i t a, κ.toWeightSeries.autFactor (certConj θG h ψ U hU vRep hvΔ uu i t a)
      * linX (certConj θG h ψ U hU vRep hvΔ uu i t a)
    = PowerSeries.C (u i t a) * linX (certConj θG h ψ U hU vRep hvΔ uu i t a) ^ (k + 1)

/-! ### Stability of the classical subspace, directly from the shape -/

omit [CharZero K] in
/-- Column `i ≤ k` of a classical-shape action is the polynomial `u·(cz+d)^{k−i}(az+b)^i`
(`QMF.autFactor_mul_mobius_pow_eq` with the constant). -/
theorem autFactor_mul_mobius_pow_of_shape {S : Submonoid (Matrix (Fin 2) (Fin 2) K)}
    (κ : AnalyticWeight UK S ρ) {γ : Matrix (Fin 2) (Fin 2) K} (hd : γ 1 1 ≠ 0) {k : ℕ} {u : K}
    (hA : κ.toWeightSeries.autFactor γ * linX γ = PowerSeries.C u * linX γ ^ (k + 1))
    {i : ℕ} (hi : i ≤ k) :
    κ.toWeightSeries.autFactor γ * mobius γ ^ i
      = PowerSeries.C u * (linX γ ^ (k - i) * numX γ ^ i) := by
  have hinv : linX γ * (linX γ)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by rw [constantCoeff_linX]; exact hd)
  have hAk : κ.toWeightSeries.autFactor γ = PowerSeries.C u * linX γ ^ k := by
    calc κ.toWeightSeries.autFactor γ
        = κ.toWeightSeries.autFactor γ * (linX γ * (linX γ)⁻¹) := by rw [hinv, mul_one]
      _ = κ.toWeightSeries.autFactor γ * linX γ * (linX γ)⁻¹ := by ring
      _ = PowerSeries.C u * linX γ ^ (k + 1) * (linX γ)⁻¹ := by rw [hA]
      _ = PowerSeries.C u * linX γ ^ k * (linX γ * (linX γ)⁻¹) := by ring
      _ = PowerSeries.C u * linX γ ^ k := by rw [hinv, mul_one]
  rw [hAk, mobius, mul_pow]
  calc PowerSeries.C u * linX γ ^ k * (numX γ ^ i * ((linX γ)⁻¹) ^ i)
      = PowerSeries.C u * (linX γ ^ (k - i) * numX γ ^ i)
          * (linX γ ^ i * ((linX γ)⁻¹) ^ i) := by
        rw [← pow_sub_mul_pow (linX γ) hi]; ring
    _ = PowerSeries.C u * (linX γ ^ (k - i) * numX γ ^ i) := by
        rw [← mul_pow, hinv, one_pow, mul_one]

omit hp [CharZero K] in
/-- **[T5.9a]** A block of a `blockOp`, applied.  (`LWX.blockProj_blockOp` in
`PhD/Main/LWX/09_DiscModel.lean` is this at `σ = ZMod (p ^ h)` and is `private`; its proper home is
`PhD/Main/TateFredholm/06_BlockOp.lean` next to `blockOp_blockIncl`.) -/
private theorem blockProj_blockOp' {σ : Type*} [Fintype σ] [DecidableEq σ] {I : Type*}
    [DecidableEq I] (T : σ → σ → (c(I, K) →L[K] c(I, K))) (f : c(σ × I, K)) (a : σ) :
    cSpace.blockProj a (blockOp T f) = ∑ b : σ, T a b (cSpace.blockProj b f) := by
  have hf : blockOp T f
      = ∑ a' : σ, ∑ b : σ, cSpace.blockIncl a' (T a' b (cSpace.blockProj b f)) := by
    rw [blockOp]
    simp only [_root_.sum_apply, ContinuousLinearMap.comp_apply]
  rw [hf, map_sum, Finset.sum_eq_single a]
  · rw [map_sum]
    exact Finset.sum_congr rfl fun b _ => by rw [cSpace.blockProj_blockIncl, if_pos rfl]
  · intro a' _ hne
    rw [map_sum]
    exact Finset.sum_eq_zero fun b _ => by
      rw [cSpace.blockProj_blockIncl, if_neg fun heq => hne heq.symm]
  · exact fun hcon => absurd (Finset.mem_univ a) hcon

omit [CharZero K] in
/-- A classical-shape action preserves polynomials of degree `≤ k` on one disc
(`QMF.polySubmodule_stable` with the constant). -/
theorem kappaSlash_mem_polySubmodule_of_shape {S : Submonoid (Matrix (Fin 2) (Fin 2) K)}
    (κ : AnalyticWeight UK S ρ) (g : S) {k : ℕ} {u : K}
    (hA : κ.toWeightSeries.autFactor g.1 * linX g.1 = PowerSeries.C u * linX g.1 ^ (k + 1))
    {f : c(ℕ, K)} (hf : f ∈ polySubmodule K k) : κ.kappaSlash g f ∈ polySubmodule K k := by
  intro j hj
  rw [AnalyticWeight.kappaSlash_def, WeightSeries.kappaSlash_apply,
    tsum_eq_sum (s := Finset.range (k + 1))
      (fun i hi => by rw [hf i (by simpa using hi), mul_zero])]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [autFactor_mul_mobius_pow_of_shape κ (κ.toWeightSeries.bounds.d_ne_zero g.2) hA hik,
    PowerSeries.coeff_C_mul, mul_comm (linX (g : Matrix (Fin 2) (Fin 2) K) ^ (k - i)),
    coeff_numX_pow_mul_linX_pow_eq_zero _ (by omega), mul_zero, zero_mul]

omit [CharZero K] in
/-- The disc action of a classical-shape weight preserves the locally polynomial functions of
degree `≤ k`. -/
theorem discSlash_mem_locPolyDegSubmodule_of_shape (κ : AnalyticWeight UK (M1Kh h ψ) ρ)
    (δ : M1 p) {k : ℕ} {u : ZMod (p ^ h) → K}
    (hA : ∀ a, κ.toWeightSeries.autFactor
          ((discConjK h δ a ψ : M1Kh h ψ) : Matrix (Fin 2) (Fin 2) K)
        * linX ((discConjK h δ a ψ : M1Kh h ψ) : Matrix (Fin 2) (Fin 2) K)
      = PowerSeries.C (u a)
        * linX ((discConjK h δ a ψ : M1Kh h ψ) : Matrix (Fin 2) (Fin 2) K) ^ (k + 1))
    {f : c(ZMod (p ^ h) × ℕ, K)} (hf : f ∈ locPolyDegSubmodule p K h k) :
    discSlash h ψ κ δ f ∈ locPolyDegSubmodule p K h k := by
  intro a j hj
  have hproj : cSpace.blockProj (discImage h δ a) f ∈ polySubmodule K k := fun m hm => by
    rw [cSpace.blockProj_apply]
    exact hf _ m hm
  rw [← cSpace.blockProj_apply a (discSlash h ψ κ δ f) j, blockProj_discSlash]
  exact kappaSlash_mem_polySubmodule_of_shape κ (discConjK h δ a ψ) (hA a) hproj j hj

omit [CharZero K] in
/-- **The classical subspace is `U_p`-stable at a classical-shape weight**, with no theta
operator: blockwise `discSlash_mem_locPolyDegSubmodule_of_shape`. -/
theorem mem_locPolyDegSubmoduleBlock_discHeckeBlockOp_of_isClassicalShape
    (κ : AnalyticWeight UK (M1Kh h ψ) ρ) {k : ℕ} {u : ι → Fin p → ZMod (p ^ h) → K}
    (hcl : IsClassicalShape θG h ψ U hU vRep hvΔ uu κ k u)
    {f : c(ι × (ZMod (p ^ h) × ℕ), K)}
    (hf : f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) :
    discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu f
      ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k := by
  intro i a j hj
  have hproj : ∀ i' : ι, cSpace.blockProj i' f ∈ locPolyDegSubmodule p K h k :=
    fun i' a' m hm => by
      rw [cSpace.blockProj_apply]
      exact hf i' a' m hm
  rw [← cSpace.blockProj_apply i (discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu f) (a, j),
    discHeckeBlockOp, blockProj_blockOp', cSpace.sum_apply]
  refine Finset.sum_eq_zero fun i' _ => ?_
  rw [discHeckeBlock, _root_.sum_apply, cSpace.sum_apply]
  refine Finset.sum_eq_zero fun t _ => ?_
  exact discSlash_mem_locPolyDegSubmodule_of_shape h ψ κ _ (hcl i t) (hproj i') a j hj

/-- The matrix of `U_p` on the classical subspace at a classical-shape weight. -/
def classicalMatrix [Nonempty ι] (κ : AnalyticWeight UK (M1Kh h ψ) ρ) {k : ℕ}
    {u : ι → Fin p → ZMod (p ^ h) → K} (hcl : IsClassicalShape θG h ψ U hU vRep hvΔ uu κ k u) :
    Matrix (Fin (Fintype.card ι * ((k + 1) * p ^ h)))
      (Fin (Fintype.card ι * ((k + 1) * p ^ h))) K :=
  upMatrix (p := p) (K := K) (ι := ι) h k (discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu)
    fun _ hf => mem_locPolyDegSubmoduleBlock_discHeckeBlockOp_of_isClassicalShape θG h ψ U hU
      vRep hvΔ idx uu κ hcl hf

/-! ### The finite factor -/

omit hp [Fintype ι] [DecidableEq ι] [CharZero K] in
/-- On the block index, forgetting the `Fin` bound is injective (the `12_StepOne.lean` helper
`triple_val_inj`, restated as an `Function.Injective` for `Finset.card_image_of_injective`). -/
private theorem triple_val_inj' {k : ℕ} :
    Function.Injective (fun x : ι × ZMod (p ^ h) × Fin (k + 1) =>
      ((x.1, (x.2.1, (x.2.2 : ℕ))) : ι × (ZMod (p ^ h) × ℕ))) := by
  rintro ⟨x1, x2, x3⟩ ⟨y1, y2, y3⟩ hxy
  simp only [Prod.mk.injEq] at hxy ⊢
  exact ⟨hxy.1, hxy.2.1, Fin.ext hxy.2.2⟩

variable (p ι) in
/-- The classical coordinates: Taylor degrees `≤ k` in every disc of every class. -/
def classicalSupport (k : ℕ) : Finset (ι × (ZMod (p ^ h) × ℕ)) :=
  Finset.univ.image fun x : ι × ZMod (p ^ h) × Fin (k + 1) => (x.1, (x.2.1, (x.2.2 : ℕ)))

omit [CharZero K] in
theorem mem_classicalSupport_iff (k : ℕ) (x : ι × (ZMod (p ^ h) × ℕ)) :
    x ∈ classicalSupport p ι h k ↔ x.2.2 ≤ k := by
  rw [classicalSupport, Finset.mem_image]
  refine ⟨?_, fun hx => ⟨⟨x.1, x.2.1, ⟨x.2.2, by omega⟩⟩, Finset.mem_univ _, rfl⟩⟩
  rintro ⟨y, -, rfl⟩
  exact Nat.lt_succ_iff.mp y.2.2.isLt

omit [CharZero K] in
theorem card_classicalSupport (k : ℕ) :
    (classicalSupport p ι h k).card = Fintype.card ι * ((k + 1) * p ^ h) := by
  rw [classicalSupport, Finset.card_image_of_injective _ (triple_val_inj' (p := p) h),
    Finset.card_univ, Fintype.card_prod, Fintype.card_prod, ZMod.card, Fintype.card_fin]
  ring

omit [CharZero K] in
/-- Truncation to the classical coordinates lands in the classical subspace. -/
theorem truncation_classicalSupport_mem (k : ℕ) (f : c(ι × (ZMod (p ^ h) × ℕ), K)) :
    truncation (classicalSupport p ι h k) f
      ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k := fun i a j hj => by
  refine (truncation_apply _ _ _).trans (if_neg fun hmem => ?_)
  have hle : j ≤ k := (mem_classicalSupport_iff h k (i, (a, j))).1 hmem
  omega

omit [CharZero K] in
/-- Truncation to the classical coordinates fixes the classical subspace. -/
theorem truncation_classicalSupport_of_mem (k : ℕ) {f : c(ι × (ZMod (p ^ h) × ℕ), K)}
    (hf : f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) :
    truncation (classicalSupport p ι h k) f = f := by
  refine DFunLike.ext _ _ fun x => ?_
  rw [truncation_apply]
  split_ifs with hmem
  · rfl
  · exact (hf x.1 x.2.1 x.2.2 (by
      by_contra hcon
      exact hmem ((mem_classicalSupport_iff h k x).2 (by omega)))).symm

omit hp [Fintype ι] [CharZero K] in
/-- **[T5.14a]** The matrix of `pr ∘ T` agrees with that of `T` on rows inside the support. -/
private theorem matrixCoeff_truncation_comp (S : Finset (ι × (ZMod (p ^ h) × ℕ)))
    (T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K))
    {j : ι × (ZMod (p ^ h) × ℕ)} (hj : j ∈ S) (i : ι × (ZMod (p ^ h) × ℕ)) :
    matrixCoeff ((truncation S).comp T) j i = matrixCoeff T j i := by
  show truncation S (T (cSpace.single i 1)) j = _
  rw [truncation_apply, if_pos hj]
  rfl

omit hp [Fintype ι] [CharZero K] in
/-- **[T5.14a]** Rows outside the support vanish. -/
private theorem matrixCoeff_truncation_comp_of_notMem (S : Finset (ι × (ZMod (p ^ h) × ℕ)))
    (T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K))
    {j : ι × (ZMod (p ^ h) × ℕ)} (hj : j ∉ S) (i : ι × (ZMod (p ^ h) × ℕ)) :
    matrixCoeff ((truncation S).comp T) j i = 0 := by
  show truncation S (T (cSpace.single i 1)) j = _
  rw [truncation_apply, if_neg hj]

/-- **[T5.14a]** The classical coordinates are indexed by `ι × ZMod (p^h) × Fin (k+1)`. -/
private def classicalEquiv (k : ℕ) :
    ι × ZMod (p ^ h) × Fin (k + 1) ≃ {x // x ∈ classicalSupport p ι h k} where
  toFun x := ⟨(x.1, (x.2.1, (x.2.2 : ℕ))),
    (mem_classicalSupport_iff h k _).2 (Nat.lt_succ_iff.mp x.2.2.isLt)⟩
  invFun y := (y.1.1, (y.1.2.1,
    ⟨y.1.2.2, Nat.lt_succ_of_le ((mem_classicalSupport_iff h k y.1).1 y.2)⟩))
  left_inv x := by obtain ⟨a, b, c⟩ := x; rfl
  right_inv y := Subtype.ext rfl

/-- The matrix of an operator on the classical coordinates. -/
def classicalCoordMatrix (k : ℕ)
    (T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K)) :
    Matrix (ι × ZMod (p ^ h) × Fin (k + 1)) (ι × ZMod (p ^ h) × Fin (k + 1)) K :=
  Matrix.of fun x y => matrixCoeff T (x.1, (x.2.1, (x.2.2 : ℕ))) (y.1, (y.2.1, (y.2.2 : ℕ)))

omit [CharZero K] in
/-- The Fredholm determinant of `pr ∘ T` is `det(1 − X·M)` for the classical coordinate matrix
`M`: rows outside the classical coordinates vanish (`charCoeff_eq_det_coeff`). -/
theorem charPowerSeries_truncation_comp (k : ℕ)
    (T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K)) :
    charPowerSeries ((truncation (classicalSupport p ι h k)).comp T)
      = ((classicalCoordMatrix h k T).charpolyRev : PowerSeries K) := by
  have hmat : (Matrix.of fun j i : {x // x ∈ classicalSupport p ι h k} =>
        Polynomial.C (matrixCoeff ((truncation (classicalSupport p ι h k)).comp T) j i))
      = ((classicalCoordMatrix h k T).map Polynomial.C).submatrix
          (classicalEquiv h k).symm (classicalEquiv h k).symm := by
    refine Matrix.ext fun a b => ?_
    have ha : ((((classicalEquiv h k).symm a).1, ((((classicalEquiv h k).symm a).2.1,
        (((classicalEquiv h k).symm a).2.2 : ℕ)))) : ι × (ZMod (p ^ h) × ℕ))
        = (a : ι × (ZMod (p ^ h) × ℕ)) :=
      congrArg Subtype.val ((classicalEquiv h k).apply_symm_apply a)
    have hb : ((((classicalEquiv h k).symm b).1, ((((classicalEquiv h k).symm b).2.1,
        (((classicalEquiv h k).symm b).2.2 : ℕ)))) : ι × (ZMod (p ^ h) × ℕ))
        = (b : ι × (ZMod (p ^ h) × ℕ)) :=
      congrArg Subtype.val ((classicalEquiv h k).apply_symm_apply b)
    rw [Matrix.submatrix_apply, Matrix.map_apply, classicalCoordMatrix, Matrix.of_apply,
      Matrix.of_apply, ha, hb, matrixCoeff_truncation_comp h (classicalSupport p ι h k) T a.2]
  refine PowerSeries.ext fun n => ?_
  rw [charPowerSeries_coeff, charCoeff_eq_det_coeff _ (classicalSupport p ι h k)
      (fun j hj i => matrixCoeff_truncation_comp_of_notMem h _ T hj i) n,
    Polynomial.coeff_coe, Matrix.charpolyRev]
  congr 1
  rw [← Matrix.det_submatrix_equiv_self (classicalEquiv h k).symm
    (1 - (Polynomial.X : Polynomial K) • (classicalCoordMatrix h k T).map Polynomial.C)]
  refine congrArg Matrix.det (Matrix.ext fun a b => ?_)
  rw [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.smul_apply, ← Matrix.submatrix_apply (1 : Matrix (ι × ZMod (p ^ h) × Fin (k + 1))
      (ι × ZMod (p ^ h) × Fin (k + 1)) (Polynomial K)) (classicalEquiv h k).symm
      (classicalEquiv h k).symm a b,
    Matrix.submatrix_one_equiv, ← Matrix.submatrix_apply
      ((classicalCoordMatrix h k T).map Polynomial.C) (classicalEquiv h k).symm
      (classicalEquiv h k).symm a b, ← hmat]

omit [CharZero K] in
/-- `T ∘ pr` and `pr ∘ T` have the same Fredholm determinant (`charPowerSeries_comm`). -/
theorem charPowerSeries_comp_truncation (k : ℕ)
    {T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K)} (hT : IsCompactoid T) :
    charPowerSeries (T.comp (truncation (classicalSupport p ι h k)))
      = charPowerSeries ((truncation (classicalSupport p ι h k)).comp T) := by
  exact charPowerSeries_comm (J := ι × (ZMod (p ^ h) × ℕ)) T
    (truncation (R := K) (classicalSupport p ι h k)) hT

omit [CharZero K] in
/-- **The finite factor** ([LWX, §3.23 Step I], the classical space as a stable piece): if `T`
preserves the classical subspace then `det(1 − X·T) = det(1 − X·T(1 − pr)) · det(1 − X·M)`, since
`T(1 − pr) · T pr = 0` (`charPowerSeries_add_of_mul_eq_zero`, one-sided). -/
theorem charPowerSeries_eq_mul_of_stable (k : ℕ)
    {T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K)} (hT : IsCompactoid T)
    (hst : ∀ f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k,
      T f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) :
    charPowerSeries T
      = charPowerSeries (T.comp (1 - truncation (classicalSupport p ι h k)))
        * ((classicalCoordMatrix h k T).charpolyRev : PowerSeries K) := by
  set pr := truncation (R := K) (classicalSupport p ι h k) with hpr
  have hsplit : T = T.comp (1 - pr) + T.comp pr := by
    rw [← ContinuousLinearMap.comp_add, sub_add_cancel]
    exact (ContinuousLinearMap.comp_id T).symm
  have hzero : (T.comp (1 - pr)) * (T.comp pr) = 0 := by
    refine ContinuousLinearMap.ext fun f => ?_
    have hmem : T (pr f) ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k :=
      hst _ (truncation_classicalSupport_mem h k f)
    have hy : (1 - pr) (T (pr f)) = 0 := by
      show T (pr f) - pr (T (pr f)) = 0
      rw [truncation_classicalSupport_of_mem h k hmem, sub_self]
    show T ((1 - pr) (T (pr f))) = 0
    rw [hy, map_zero]
  calc charPowerSeries T
      = charPowerSeries (T.comp (1 - pr) + T.comp pr) := by rw [← hsplit]
    _ = charPowerSeries (T.comp (1 - pr)) * charPowerSeries (T.comp pr) :=
        charPowerSeries_add_of_mul_eq_zero (hT.comp_right _) (hT.comp_right _) hzero
    _ = charPowerSeries (T.comp (1 - pr))
          * ((classicalCoordMatrix h k T).charpolyRev : PowerSeries K) := by
        rw [hpr, charPowerSeries_comp_truncation h k hT, charPowerSeries_truncation_comp h k T]

omit [CharZero K] in
/-- **[T5.17a]** The classical basis: the coordinate basis of the classical subspace, indexed by
`ι × ZMod (p^h) × Fin (k+1)` through `LWX.locPolyDegBlockEquiv`. -/
private noncomputable def classicalBasis (k : ℕ) :
    Module.Basis (ι × ZMod (p ^ h) × Fin (k + 1)) K
      (locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) :=
  (Pi.basisFun K (ι × ZMod (p ^ h) × Fin (k + 1))).map (locPolyDegBlockEquiv h k).symm

omit [CharZero K] in
/-- **[T5.17a]** The coordinates of a classical form in the classical basis are its values at the
classical coordinates. -/
private theorem repr_classicalBasis (k : ℕ)
    (f : locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k)
    (x : ι × ZMod (p ^ h) × Fin (k + 1)) :
    (classicalBasis h k).repr f x
      = (f : c(ι × (ZMod (p ^ h) × ℕ), K)) (x.1, (x.2.1, (x.2.2 : ℕ))) := rfl

omit [CharZero K] in
/-- **[T5.17a]** The classical basis vectors are the coordinate deltas. -/
private theorem coe_classicalBasis (k : ℕ) (y : ι × ZMod (p ^ h) × Fin (k + 1)) :
    ((classicalBasis h k y : locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) :
      c(ι × (ZMod (p ^ h) × ℕ), K))
      = cSpace.single (y.1, (y.2.1, (y.2.2 : ℕ))) 1 := by
  show (∑ x : ι × ZMod (p ^ h) × Fin (k + 1),
      cSpace.single (x.1, (x.2.1, (x.2.2 : ℕ)))
        (Pi.basisFun K (ι × ZMod (p ^ h) × Fin (k + 1)) y x)) = _
  rw [Finset.sum_eq_single y
      (fun x _ hx => by
        rw [Pi.basisFun_apply, Pi.single_eq_of_ne hx]
        exact DFunLike.ext _ _ fun z => by
          by_cases hz : z = (x.1, (x.2.1, (x.2.2 : ℕ)))
          · rw [hz, cSpace.single_apply_self]; rfl
          · rw [cSpace.single_apply_of_ne hz]; rfl) (by simp),
    Pi.basisFun_apply, Pi.single_eq_same]

omit [CharZero K] in
/-- **[T5.17a]** `classicalCoordMatrix` is the matrix of the restricted operator in the classical
basis. -/
private theorem classicalCoordMatrix_eq_toMatrix (k : ℕ)
    (T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K))
    (hT : ∀ f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k,
      T f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) :
    classicalCoordMatrix h k T
      = LinearMap.toMatrix (classicalBasis h k) (classicalBasis h k)
          ((T : c(ι × (ZMod (p ^ h) × ℕ), K) →ₗ[K] _).restrict hT) := by
  refine Matrix.ext fun x y => ?_
  rw [LinearMap.toMatrix_apply, repr_classicalBasis, classicalCoordMatrix, Matrix.of_apply]
  show matrixCoeff T (x.1, (x.2.1, (x.2.2 : ℕ))) (y.1, (y.2.1, (y.2.2 : ℕ)))
      = T ((classicalBasis h k y : locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) :
          c(ι × (ZMod (p ^ h) × ℕ), K)) (x.1, (x.2.1, (x.2.2 : ℕ)))
  rw [coe_classicalBasis]
  rfl

omit [CharZero K] in
/-- The classical coordinate matrix and `upMatrix` are matrices of the same restricted map in
two bases (`LinearMap.det_toMatrix`). -/
theorem det_classicalCoordMatrix_eq_det_upMatrix [Nonempty ι] (k : ℕ)
    (T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K))
    (hT : ∀ f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k,
      T f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) :
    (classicalCoordMatrix h k T).det = (upMatrix (p := p) (K := K) (ι := ι) h k T hT).det := by
  haveI := finite_locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k
  rw [classicalCoordMatrix_eq_toMatrix h k T hT, upMatrix, LinearMap.det_toMatrix,
    LinearMap.det_toMatrix]

omit [CharZero K] in
/-- The same for characteristic polynomials (`LinearMap.charpoly_toMatrix`); consumed by
Step III. -/
theorem charpoly_classicalCoordMatrix_eq_charpoly_upMatrix [Nonempty ι] (k : ℕ)
    (T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K))
    (hT : ∀ f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k,
      T f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) :
    (classicalCoordMatrix h k T).charpoly
      = (upMatrix (p := p) (K := K) (ι := ι) h k T hT).charpoly := by
  haveI := finite_locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k
  rw [classicalCoordMatrix_eq_toMatrix h k T hT, upMatrix, LinearMap.charpoly_toMatrix,
    LinearMap.charpoly_toMatrix]

omit [CharZero K] in
/-- The same for the reversed characteristic polynomials (`Matrix.reverse_charpoly`). -/
theorem charpolyRev_classicalCoordMatrix_eq_charpolyRev_upMatrix [Nonempty ι] (k : ℕ)
    (T : c(ι × (ZMod (p ^ h) × ℕ), K) →L[K] c(ι × (ZMod (p ^ h) × ℕ), K))
    (hT : ∀ f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k,
      T f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k) :
    (classicalCoordMatrix h k T).charpolyRev
      = (upMatrix (p := p) (K := K) (ι := ι) h k T hT).charpolyRev := by
  rw [← Matrix.reverse_charpoly, ← Matrix.reverse_charpoly,
    charpoly_classicalCoordMatrix_eq_charpoly_upMatrix h k T hT]

/-! ### The Minkowski upper bound at the classical dimension -/

/-- **The height of the overconvergent polygon at `n_{k+1}` is at most `−log‖det A‖`**: the finite
factor and the Minkowski bound. -/
theorem height_le_negLogNorm_det [Nonempty ι] (κ : AnalyticWeight UK (M1Kh h ψ) ρ) {k : ℕ}
    {u : ι → Fin p → ZMod (p ^ h) → K} (hcl : IsClassicalShape θG h ψ U hU vRep hvΔ uu κ k u)
    (hρ : 0 ≤ ρ) (hσ : max ρ (p : ℝ)⁻¹ < 1)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape) :
    (newtonPolygon₀OfPowerSeries negLogNorm
        (discHeckeCharPowerSeries θG h ψ κ U hU vRep hvΔ idx uu)).height
          (Fintype.card ι * ((k + 1) * p ^ h))
      ≤ ((negLogNorm (classicalMatrix θG h ψ U hU vRep hvΔ idx uu κ hcl).det : WithTop ℝ) :
          WithBotTop ℝ) := by
  have hcomp : IsCompactoid (discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu) :=
    isCompactoid_discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu hρ hσ hshape
  have hst : ∀ f ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k,
      discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu f
        ∈ locPolyDegSubmoduleBlock (p := p) (K := K) (ι := ι) h k := fun f hf =>
    mem_locPolyDegSubmoduleBlock_discHeckeBlockOp_of_isClassicalShape θG h ψ U hU vRep hvΔ idx uu
      κ hcl hf
  set G : Polynomial K :=
    (classicalCoordMatrix h k (discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu)).charpolyRev with hG
  set R : PowerSeries K :=
    charPowerSeries ((discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu).comp
      (1 - truncation (R := K) (classicalSupport p ι h k))) with hRdef
  have hsplit : discHeckeCharPowerSeries θG h ψ κ U hU vRep hvΔ idx uu = R * (G : PowerSeries K) :=
    charPowerSeries_eq_mul_of_stable h k hcomp hst
  have hRres : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c R := fun c hc =>
    charPowerSeries_isEntire _ (hcomp.comp_right _) c hc
  have hR0 : PowerSeries.coeff 0 R = 1 := by
    rw [hRdef, charPowerSeries_coeff, charCoeff_zero]
  have hGres : ∀ c : ℝ, 0 < c → PowerSeries.IsRestricted c (G : PowerSeries K) := fun c _ =>
    Polynomial.isRestricted_toPowerSeries (c := c) G
  have hG0 : PowerSeries.coeff 0 (G : PowerSeries K) = 1 := by
    rw [Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero, hG, Matrix.eval_charpolyRev]
  have hcard : Fintype.card (ι × ZMod (p ^ h) × Fin (k + 1))
      = Fintype.card ι * ((k + 1) * p ^ h) := by
    rw [Fintype.card_prod, Fintype.card_prod, ZMod.card, Fintype.card_fin]
    ring
  have hdet : (classicalCoordMatrix h k (discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu)).det
      = (classicalMatrix θG h ψ U hU vRep hvΔ idx uu κ hcl).det :=
    det_classicalCoordMatrix_eq_det_upMatrix h k _ hst
  have hcc := coeff_charpolyRev_card
    (classicalCoordMatrix h k (discHeckeBlockOp θG h ψ κ U hU vRep hvΔ idx uu))
  rw [hcard] at hcc
  rw [show ((Fintype.card ι : ℤ) * (((k : ℤ) + 1) * (p : ℤ) ^ h))
      = ((Fintype.card ι * ((k + 1) * p ^ h) : ℕ) : ℤ) by push_cast; ring]
  refine le_trans (le_trans ?_
    (height_le_coeffVal hGres hG0 (Fintype.card ι * ((k + 1) * p ^ h)))) (le_of_eq ?_)
  · rw [hsplit]
    exact height_mul_le_height_right hRres hGres hR0 hG0 _
  · rw [coeffVal_apply, Polynomial.coeff_coe, hG, hcc, hdet, negLogNorm, negLogNorm, norm_mul,
      norm_pow, norm_neg, norm_one, one_pow, one_mul]

/-! ### The lower bound and the arithmetic -/

omit [CharZero K] in
/-- [LWX, Cor 3.18] read as a height inequality: `λ(n)·v(T₀) ≤ height n`. -/
theorem lwxLambda_mul_le_height_specCharSeries (hp2 : p ≠ 2) (D : UpDatum p ι)
    (ω : (ZMod p)ˣ →* ℤ_[p]ˣ) (ψ₀ : ℤ_[p] →+* K) (hψ₀ : ∀ x, ‖ψ₀ x‖ = ‖x‖) {T₀ : K}
    (h0 : (p : ℝ)⁻¹ < ‖T₀‖) (h1 : ‖T₀‖ < 1) (n : ℕ) :
    (((lwxLambda p (Fintype.card ι) n : ℝ) * (-Real.log ‖T₀‖) : ℝ) : WithBotTop ℝ) ≤
      (newtonPolygon₀OfPowerSeries negLogNorm (specCharSeries D ω ψ₀ T₀)).height n := by
  have hbelow := isBelow_newtonPolygon_specCharSeries hp2 D ω ψ₀ hψ₀ h0 h1 (n : ℤ)
  rw [NewtonPolygon₀.height_toNewtonPolygon, NewtonPolygon₀.height_toNewtonPolygon,
    NewtonPolygon₀.height_ofSlopes, sum_lwxSlopes, zero_add] at hbelow
  exact hbelow

omit [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- **[LWX, (3.23.1)]** at a point with `v(T₀) = v(p)/(p−1)`:
`2·λ(n_{k+1})·v(T₀) = n_{k+1}·(k+1)·v(p)` with `n_{k+1} = t·(k+1)·p`.

`_hT0` is **slack**: `Real.log_pow` needs no positivity.  It is kept because the ticketed
statement (T5.21) carries it and it records that `T₀ ≠ 0` is the intended setting. -/
theorem two_mul_lwxLambda_touchX_mul_eq (t k : ℕ) {T₀ c : K} (_hT0 : 0 < ‖T₀‖)
    (hT : ‖T₀‖ ^ (p - 1) = ‖c‖) :
    2 * ((lwxLambda p t (touchX p t (k + 1)) : ℝ) * (-Real.log ‖T₀‖))
      = ((t * ((k + 1) * p ^ 1) : ℕ) : ℝ) * ((k + 1) * (-Real.log ‖c‖)) := by
  have hp1 : 1 ≤ p := hp.out.one_le
  have hcast : (2 : ℝ) * ((lwxLambda p t (touchX p t (k + 1)) : ℕ) : ℝ)
      = ((k : ℝ) + 1) ^ 2 * p * ((p : ℝ) - 1) * t := by
    have hnat := congrArg (fun n : ℕ => (n : ℝ)) (two_mul_lwxLambda_touchX p t (k + 1))
    push_cast [Nat.cast_sub hp1] at hnat
    linarith
  have hlog : -Real.log ‖c‖ = ((p : ℝ) - 1) * (-Real.log ‖T₀‖) := by
    rw [← hT, Real.log_pow]
    push_cast [Nat.cast_sub hp1]
    ring
  rw [hlog]
  push_cast
  linear_combination (-Real.log ‖T₀‖) * hcast

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- `n_{k+1} = t·(k+1)·p` in the two spellings used by `touchX` and `finrank`. -/
theorem touchX_succ_eq (t k : ℕ) : touchX p t (k + 1) = t * ((k + 1) * p ^ 1) := by
  rw [touchX, pow_one]
  ring

/-! ### The classical data at a halo point, and Step I -/

/-- **A classical weight, seen from the halo**: a halo point `T₀` at level `h = 1` whose norm is
that of a classical point of conductor `p²` (`‖T₀‖^{p−1} = ‖p‖`, i.e. `v(T₀) = v(p)/(p−1)`), and
whose halo weight has the classical shape of exponent `k`. -/
structure ClassicalData (hp2 : p ≠ 2) (hψ : ∀ x, ‖ψ x‖ = ‖x‖) (ω : (ZMod p)ˣ →* ℤ_[p]ˣ)
    (T₀ : K) (k : ℕ) where
  /-- The halo annulus, lower bound. -/
  h0 : (p : ℝ)⁻¹ < ‖T₀‖
  /-- The halo annulus, upper bound. -/
  h1 : ‖T₀‖ < 1
  /-- The level-`1` analyticity condition. -/
  hT : ‖TH p 1 T₀‖ ^ 2 < (p : ℝ)⁻¹
  /-- The norm of a classical point of conductor `p²`. -/
  hnorm : ‖T₀‖ ^ (p - 1) = ‖ψ p‖
  /-- The nebentypus constants. -/
  u : ι → Fin p → ZMod (p ^ 1) → K
  /-- The classical shape of exponent `k`. -/
  shape : IsClassicalShape θG 1 ψ U hU vRep hvΔ uu (haloWeightH 1 ψ T₀ ω hp2 hψ h0 h1 hT) k u

namespace ClassicalData

variable {θG h ψ U hU vRep hvΔ uu} {hp2 : p ≠ 2} {hψ : ∀ x, ‖ψ x‖ = ‖x‖}
  {ω : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ : K} {k : ℕ}

/-- The halo weight of the datum. -/
def weight (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k) :
    AnalyticWeight (haloUnitsH 1 ψ) (M1Kh 1 ψ) (haloRhoH p 1 T₀) :=
  haloWeightH 1 ψ T₀ ω hp2 hψ c.h0 c.h1 c.hT

/-- The matrix of `U_p` on the classical subspace at the datum. -/
def matrix [Nonempty ι] (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k) :
    Matrix (Fin (Fintype.card ι * ((k + 1) * p ^ 1)))
      (Fin (Fintype.card ι * ((k + 1) * p ^ 1))) K :=
  classicalMatrix θG 1 ψ U hU vRep hvΔ idx uu c.weight c.shape

end ClassicalData

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
/-- The two ways of landing in `WithBotTop ℝ` agree: `WithBotTop.coe` is `WithBot.some ∘
WithTop.some`.  Used to compare a `negLogNorm` (a `WithTop ℝ`) with a height's `ℝ`-coercion. -/
private theorem coe_withTop_coe (x : ℝ) : ((x : WithTop ℝ) : WithBotTop ℝ) = (x : WithBotTop ℝ) :=
  rfl

/-- **[LWX, §3.23 Step I]: the touching**, granted H1.  At a classical point `T₀` of weight `k`
whose Atkin–Lehner partner is the classical point `T₀'` (of the conjugate nebentypus), the Newton
polygon of `∑ c_n(T₀) Xⁿ` passes through `(n_{k+1}, λ(n_{k+1})·v(T₀))`. -/
theorem isStepOneTouching_of_atkinLehnerHypothesis (hp2 : p ≠ 2) [Nonempty ι]
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    {ω ω' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k (c.matrix idx) B
      (c'.matrix idx)) :
    IsStepOneTouching (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (intHom ψ) T₀ (k + 1) := by
  obtain ⟨B, hAB, P, Q, hQP, hA'⟩ := hAL
  have hp0 : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hp.out.pos)
  have hT0 : (0 : ℝ) < ‖T₀‖ := hp0.trans c.h0
  have hT0' : (0 : ℝ) < ‖T₀'‖ := hp0.trans c'.h0
  have hψp : ψ (p : ℚ_[p]) ≠ 0 := fun hcon =>
    (Nat.cast_ne_zero.2 hp.out.ne_zero) (ψ.injective (by rw [hcon, map_zero]))
  have hcne : (ψ (p : ℚ_[p])) ^ (k + 1) ≠ 0 := pow_ne_zero _ hψp
  have hA0 : (c.matrix idx).det ≠ 0 := det_ne_zero_of_mul_eq_smul' hcne hAB
  have hA'0 : (c'.matrix idx).det ≠ 0 := det_ne_zero_of_mul_eq_smul_conj hcne hAB hQP hA'
  -- The index `n_{k+1} = t·(k+1)·p`, in the two spellings.
  have hidx : ((Fintype.card ι : ℤ) * (((k : ℤ) + 1) * (p : ℤ) ^ 1))
      = ((touchX p (Fintype.card ι) (k + 1) : ℕ) : ℤ) := by
    rw [touchX_succ_eq]; push_cast; ring
  -- The Minkowski upper bound at both points, through the seam.
  have hup : ∀ {ω₁ : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₁ : K}
      (c₁ : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω₁ T₁ k),
      (newtonPolygon₀OfPowerSeries negLogNorm
          (specCharSeries (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω₁ (intHom ψ) T₁)).height
            ((touchX p (Fintype.card ι) (k + 1) : ℕ) : ℤ)
        ≤ ((negLogNorm (c₁.matrix idx).det : WithTop ℝ) : WithBotTop ℝ) := by
    intro ω₁ T₁ c₁
    rw [specCharSeries_ofCerts_eq_discHeckeCharPowerSeries ψ hψ T₁ ω₁ 1 θG U hU vRep hvΔ idx uu
        hp2 c₁.h0 c₁.h1 c₁.hT hshape, ← hidx]
    exact height_le_negLogNorm_det θG 1 ψ U hU vRep hvΔ idx uu c₁.weight c₁.shape
      (haloRhoH_nonneg 1 T₁) (max_lt (haloRhoH_lt_one 1 T₁ c₁.hT) inv_lt_one_p) hshape
  -- The [LWX, Cor 3.18] lower bound at both points.
  have hlow : ∀ {ω₁ : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₁ : K}
      (c₁ : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω₁ T₁ k),
      (((lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) (k + 1)) : ℝ)
            * (-Real.log ‖T₁‖) : ℝ) : WithBotTop ℝ)
        ≤ (newtonPolygon₀OfPowerSeries negLogNorm
            (specCharSeries (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω₁ (intHom ψ)
              T₁)).height ((touchX p (Fintype.card ι) (k + 1) : ℕ) : ℤ) := fun c₁ =>
    lwxLambda_mul_le_height_specCharSeries hp2 _ _ (intHom ψ) (norm_intHom ψ hψ) c₁.h0 c₁.h1 _
  -- Squeezing the two bounds against each other, in `ℝ`.
  have hsq : ∀ {ω₁ : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₁ : K}
      (c₁ : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω₁ T₁ k), (c₁.matrix idx).det ≠ 0 →
      (lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) (k + 1)) : ℝ) * (-Real.log ‖T₁‖)
        ≤ -Real.log ‖(c₁.matrix idx).det‖ := by
    intro ω₁ T₁ c₁ h₁
    have hchain := (hlow c₁).trans (hup c₁)
    rwa [negLogNorm_of_ne_zero h₁, coe_withTop_coe, WithBotTop.coe_le_coe] at hchain
  -- [LWX, (3.23.1)] at both points, and H1 on the determinants.
  have har : ∀ {T₁ : K}, 0 < ‖T₁‖ → ‖T₁‖ ^ (p - 1) = ‖ψ (p : ℚ_[p])‖ →
      2 * ((lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) (k + 1)) : ℝ)
          * (-Real.log ‖T₁‖))
        = ((Fintype.card ι * ((k + 1) * p ^ 1) : ℕ) : ℝ)
            * (((k : ℝ) + 1) * (-Real.log ‖ψ (p : ℚ_[p])‖)) :=
    fun h₁ h₂ => two_mul_lwxLambda_touchX_mul_eq (Fintype.card ι) k h₁ h₂
  have hsum : -Real.log ‖(c.matrix idx).det‖ + -Real.log ‖(c'.matrix idx).det‖
      = ((Fintype.card ι * ((k + 1) * p ^ 1) : ℕ) : ℝ)
          * (((k : ℝ) + 1) * (-Real.log ‖ψ (p : ℚ_[p])‖)) := by
    have hAL := neg_log_norm_det_add_of_mul_eq_smul hcne hAB hQP hA'
    rw [Fintype.card_fin, norm_pow, Real.log_pow] at hAL
    rw [hAL]
    push_cast
    ring
  -- The touching.
  have key : -Real.log ‖(c.matrix idx).det‖
      = (lwxLambda p (Fintype.card ι) (touchX p (Fintype.card ι) (k + 1)) : ℝ)
          * (-Real.log ‖T₀‖) := by
    have h1 := hsq c hA0
    have h2 := hsq c' hA'0
    have h3 := har hT0 c.hnorm
    have h4 := har hT0' c'.hnorm
    linarith
  refine le_antisymm ((hup c).trans (le_of_eq ?_)) (hlow c)
  rw [negLogNorm_of_ne_zero hA0, coe_withTop_coe, key]

/-- **The hand-off to Step II**: the touching hypothesis at `n_{k+1}`. -/
theorem hasUnitBand_of_atkinLehnerHypothesis (hp2 : p ≠ 2) [Nonempty ι]
    (hψ : ∀ x, ‖ψ x‖ = ‖x‖)
    (hshape : ∀ i t, (M1.toLocalMat (certM1 θG U hU vRep hvΔ uu i t)).IsUpShape)
    {ω ω' : (ZMod p)ˣ →* ℤ_[p]ˣ} {T₀ T₀' : K} {k : ℕ}
    (c : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω T₀ k)
    (c' : ClassicalData θG ψ U hU vRep hvΔ uu hp2 hψ ω' T₀' k)
    (hAL : ∃ B, AtkinLehnerHypothesis (p := p) (K := K) (ι := ι) ψ 1 k (c.matrix idx) B
      (c'.matrix idx)) :
    HasUnitBand (UpDatum.ofCerts θG U hU vRep hvΔ idx uu hshape) ω (k + 1) :=
  hasUnitBand_of_isStepOneTouching hp2 _ ω (intHom ψ) (norm_intHom ψ hψ) c.h0 c.h1
    (isStepOneTouching_of_atkinLehnerHypothesis θG ψ U hU vRep hvΔ idx uu hp2 hψ hshape c c' hAL)

end LWX

end
