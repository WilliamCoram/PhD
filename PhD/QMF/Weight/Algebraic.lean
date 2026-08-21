/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.QMF.Weight.Forms
import PhD.QMF.Slash.WeightModule

/-!
# The classical algebraic weights as an instance of the abstract weight action

For the algebraic character `κ(u) = u^(n+2)`, [Jacobs, Def 1.27]'s formula
`z^k ↦ κ(cz+d)/(cz+d)²((az+b)/(cz+d))^k = (cz+d)^(n−k)(az+b)^k` is, for `k ≤ n`, a
polynomial of degree `≤ n` — so the span of `e₀, …, e_n` in the Tate algebra is stable
and carries the dehomogenisation of Buzzard's right action on `L_{n,ν}`
(`P(X,Y) ↦ ν(adj δ)·P(aX+bY, cX+dY)`, i.e. `p(z) ↦ ν·(cz+d)^n·p((az+b)/(cz+d))` at
`p(z) = P(z, 1)`), with the determinant character `ν` as the scalar twist
(`RightSlashAction.twist`).  Nothing about `WeightModule` is re-proved: the bridge
consumes the existing classical slash and exhibits it inside the general action.

## Main definitions

* `QMF.algWeight hb n : AnalyticWeight ⊤ S ρ` — the classical weight `κ(u) = u^(n+2)` as a
  headline weight (`algExpansionData`: the honest character `u ↦ u^(n+2)` with its polynomial
  expansion `col c d = (C d + C c·X)^(n+2)`).
* `QMF.polyEmbed` — dehomogenisation `WeightModule K n ν →ₗ[K] c(ℕ, K)`,
  `P ↦ (coefficient of X^k·Y^(n−k) in P)_k`.
* `QMF.detTwist ν` — the classical character `ν` read on `Σ₀'` through the adjugate.
* `AutomorphicFunction.mapCoeff` — functoriality of automorphic functions in the
  coefficient module.

## Main results

* `QMF.polyEmbed_slash` — **the bridge**: `polyEmbed (P ∣ₛ δ) =
  detTwist ν δ • (algWeight hb n).toWeightSeries.kappaSlash δ (polyEmbed P)`.
* `AutomorphicFunction.mapCoeff_slash` / `mapCoeff_mem_levelSubmoduleSlash` /
  `heckeOperatorSlash_mapCoeff` — an equivariant coefficient map induces a
  Hecke-equivariant map of form spaces ([Jacobs, Def 1.30/1.32]: the transformation
  law and `[UvU]φ = Σ φ|v_t` are preserved by postcomposition).
* `QMF.classicalForms`, `QMF.classicalHeckeOperator` — the classical space `S^D_{k,w}(U)` and
  its Hecke operators at abstract `(G, θ)`.
* `QMF.map_classicalForms_le_forms` — **[Buzzard, §11]**: `S^D_{k,w}(U) ⊆ S^D_κ(U)`: the
  classical space maps into the headline `Weight.Forms` at `algWeight hb n` twisted by `ν`;
  `QMF.heckeOperator_mapCoeff_polyEmbed` — Hecke-equivariantly; and
  `QMF.mem_map_classicalForms_iff` — *classical = polynomial-valued overconvergent*.
-/

open TateFredholm PowerSeries
open scoped TateFredholm QMF Pointwise

namespace QMF

variable {K : Type*} [NontriviallyNormedField K] [iu : IsUltrametricDist K]
  [cs : CompleteSpace K]
variable {S : Submonoid (Matrix (Fin 2) (Fin 2) K)} {ρ : ℝ}

omit iu cs in
/-- Coefficient decay of powers of a linear factor: `‖coeff m ((C d + C c·X)^k)‖ ≤ ρ^m`
when `‖c‖ ≤ ρ ≤ 1` and `‖d‖ ≤ 1` — the algebraic weight's row decay, by induction on
the exponent through the two-term convolution with `C d + C c·X`. -/
private theorem norm_coeff_linear_pow_le [IsUltrametricDist K] {c d : K} {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (hc : ‖c‖ ≤ ρ) (hd : ‖d‖ ≤ 1) (k : ℕ) (m : ℕ) :
    ‖PowerSeries.coeff m ((PowerSeries.C d + PowerSeries.C c * PowerSeries.X) ^ k)‖
      ≤ ρ ^ m := by
  induction k generalizing m with
  | zero =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · rw [pow_zero, PowerSeries.coeff_one, if_neg hm.ne']
      simpa using pow_nonneg hρ0 m
  | succ k ih =>
    rw [pow_succ, mul_add, map_add]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [mul_comm _ (PowerSeries.C d), PowerSeries.coeff_C_mul, norm_mul]
      calc ‖d‖ * ‖PowerSeries.coeff m (_ ^ k)‖ ≤ 1 * ρ ^ m :=
            mul_le_mul hd (ih m) (norm_nonneg _) zero_le_one
        _ = ρ ^ m := one_mul _
    · rw [show (PowerSeries.C c * PowerSeries.X : PowerSeries K)
          = PowerSeries.C c * PowerSeries.X from rfl, ← mul_assoc,
        mul_comm _ (PowerSeries.C c), mul_assoc, PowerSeries.coeff_C_mul, norm_mul]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [PowerSeries.coeff_zero_eq_constantCoeff, map_mul]
        simp
      · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
        rw [mul_comm (_ ^ k) PowerSeries.X, PowerSeries.coeff_succ_X_mul]
        calc ‖c‖ * ‖PowerSeries.coeff m' (_ ^ k)‖ ≤ ρ * ρ ^ m' :=
              mul_le_mul hc (ih m') (norm_nonneg _) hρ0
          _ = ρ ^ (m' + 1) := (pow_succ' ρ m').symm

/-- **The algebraic weight as an honest character datum** ([Buzzard, §11 p. 73]'s
`κ = (α ↦ αⁿ, …)` in Jacobs's normalisation `u ↦ u^(n+2)`): the character `u ↦ u^(n+2)` of
`Kˣ` with the polynomial expansion `(C d + C c·X)^(n+2)` of `κ(c·x + d)` (row decay is the
binomial estimate), evaluating to `(cz + d)^(n+2)` by finite-sum evaluation (`evalAt_pow`,
`evalAt_linX`).  The κ-cocycle is derived by evaluation injectivity, as for every honest
character. -/
noncomputable def algExpansionData (hb : LevelBounds S ρ) (n : ℕ) :
    ExpansionData S ρ (⊤ : Subgroup Kˣ)
      ((powMonoidHom (n + 2)).comp (⊤ : Subgroup Kˣ).subtype) where
  bounds := hb
  col c d := (PowerSeries.C d + PowerSeries.C c * PowerSeries.X) ^ (n + 2)
  rowDecay hg m :=
    norm_coeff_linear_pow_le hb.rho_nonneg (hb.c_le hg) (hb.integral hg 1 1) (n + 2) m
  mem_level _ _ _ _ := Subgroup.mem_top _
  eval {g} hg z hz hu := by
    show evalAt (linX g ^ (n + 2)) z = _
    rw [evalAt_pow (WeightSeries.absSummable_linX g) hz, evalAt_linX g hz]
    simp [IsUnit.unit_spec]

/-- **The classical weight `κ(u) = u^(n+2)` as a weight in the headline sense**
(`AnalyticWeight`), analytic at every level `(S, ρ)` (its expansion is a polynomial). -/
noncomputable def algWeight (hb : LevelBounds S ρ) (n : ℕ) : AnalyticWeight ⊤ S ρ :=
  ⟨_, algExpansionData hb n⟩

@[simp] theorem algWeight_toChar (hb : LevelBounds S ρ) (n : ℕ) (u : (⊤ : Subgroup Kˣ)) :
    (algWeight hb n).toChar u = (u : Kˣ) ^ (n + 2) :=
  rfl

/-- The column of the algebraic weight is the polynomial `(C d + C c·X)^(n+2)`. -/
@[simp] theorem algWeight_col (hb : LevelBounds S ρ) (n : ℕ) (c d : K) :
    (algWeight hb n).expansion.col c d
      = (PowerSeries.C d + PowerSeries.C c * PowerSeries.X) ^ (n + 2) :=
  rfl

/-- At the algebraic weight the automorphy factor is the polynomial `(cx+d)^n`:
`κ(cx+d)/(cx+d)² = (cx+d)^(n+2)·(cx+d)⁻² = linX^n`. -/
theorem autFactor_algWeight (hb : LevelBounds S ρ) (n : ℕ)
    {γ : Matrix (Fin 2) (Fin 2) K} (hd : γ 1 1 ≠ 0) :
    (algWeight hb n).toWeightSeries.autFactor γ = linX γ ^ n := by
  have hl0 : PowerSeries.constantCoeff (linX γ) ≠ 0 := by
    rw [constantCoeff_linX]; exact hd
  have hcol : (algWeight hb n).toWeightSeries.col (γ 1 0) (γ 1 1) = linX γ ^ (n + 2) := rfl
  rw [WeightSeries.autFactor, hcol, pow_add, mul_assoc, ← mul_pow,
    PowerSeries.mul_inv_cancel _ hl0, one_pow, mul_one]

/-- The `i`-th column of the algebraic weight action is the **polynomial**
`(cx+d)^(n−i)·(ax+b)^i`: the inverse powers in `autFactor·mobius^i` cancel for
`i ≤ n`.  (The R6 hand-off: the polynomial-submodule tranche consumes this for the
degree bound.) -/
theorem autFactor_mul_mobius_pow_eq (hb : LevelBounds S ρ) (n : ℕ)
    {γ : Matrix (Fin 2) (Fin 2) K} (hd : γ 1 1 ≠ 0) {i : ℕ} (hi : i ≤ n) :
    (algWeight hb n).toWeightSeries.autFactor γ * mobius γ ^ i
      = linX γ ^ (n - i) * numX γ ^ i := by
  have hl0 : PowerSeries.constantCoeff (linX γ) ≠ 0 := by
    rw [constantCoeff_linX]; exact hd
  have h1 : linX γ ^ i * ((linX γ)⁻¹) ^ i = 1 := by
    rw [← mul_pow, PowerSeries.mul_inv_cancel _ hl0, one_pow]
  calc (algWeight hb n).toWeightSeries.autFactor γ * mobius γ ^ i
      = linX γ ^ n * (numX γ ^ i * ((linX γ)⁻¹) ^ i) := by
        rw [autFactor_algWeight hb n hd, mobius, mul_pow]
    _ = linX γ ^ (n - i) * (linX γ ^ i * ((linX γ)⁻¹) ^ i) * numX γ ^ i := by
        rw [← pow_sub_mul_pow (linX γ) hi]; ring
    _ = linX γ ^ (n - i) * numX γ ^ i := by rw [h1, mul_one]

omit iu cs in
/-- Truncation of the slash tsum against a sequence supported in degrees `≤ n`.
(Stated outside the `Valued` section: the tsum must be read in the **norm** topology
of `K` — the one `kappaSlash_apply` is stated in — not the valuation topology that
`[Valued K Γ₀]` would put in scope.) -/
private theorem tsum_mul_eq_sum_range {n : ℕ} {a f : ℕ → K}
    (hf : ∀ i, n < i → f i = 0) :
    ∑' i, a i * f i = ∑ i ∈ Finset.range (n + 1), a i * f i :=
  tsum_eq_sum fun i hi => by
    rw [Finset.mem_range, not_lt] at hi
    rw [hf i (by omega), mul_zero]

omit iu cs in
private theorem add_apply (f g : c(ℕ, K)) (j : ℕ) : (f + g) j = f j + g j := rfl

omit iu cs in
private theorem smul_apply (r : K) (f : c(ℕ, K)) (j : ℕ) : (r • f) j = r * f j := rfl

omit iu cs in
private theorem zero_apply (j : ℕ) : (0 : c(ℕ, K)) j = 0 := rfl

/-- Dehomogenisation into power series, `P(X, Y) ↦ P(z, 1)`. -/
private noncomputable def dehom : MvPolynomial (Fin 2) K →ₐ[K] PowerSeries K :=
  MvPolynomial.aeval ![PowerSeries.X, 1]

omit iu cs in
private theorem dehom_monomial (m : Fin 2 →₀ ℕ) (c : K) :
    dehom (MvPolynomial.monomial m c) = PowerSeries.C c * PowerSeries.X ^ (m 0) := by
  rw [dehom, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
  simp

omit iu cs in
/-- The dehomogenisation seam: for `F` homogeneous of degree `n` the `z^j`-coefficient
of `F(z, 1)` is the `X^j·Y^(n−j)`-coefficient of `F` — at every `j` (both vanish for
`j > n`). -/
private theorem coeff_dehom (n : ℕ) {F : MvPolynomial (Fin 2) K}
    (hF : F.IsHomogeneous n) (j : ℕ) :
    PowerSeries.coeff j (dehom F) = MvPolynomial.coeff
      (Finsupp.single (0 : Fin 2) j + Finsupp.single (1 : Fin 2) (n - j)) F := by
  conv_lhs => rw [F.as_sum, map_sum, map_sum]
  simp only [dehom_monomial, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  rw [Finset.sum_eq_single
    (Finsupp.single (0 : Fin 2) j + Finsupp.single (1 : Fin 2) (n - j))]
  · simp
  · intro m hm hne
    have hm01 : m 0 + m 1 = n := by
      have hdeg := hF (MvPolynomial.mem_support_iff.mp hm)
      rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun i => by simp),
        Fin.sum_univ_two] at hdeg
      simpa using hdeg
    rw [if_neg, mul_zero]
    intro hj0
    exact hne (by
      ext k
      fin_cases k <;> simp <;> omega)
  · intro hnot
    rw [MvPolynomial.notMem_support_iff.mp hnot, zero_mul]

omit iu cs in
/-- Composing the substitution slash with dehomogenisation substitutes the Möbius
numerator and denominator: `(P ∣ γ)(z, 1) = P(az + b, cz + d)`. -/
private theorem dehom_comp_matrixSubstR (γ : Matrix (Fin 2) (Fin 2) K) :
    dehom.comp (matrixSubstR (R := K) γ)
      = MvPolynomial.aeval ![numX γ, linX γ] := by
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;>
    · simp [dehom, matrixSubstR_X, Fin.sum_univ_two, Algebra.smul_def, numX, linX]
      ring

omit iu cs in
/-- Coefficients of powers of a linear factor vanish above the exponent:
`(C d + C c·X)^k` has `X`-degree `≤ k`. -/
private theorem coeff_linear_pow_eq_zero {c d : K} {k j : ℕ} (hjk : k < j) :
    PowerSeries.coeff j ((PowerSeries.C d + PowerSeries.C c * PowerSeries.X) ^ k)
      = 0 := by
  induction k generalizing j with
  | zero => rw [pow_zero, PowerSeries.coeff_one, if_neg (by omega)]
  | succ k ih =>
    rw [pow_succ, mul_add, map_add, mul_comm _ (PowerSeries.C d),
      PowerSeries.coeff_C_mul, ih (by omega), mul_zero, ← mul_assoc,
      mul_comm _ (PowerSeries.C c), mul_assoc, PowerSeries.coeff_C_mul]
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [mul_comm (_ ^ k) PowerSeries.X, PowerSeries.coeff_succ_X_mul, ih (by omega),
      mul_zero, add_zero]

omit iu cs in
/-- The `i`-th column polynomial `linX^a · numX^b` has `X`-degree `≤ a + b`. -/
private theorem coeff_linX_pow_mul_numX_pow_eq_zero (γ : Matrix (Fin 2) (Fin 2) K)
    {a b j : ℕ} (h : a + b < j) :
    PowerSeries.coeff j (linX γ ^ a * numX γ ^ b) = 0 := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [Finset.mem_antidiagonal] at hp
  rcases Nat.lt_or_ge a p.1 with h1 | h1
  · rw [show linX γ = PowerSeries.C (γ 1 1) + PowerSeries.C (γ 1 0) * PowerSeries.X
        from rfl, coeff_linear_pow_eq_zero h1, zero_mul]
  · rw [show numX γ = PowerSeries.C (γ 0 1) + PowerSeries.C (γ 0 0) * PowerSeries.X
        from rfl, coeff_linear_pow_eq_zero (by omega), mul_zero]

omit iu cs in
variable (K) in
/-- **The polynomial submodule** of the Tate algebra: sequences supported in degrees
`≤ n` — the dehomogenised classical weight space, uniformised inside `c(ℕ, K)`. -/
def polySubmodule (n : ℕ) : Submodule K c(ℕ, K) where
  carrier := {f | ∀ m : ℕ, n < m → f m = 0}
  add_mem' hf hg m hm := by rw [add_apply, hf m hm, hg m hm, add_zero]
  zero_mem' m _ := zero_apply m
  smul_mem' r f hf m hm := by rw [smul_apply, hf m hm, mul_zero]

omit iu cs in
@[simp] theorem mem_polySubmodule_iff {n : ℕ} {f : c(ℕ, K)} :
    f ∈ polySubmodule K n ↔ ∀ m : ℕ, n < m → f m = 0 :=
  Iff.rfl

/-- The basis vectors of degree `≤ n` are polynomials. -/
theorem single_mem_polySubmodule {k n : ℕ} (hk : k ≤ n) (r : K) :
    cSpace.single k r ∈ polySubmodule K n :=
  fun m hm => cSpace.single_apply_of_ne (by omega) r

/-- **Stability of the polynomial submodule** ([Jacobs, Def 1.27] at `κ(u) = u^(n+2)`:
the formula `z^k ↦ (az+b)^k (cz+d)^(n−k)` has degree `≤ n`): the algebraic weight
action preserves polynomials of degree `≤ n`.  The R6 uniformisation lemma. -/
theorem polySubmodule_stable (hb : LevelBounds S ρ) (n : ℕ) (g : S) {f : c(ℕ, K)}
    (hf : f ∈ polySubmodule K n) :
    (algWeight hb n).toWeightSeries.kappaSlash g f ∈ polySubmodule K n := by
  intro j hj
  rw [WeightSeries.kappaSlash_apply, tsum_mul_eq_sum_range fun m hm => hf m hm]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [autFactor_mul_mobius_pow_eq hb n (hb.d_ne_zero g.2) hin,
    coeff_linX_pow_mul_numX_pow_eq_zero _ (by omega), zero_mul]

section Valued

variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
  {γv : Γ₀} {hγv : γv < 1}

/-- The classical character `ν` (always `Σ₀`-indexed in the library), read on `Σ₀'`
through the adjugate dictionary — multiplicative because `adj` is an anti-homomorphism
and `Kˣ` is commutative.  For `ν = Sigma0.detChar w` this is `det^w` on the nose. -/
noncomputable def detTwist (ν : Sigma0 K γv hγv →* Kˣ) : Sigma0' K γv hγv →* Kˣ where
  toFun δ := ν (Sigma0'.adj δ)
  map_one' := by rw [Sigma0'.adj_one, map_one]
  map_mul' δ₁ δ₂ := by rw [Sigma0'.adj_mul, map_mul, mul_comm]

omit iu cs in
@[simp] theorem detTwist_apply (ν : Sigma0 K γv hγv →* Kˣ) (δ : Sigma0' K γv hγv) :
    detTwist ν δ = ν (Sigma0'.adj δ) :=
  rfl


private theorem single_add (k : ℕ) (a b : K) :
    cSpace.single k (a + b) = cSpace.single k a + cSpace.single k b := by
  refine DFunLike.ext _ _ fun j => ?_
  rw [add_apply]
  rcases eq_or_ne j k with rfl | hj
  · simp
  · simp [cSpace.single_apply_of_ne hj]

private theorem single_smul (k : ℕ) (r a : K) :
    cSpace.single k (r * a) = r • cSpace.single k a := by
  refine DFunLike.ext _ _ fun j => ?_
  rw [smul_apply]
  rcases eq_or_ne j k with rfl | hj
  · simp
  · simp [cSpace.single_apply_of_ne hj]

omit iu cs in
private theorem sum_apply (s : Finset ℕ) (f : ℕ → c(ℕ, K)) (k : ℕ) :
    (∑ j ∈ s, f j) k = ∑ j ∈ s, f j k := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, zero_apply]
  | insert j t hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, add_apply, ih]

/-- **Dehomogenisation** `WeightModule K n ν →ₗ[K] c(ℕ, K)`: the degree-`n` homogeneous
polynomial `P(X, Y)` becomes the coefficient sequence of `p(z) = P(z, 1)`, supported in
degrees `≤ n`. -/
noncomputable def polyEmbed (n : ℕ) (ν : Sigma0 K γv hγv →* Kˣ) :
    WeightModule K n ν →ₗ[K] c(ℕ, K) where
  toFun P := ∑ k ∈ Finset.range (n + 1),
    cSpace.single k (MvPolynomial.coeff
      (Finsupp.single (0 : Fin 2) k + Finsupp.single (1 : Fin 2) (n - k)) P.1)
  map_add' P Q := by
    simp only [WeightModule.coe_add, MvPolynomial.coeff_add, single_add,
      Finset.sum_add_distrib]
  map_smul' r P := by
    simp only [WeightModule.coe_rsmul, MvPolynomial.coeff_smul, smul_eq_mul,
      RingHom.id_apply, single_smul, Finset.smul_sum]

theorem polyEmbed_apply (n : ℕ) (ν : Sigma0 K γv hγv →* Kˣ) (P : WeightModule K n ν)
    (k : ℕ) (hk : k ≤ n) :
    polyEmbed n ν P k = MvPolynomial.coeff
      (Finsupp.single (0 : Fin 2) k + Finsupp.single (1 : Fin 2) (n - k)) P.1 := by
  show (∑ j ∈ Finset.range (n + 1), cSpace.single j _) k = _
  rw [sum_apply, Finset.sum_eq_single k
    (fun j _ hj => cSpace.single_apply_of_ne (Ne.symm hj) _)
    (fun hk' => absurd (Finset.mem_range.mpr (by omega)) hk')]
  exact cSpace.single_apply_self _ _

/-- A two-variable multidegree splits as the sum of its component singles. -/
private theorem finsupp_eq_single_add_single (m : Fin 2 →₀ ℕ) :
    m = Finsupp.single (0 : Fin 2) (m 0) + Finsupp.single (1 : Fin 2) (m 1) := by
  ext i
  fin_cases i <;> simp

theorem polyEmbed_injective (n : ℕ) (ν : Sigma0 K γv hγv →* Kˣ) :
    Function.Injective (polyEmbed n ν) := by
  have hker : ∀ R : WeightModule K n ν, polyEmbed n ν R = 0 → R = 0 := by
    intro R hR
    refine Subtype.ext ?_
    rw [WeightModule.coe_zero]
    refine MvPolynomial.ext _ _ fun m => ?_
    rw [MvPolynomial.coeff_zero]
    by_contra hne
    have hhom : R.1.IsHomogeneous n :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mp R.2
    have hdeg := hhom hne
    have hm01 : m 0 + m 1 = n := by
      rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun i => by simp),
        Fin.sum_univ_two] at hdeg
      simpa using hdeg
    have hm0 : m 0 ≤ n := by omega
    have hval := congrArg (fun f : c(ℕ, K) => f (m 0)) hR
    rw [polyEmbed_apply n ν R (m 0) hm0] at hval
    rw [zero_apply] at hval
    have hm : Finsupp.single (0 : Fin 2) (m 0) + Finsupp.single (1 : Fin 2) (n - m 0)
        = m := by
      conv_rhs => rw [finsupp_eq_single_add_single m]
      congr 1
      rw [show n - m 0 = m 1 by omega]
    rw [hm] at hval
    exact hne hval
  intro P Q h
  have h0 : P - Q = 0 := hker _ (by rw [map_sub, h, sub_self])
  have hval : P.1 - Q.1 = 0 := by
    have h1 := congrArg Subtype.val h0
    rw [show ((P - Q).1 : MvPolynomial (Fin 2) K) = P.1 - Q.1 from rfl,
      WeightModule.coe_zero] at h1
    exact h1
  exact Subtype.ext (sub_eq_zero.mp hval)

private theorem polyEmbed_apply_of_gt (n : ℕ) (ν : Sigma0 K γv hγv →* Kˣ)
    (P : WeightModule K n ν) {k : ℕ} (hk : n < k) : polyEmbed n ν P k = 0 := by
  show (∑ j ∈ Finset.range (n + 1), cSpace.single j _) k = 0
  rw [sum_apply]
  exact Finset.sum_eq_zero fun j hj =>
    cSpace.single_apply_of_ne (by rw [Finset.mem_range] at hj; omega) _

/-- `polyEmbed` with no degree restriction: for `k > n` both sides vanish (the sequence
by support, the coefficient by homogeneity). -/
theorem polyEmbed_eq_coeff (n : ℕ) (ν : Sigma0 K γv hγv →* Kˣ) (P : WeightModule K n ν)
    (k : ℕ) :
    polyEmbed n ν P k = MvPolynomial.coeff
      (Finsupp.single (0 : Fin 2) k + Finsupp.single (1 : Fin 2) (n - k)) P.1 := by
  rcases Nat.lt_or_ge n k with hk | hk
  swap
  · exact polyEmbed_apply n ν P k hk
  · rw [polyEmbed_apply_of_gt n ν P hk]
    refine (((MvPolynomial.mem_homogeneousSubmodule _ _).mp P.2).coeff_eq_zero ?_).symm
    rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
    omega

omit iu cs in
/-- A degree-`n` homogeneous two-variable polynomial is the sum of its `n + 1`
bidegree components. -/
private theorem homog_repr (n : ℕ) (ν : Sigma0 K γv hγv →* Kˣ) (P : WeightModule K n ν) :
    (P.1 : MvPolynomial (Fin 2) K)
      = ∑ i ∈ Finset.range (n + 1),
          MvPolynomial.monomial
            (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (n - i))
            (MvPolynomial.coeff
              (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (n - i)) P.1) := by
  have hP : (P.1 : MvPolynomial (Fin 2) K).IsHomogeneous n :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mp P.2
  refine MvPolynomial.ext _ _ fun m => ?_
  rw [MvPolynomial.coeff_sum]
  by_cases hm : m ∈ (P.1 : MvPolynomial (Fin 2) K).support
  · have hm01 : m 0 + m 1 = n := by
      have hdeg := hP (MvPolynomial.mem_support_iff.mp hm)
      rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (fun i => by simp),
        Fin.sum_univ_two] at hdeg
      simpa using hdeg
    rw [Finset.sum_eq_single (m 0)
      (fun i _ hine => by
        rw [MvPolynomial.coeff_monomial, if_neg]
        intro heq
        exact hine (by
          have h0 := DFunLike.congr_fun heq 0
          simpa [Finsupp.single_apply] using h0))
      (fun hnot => absurd (Finset.mem_range.mpr (by omega)) hnot)]
    have hexp : Finsupp.single (0 : Fin 2) (m 0) + Finsupp.single (1 : Fin 2) (n - m 0)
        = m := by
      ext k
      fin_cases k <;> simp
      omega
    rw [hexp, MvPolynomial.coeff_monomial, if_pos rfl]
  · rw [MvPolynomial.notMem_support_iff.mp hm]
    symm
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [MvPolynomial.coeff_monomial]
    split_ifs with hif
    · rw [hif]
      exact MvPolynomial.notMem_support_iff.mp hm
    · rfl

/-- **The bridge** (the classical weights as an application of [Jacobs, Def 1.27]):
dehomogenisation intertwines Buzzard's right slash on `L_{n,ν}` with the general
weight-`κ` action at `κ(u) = u^(n+2)`, twisted by the determinant character.
Columnwise, both sides are the polynomial `(az+b)^k (cz+d)^(n−k)`. -/
theorem polyEmbed_slash (hb : LevelBounds S ρ) (n : ℕ) (ν : Sigma0 K γv hγv →* Kˣ)
    (δ : Sigma0' K γv hγv) (hδ : δ.1 ∈ S) (P : WeightModule K n ν) :
    polyEmbed n ν (P ∣ₛ δ)
      = detTwist ν δ •
          (algWeight hb n).toWeightSeries.kappaSlash ⟨δ.1, hδ⟩ (polyEmbed n ν P) := by
  have hd : δ.1 1 1 ≠ 0 := hb.d_ne_zero hδ
  have hsub : (matrixSubstR δ.1 (P.1 : MvPolynomial (Fin 2) K)).IsHomogeneous n :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mp
      (matrixSubstR_mem_homogeneousSubmodule δ.1 P.2)
  refine DFunLike.ext _ _ fun j => ?_
  rw [polyEmbed_eq_coeff, WeightModule.slash_coe, Units.smul_def,
    MvPolynomial.coeff_smul, smul_eq_mul, ← coeff_dehom n hsub j,
    show dehom (matrixSubstR δ.1 (P.1 : MvPolynomial (Fin 2) K))
        = MvPolynomial.aeval ![numX δ.1, linX δ.1] (P.1 : MvPolynomial (Fin 2) K) from
      DFunLike.congr_fun (dehom_comp_matrixSubstR δ.1) P.1]
  conv_lhs => rw [homog_repr n ν P, map_sum, map_sum]
  rw [Units.smul_def, smul_apply, detTwist_apply, WeightSeries.kappaSlash_apply]
  refine congrArg (fun x => (ν (Sigma0'.adj δ) : K) * x) ?_
  refine Eq.trans (Finset.sum_congr rfl fun i hi => ?_)
    (tsum_mul_eq_sum_range fun i hi => polyEmbed_apply_of_gt n ν P hi).symm
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [show ((⟨δ.1, hδ⟩ : S) : Matrix (Fin 2) (Fin 2) K) = δ.1 from rfl,
    MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun k => pow_zero _),
    Fin.prod_univ_two,
    show (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (n - i)) 0 = i by
      simp,
    show (Finsupp.single (0 : Fin 2) i + Finsupp.single (1 : Fin 2) (n - i)) 1 = n - i by
      simp]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, PowerSeries.algebraMap_eq,
    PowerSeries.coeff_C_mul]
  rw [autFactor_mul_mobius_pow_eq hb n hd hin, polyEmbed_apply n ν P i hin,
    mul_comm (numX δ.1 ^ i) (linX δ.1 ^ (n - i))]
  ring

/-- Homogenisation, the section of `polyEmbed`: `f ↦ ∑_{k ≤ n} f k · X^k Y^(n−k)`. -/
noncomputable def homogenise (n : ℕ) (ν : Sigma0 K γv hγv →* Kˣ) :
    c(ℕ, K) →ₗ[K] WeightModule K n ν where
  toFun f := ⟨∑ k ∈ Finset.range (n + 1),
      MvPolynomial.monomial
        (Finsupp.single (0 : Fin 2) k + Finsupp.single (1 : Fin 2) (n - k)) (f k),
    Submodule.sum_mem _ fun k hk =>
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
        (MvPolynomial.isHomogeneous_monomial _ (by
          rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
          have := Finset.mem_range.mp hk
          omega))⟩
  map_add' f g := Subtype.ext (by
    show (∑ k ∈ Finset.range (n + 1), MvPolynomial.monomial
          (Finsupp.single (0 : Fin 2) k + Finsupp.single (1 : Fin 2) (n - k))
          ((f + g) k))
        = (∑ k ∈ Finset.range (n + 1), MvPolynomial.monomial
            (Finsupp.single (0 : Fin 2) k + Finsupp.single (1 : Fin 2) (n - k)) (f k))
          + ∑ k ∈ Finset.range (n + 1), MvPolynomial.monomial
              (Finsupp.single (0 : Fin 2) k + Finsupp.single (1 : Fin 2) (n - k)) (g k)
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [add_apply, map_add])
  map_smul' r f := Subtype.ext (by
    show (∑ k ∈ Finset.range (n + 1), MvPolynomial.monomial
          (Finsupp.single (0 : Fin 2) k + Finsupp.single (1 : Fin 2) (n - k))
          ((r • f) k))
        = r • ∑ k ∈ Finset.range (n + 1), MvPolynomial.monomial
            (Finsupp.single (0 : Fin 2) k + Finsupp.single (1 : Fin 2) (n - k)) (f k)
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [smul_apply, ← smul_eq_mul, map_smul])

theorem polyEmbed_homogenise (n : ℕ) (ν : Sigma0 K γv hγv →* Kˣ) (f : c(ℕ, K))
    (k : ℕ) (hk : k ≤ n) : polyEmbed n ν (homogenise n ν f) k = f k := by
  have hcoe : (homogenise n ν f).1 = ∑ k ∈ Finset.range (n + 1),
      MvPolynomial.monomial
        (Finsupp.single (0 : Fin 2) k + Finsupp.single (1 : Fin 2) (n - k)) (f k) := rfl
  rw [polyEmbed_apply n ν _ k hk, hcoe, MvPolynomial.coeff_sum,
    Finset.sum_eq_single k
      (fun i _ hine => by
        rw [MvPolynomial.coeff_monomial, if_neg]
        intro heq
        exact hine (by
          have h0 := DFunLike.congr_fun heq 0
          simpa [Finsupp.single_apply] using h0))
      (fun hnot => absurd (Finset.mem_range.mpr (by omega)) hnot),
    MvPolynomial.coeff_monomial, if_pos rfl]

theorem homogenise_polyEmbed (n : ℕ) (ν : Sigma0 K γv hγv →* Kˣ)
    (P : WeightModule K n ν) : homogenise n ν (polyEmbed n ν P) = P := by
  refine Subtype.ext ?_
  have hcoe : (homogenise n ν (polyEmbed n ν P)).1 = ∑ k ∈ Finset.range (n + 1),
      MvPolynomial.monomial
        (Finsupp.single (0 : Fin 2) k + Finsupp.single (1 : Fin 2) (n - k))
        (polyEmbed n ν P k) := rfl
  rw [hcoe]
  conv_rhs => rw [homog_repr n ν P]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [polyEmbed_apply n ν P k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))]

theorem polyEmbed_mem_polySubmodule (n : ℕ) (ν : Sigma0 K γv hγv →* Kˣ)
    (P : WeightModule K n ν) : polyEmbed n ν P ∈ polySubmodule K n :=
  fun _ hm => polyEmbed_apply_of_gt n ν P hm

/-- The image of dehomogenisation is exactly the polynomial submodule. -/
theorem range_polyEmbed (n : ℕ) (ν : Sigma0 K γv hγv →* Kˣ) :
    LinearMap.range (polyEmbed n ν) = polySubmodule K n := by
  refine le_antisymm ?_ fun f hf => ⟨homogenise n ν f, ?_⟩
  · rintro _ ⟨P, rfl⟩
    exact polyEmbed_mem_polySubmodule n ν P
  · refine DFunLike.ext _ _ fun k => ?_
    rcases Nat.lt_or_ge n k with hk | hk
    · rw [polyEmbed_apply_of_gt n ν _ hk, hf k hk]
    · rw [polyEmbed_homogenise n ν f k hk]

/-- **The slash-equivariant identification**: the classical weight space *is* the
polynomial submodule of the Tate algebra (`polyEmbed` corestricted, with inverse the
homogenisation).  The underlying equivalence is `ν`-uniform (`ν` is a phantom of
`WeightModule`); `ν` enters only through `polyEmbedEquiv_slash`. -/
noncomputable def polyEmbedEquiv (n : ℕ) (ν : Sigma0 K γv hγv →* Kˣ) :
    WeightModule K n ν ≃ₗ[K] polySubmodule K n :=
  LinearEquiv.ofLinear
    (LinearMap.codRestrict (polySubmodule K n) (polyEmbed n ν)
      (polyEmbed_mem_polySubmodule n ν))
    ((homogenise n ν).comp (polySubmodule K n).subtype)
    (LinearMap.ext fun f => Subtype.ext (by
      show polyEmbed n ν (homogenise n ν f.1) = f.1
      refine DFunLike.ext _ _ fun k => ?_
      rcases Nat.lt_or_ge n k with hk | hk
      · rw [polyEmbed_apply_of_gt n ν _ hk, f.2 k hk]
      · exact polyEmbed_homogenise n ν f.1 k hk))
    (LinearMap.ext fun P => homogenise_polyEmbed n ν P)

@[simp] theorem polyEmbedEquiv_coe (n : ℕ) (ν : Sigma0 K γv hγv →* Kˣ)
    (P : WeightModule K n ν) :
    (polyEmbedEquiv n ν P : c(ℕ, K)) = polyEmbed n ν P :=
  rfl

/-- `polyEmbed_slash` read on the equivalence: the classical slash on `L_{n,ν}` is the
`ν`-twisted weight-`u^(n+2)` action restricted to the polynomial submodule. -/
theorem polyEmbedEquiv_slash (hb : LevelBounds S ρ) (n : ℕ)
    (ν : Sigma0 K γv hγv →* Kˣ) (δ : Sigma0' K γv hγv) (hδ : δ.1 ∈ S)
    (P : WeightModule K n ν) :
    (polyEmbedEquiv n ν (P ∣ₛ δ) : c(ℕ, K))
      = detTwist ν δ • (algWeight hb n).toWeightSeries.kappaSlash ⟨δ.1, hδ⟩
          (polyEmbedEquiv n ν P) := by
  rw [polyEmbedEquiv_coe, polyEmbedEquiv_coe, polyEmbed_slash hb n ν δ hδ P]

end Valued

end QMF

namespace AutomorphicFunction

variable {G : Type*} [Group G] {Γ : Subgroup G} {R : Type*} [Semiring R]
variable {A B : Type*} [AddCommMonoid A] [AddCommMonoid B] [Module R A] [Module R B]

/-- Postcomposition with a linear map of coefficient modules, on automorphic
functions. -/
noncomputable def mapCoeff (T : A →ₗ[R] B) :
    AutomorphicFunction G Γ A →ₗ[R] AutomorphicFunction G Γ B where
  toFun φ := ⟨fun g => T (φ g), fun γ hγ g => by rw [φ.left_invt' hγ]⟩
  map_add' φ ψ := ext fun g => by simp
  map_smul' r φ := ext fun g => by simp

@[simp] theorem mapCoeff_apply (T : A →ₗ[R] B) (φ : AutomorphicFunction G Γ A) (g : G) :
    mapCoeff T φ g = T (φ g) :=
  rfl

variable {Δ' : Submonoid G} [RightSlashAction Δ' A] [RightSlashAction Δ' B]

/-- A slash-equivariant coefficient map commutes with the slash on automorphic
functions. -/
theorem mapCoeff_slash (T : A →ₗ[R] B)
    (hT : ∀ (a : A) (δ : Δ'), T (a ∣ₛ δ) = T a ∣ₛ δ)
    (φ : AutomorphicFunction G Γ A) (δ : Δ') :
    mapCoeff T (φ ∣ₛ δ) = mapCoeff T φ ∣ₛ δ :=
  ext fun g => by simp [hT]

variable [RightSlashAction.SMulSlashClass R Δ' A] [RightSlashAction.SMulSlashClass R Δ' B]

/-- Def 1.30 functoriality: an equivariant coefficient map preserves the
transformation law, hence maps `L(U, A)` into `L(U, B)`. -/
theorem mapCoeff_mem_levelSubmoduleSlash (T : A →ₗ[R] B)
    (hT : ∀ (a : A) (δ : Δ'), T (a ∣ₛ δ) = T a ∣ₛ δ)
    {U : Subgroup G} (hU : (U : Set G) ⊆ Δ') {φ : AutomorphicFunction G Γ A}
    (hφ : φ ∈ levelSubmoduleSlash R U hU) :
    mapCoeff T φ ∈ levelSubmoduleSlash (Γ := Γ) R U hU := by
  rw [mem_levelSubmoduleSlash_iff] at hφ ⊢
  intro u
  rw [← mapCoeff_slash T hT, hφ u]

/-- The image of a slash-fixed point under an equivariant coefficient map is again a
slash-fixed point (`slashFixedPointsOfLE` form of `mapCoeff_mem_levelSubmoduleSlash`). -/
theorem mapCoeff_mem_slashFixedPointsOfLE (T : A →ₗ[R] B)
    (hT : ∀ (a : A) (δ : Δ'), T (a ∣ₛ δ) = T a ∣ₛ δ)
    {U : Subgroup G} (hU : (U : Set G) ⊆ Δ')
    {φ : AutomorphicFunction G Γ A}
    (hφ : φ ∈ AbstractHeckeOperatorSlash.slashFixedPointsOfLE (U := U) R
      (AutomorphicFunction G Γ A) hU) :
    mapCoeff T φ ∈ AbstractHeckeOperatorSlash.slashFixedPointsOfLE (U := U) R
      (AutomorphicFunction G Γ B) hU := by
  rw [AbstractHeckeOperatorSlash.mem_slashFixedPointsOfLE_iff] at hφ ⊢
  intro u
  rw [← mapCoeff_slash T hT, hφ u]

/-- Def 1.32 functoriality: the Hecke operator `[UηU]` commutes with an equivariant
coefficient map (`[UvU]φ = Σ_t φ|v_t` is preserved by postcomposition). -/
theorem heckeOperatorSlash_mapCoeff (T : A →ₗ[R] B)
    (hT : ∀ (a : A) (δ : Δ'), T (a ∣ₛ δ) = T a ∣ₛ δ)
    {U : Subgroup G} (hU : (U : Set G) ⊆ Δ') {η : G} (hη : η ∈ Δ')
    (h : (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
        ({η} * (U : Set G))) : Set (AbstractHeckeOperatorSlash.RightCosets U)).Finite)
    (φ : AbstractHeckeOperatorSlash.slashFixedPointsOfLE (U := U) R
      (AutomorphicFunction G Γ A) hU) :
    mapCoeff T (AbstractHeckeOperatorSlash.heckeOperatorSlash R hU hU hη h φ :
        AutomorphicFunction G Γ A)
      = (AbstractHeckeOperatorSlash.heckeOperatorSlash R hU hU hη h
          ⟨mapCoeff T φ.1, mapCoeff_mem_slashFixedPointsOfLE T hT hU φ.2⟩ :
          AutomorphicFunction G Γ B) := by
  have : Fintype (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
      ({η} * (U : Set G))) : Set (AbstractHeckeOperatorSlash.RightCosets U)) := h.fintype
  rw [AbstractHeckeOperatorSlash.heckeOperatorSlash_apply,
    AbstractHeckeOperatorSlash.heckeOperatorSlash_apply, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, map_sum]
  exact Finset.sum_congr rfl fun x _ => mapCoeff_slash T hT _ _

end AutomorphicFunction

namespace QMF

variable {K : Type*} [NontriviallyNormedField K] [iu2 : IsUltrametricDist K]
  [cs2 : CompleteSpace K]
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]
  {γv : Γ₀} {hγv : γv < 1} {ρ : ℝ}
variable {G : Type*} [Group G] {Γ : Subgroup G}

/-- The classical coefficient action of the wild-level monoid `θ⁻¹(Σ₀'(γ))` on the
weight module, through the corestriction of `θ` (Buzzard's convention; for
`G = Dfx F D`, `θ = toMatrix F D v` the monoid is `QMF.levelMonoid'` and this is the
`WeightModule` slash instance of `PhD/QMF/Slash/Quaternionic.lean` on the nose). -/
@[instance_reducible]
noncomputable def classicalWeightAction (θ : G →* Matrix (Fin 2) (Fin 2) K) (n : ℕ)
    (ν : Sigma0 K γv hγv →* Kˣ) :
    RightSlashAction (Weight.levelMonoidOf θ (Sigma0' K γv hγv)) (WeightModule K n ν) :=
  RightSlashAction.comap (Weight.levelMonoidOfToS θ (Sigma0' K γv hγv)) inferInstance

omit iu2 cs2 in
/-- The classical action commutes with scalars. -/
theorem classicalWeightSMulSlash (θ : G →* Matrix (Fin 2) (Fin 2) K) (n : ℕ)
    (ν : Sigma0 K γv hγv →* Kˣ) :
    letI := classicalWeightAction θ n ν
    RightSlashAction.SMulSlashClass K (Weight.levelMonoidOf θ (Sigma0' K γv hγv))
      (WeightModule K n ν) :=
  letI := classicalWeightAction θ n ν
  ⟨fun r P δ => RightSlashAction.SMulSlashClass.smul_slash r P
    (Weight.levelMonoidOfToS θ (Sigma0' K γv hγv) δ)⟩

/-- **Pointwise embedding**: dehomogenisation intertwines the classical weight action
with the `ν`-twisted overconvergent action of the headline weight `algWeight hb n` —
`polyEmbed_slash` read through the level plumbing. -/
theorem polyEmbed_slash_level (θ : G →* Matrix (Fin 2) (Fin 2) K)
    (hb : LevelBounds (Sigma0' K γv hγv) ρ) (n : ℕ) (ν : Sigma0 K γv hγv →* Kˣ)
    (P : WeightModule K n ν) (u : Weight.levelMonoidOf θ (Sigma0' K γv hγv)) :
    letI := classicalWeightAction θ n ν
    letI := Weight.kappaLevelSlashActionTwisted θ (algWeight hb n) (detTwist ν)
    polyEmbed n ν (P ∣ₛ u) = polyEmbed n ν P ∣ₛ u := by
  letI := classicalWeightAction θ n ν
  letI := Weight.kappaLevelSlashActionTwisted θ (algWeight hb n) (detTwist ν)
  show polyEmbed n ν (P ∣ₛ Weight.levelMonoidOfToS θ (Sigma0' K γv hγv) u)
      = detTwist ν (Weight.levelMonoidOfToS θ (Sigma0' K γv hγv) u)
          • (algWeight hb n).toWeightSeries.kappaSlash
              (Weight.levelMonoidOfToS θ (Sigma0' K γv hγv) u) (polyEmbed n ν P)
  exact polyEmbed_slash hb n ν (Weight.levelMonoidOfToS θ (Sigma0' K γv hγv) u)
    (Weight.levelMonoidOfToS θ (Sigma0' K γv hγv) u).2 P

/-! ### The classical inclusion at the headline (Buzzard §11)

[Buzzard, *Eigenvarieties*, §11 p. 73]: "If `r ∈ (N_K)^J` then there is a natural
injection `L_{n,v} → A_{κ,r} = O(B_r)` … and one checks easily that this is an
`M₁`-equivariant inclusion.  If `U ⊂ D^×_f` is a compact open subgroup of level `≥ π`
then we get an inclusion `S^D_{k,w}(U) = L(U, L_{n,v}) ⊆ L(U, A_{κ,r}) = S^D_κ(U; r)`
between the finite-dimensional space of classical forms and the typically
infinite-dimensional space of overconvergent ones."

The `M₁`-equivariant injection is `polyEmbed` (`polyEmbed_slash`), and the inclusion is
`map_classicalForms_le_forms`, stated for the headline `Weight.Forms` at the weight
`algWeight hb n` (`κ(u) = u^(n+2)`) twisted by `detTwist ν` (Buzzard's `v(det γ)`). -/

/-- **The classical space `S^D_{k,w}(U)` at abstract `(G, θ)`** ([Buzzard, §9 p. 70]: "the
space of classical automorphic forms `S^D_{k,w}(U)` of weight `(k, w)` and level `U` for
`D` is the space `L(U, L_{n,v})`"): the slash-fixed points of `U` on `L_{n,ν}`-valued
automorphic functions, for the classical action of the level monoid `θ⁻¹(Σ₀'(γ))`.  The
quaternionic instance (`G = Dfx F D`, `θ = toMatrix F D v`) is `QMF.SpaceSlash`. -/
noncomputable def classicalForms (θ : G →* Matrix (Fin 2) (Fin 2) K) (n : ℕ)
    (ν : Sigma0 K γv hγv →* Kˣ) (U : Subgroup G)
    (hU : (U : Set G) ⊆ Weight.levelMonoidOf θ (Sigma0' K γv hγv)) :
    Submodule K (AutomorphicFunction G Γ (WeightModule K n ν)) :=
  letI := classicalWeightAction θ n ν
  letI := classicalWeightSMulSlash θ n ν
  AbstractHeckeOperatorSlash.slashFixedPointsOfLE K
    (AutomorphicFunction G Γ (WeightModule K n ν)) hU

/-- **The classical Hecke operator `[UηU]`** on `classicalForms` ([Buzzard, §9 p. 69]). -/
noncomputable def classicalHeckeOperator (θ : G →* Matrix (Fin 2) (Fin 2) K) (n : ℕ)
    (ν : Sigma0 K γv hγv →* Kˣ) (U : Subgroup G)
    (hU : (U : Set G) ⊆ Weight.levelMonoidOf θ (Sigma0' K γv hγv)) {η : G}
    (hη : η ∈ Weight.levelMonoidOf θ (Sigma0' K γv hγv))
    (h : (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
        ({η} * (U : Set G))) : Set (AbstractHeckeOperatorSlash.RightCosets U)).Finite) :
    classicalForms (Γ := Γ) θ n ν U hU →ₗ[K] classicalForms (Γ := Γ) θ n ν U hU :=
  letI := classicalWeightAction θ n ν
  letI := classicalWeightSMulSlash θ n ν
  AbstractHeckeOperatorSlash.heckeOperatorSlash K hU hU hη h

/-- **[Buzzard, §11 p. 73]: classical forms are overconvergent** —
`S^D_{k,w}(U) = L(U, L_{n,v}) ⊆ L(U, A_{κ,r}) = S^D_κ(U; r)`: dehomogenisation maps the
classical space of weight `(n, ν)` into the forms of the headline weight `κ(u) = u^(n+2)`
twisted by `ν`. -/
theorem map_classicalForms_le_forms (θ : G →* Matrix (Fin 2) (Fin 2) K)
    (hb : LevelBounds (Sigma0' K γv hγv) ρ) (n : ℕ) (ν : Sigma0 K γv hγv →* Kˣ)
    {U : Subgroup G} (hU : (U : Set G) ⊆ Weight.levelMonoidOf θ (Sigma0' K γv hγv)) :
    (classicalForms (Γ := Γ) θ n ν U hU).map (AutomorphicFunction.mapCoeff (polyEmbed n ν))
      ≤ Weight.Forms Γ θ (algWeight hb n) U hU (detTwist ν) := by
  letI := classicalWeightAction θ n ν
  letI := classicalWeightSMulSlash θ n ν
  letI := Weight.kappaLevelSlashActionTwisted θ (algWeight hb n) (detTwist ν)
  letI := Weight.kappaLevelSMulSlashClassTwisted θ (algWeight hb n) (detTwist ν)
  rintro _ ⟨φ, hφ, rfl⟩
  exact AutomorphicFunction.mapCoeff_mem_levelSubmoduleSlash (polyEmbed n ν)
    (fun P u => polyEmbed_slash_level θ hb n ν P u) hU hφ

/-- **The R6 endpoint at the headline** — *classical = polynomial-valued overconvergent*:
`ψ` is the image of a classical form of weight `(n, ν)` iff it is an overconvergent form of
the headline weight all of whose values are polynomials of degree `≤ n`. -/
theorem mem_map_classicalForms_iff (θ : G →* Matrix (Fin 2) (Fin 2) K)
    (hb : LevelBounds (Sigma0' K γv hγv) ρ) (n : ℕ) (ν : Sigma0 K γv hγv →* Kˣ)
    {U : Subgroup G} (hU : (U : Set G) ⊆ Weight.levelMonoidOf θ (Sigma0' K γv hγv))
    (ψ : AutomorphicFunction G Γ c(ℕ, K)) :
    ψ ∈ (classicalForms (Γ := Γ) θ n ν U hU).map
        (AutomorphicFunction.mapCoeff (polyEmbed n ν))
      ↔ ψ ∈ Weight.Forms Γ θ (algWeight hb n) U hU (detTwist ν)
          ∧ ∀ g : G, ψ g ∈ polySubmodule K n := by
  letI := classicalWeightAction θ n ν
  letI := classicalWeightSMulSlash θ n ν
  letI := Weight.kappaLevelSlashActionTwisted θ (algWeight hb n) (detTwist ν)
  letI := Weight.kappaLevelSMulSlashClassTwisted θ (algWeight hb n) (detTwist ν)
  have hE : ∀ x : polySubmodule K n,
      polyEmbed n ν ((polyEmbedEquiv n ν).symm x) = x.1 := fun x => by
    rw [← polyEmbedEquiv_coe n ν, LinearEquiv.apply_symm_apply]
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact ⟨map_classicalForms_le_forms θ hb n ν hU (Submodule.mem_map_of_mem hφ),
      fun g => polyEmbed_mem_polySubmodule n ν (φ g)⟩
  · rintro ⟨hψ, hval⟩
    refine ⟨⟨fun g => (polyEmbedEquiv n ν).symm ⟨ψ g, hval g⟩,
      fun γ' hγ' g => congrArg (polyEmbedEquiv n ν).symm
        (Subtype.ext (ψ.left_invt' hγ' g))⟩, ?_, ?_⟩
    · refine (AbstractHeckeOperatorSlash.mem_slashFixedPointsOfLE_iff K hU).mpr fun u => ?_
      refine AutomorphicFunction.ext fun g => ?_
      simp only [AutomorphicFunction.slash_apply, AutomorphicFunction.coe_mk]
      refine polyEmbed_injective n ν ?_
      rw [polyEmbed_slash_level θ hb n ν, hE, hE]
      have hψu := DFunLike.congr_fun
        ((AbstractHeckeOperatorSlash.mem_slashFixedPointsOfLE_iff K hU).mp hψ u) g
      rwa [AutomorphicFunction.slash_apply] at hψu
    · refine AutomorphicFunction.ext fun g => ?_
      rw [AutomorphicFunction.mapCoeff_apply]
      exact hE ⟨ψ g, hval g⟩

/-- **Hecke equivariance at the headline** ([Jacobs, Def 1.32]): through dehomogenisation,
the headline `heckeOperator` at the twisted weight `(algWeight hb n, detTwist ν)` is the
classical Hecke operator. -/
theorem heckeOperator_mapCoeff_polyEmbed (θ : G →* Matrix (Fin 2) (Fin 2) K)
    (hb : LevelBounds (Sigma0' K γv hγv) ρ) (n : ℕ) (ν : Sigma0 K γv hγv →* Kˣ)
    {U : Subgroup G} (hU : (U : Set G) ⊆ Weight.levelMonoidOf θ (Sigma0' K γv hγv))
    {η : G} (hη : η ∈ Weight.levelMonoidOf θ (Sigma0' K γv hγv))
    (h : (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
        ({η} * (U : Set G))) : Set (AbstractHeckeOperatorSlash.RightCosets U)).Finite)
    (φ : classicalForms (Γ := Γ) θ n ν U hU)
    (ψ : Weight.Forms Γ θ (algWeight hb n) U hU (detTwist ν))
    (hψ : (ψ : AutomorphicFunction G Γ c(ℕ, K))
      = AutomorphicFunction.mapCoeff (polyEmbed n ν) φ) :
    (Weight.heckeOperator θ (algWeight hb n) U hU hη h ψ :
        AutomorphicFunction G Γ c(ℕ, K))
      = AutomorphicFunction.mapCoeff (polyEmbed n ν)
          (classicalHeckeOperator θ n ν U hU hη h φ :
            AutomorphicFunction G Γ (WeightModule K n ν)) := by
  letI := classicalWeightAction θ n ν
  letI := classicalWeightSMulSlash θ n ν
  letI := Weight.kappaLevelSlashActionTwisted θ (algWeight hb n) (detTwist ν)
  letI := Weight.kappaLevelSMulSlashClassTwisted θ (algWeight hb n) (detTwist ν)
  have key := AutomorphicFunction.heckeOperatorSlash_mapCoeff (polyEmbed n ν)
    (fun P u => polyEmbed_slash_level θ hb n ν P u) hU hη h φ
  have hψ' : ψ = ⟨AutomorphicFunction.mapCoeff (polyEmbed n ν) φ,
      AutomorphicFunction.mapCoeff_mem_slashFixedPointsOfLE (polyEmbed n ν)
        (fun P u => polyEmbed_slash_level θ hb n ν P u) hU φ.2⟩ := Subtype.ext hψ
  subst hψ'
  exact key.symm

end QMF

