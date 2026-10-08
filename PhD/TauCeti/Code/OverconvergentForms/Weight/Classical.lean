/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import PhD.TauCeti.Code.OverconvergentForms.Weight.Algebraic

/-!
# The classical weight modules `L_n = ⊗ᵢ Sym^{nᵢ}` and the bridge to the Tate algebra

The classical weight module `L_n`, `n ∈ ℕ^ι`, is realised as the multi-homogeneous polynomials of
degree `n_i` in each pair `(X_i, Y_i)` — Mathlib's `weightedHomogeneousSubmodule` for the weight
`(i, _) ↦ Pi.single i 1` on `MvPolynomial (ι × Fin 2) K`. *Every* multi-matrix acts on it by
`P(X, Y) ↦ P(aX + bY, cX + dY)`, a right action by composition of `aeval`s, with no determinant and
no level condition; the determinant twist `det^v` is the twist of §1.2.8. The dehomogenisation
`X_i ↦ z_i`, `Y_i ↦ 1` identifies `L_n` with the polynomials of the Tate algebra of degree at most
`n_i` in each `z_i` (`polySubmodule`), of dimension `∏ (n_i + 1)`, and **the bridge**: for `γ` in a
level, dehomogenisation intertwines the action on `L_n` with the weight action of the algebraic
weight `algWeight (n, 1)` — so `L_n ⊆ A` is a `Σ`-stable finite-dimensional subspace, exactly the
span of the monomials `z^m`, `m ≤ n`.

[Buz07, §9, p. 68]: "If `n ∈ ℤ^I_{≥0}` then we define `L_n` to be the `K`-vector space with basis
the monomials `∏_{i ∈ I} Z_i^{m_i}`, where `m ∈ ℤ^I_{≥0}`, `0 ≤ m_i ≤ n_i` […]. If `v ∈ ℤ^I` and
`n ∈ ℤ^I_{≥0}` then define the right `M_1`-module `L_{n,v}` to be the `K`-vector space `L_n`
equipped with the action of `M_1` defined by letting `(γ_j) = (((a_j b_j), (c_j d_j)))_{j ∈ J}`
send `∏_i Z_i^{m_i}` to
`∏_i (c_i Z_i + d_i)^{n_i} (a_i d_i − b_i c_i)^{v_i} ((a_i Z_i + b_i)/(c_i Z_i + d_i))^{m_i}`
and extending `K`-linearly […]. Note that in fact the same definition gives an action of
`GL₂(F_p)` on `L_{n,v}`."
[Buz07, §11, p. 73]: "there is a natural injection `L_{n,v} → A_{κ,r} = 𝒪(B_r)` induced from the
natural inclusion `B_r ⊂ (𝔸¹)^I` and one checks easily that this is an `M_1`-equivariant inclusion."

## Main definitions

* `AutomorphicForm.SymPow K ι n`: the module `⊗ᵢ Sym^{nᵢ}` in its homogeneous model.
* `AutomorphicForm.symAct γ`: the action `P ↦ P(aX + bY, cX + dY)` of a multi-matrix.
* `AutomorphicForm.symPowAction`, `AutomorphicForm.classicalAction e n v`: the right actions on
  `L_n` and on `L_{n,v}` (of `GL₂(L)` through the embeddings).
* `AutomorphicForm.toTate K ι`: the dehomogenisation `X_i ↦ z_i`, `Y_i ↦ 1`.
* `AutomorphicForm.polySubmodule K ι n`: the span of the monomials `z^m`, `m ≤ n`.

## Main results

* `AutomorphicForm.symAct_mul`, `AutomorphicForm.symAct_mem_symPow`: the right action.
* `AutomorphicForm.finrank_symPow`: `dim L_n = ∏ (n_i + 1)`.
* `AutomorphicForm.toTateEquiv`: `L_n ≃ polySubmodule n`.
* `AutomorphicForm.toTate_symAct`: **the bridge**.
* `AutomorphicForm.polySubmodule_stable`: `L_n ⊆ A` is `Σ`-stable.

Roadmap: §1.3.2–§1.3.3. Tau Ceti home:
`TauCeti/NumberTheory/AutomorphicForm/Weight/Classical.lean`.
-/

open MvPowerSeries MvPowerSeries.Restricted MvPolynomial

namespace MvPolynomial

variable {R σ τ M : Type*} [CommSemiring R] [AddCommMonoid M]

/-- Substituting weighted-homogeneous polynomials of the right degrees into a weighted-homogeneous
polynomial gives a weighted-homogeneous polynomial. -/
theorem IsWeightedHomogeneous.aeval {w : σ → M} {w' : τ → M} {f : σ → MvPolynomial τ R}
    (hf : ∀ s, IsWeightedHomogeneous w' (f s) (w s)) {φ : MvPolynomial σ R} {m : M}
    (hφ : IsWeightedHomogeneous w φ m) : IsWeightedHomogeneous w' (aeval f φ) m := by
  induction hφ using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact isWeightedHomogeneous_zero R w' m
  | add p q hp hq ihp ihq => rw [map_add]; exact ihp.add ihq
  | monomial d r hr =>
    rw [aeval_monomial, algebraMap_eq, ← hr, Finsupp.weight_apply, ← zero_add (d.sum _)]
    exact (isWeightedHomogeneous_C w' r).mul
      (IsWeightedHomogeneous.prod _ _ _ fun s _ => (hf s).pow (d s))

end MvPolynomial

namespace AutomorphicForm

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### `Sym^n` and the action of the multi-matrices -/

variable (ι) in
/-- The multi-grading of `K[X_i, Y_i : i ∈ ι]` by the degree in each pair `(X_i, Y_i)`. -/
def symWeight : ι × Fin 2 → (ι → ℕ) := fun v => Pi.single v.1 1

variable (K ι) in
/-- **The classical weight module** `L_n = ⊗ᵢ Sym^{nᵢ}`: the polynomials in `X_i, Y_i` homogeneous
of degree `n_i` in each pair. Source: roadmap §1.3.2 ("`⊗_i K[X_i, Y_i]_{n_i}`, Mathlib's
`homogeneousSubmodule`"); [Buz07, §9, p. 68]. -/
def SymPow (n : ι → ℕ) : Submodule K (MvPolynomial (ι × Fin 2) K) :=
  weightedHomogeneousSubmodule K (symWeight ι) n

omit [IsUltrametricDist K] [CompleteSpace K] [Fintype ι] in
theorem mem_symPow_iff {n : ι → ℕ} {P : MvPolynomial (ι × Fin 2) K} :
    P ∈ SymPow K ι n ↔ IsWeightedHomogeneous (symWeight ι) P n :=
  Iff.rfl

/-- The substituted variables: `X_{(i,j)} ↦ ∑_k γ_{i,jk} X_{(i,k)}`, i.e.
`(X_i, Y_i) ↦ (a_i X_i + b_i Y_i, c_i X_i + d_i Y_i)`. -/
noncomputable def symVars (γ : ι → Matrix (Fin 2) (Fin 2) K) :
    ι × Fin 2 → MvPolynomial (ι × Fin 2) K :=
  fun v => ∑ k, MvPolynomial.C (γ v.1 v.2 k) * MvPolynomial.X (v.1, k)

/-- **The action of a multi-matrix on polynomials**: `P(X, Y) ↦ P(aX + bY, cX + dY)`, for every
matrix (no determinant condition). Source: roadmap §1.3.2; [Buz07, §9, p. 68]. -/
noncomputable def symAct (γ : ι → Matrix (Fin 2) (Fin 2) K) :
    MvPolynomial (ι × Fin 2) K →ₐ[K] MvPolynomial (ι × Fin 2) K :=
  aeval (symVars γ)

omit [IsUltrametricDist K] [CompleteSpace K] [Fintype ι] [DecidableEq ι] in
@[simp] theorem symAct_X (γ : ι → Matrix (Fin 2) (Fin 2) K) (v : ι × Fin 2) :
    symAct γ (MvPolynomial.X v) = ∑ k, MvPolynomial.C (γ v.1 v.2 k) * MvPolynomial.X (v.1, k) :=
  aeval_X _ v

omit [IsUltrametricDist K] [CompleteSpace K] [Fintype ι] [DecidableEq ι] in
theorem symAct_one : symAct (1 : ι → Matrix (Fin 2) (Fin 2) K) = AlgHom.id K _ := by
  refine MvPolynomial.algHom_ext fun v => ?_
  have h : ∀ k ∈ (Finset.univ : Finset (Fin 2)), k ≠ v.2 →
      MvPolynomial.C ((1 : ι → Matrix (Fin 2) (Fin 2) K) v.1 v.2 k) * MvPolynomial.X (v.1, k) = 0 :=
    fun k _ hk => by simp [Matrix.one_apply_ne (Ne.symm hk)]
  rw [symAct_X, AlgHom.id_apply,
    Finset.sum_eq_single v.2 h fun h' => absurd (Finset.mem_univ _) h']
  simp

omit [IsUltrametricDist K] [CompleteSpace K] [Fintype ι] [DecidableEq ι] in
/-- `(P ∣ δ) ∣ γ = P ∣ (δγ)`: a right action. Source: roadmap §1.3.2. -/
theorem symAct_mul (γ δ : ι → Matrix (Fin 2) (Fin 2) K) :
    symAct (δ * γ) = (symAct γ).comp (symAct δ) := by
  refine MvPolynomial.algHom_ext fun v => ?_
  simp only [AlgHom.comp_apply, symAct, MvPolynomial.aeval_X, symVars, map_mul,
    MvPolynomial.aeval_C, algebraMap_eq, Fin.sum_univ_two, Pi.mul_apply, Matrix.mul_apply, map_add]
  ring

omit [IsUltrametricDist K] [CompleteSpace K] [Fintype ι] in
theorem isWeightedHomogeneous_symVars (γ : ι → Matrix (Fin 2) (Fin 2) K) (v : ι × Fin 2) :
    IsWeightedHomogeneous (symWeight ι) (symVars γ v) (symWeight ι v) :=
  IsWeightedHomogeneous.sum _ _ _ fun k _ =>
    (isWeightedHomogeneous_X K (symWeight ι) (v.1, k)).C_mul _

omit [IsUltrametricDist K] [CompleteSpace K] [Fintype ι] in
/-- `L_n` is stable under every multi-matrix. Source: roadmap §1.3.2 ("a polynomial in `L_n`"). -/
theorem symAct_mem_symPow (γ : ι → Matrix (Fin 2) (Fin 2) K) {n : ι → ℕ}
    {P : MvPolynomial (ι × Fin 2) K} (hP : P ∈ SymPow K ι n) : symAct γ P ∈ SymPow K ι n :=
  hP.aeval (isWeightedHomogeneous_symVars γ)

variable (n : ι → ℕ)

/-- The action restricted to `L_n`. -/
noncomputable def symActₗ (γ : ι → Matrix (Fin 2) (Fin 2) K) : SymPow K ι n →ₗ[K] SymPow K ι n :=
  (symAct γ).toLinearMap.restrict fun _ hP => symAct_mem_symPow γ hP

/-- The right action of the multi-matrices on `L_n`, as a homomorphism from the opposite monoid. -/
noncomputable def symPowHom : (ι → Matrix (Fin 2) (Fin 2) K)ᵐᵒᵖ →* Module.End K (SymPow K ι n) where
  toFun γ := symActₗ n γ.unop
  map_one' := by
    refine LinearMap.ext fun P => Subtype.ext ?_
    show symAct (MulOpposite.unop 1) (P : MvPolynomial (ι × Fin 2) K) = P
    rw [MulOpposite.unop_one, symAct_one, AlgHom.id_apply]
  map_mul' γ δ := by
    refine LinearMap.ext fun P => Subtype.ext ?_
    show symAct (γ * δ).unop (P : MvPolynomial (ι × Fin 2) K) =
      symAct γ.unop (symAct δ.unop (P : MvPolynomial (ι × Fin 2) K))
    rw [MulOpposite.unop_mul, symAct_mul, AlgHom.comp_apply]

/-- **The right action on `L_n`** (README convention 2). -/
@[instance_reducible]
noncomputable def symPowAction :
    DistribMulAction (ι → Matrix (Fin 2) (Fin 2) K)ᵐᵒᵖ (SymPow K ι n) :=
  DistribMulAction.compHom _ (symPowHom n)

/-- The `i`-th coordinate of the multi-degree of a monomial of `K[X_i, Y_i]` is its degree in the
pair `(X_i, Y_i)`. -/
theorem weight_symWeight_apply (d : ι × Fin 2 →₀ ℕ) (i : ι) :
    Finsupp.weight (symWeight ι) d i = d (i, 0) + d (i, 1) := by
  rw [Finsupp.weight_apply,
    Finsupp.sum_fintype d (fun v c => c • symWeight ι v) (fun _ => zero_smul _ _)]
  simp [symWeight, Fintype.sum_prod_type, Fin.sum_univ_two, Pi.single_apply, Finset.sum_add_distrib]

/-- The exponents of the monomials of `L_n`: `d ↦ (d(i, 0))_i` identifies `{d | weight d = n}` with
`∏_i {0, …, n_i}`. -/
noncomputable def symPowSupportEquiv :
    {d : ι × Fin 2 →₀ ℕ // Finsupp.weight (symWeight ι) d = n} ≃ ((i : ι) → Fin (n i + 1)) where
  toFun d i := ⟨d.1 (i, 0), by
    have h := congrFun d.2 i
    rw [weight_symWeight_apply] at h
    omega⟩
  invFun m :=
    ⟨Finsupp.equivFunOnFinite.symm fun v => if v.2 = 0 then (m v.1 : ℕ) else n v.1 - m v.1, by
      funext i
      have := (m i).2
      rw [weight_symWeight_apply]
      simp only [Finsupp.coe_equivFunOnFinite_symm]
      simp
      omega⟩
  left_inv d := by
    refine Subtype.ext (Finsupp.ext fun v => ?_)
    obtain ⟨i, k⟩ := v
    have h := congrFun d.2 i
    rw [weight_symWeight_apply] at h
    fin_cases k
    · simp
    · simp only [Finsupp.coe_equivFunOnFinite_symm]
      simp
      omega
  right_inv m := by
    funext i
    simp

theorem symPowSupportEquiv_apply (d : {d : ι × Fin 2 →₀ ℕ // Finsupp.weight (symWeight ι) d = n})
    (i : ι) : (symPowSupportEquiv n d i : ℕ) = d.1 (i, 0) :=
  rfl

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **The dimension of `L_n`**: `∏_i (n_i + 1)`. Source: roadmap §1.3.2 ("free of rank
`∏ (n_i + 1)`"); [Buz07, §9, p. 68]. -/
theorem finrank_symPow : Module.finrank K (SymPow K ι n) = ∏ i, (n i + 1) := by
  classical
  have e : {d : ι × Fin 2 →₀ ℕ | Finsupp.weight (symWeight ι) d = n} ≃ ((i : ι) → Fin (n i + 1)) :=
    symPowSupportEquiv n
  haveI : Fintype {d : ι × Fin 2 →₀ ℕ | Finsupp.weight (symWeight ι) d = n} :=
    Fintype.ofEquiv _ e.symm
  rw [SymPow, weightedHomogeneousSubmodule_eq_finsupp_supported,
    (AddMonoidAlgebra.supportedEquivFinsupp _).finrank_eq, Module.finrank_finsupp_self,
    Fintype.card_congr e, Fintype.card_pi]
  simp

/-! ### The `(n, v)`-module of `GL₂(L)` -/

section Classical

variable {L : Type*} [NormedField L] [IsUltrametricDist L] (e : Embeddings L K ι)

/-- **Buzzard's `L_{n,v}`**: `GL₂(L)` acts on `L_n` through the embeddings by
`P ↦ v(det g) · P(aX + bY, cX + dY)`. Source: roadmap §1.3.2; [Buz07, §9, p. 68] ("the same
definition gives an action of `GL₂(F_p)` on `L_{n,v}`"). -/
noncomputable def classicalHom (v : Lˣ →* Kˣ) :
    (GL (Fin 2) L)ᵐᵒᵖ →* Module.End K (SymPow K ι n) where
  toFun g := (v (Matrix.GeneralLinearGroup.det g.unop) : K) • symActₗ n (e.toMulti g.unop)
  map_one' := by
    have h1 : e.toMulti (1 : Matrix (Fin 2) (Fin 2) L) = 1 := e.toMultiHom.map_one
    refine LinearMap.ext fun P => Subtype.ext ?_
    simp [symActₗ, h1, symAct_one]
  map_mul' g h := by
    have hm : e.toMulti ((h.unop : Matrix (Fin 2) (Fin 2) L) * g.unop) =
        e.toMulti h.unop * e.toMulti g.unop :=
      e.toMultiHom.map_mul _ _
    refine LinearMap.ext fun P => Subtype.ext ?_
    simp [symActₗ, hm, symAct_mul, smul_smul, mul_comm]
    rfl

/-- **The right action of `GL₂(L)` on `L_{n,v}`** (README convention 2). -/
@[instance_reducible]
noncomputable def classicalAction (v : Lˣ →* Kˣ) :
    DistribMulAction (GL (Fin 2) L)ᵐᵒᵖ (SymPow K ι n) :=
  DistribMulAction.compHom _ (classicalHom n e v)

omit [CompleteSpace K] [IsUltrametricDist K] [IsUltrametricDist L] in
theorem classicalAction_op_smul (v : Lˣ →* Kˣ) (g : GL (Fin 2) L) (P : SymPow K ι n) :
    letI := classicalAction n e v
    MulOpposite.op g • P = (v (Matrix.GeneralLinearGroup.det g) : K) • symActₗ n (e.toMulti g) P :=
  rfl

end Classical

/-! ### Dehomogenisation and the bridge -/

variable (K ι) in
/-- **Dehomogenisation** `X_i ↦ z_i`, `Y_i ↦ 1`, from `K[X_i, Y_i]` to the Tate algebra. Source:
roadmap §1.3.2 ("with `z_i = X_i / Y_i`"). -/
noncomputable def toTate : MvPolynomial (ι × Fin 2) K →ₐ[K] Restricted K (1 : ι → ℝ) :=
  MvPolynomial.aeval fun v => if v.2 = 0 then MvPowerSeries.Restricted.X K 1 v.1 else 1

variable (K ι) in
/-- **The polynomials of degree at most `n_i` in each `z_i`**: the span of the monomials `z^m`,
`m ≤ n`, in the Tate algebra. Source: roadmap §1.3.2–§1.3.3 ("exactly the subspace spanned by the
monomials `z^m`, `m ≤ n`"). -/
noncomputable def polySubmodule : Submodule K (Restricted K (1 : ι → ℝ)) :=
  Submodule.span K (Set.range fun m : {m : ι →₀ ℕ // ∀ i, m i ≤ n i} => monomial 1 m.1 1)

omit [DecidableEq ι] in
/-- The dehomogenisation of a monomial. -/
theorem toTate_monomial (d : ι × Fin 2 →₀ ℕ) (a : K) :
    toTate K ι (MvPolynomial.monomial d a) =
      monomial 1 (Finsupp.equivFunOnFinite.symm fun i => d (i, 0)) a := by
  rw [toTate, MvPolynomial.aeval_monomial, monomial_eq_C_mul_prod, algebraMap_apply,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Fintype.prod_prod_type]
  simp

/-- The image of `L_n` under dehomogenisation is `polySubmodule n`. -/
theorem map_symPow_toTate : (SymPow K ι n).map (toTate K ι).toLinearMap = polySubmodule K ι n := by
  rw [SymPow, weightedHomogeneousSubmodule_eq_finsupp_supported,
    AddMonoidAlgebra.supported_eq_span_single, Submodule.map_span, polySubmodule, ← Set.image_comp]
  congr 1
  ext f
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, Function.comp_apply,
    AlgHom.toLinearMap_apply, single_eq_monomial, toTate_monomial]
  constructor
  · rintro ⟨d, hd, rfl⟩
    refine ⟨⟨Finsupp.equivFunOnFinite.symm fun i => d (i, 0), fun i => ?_⟩, rfl⟩
    have h := congrFun hd i
    rw [weight_symWeight_apply] at h
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    omega
  · rintro ⟨⟨m, hm⟩, rfl⟩
    let m' : (i : ι) → Fin (n i + 1) := fun i => ⟨m i, Nat.lt_succ_of_le (hm i)⟩
    let d := (symPowSupportEquiv n).symm m'
    refine ⟨d.1, d.2, ?_⟩
    congr 1
    ext i
    exact congrArg Fin.val (congrFun ((symPowSupportEquiv n).apply_symm_apply m') i)

/-- Dehomogenisation is injective on `L_n`. -/
theorem toTate_injOn : Set.InjOn (toTate K ι) (SymPow K ι n) := by
  classical
  intro P hP Q hQ hPQ
  rw [← sub_eq_zero]
  have hR : P - Q ∈ SymPow K ι n := sub_mem hP hQ
  have h0 : toTate K ι (P - Q) = 0 := by rw [map_sub, hPQ, sub_self]
  generalize P - Q = R at hR h0
  ext d
  rw [MvPolynomial.coeff_zero]
  by_contra hd
  have hwd : Finsupp.weight (symWeight ι) d = n := hR hd
  -- the coefficient of `toTate R` at `(d(i, 0))_i` is the coefficient of `R` at `d`
  have hcoeff := congrArg (fun f : Restricted K (1 : ι → ℝ) =>
    MvPowerSeries.coeff (Finsupp.equivFunOnFinite.symm fun i => d (i, 0)) f.1) h0
  simp only [val_zero, map_zero] at hcoeff
  conv_lhs at hcoeff => rw [R.as_sum, map_sum]
  simp only [toTate_monomial, val_sum, val_monomial, map_sum, MvPowerSeries.coeff_monomial]
    at hcoeff
  rw [Finset.sum_eq_single d (fun e he hed => if_neg fun hde => hed ?_) (fun hd' => absurd
    (MvPolynomial.mem_support_iff.mpr hd) hd'), if_pos rfl] at hcoeff
  · exact hd hcoeff
  · have hwe : Finsupp.weight (symWeight ι) e = n := hR (MvPolynomial.mem_support_iff.mp he)
    have h0' : ∀ i, d (i, 0) = e (i, 0) := fun i => by
      simpa using congrArg (fun m : ι →₀ ℕ => m i) hde
    ext ⟨i, k⟩
    have hdi := congrFun hwd i
    have hei := congrFun hwe i
    rw [weight_symWeight_apply] at hdi hei
    have := h0' i
    fin_cases k
    · exact this.symm
    · show e (i, 1) = d (i, 1)
      omega

/-- **`L_n ≃ polySubmodule n`**. Source: roadmap §1.3.2–§1.3.3. -/
noncomputable def toTateEquiv : SymPow K ι n ≃ₗ[K] polySubmodule K ι n :=
  (LinearEquiv.ofInjective ((toTate K ι).toLinearMap.domRestrict (SymPow K ι n))
    fun P Q h => Subtype.ext (toTate_injOn n P.2 Q.2 h)).trans
    (LinearEquiv.ofEq _ _ ((LinearMap.range_domRestrict _ _).trans (map_symPow_toTate n)))

theorem coe_toTateEquiv_apply (P : SymPow K ι n) :
    (toTateEquiv n P : Restricted K (1 : ι → ℝ)) = toTate K ι P :=
  rfl

theorem finrank_polySubmodule : Module.finrank K (polySubmodule K ι n) = ∏ i, (n i + 1) :=
  (toTateEquiv n).finrank_eq.symm.trans (finrank_symPow n)

omit [IsUltrametricDist K] [CompleteSpace K] in
/-- **The scaling identity of multi-homogeneous polynomials**: for `P ∈ L_n`,
`P(λ_i X_i, λ_i Y_i) = ∏ λ_i^{n_i} P(X, Y)`, in any commutative `K`-algebra. -/
theorem aeval_mul_of_mem_symPow {B : Type*} [CommRing B] [Algebra K B]
    {P : MvPolynomial (ι × Fin 2) K} (hP : P ∈ SymPow K ι n) (lam : ι → B) (g : ι × Fin 2 → B) :
    MvPolynomial.aeval (fun v => lam v.1 * g v) P =
      (∏ i, lam i ^ n i) * MvPolynomial.aeval g P := by
  rw [mem_symPow_iff] at hP
  induction hP using IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq => rw [map_add, map_add, ihp, ihq, mul_add]
  | monomial d r hr =>
    rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial,
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
      Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    simp_rw [mul_pow, Finset.prod_mul_distrib]
    have hlam : ∏ v : ι × Fin 2, lam v.1 ^ d v = ∏ i, lam i ^ n i := by
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Fin.prod_univ_two, ← pow_add, ← weight_symWeight_apply, hr]
    rw [hlam]
    ring

section Bridge

variable {L : Type*} [NormedField L] [IsUltrametricDist L] (e : Embeddings L K ι)
  {S : Submonoid (Matrix (Fin 2) (Fin 2) L)} {ρ : ℝ}

/-- **The bridge**: for `γ` in the level, dehomogenisation intertwines the action on `L_n` with the
weight action of the algebraic weight `algWeight (n, 1)`:
`∏ (c_i z_i + d_i)^{n_i} P(w_γ(z), 1) = P(a z + b, c z + d)`. Source: roadmap §1.3.3; [Buz07, §11,
p. 73] ("an `M_1`-equivariant inclusion"). -/
theorem toTate_symAct [CharZero K] (hb : LevelBounds S ρ) (γ : S) {P : MvPolynomial (ι × Fin 2) K}
    (hP : P ∈ SymPow K ι n) :
    toTate K ι (symAct (e.toMulti γ) P) =
      (e.algWeight hb (fun i => (n i : ℤ)) 1 (by simp)).kappaSlash γ (toTate K ι P) := by
  have hM : MultiBounds ρ (e.toMulti γ) := e.multiBounds_toMulti hb γ.2
  -- the Möbius point, homogenised: `X_i ↦ w_i`, `Y_i ↦ 1`
  let g : ι × Fin 2 → Restricted K (1 : ι → ℝ) :=
    fun v => if v.2 = 0 then mobius (e.toMulti γ) v.1 else 1
  have hR : mobiusSubst hM (toTate K ι P) = MvPolynomial.aeval g P := by
    rw [toTate, MvPolynomial.comp_aeval_apply]
    refine congrArg (fun F => MvPolynomial.aeval F P) (funext fun v => ?_)
    show mobiusSubst hM (if v.2 = 0 then X K 1 v.1 else 1) =
      if v.2 = 0 then mobius (e.toMulti γ) v.1 else 1
    split_ifs
    · exact mobiusSubst_X hM v.1
    · exact map_one _
  have hL : toTate K ι (symAct (e.toMulti γ) P) =
      MvPolynomial.aeval (fun v => lin (e.toMulti γ) v.1 * g v) P := by
    rw [symAct, MvPolynomial.comp_aeval_apply]
    refine congrArg (fun F => MvPolynomial.aeval F P) (funext fun v => ?_)
    obtain ⟨i, j⟩ := v
    fin_cases j
    · show toTate K ι (symVars (e.toMulti γ) (i, 0)) =
        lin (e.toMulti γ) i * mobius (e.toMulti γ) i
      rw [mobius, mul_left_comm, lin_mul_linInv hM i, mul_one]
      simp [toTate, symVars, Fin.sum_univ_two, num, algebraMap_apply, add_comm]
    · show toTate K ι (symVars (e.toMulti γ) (i, 1)) = lin (e.toMulti γ) i * 1
      rw [mul_one]
      simp [toTate, symVars, Fin.sum_univ_two, lin, algebraMap_apply, add_comm]
  have hA : (e.algWeight hb (fun i => (n i : ℤ)) 1 (by simp)).autFactor γ =
      ∏ i, lin (e.toMulti γ) i ^ n i := by
    have h1 : ((e.algWeight hb (fun i => (n i : ℤ)) 1 (by simp)).detChar γ : K) = 1 := rfl
    rw [AnalyticWeight.autFactor, h1, one_smul]
    exact (e.algCol_natCast n _ _).trans (Finset.prod_congr rfl fun i _ => rfl)
  rw [AnalyticWeight.kappaSlash_apply, hA, hL, aeval_mul_of_mem_symPow n hP]
  exact congrArg _ hR.symm

/-- The bridge for `L_{n,v}`: with the determinant twist on both sides. -/
theorem toTate_classicalAction [CharZero K] (hb : LevelBounds S ρ) (v : Lˣ →* Kˣ)
    (hv : ∀ x, ‖(v x : K)‖ = 1) (γ : S) (P : SymPow K ι n) :
    letI := classicalAction n e v
    toTate K ι (MulOpposite.op (hb.toGL γ) • P : SymPow K ι n) =
      (e.algWeight hb (fun i => (n i : ℤ)) v hv).kappaSlash γ (toTate K ι P) := by
  show toTate K ι ((v (Matrix.GeneralLinearGroup.det (hb.toGL γ)) : K) •
    symAct (e.toMulti (hb.toGL γ : Matrix (Fin 2) (Fin 2) L)) (P : MvPolynomial (ι × Fin 2) K)) = _
  rw [map_smul, LevelBounds.coe_toGL, toTate_symAct n e hb γ P.2,
    AnalyticWeight.kappaSlash_apply, AnalyticWeight.kappaSlash_apply, AnalyticWeight.autFactor,
    AnalyticWeight.autFactor, smul_mul_assoc, smul_mul_assoc]
  show (v (Matrix.GeneralLinearGroup.det (hb.toGL γ)) : K) • ((1 : K) • _) = _
  have hdet : Matrix.GeneralLinearGroup.det (hb.toGL γ) = hb.detUnits γ := Units.ext rfl
  rw [one_smul, hdet]
  rfl

/-- `L_n ⊆ A` is stable under the weight action of the algebraic weights. Source: roadmap §1.3.3
("hence `L_n` is a `Σ`-stable finite-dimensional subspace of `A`"). -/
theorem polySubmodule_stable [CharZero K] (hb : LevelBounds S ρ) (v : Lˣ →* Kˣ)
    (hv : ∀ x, ‖(v x : K)‖ = 1) (γ : S) {f : Restricted K (1 : ι → ℝ)}
    (hf : f ∈ polySubmodule K ι n) :
    (e.algWeight hb (fun i => (n i : ℤ)) v hv).kappaSlash γ f ∈ polySubmodule K ι n := by
  rw [← map_symPow_toTate] at hf ⊢
  obtain ⟨P, hP, rfl⟩ := Submodule.mem_map.mp hf
  letI := classicalAction n e v
  exact Submodule.mem_map.mpr ⟨_, (MulOpposite.op (hb.toGL γ) • (⟨P, hP⟩ : SymPow K ι n)).2,
    toTate_classicalAction n e hb v hv γ ⟨P, hP⟩⟩

end Bridge

end AutomorphicForm
