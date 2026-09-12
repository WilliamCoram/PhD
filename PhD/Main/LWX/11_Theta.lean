/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.LWX.«10_DiscForms»
import PhD.Main.TateFredholm.«08_BlockMap»

/-!
# The theta operator on the disc model, and the classical subspace — SKELETON

[Bu04, §7] defines, for a classical weight `κ = (k, ε_p)`, the map
`θ^{1−k} : S^D_κ(U,1) → S^D_{κ'}(U,1)`, `κ' = (2−k, ε_p)`, by
`(θ^{1−k} f)(g) = (|ν(g)| det g_p)^{1−k} · d^{k−1}f(g)/dz^{k−1}`; [LWX, §3.23 Step III] writes the
same map as `(d/dz)^{k+1}` in its own weight indexing.  This file builds the derivative half on the
disc model of `PhD/Main/LWX/09_DiscModel.lean`, where it is completely explicit.

**Why the disc model makes this easy.**  A disc-model element of `c(ZMod (p^h) × ℕ, K)` *is* the
family of Taylor coefficients of a function on each disc `a + pʰℤ_p`, in the coordinate
`z = a + pʰ w`.  Differentiating `r` times in `w` sends the coefficient array
`(a, j) ↦ c (a, j)` to `(a, j) ↦ (j+1)(j+2)⋯(j+r) · c (a, j+r)` — a shift composed with a
diagonal of *integers*, so it is bounded by `1` and column-finite, hence a continuous linear map
built by `TateFredholm.ofCoeffs` exactly as `diagFactorialH` is, and block-diagonal
over the discs.  The `p^{−hr}` relating `d/dw` to
`d/dz` is a scalar and is carried explicitly at the call site rather than baked in.

**The classical subspace** is then transparent: `ker (thetaDisc h (k+1))` is exactly the elements
supported in Taylor degrees `≤ k`, i.e. the locally polynomial functions of degree `≤ k`.  That is
[Bu04, Prop 4]'s first sentence, and the dimension count `t · (k+1) · p^h` is [LWX, (3.21.1)].

## Main declarations

* `LWX.thetaOne`, `LWX.thetaDisc` — `θ^r` on one disc and on the disc model.
* `LWX.thetaDisc_apply` — the coefficient formula.
* `LWX.IsLocPolyDeg`, `LWX.locPolyDegSubmodule` — locally polynomial of degree `≤ k`.
* `LWX.thetaDisc_eq_zero_iff` — `ker θ^{k+1}` = degree `≤ k` ([Bu04, Prop 4], first sentence).
* `LWX.finrank_locPolyDegSubmodule` — `(k+1)·p^h`, the local half of [LWX, (3.21.1)].

**The weight equivariance is *not* here.**  A first draft stated it for a pair of weights sharing
an arbitrary finite part `ν : UK →* Kˣ`, which is false: `ν(cz + d)` need not be constant in `z`,
so differentiating leaves a term the other side cannot match ([Bu04, §7]'s displayed identity
carries no nebentypus factor at all).  Those three statements were removed on 2026-09-09; the
correct ones — together with Bol's identity `LWX.bol`, which is what they rest on — are
`LWX.thetaOne_comp_kappaSlash_of_autFactor`, `LWX.thetaDisc_comp_discSlash_of_autFactor` and
`LWX.thetaDisc_comp_discHeckeBlock_of_autFactor` in `PhD/Main/LWX/12_Bol.lean`, all sorry-free.  The
counterexample is recorded in `.mathlib-quality/lwx-theta/b2_log.jsonl`.

See `.mathlib-quality/lwx-stepone/JL-AUDIT.md`: nothing in this file depends on
Jacquet–Langlands.  [Bu04, Prop 4]'s *first* sentence and its small-slope half are
Jacquet–Langlands-free; only its converse half uses it, and we never import that (we derive the
converse from hypothesis H1 instead — see `PhD/Main/LWX/Classicality.lean`).
-/

open AbstractHeckeOperatorSlash RightSlashAction TateFredholm QMF QMF.Weight

open scoped Pointwise QMF TateFredholm

noncomputable section

namespace LWX

variable {p : ℕ} [hp : Fact p.Prime]
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [CharZero K]

/-! ### The operator -/

variable (K) in
/-- **`θ^r` on one disc**: the `r`-th derivative in the disc coordinate, read on Taylor
coefficients as `(θ^r c) j = (j+1)(j+2)⋯(j+r) · c (j+r)` — a shift composed with an integer
diagonal, hence bounded by `1` and column-finite. -/
def thetaOne (r : ℕ) : c(ℕ, K) →L[K] c(ℕ, K) :=
  ofCoeffs (fun j i => if i = j + r then ((Nat.descFactorial (j + r) r : ℕ) : K) else 0)
    ⟨1, fun j i => by
      split_ifs
      · exact IsUltrametricDist.norm_natCast_le_one K _
      · simp⟩
    (fun i => by
      refine tendsto_const_nhds.congr' ?_
      rw [Filter.EventuallyEq, Filter.eventually_cofinite]
      refine (Set.finite_singleton (i - r)).subset fun j hj => ?_
      rw [Set.mem_singleton_iff]
      by_contra hcon
      exact hj (by simp [show i ≠ j + r by omega]))

omit [CharZero K] in
theorem matrixCoeff_thetaOne (r j i : ℕ) :
    matrixCoeff (thetaOne K r) j i
      = if i = j + r then ((Nat.descFactorial (j + r) r : ℕ) : K) else 0 :=
  matrixCoeff_ofCoeffs _ _ _ j i

variable (p K) in
/-- **`θ^r` on the disc model.**  Block-diagonal with the same single-disc `θ^r` in every block:
differentiation does not mix discs.  The scalar `p^{−hr}` converting `d/dw` to `d/dz` is not
included; carry it at the call site. -/
def thetaDisc (h r : ℕ) : c(ZMod (p ^ h) × ℕ, K) →L[K] c(ZMod (p ^ h) × ℕ, K) :=
  blockMap (σ := ZMod (p ^ h)) (thetaOne K r)

omit hp [CharZero K] in
/-- A block-diagonal operator acts on each block separately.  (Stated here rather than in
`PhD/Main/TateFredholm/08_BlockMap.lean` to avoid a rebuild of the whole `TateFredholm` tree; moving it
there is a `/cleanup` decision.) -/
theorem blockMap_apply_prod {σ : Type*} [Fintype σ] [DecidableEq σ]
    {I I' : Type*} (f : c(I, K) →L[K] c(I', K))
    (x : c(σ × I, K)) (a : σ) (j : I') :
    blockMap (σ := σ) f x (a, j) = f (cSpace.blockProj a x) j := by
  rw [blockMap, blockOpMap, _root_.sum_apply, cSpace.sum_apply,
    Finset.sum_eq_single a (fun b _ hb => by simp [cSpace.sum_apply, Ne.symm hb]) (by simp),
    _root_.sum_apply, cSpace.sum_apply,
    Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]; rfl) (by simp)]
  simp

omit [CharZero K] in
/-- The coefficient formula for `θ^r`. -/
theorem thetaDisc_apply (h r : ℕ) (c : c(ZMod (p ^ h) × ℕ, K)) (a : ZMod (p ^ h)) (j : ℕ) :
    thetaDisc p K h r c (a, j) = ((Nat.descFactorial (j + r) r : ℕ) : K) * c (a, j + r) := by
  rw [thetaDisc, blockMap_apply_prod, thetaOne, ofCoeffs_apply,
    tsum_eq_single (j + r) (fun i hi => by simp [hi])]
  simp

omit [CharZero K] in
@[simp]
theorem thetaDisc_zero (h : ℕ) : thetaDisc p K h 0 = ContinuousLinearMap.id K _ := by
  refine ContinuousLinearMap.ext fun f => DFunLike.ext _ _ fun x => ?_
  obtain ⟨a, j⟩ := x
  rw [thetaDisc_apply]
  simp

/-! ### The classical subspace: locally polynomial of degree `≤ k` -/

variable (p K) in
/-- **Locally polynomial of degree `≤ k`**: the Taylor coefficients vanish above degree `k` on
every disc.  This is [Bu04, §7]'s "the space of polynomials of degree at most `k − 2`" in
Buzzard's weight indexing, i.e. the classical subspace. -/
def IsLocPolyDeg (h k : ℕ) (c : c(ZMod (p ^ h) × ℕ, K)) : Prop :=
  ∀ a : ZMod (p ^ h), ∀ j : ℕ, k < j → c (a, j) = 0

variable (p K) in
/-- The locally-polynomial-of-degree-`≤ k` elements, as a submodule. -/
def locPolyDegSubmodule (h k : ℕ) : Submodule K c(ZMod (p ^ h) × ℕ, K) where
  carrier := {c | IsLocPolyDeg p K h k c}
  add_mem' := by
    intro x y hx hy a j hj
    have hadd : (x + y) (a, j) = x (a, j) + y (a, j) := rfl
    rw [hadd, hx a j hj, hy a j hj, add_zero]
  zero_mem' := by
    intro _ _ _
    rfl
  smul_mem' := by
    intro r x hx a j hj
    have hsmul : (r • x) (a, j) = r * x (a, j) := rfl
    rw [hsmul, hx a j hj, mul_zero]

omit hp [IsUltrametricDist K] [CompleteSpace K] [CharZero K] in
theorem mem_locPolyDegSubmodule_iff (h k : ℕ) (c : c(ZMod (p ^ h) × ℕ, K)) :
    c ∈ locPolyDegSubmodule p K h k ↔ IsLocPolyDeg p K h k c := Iff.rfl

/-- **[Bu04, Prop 4], first sentence.**  The kernel of `θ^{k+1}` is exactly the locally polynomial
functions of degree `≤ k` — the classical subspace. -/
theorem thetaDisc_eq_zero_iff (h k : ℕ) (c : c(ZMod (p ^ h) × ℕ, K)) :
    thetaDisc p K h (k + 1) c = 0 ↔ IsLocPolyDeg p K h k c := by
  have hne : ∀ j : ℕ, ((Nat.descFactorial (j + (k + 1)) (k + 1) : ℕ) : K) ≠ 0 := fun j =>
    Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr (Nat.le_add_left _ _)).ne'
  constructor
  · intro hzero a j hj
    have happ := congrArg (fun f : c(ZMod (p ^ h) × ℕ, K) => f (a, j - (k + 1))) hzero
    simp only [thetaDisc_apply] at happ
    have hj' : j - (k + 1) + (k + 1) = j := by omega
    rw [hj'] at happ
    exact (mul_eq_zero.mp happ).resolve_left (by rw [← hj']; exact hne _)
  · intro hpoly
    refine DFunLike.ext _ _ fun x => ?_
    obtain ⟨a, j⟩ := x
    rw [thetaDisc_apply, hpoly a (j + (k + 1)) (by omega), mul_zero]
    rfl

omit hp [CharZero K] in
/-- On the index `ZMod (p^h) × Fin (k+1)`, forgetting the `Fin` bound is injective. -/
private theorem prod_val_inj {h k : ℕ} {x y : ZMod (p ^ h) × Fin (k + 1)}
    (hxy : ((x.1, (x.2 : ℕ)) : ZMod (p ^ h) × ℕ) = (y.1, (y.2 : ℕ))) : x = y := by
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp only [Prod.mk.injEq] at hxy ⊢
  exact ⟨hxy.1, Fin.ext hxy.2⟩

/-- The classical subspace of one disc model is `(ZMod (p^h) × Fin (k+1))`-many coordinates: a
function supported in Taylor degrees `≤ k` is exactly its values there, and every such family
occurs (extend by zero — a finite sum of `cSpace.single`s). -/
private def locPolyDegEquiv (h k : ℕ) :
    locPolyDegSubmodule p K h k ≃ₗ[K] (ZMod (p ^ h) × Fin (k + 1) → K) where
  toFun f x := (f : c(ZMod (p ^ h) × ℕ, K)) (x.1, (x.2 : ℕ))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun g :=
    ⟨∑ x : ZMod (p ^ h) × Fin (k + 1), cSpace.single (x.1, (x.2 : ℕ)) (g x), by
      intro a j hj
      rw [cSpace.sum_apply]
      refine Finset.sum_eq_zero fun x _ => cSpace.single_apply_of_ne (fun hcon => ?_) _
      exact absurd (congrArg Prod.snd hcon) (by omega)⟩
  left_inv f := by
    refine Subtype.ext (DFunLike.ext _ _ fun y => ?_)
    obtain ⟨a, j⟩ := y
    rw [cSpace.sum_apply]
    by_cases hj : j < k + 1
    · rw [Finset.sum_eq_single (a, (⟨j, hj⟩ : Fin (k + 1))) ?_ (by simp)]
      · exact cSpace.single_apply_self _ _
      · exact fun x _ hx => cSpace.single_apply_of_ne (fun hcon => hx (prod_val_inj hcon.symm)) _
    · rw [Finset.sum_eq_zero fun x _ =>
        cSpace.single_apply_of_ne (fun hcon => absurd (congrArg Prod.snd hcon) (by omega)) _]
      exact (f.2 a j (by omega)).symm
  right_inv g := by
    refine funext fun x => ?_
    show (∑ y : ZMod (p ^ h) × Fin (k + 1), cSpace.single (y.1, (y.2 : ℕ)) (g y))
      (x.1, (x.2 : ℕ)) = g x
    rw [cSpace.sum_apply, Finset.sum_eq_single x ?_ (by simp)]
    · exact cSpace.single_apply_self _ _
    · exact fun y _ hy => cSpace.single_apply_of_ne (fun hcon => hy (prod_val_inj hcon.symm)) _

omit [CharZero K] in
/-- The local half of **[LWX, (3.21.1)]**: the degree-`≤ k` subspace of one disc model has
dimension `(k+1)·p^h`.  Multiplying by the class number `t` gives `(k+1)q⁻¹pᵐt`. -/
theorem finrank_locPolyDegSubmodule (h k : ℕ) :
    Module.finrank K (locPolyDegSubmodule p K h k) = (k + 1) * p ^ h := by
  rw [(locPolyDegEquiv (p := p) (K := K) h k).finrank_eq, Module.finrank_pi,
    Fintype.card_prod, ZMod.card, Fintype.card_fin, mul_comm]

end LWX
