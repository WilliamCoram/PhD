/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.QMF.Sigma0
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Classical weight modules `L_{n,ν}`

Buzzard's classical coefficient module [*Eigenvarieties*, §9 p. 68]:

> "If `n ∈ ℤ^I_{≥0}` then we define `Lₙ` to be the `K`-vector space with basis the
> monomials `∏ᵢ Zᵢ^{mᵢ}`, `0 ≤ mᵢ ≤ nᵢ` … define the right `M₁`-module `L_{n,v}` to be
> the `K`-vector space `Lₙ` equipped with the action of `M₁` defined by letting
> `(γⱼ) = ((aⱼ bⱼ; cⱼ dⱼ))ⱼ` send `∏ᵢ Zᵢ^{mᵢ}` to
> `∏ᵢ (cᵢZᵢ + dᵢ)^{nᵢ} (aᵢdᵢ − bᵢcᵢ)^{vᵢ} ((aᵢZᵢ + bᵢ)/(cᵢZᵢ + dᵢ))^{mᵢ}`."

We formalise the one-place case in the projective (two-variable homogeneous) model:
`WeightModule R n ν` is the space of homogeneous polynomials of degree `n` in two
variables over `R`, with `g ∈ Σ₀(γ)` acting on the left by the transposed linear
substitution `(X, Y) ↦ (aX + cY, bX + dY)` twisted by a character `ν` of `Σ₀(γ)`
(Buzzard's determinant twist `det^v` is `ν = detChar v`).  The single-variable
picture is recovered by `Z = X/Y`; the substitution action is polynomial, so —
as Buzzard remarks — it needs no integrality and extends to all of `M₂(K)`.

## The character `ν`, and where the general weights live

A weight here is a *pair* `(n, ν)`: the degree `n` governs the `Symⁿ` substitution
part, and `ν : Σ₀(γ) →* Rˣ` is a **character** of the monoid `Σ₀(γ)` — a
multiplicative scalar twist, so that `WeightModule R n ν = Symⁿ ⊗ ν` as a
`Σ₀(γ)`-module.  Any abstract character is allowed (no continuity is needed to twist
a finite-dimensional module); the classical weights are `ν = detChar w`.

The genuinely *p-adic* weights — Jacobs's locally analytic characters
`κ : ℤ_p^× → 𝒪_p^×` [Def 1.27] — are **not** a larger class of `ν`'s: local
analyticity is invisible on this polynomial module.  Its content is to deform the
degree `n` itself, replacing `Symⁿ` by the Tate-algebra model of locally analytic
functions, on which the action evaluates the expansion of `κ(cz + d)`.  That
generalisation lives in `PhD/QMF/Weight/` (`WeightSeries`, `kappaSlash`); this
module embeds into it via `QMF.polyEmbed` (`Weight/Algebraic.lean`), with `ν`
reappearing there as the scalar twist `RightSlashAction.twist` at `detTwist ν`.
-/

open MvPolynomial

section MatrixSubst

variable {K : Type*} [Field K] {R : Type*} [CommRing R] [Algebra K R]

/-- Left substitution action of a `2×2` matrix on two-variable polynomials:
`g • P = P(aX + cY, bX + dY)` (substitution by the transpose, which makes this a
*left* monoid action: `matrixSubst (g*h) = matrixSubst g ∘ matrixSubst h`). -/
noncomputable def matrixSubst (g : Matrix (Fin 2) (Fin 2) K) :
    MvPolynomial (Fin 2) R →ₐ[R] MvPolynomial (Fin 2) R :=
  aeval fun i => ∑ j, algebraMap K R (g j i) • (X j : MvPolynomial (Fin 2) R)

@[simp]
lemma matrixSubst_X (g : Matrix (Fin 2) (Fin 2) K) (i : Fin 2) :
    matrixSubst (R := R) g (X i) = ∑ j, algebraMap K R (g j i) • X j := by
  simp [matrixSubst]

lemma matrixSubst_one : matrixSubst (R := R) (1 : Matrix (Fin 2) (Fin 2) K) = AlgHom.id R _ := by
  refine MvPolynomial.algHom_ext fun i => ?_
  fin_cases i <;> simp [Matrix.one_apply]

/-- Transposed substitution is a left action: `(gh) • P = g • (h • P)`. -/
lemma matrixSubst_mul (g h : Matrix (Fin 2) (Fin 2) K) :
    matrixSubst (R := R) (g * h) = (matrixSubst (R := R) g).comp (matrixSubst h) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp only [AlgHom.coe_comp, Function.comp_apply, matrixSubst_X, map_sum, map_smul,
    Matrix.mul_apply, map_mul, Finset.sum_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by rw [mul_comm]

/-- Linear substitution preserves homogeneity of degree `n`. -/
lemma matrixSubst_mem_homogeneousSubmodule (g : Matrix (Fin 2) (Fin 2) K) {n : ℕ}
    {P : MvPolynomial (Fin 2) R} (hP : P ∈ homogeneousSubmodule (Fin 2) R n) :
    matrixSubst g P ∈ homogeneousSubmodule (Fin 2) R n := by
  rw [mem_homogeneousSubmodule] at hP ⊢
  have h1 : ∀ i, (∑ j, algebraMap K R (g j i) • (X j : MvPolynomial (Fin 2) R)).IsHomogeneous 1 := by
    intro i
    apply IsHomogeneous.sum
    intro j _
    rw [smul_eq_C_mul]
    exact (isHomogeneous_X R j).C_mul _
  simpa [matrixSubst] using hP.aeval _ h1

end MatrixSubst

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  [Valued K Γ₀] {γ : Γ₀} {hγ : γ < 1}
variable (R : Type*) [CommRing R] [Algebra K R]

variable (γ hγ) in
/-- Buzzard's determinant character `det^v` as a character of `Σ₀(γ)` valued in `Rˣ`. -/
noncomputable def Sigma0.detChar (w : ℤ) : Sigma0 K γ hγ →* Rˣ :=
  ((Units.map (algebraMap K R).toMonoidHom).comp (zpowGroupHom w)).comp (Sigma0.detUnits γ hγ)

/-- The weight-`(n, ν)` coefficient module: homogeneous polynomials of degree `n` in two
variables over `R`, as a left `Σ₀(γ)`-module via transposed substitution twisted by `ν`.
One-place, left-handed version of Buzzard's `L_{n,v}` [*Eigenvarieties*, §9 p. 68];
`ν = Sigma0.detChar γ hγ w` recovers Buzzard's `(n, v) = (n, w)`, and classical weight
`(k, w)` corresponds to `(n, v) = (k − 2, w − n − 1)` [ibid., §9 p. 70].

Here `ν` is an arbitrary *character* of the monoid `Σ₀(γ)` — a monoid homomorphism
into `Rˣ`, acting as the one-dimensional scalar twist in `g • P = ν g • P∘g`; as a
module this is `Symⁿ ⊗ ν`.  For the p-adic weights that deform `n` itself (locally
analytic κ, [Jacobs, Def 1.27]) see `PhD/QMF/Weight/` and the module docstring above.
(`ν` is a phantom parameter of the type; it enters through the action instances.) -/
@[nolint unusedArguments]
def WeightModule (n : ℕ) (_ν : Sigma0 K γ hγ →* Rˣ) : Type _ :=
  homogeneousSubmodule (Fin 2) R n

variable (n : ℕ) (ν : Sigma0 K γ hγ →* Rˣ)

namespace WeightModule

noncomputable instance : AddCommGroup (WeightModule R n ν) :=
  inferInstanceAs (AddCommGroup (homogeneousSubmodule (Fin 2) R n))

noncomputable instance : Module R (WeightModule R n ν) :=
  inferInstanceAs (Module R (homogeneousSubmodule (Fin 2) R n))

/-- The weight action: `g • P = ν(g) • P((aX + cY, bX + dY))`. -/
noncomputable instance : SMul (Sigma0 K γ hγ) (WeightModule R n ν) :=
  ⟨fun g P => ⟨ν g • matrixSubst g.1 P.1,
    by rw [Units.smul_def]; exact Submodule.smul_mem _ _ (matrixSubst_mem_homogeneousSubmodule _ P.2)⟩⟩

@[simp]
lemma smul_coe (g : Sigma0 K γ hγ) (P : WeightModule R n ν) :
    (g • P).1 = ν g • matrixSubst g.1 P.1 := rfl

omit [Algebra K R] in
@[simp] lemma coe_zero : (0 : WeightModule R n ν).1 = 0 := rfl

omit [Algebra K R] in
@[simp] lemma coe_add (P Q : WeightModule R n ν) : (P + Q).1 = P.1 + Q.1 := rfl

omit [Algebra K R] in
@[simp] lemma coe_rsmul (r : R) (P : WeightModule R n ν) : (r • P).1 = r • P.1 := rfl

noncomputable instance : DistribMulAction (Sigma0 K γ hγ) (WeightModule R n ν) where
  one_smul P := Subtype.ext (by simp [matrixSubst_one])
  mul_smul g h P := Subtype.ext (by
    simp [matrixSubst_mul, Units.smul_def, map_smul, mul_smul])
  smul_zero g := Subtype.ext (by simp)
  smul_add g P Q := Subtype.ext (by simp)

instance : SMulCommClass (Sigma0 K γ hγ) R (WeightModule R n ν) where
  smul_comm g r P := Subtype.ext (by
    simp [Units.smul_def, map_smul, smul_smul, mul_comm])

end WeightModule
