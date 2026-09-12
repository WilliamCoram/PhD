/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import PhD.Main.QMF.Weight.«04_Char»
import PhD.Main.QMF.Slash.«03_AutomorphicFunction»
import PhD.Main.QMF.Slash.«03_HeckeMonoid»

/-!
# Overconvergent automorphic forms at an abstract weight (Jacobs, Def 1.28–1.32)

[Jacobs, Ch. 1 §1.5 Definitions 1.28 and 1.30]:

> "Let α belong to ℕ and suppose that U is an open compact subgroup of D×_f.  We say
> that U has wild level ≥ p^α if the projection U → D×_p, i.e. U_p, is contained in Σ_α."
>
> "Fix α ∈ ℕ and κ as in Definition 1.27.  Let U be an open, compact subgroup of D×_f
> of wild level ≥ p^α.  Let A be **any right Σ_α-module**.  The level U, weight κ space
> of automorphic forms is the space L(U, A) = {φ : D×_f → A : φ(dgu) = φ(g)‖_κ u_p}."

The existing right-slash layer (`levelSubmoduleSlash`, `heckeOperatorSlash`) already
implements `L(U, A)` for **any** coefficient right-module — Def 1.30's phrase "any
right Σ_α-module" is the existing design.  This file instantiates it at the Tate
algebra with the abstract weight-`κ` action of `PhD/Main/QMF/Weight/03_SlashAction.lean`.

The wild-level mechanism is abstracted exactly as in Def 1.28: a group `G` (the adelic
units) with a monoid homomorphism `θ : G →* M₂(K)` (the `p`-component / `toMatrix`),
and the level condition `θ(U) ⊆ S`.  The quaternionic instantiation
(`G = Dfx F D`, `θ = toMatrix F D v`) is `QMF.levelMonoid'`-shaped and happens
downstream (at `K₃` in `PhD/Main/JacobsSlash/U3/5_KappaWeight.lean`; at a general
completion once its normed-field instances are in scope).

## Design note: the wild level belongs to the weight

`Forms` takes a weight `κ : AnalyticWeight UK S ρ` — a character *together with* the
wild level `(S, ρ)` at which it is analytic — and a level `U` with `θ(U) ⊆ S`.  One
might expect the wild level to be a property of `U` alone.  It is not, for three
reasons, and this is exactly the structure of the sources ("κ a `t`-analytic weight,
`U` of wild level `≥ p^t`" — Buzzard; "fix `α` and `κ` as in Def 1.27, `U` of wild
level `≥ p^α`" — Jacobs):

1. **Analyticity is a joint condition on `κ` and `α`.**  The action of `(a b; c d)`
   evaluates `κ` at `c·z + d`, `‖z‖ ≤ 1`, i.e. on the disc of radius `‖c‖ ≤ ρ` about
   the unit `d`.  The expansion `κ(c·z + d) = ∑ aₘ zᵐ` with `‖aₘ‖ ≤ ρᵐ` — the datum the
   action and its compactness estimates consume — exists iff `κ` is analytic on that
   disc.  So "κ is `α`-analytic" is the *only* place local analyticity has content, and
   it references `α`.  In Lean the character has no analyticity of its own (over a
   general `K` there is no "continuous ⇒ locally analytic"; that is special to `ℤ_p^×`),
   so the expansion data *is* the analyticity, and it is radius-indexed.
2. **The weight-`κ` module is level-indexed.**  Def 1.27's `A_κ` is a right
   `Σ_α`-module; `Forms` is `L(U, A_κ)`, which needs `U_p ⊆ Σ_α` acting through it.
   Both `κ` and `U` must therefore reference the same `Σ_α`; `AnalyticWeight UK S ρ`
   *is* the `Σ_S`-module structure on the Tate algebra, and `hU` is `U_p ⊆ Σ_S`.
3. **`α` is genuinely free above the analyticity radius, and there is no canonical
   `S` for a `κ`.**  Hecke operators, `U_p`, and classicality all move between levels;
   Jacobs's own weight acts through `Σ₁(3)` and `Σ₁(9)`.  Deriving the monoid from `κ`
   would bake in a choice; carrying it in the weight and passing to finer levels by
   `AnalyticWeight.restrict` keeps the choice explicit and monotone.

## Main definitions

* `QMF.Weight.levelMonoidOf θ S` — Def 1.28's wild-level monoid `θ⁻¹(S)`.
* `QMF.Weight.kappaLevelSlashAction` — the weight action pulled back to `θ⁻¹(S)`.
* `QMF.Weight.Forms Γ θ κ U hU` — **`S_κ(U)`, the forms of weight `κ` and level `U`**, for
  `κ : AnalyticWeight UK S ρ` (an honest character analytic at the wild level) and `U`
  of wild level `≥ S`.  This is Def 1.27–1.30 in the source's own reading: weight and
  level are the two inputs, with their compatibility (`κ` analytic at `(S, ρ)`,
  `θ(U) ⊆ S`) as hypotheses; the analytic weight datum is derived from `κ`.
* `QMF.Weight.mem_forms_iff` — Def 1.30's `φ(gu) = φ(g)‖_κ u_p`, unfolded.
* `QMF.Weight.heckeOperator` — `[UηU]` on it, from the existing abstract layer.
-/

open TateFredholm
open scoped TateFredholm QMF Pointwise

namespace QMF.Weight

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {G : Type*} [Group G] {Γ : Subgroup G}
variable (θ : G →* Matrix (Fin 2) (Fin 2) K)
variable (S : Submonoid (Matrix (Fin 2) (Fin 2) K)) {ρ : ℝ}

/-- Def 1.28's wild-level monoid: elements of `G` whose matrix component lies in the
weight's acting monoid `S` (for the quaternionic `G = D×_f`, `θ = toMatrix`, this is
`levelMonoid'`-shaped: "the projection U_p is contained in Σ_α"). -/
noncomputable def levelMonoidOf : Submonoid G := S.comap θ

/-- The corestriction `θ⁻¹(S) →* S` of the component map. -/
noncomputable def levelMonoidOfToS : levelMonoidOf θ S →* S where
  toFun g := ⟨θ g.1, g.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by simp)

variable {S} {UK : Subgroup Kˣ}

/-- The weight-`κ` action of the wild-level monoid on the Tate algebra, pulled back
along the component map. -/
@[instance_reducible]
noncomputable def kappaLevelSlashAction (κ : AnalyticWeight UK S ρ) :
    RightSlashAction (levelMonoidOf θ S) c(ℕ, K) :=
  RightSlashAction.comap (levelMonoidOfToS θ S) κ.kappaSlashAction

/-- **The `χ`-twisted weight-`κ` action** of the wild-level monoid on the Tate algebra:
`f ∣ₛ δ = χ(θ δ) • (f ∣_κ θ δ)`.  The scalar character `χ` of the acting monoid is
Buzzard's second weight component `v(det γ)` [*Eigenvarieties*, §10 p. 72:
`(h.γ)(z, x) := n(cz + d, x)(v(det γ)(x)) h((az + b)/(cz + d), x)`]; the classical
determinant character `ν` enters as `χ = detTwist ν` (`PhD/Main/QMF/Weight/06_Algebraic.lean`),
and [Jacobs, Def 1.27] is the untwisted case `χ = 1`. -/
@[instance_reducible]
noncomputable def kappaLevelSlashActionTwisted (κ : AnalyticWeight UK S ρ) (χ : S →* Kˣ) :
    RightSlashAction (levelMonoidOf θ S) c(ℕ, K) :=
  RightSlashAction.twist (kappaLevelSlashAction θ κ)
    (fun r f δ => map_smul (κ.kappaSlash (levelMonoidOfToS θ S δ)) r f)
    (χ.comp (levelMonoidOfToS θ S))

/-- The twisted level action, unfolded: `f ∣ₛ δ = χ(θ δ) • κ.kappaSlash (θ δ) f`.  (Not a
`simp` lemma: `twist_slash`/`comap_slash` already rewrite the left-hand side to a different
normal form; use it with `rw`/`simp only`.) -/
theorem kappaLevelSlashActionTwisted_slash (κ : AnalyticWeight UK S ρ) (χ : S →* Kˣ)
    (f : c(ℕ, K)) (δ : levelMonoidOf θ S) :
    (kappaLevelSlashActionTwisted θ κ χ).slash f δ = χ ⟨θ δ, δ.2⟩ • κ.kappaSlash ⟨θ δ, δ.2⟩ f :=
  rfl

/-- The twisted action commutes with scalars. -/
theorem kappaLevelSMulSlashClassTwisted (κ : AnalyticWeight UK S ρ) (χ : S →* Kˣ) :
    letI := kappaLevelSlashActionTwisted θ κ χ
    RightSlashAction.SMulSlashClass K (levelMonoidOf θ S) c(ℕ, K) := by
  letI := kappaLevelSlashActionTwisted θ κ χ
  exact ⟨fun r f δ => by
    show (χ.comp (levelMonoidOfToS θ S)) δ
          • κ.kappaSlash (levelMonoidOfToS θ S δ) (r • f)
        = r • ((χ.comp (levelMonoidOfToS θ S)) δ
          • κ.kappaSlash (levelMonoidOfToS θ S δ) f)
    rw [map_smul, Units.smul_def, Units.smul_def, smul_comm]⟩

variable (Γ) in
/-- **`S_κ(U)`: the overconvergent automorphic forms of weight `κ` and level `U`**
([Jacobs, Def 1.30] at `A = A_p`; Buzzard's `S^D_κ(U)`): automorphic functions `φ` with
`φ ∣ₛ u = φ` for all `u ∈ U`, where `κ` is a weight analytic at wild level `(S, ρ)` and
`U` has wild level `≥ S`.  The coefficient action is the weight-`κ` action
`κ.kappaSlash` on the Tate algebra through the component map `θ`, twisted by the
optional scalar character `χ` of the acting monoid (Buzzard's `v(det γ)`; the default
`χ = 1` is [Jacobs, Def 1.27]).  `Forms Γ θ κ U hU` is the untwisted space,
`Forms Γ θ κ U hU χ` the twisted one; `Γ` is the global group (`Dˣ` for a quaternion
algebra), explicit because nothing else determines it. -/
noncomputable def Forms (κ : AnalyticWeight UK S ρ) (U : Subgroup G)
    (hU : (U : Set G) ⊆ levelMonoidOf θ S) (χ : S →* Kˣ := 1) :
    Submodule K (AutomorphicFunction G Γ c(ℕ, K)) :=
  letI := kappaLevelSlashActionTwisted θ κ χ
  letI := kappaLevelSMulSlashClassTwisted θ κ χ
  AbstractHeckeOperatorSlash.slashFixedPointsOfLE K (AutomorphicFunction G Γ c(ℕ, K)) hU

/-- Membership in `Forms κ U χ`, unfolded ([Jacobs, Def 1.30]: `φ(gu) = φ(g)‖_κ u_p`,
with Buzzard's scalar `v(det u_p)`): `φ (g * u) = χ(θ u) • (φ g) ∣_κ θ(u)` for all
`u ∈ U`, `g ∈ G`. -/
theorem mem_forms_iff (κ : AnalyticWeight UK S ρ) {U : Subgroup G}
    (hU : (U : Set G) ⊆ levelMonoidOf θ S) (χ : S →* Kˣ)
    {φ : AutomorphicFunction G Γ c(ℕ, K)} :
    φ ∈ Forms Γ θ κ U hU χ ↔
      ∀ (u : U) (g : G), φ (g * u)
        = χ ⟨θ u, hU u.2⟩ • κ.kappaSlash ⟨θ u, hU u.2⟩ (φ g) := by
  letI := kappaLevelSlashActionTwisted θ κ χ
  letI := kappaLevelSMulSlashClassTwisted θ κ χ
  exact AutomorphicFunction.mem_levelSubmoduleSlash_iff' K hU

/-- Membership in the untwisted `Forms κ U` ([Jacobs, Def 1.30] verbatim):
`φ (g * u) = (φ g) ∣_κ θ(u)`. -/
theorem mem_forms_iff_one (κ : AnalyticWeight UK S ρ) {U : Subgroup G}
    (hU : (U : Set G) ⊆ levelMonoidOf θ S) {φ : AutomorphicFunction G Γ c(ℕ, K)} :
    φ ∈ Forms Γ θ κ U hU ↔
      ∀ (u : U) (g : G), φ (g * u) = κ.kappaSlash ⟨θ u, hU u.2⟩ (φ g) := by
  rw [mem_forms_iff]
  simp only [MonoidHom.one_apply, one_smul]

/-- **The Hecke operator `[UηU]`** on the forms of weight `κ` and level `U`
([Jacobs, Def 1.32], from the existing weight-agnostic abstract layer).  The global group
`Γ` and the twist `χ` are implicit: they are read off the form the operator is applied to
(`heckeOperator θ κ U hU hη h φ`). -/
noncomputable def heckeOperator {Γ : Subgroup G} (κ : AnalyticWeight UK S ρ) (U : Subgroup G)
    (hU : (U : Set G) ⊆ levelMonoidOf θ S) {η : G} (hη : η ∈ levelMonoidOf θ S)
    (h : (((Quotient.mk'' : G → AbstractHeckeOperatorSlash.RightCosets U) ''
          (({η} : Set G) * (U : Set G))) :
        Set (AbstractHeckeOperatorSlash.RightCosets U)).Finite) {χ : S →* Kˣ} :
    Forms Γ θ κ U hU χ →ₗ[K] Forms Γ θ κ U hU χ :=
  letI := kappaLevelSlashActionTwisted θ κ χ
  letI := kappaLevelSMulSlashClassTwisted θ κ χ
  AbstractHeckeOperatorSlash.heckeOperatorSlash K hU hU hη h

end QMF.Weight
