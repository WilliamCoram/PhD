# PhD/QMF — quaternionic modular forms: status, design, next steps

**Status 2026-09-02 (unchanged since the 2026-08-20 slopes-hecke board close): every file
under `PhD/Main/QMF/` builds, sorry-free, on standard axioms (`propext`, `Classical.choice`,
`Quot.sound`); the `Weight/` modules are `runLinter`-clean.**
This file is the folder's explanations document while the work is in progress; it will
move up (or into a blueprint) when the QMF development is finished.  Boards:
`.mathlib-quality/qmf/` (classical layer), `.mathlib-quality/slashRefactor/` (right-slash
fork), `.mathlib-quality/laweights/` (general weights, R0–R8),
`.mathlib-quality/forms-headline/` (headline `Forms`, classical inclusion, compactness —
complete 2026-08-19), `.mathlib-quality/forms-followups/` (neat-level model isomorphism,
Fredholm determinant at general weight, quaternionic `S^D_κ(U)`, housekeeping — complete
2026-08-19), `.mathlib-quality/forms-riesz/` (base change of weights, the Jacobs crux for
eigenforms, Riesz decomposition on `S_κ(U)`, non-neat levels via property (Pr) — complete
2026-08-20), `.mathlib-quality/slopes-hecke/` (the slope bound at general weight, the
Hecke algebra and eigensystem on the finite-slope subspace, the valuation↔norm level
dictionary, compact open levels — complete 2026-08-20).  The Jacobs application lives in
`PhD/Main/JacobsSlash/` (map:
`PhD/Main/JacobsSlash/PROGRESS.md`); since the forms-headline board it is an *instance* of the
`Weight/` layer, not a parallel development.

Sources: [Buzzard, *Eigenvarieties*, LMS 320 (2007), §§8–9], [Jacobs, *Slopes of Compact
Hecke Operators*, Imperial 2003, Ch. 1 §1.5–1.6, Ch. 2], [Loeffler, *Overconvergent
algebraic automorphic forms*, Def. 3.3.2], and FLT's `WeightTwoAutomorphicForm`.

---

## 0. File order

The project's own modules — `PhD/Main/QMF/*.lean`, `Weight/` and `Slash/`, 31 files — are numbered.
Each filename carries **its depth in this folder's own import graph**: a file `NN_Name.lean`
imports only files of this folder with a strictly smaller `NN` (plus `PhD/Main/TateFredholm/`, `PhD/Main/ForMathlib/` and `PhD/Main/QMF/FLTstuff/`).  Files that share a number
are independent of one another and can be read in any order.  Because the module names start with a
digit they are imported in French quotes:

```lean
import PhD.Main.QMF.Weight.«08_Slopes»
```

`PhD/Main/QMF/FLTstuff/` (92 files) is **not** numbered: it mirrors the upstream FLT paths so that it
stays diffable against that project, and nothing in it imports the modules above.

- **00** — `HeckeMonoid`, `Sigma0`, `Weight/Series`
- **01** — `AutomorphicFunction`, `Slash/Sigma0`, `WeightModule`
- **02** — `Decomposition`, `Slash/Basic`
- **03** — `HeckeMatrix`, `Quaternionic`, `Slash/AutomorphicFunction`, `Slash/HeckeMonoid`, `Slash/WeightModule`, `Weight/SlashAction`
- **04** — `Finiteness`, `Level`, `Slash/HeckeMatrix`, `UpiElement`, `Weight/AdicLevel`, `Weight/Char`
- **05** — `FiniteDimensional`, `Slash/Quaternionic`, `Weight/Forms`
- **06** — `Weight/Algebraic`, `Weight/Compact`
- **07** — `Weight/Fredholm`, `Weight/Quaternionic`
- **08** — `Weight/BaseChange`, `Weight/HeckeAlgebra`, `Weight/Pr`, `Weight/Slopes`

| file | imports in this folder | what it is |
|---|---|---|
| `00_HeckeMonoid.lean` | — | Abstract Hecke operators for a submonoid of a group |
| `Weight/00_Series.lean` | — *(+ TateFredholm)* | Abstract weight data for the weight-`κ` action (Jacobs, Definition 1.27) |
| `00_Sigma0.lean` | — | The local monoid `Σ₀(γ)` at a nonarchimedean place |
| `01_AutomorphicFunction.lean` | `00_HeckeMonoid` | Abstract automorphic functions with monoid-twisted level action |
| `Slash/01_Sigma0.lean` | `00_Sigma0` | The right-handed monoid `Σ₀'(γ)` and the adjugate dictionary |
| `01_WeightModule.lean` | `00_Sigma0` | Classical weight modules `L_{n,ν}` |
| `Slash/02_Basic.lean` | `01_Sigma0` | The right-slash action class |
| `02_Decomposition.lean` | `01_AutomorphicFunction` | Decomposition of `L(U, A)` over the class set |
| `Slash/03_AutomorphicFunction.lean` | `01_AutomorphicFunction`, `02_Basic` | The right slash on automorphic functions, and slash-form level spaces |
| `03_HeckeMatrix.lean` | `02_Decomposition` | The matrix of a Hecke operator in the class-set basis |
| `Slash/03_HeckeMonoid.lean` | `00_HeckeMonoid`, `02_Basic` | Abstract Hecke operators for the right slash |
| `03_Quaternionic.lean` | `01_WeightModule`, `02_Decomposition` | Quaternionic modular forms of general weight |
| `Weight/03_SlashAction.lean` | `00_Series`, `01_Sigma0`, `02_Basic` | The weight-`κ` action of an abstract weight on the Tate algebra |
| `Slash/03_WeightModule.lean` | `01_WeightModule`, `02_Basic` | The right slash on classical weight modules |
| `Weight/04_AdicLevel.lean` | `03_SlashAction` *(+ ForMathlib)* | Wild levels at a finite place |
| `Weight/04_Char.lean` | `03_SlashAction` | Honest locally analytic characters and their weight data |
| `04_Finiteness.lean` | `03_Quaternionic` *(+ QMF)* | Finiteness of the class set, and of the decomposition of `QMF.Space` |
| `Slash/04_HeckeMatrix.lean` | `03_AutomorphicFunction`, `03_HeckeMonoid` | The matrix of a right-slash Hecke operator, and the class-set decomposition |
| `04_Level.lean` | `03_HeckeMonoid`, `03_Quaternionic` *(+ QMF)* | Compact open levels |
| `04_UpiElement.lean` | `03_Quaternionic` *(+ QMF)* | The standard `U_ϖ` Hecke element |
| `05_FiniteDimensional.lean` | `04_Finiteness` | Finite-dimensionality of the space of quaternionic modular forms |
| `Weight/05_Forms.lean` | `03_AutomorphicFunction`, `03_HeckeMonoid`, `04_Char` | Overconvergent automorphic forms at an abstract weight (Jacobs, Def 1.28–1.32) |
| `Slash/05_Quaternionic.lean` | `03_Quaternionic`, `03_WeightModule`, `04_HeckeMatrix`, `04_UpiElement` | Quaternionic modular forms with the classical right slash |
| `Weight/06_Algebraic.lean` | `03_WeightModule`, `05_Forms` | The classical algebraic weights as an instance of the abstract weight action |
| `Weight/06_Compact.lean` | `04_HeckeMatrix`, `05_Forms` *(+ TateFredholm)* | Compactness of `U_ϖ` on the forms of weight `κ` (Jacobs Lemma 2.7, Buzzard Lemma 12.2) |
| `Weight/07_Fredholm.lean` | `06_Compact` | The Fredholm determinant of a Hecke operator on `S_κ(U)` |
| `Weight/07_Quaternionic.lean` | `04_Finiteness`, `05_Quaternionic`, `06_Compact` *(+ ForMathlib)* | Overconvergent quaternionic modular forms `S^D_κ(U)` |
| `Weight/08_BaseChange.lean` | `07_Fredholm` *(+ ForMathlib, TateFredholm)* | Base change of weights, Hecke blocks and Fredholm determinants |
| `Weight/08_HeckeAlgebra.lean` | `07_Fredholm` | The Hecke algebra acting on `S_κ(U)` |
| `Weight/08_Pr.lean` | `07_Fredholm` | Non-neat levels: the Fredholm determinant on `S_κ(U)` as a direct summand |
| `Weight/08_Slopes.lean` | `07_Fredholm` *(+ NewtonPolygons, TateFredholm)* | Slopes of `det(1 − T·[UηU])` at a general analytic weight |

## 1. The four layers

| Layer | Files | Content |
|---|---|---|
| **FLT vendor** | `FLTstuff/` (~90 files) | Ported FLT infrastructure: finite adeles, base change, Haar characters, and Fujisaki's lemma `NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset`.  Frozen; do not develop here. |
| **Left-action core** | `Sigma0`, `WeightModule`, `AutomorphicFunction`, `Decomposition`, `HeckeMonoid`, `HeckeMatrix`, `Quaternionic`, `UpiElement`, `Finiteness`, `FiniteDimensional` | Classical weight `(n, ν)`: the monoid `Σ₀(γ)`, `L_{n,ν} = Symⁿ ⊗ ν`, abstract `L(U, A)` for a monoid-twisted action, class-set decomposition `L(U,A) ≅ ∏ A^{Γ_λ}`, Hecke operators `[UgV]` for a *submonoid* `Δ ≤ G`, the `U_ϖ` element, `QMF.Space` (= Buzzard's `S^D_{k,w}(U)`), finite-dimensionality via Fujisaki. |
| **Right-slash dialect** | `Slash/Sigma0`, `Slash/Basic`, `Slash/WeightModule`, `Slash/AutomorphicFunction`, `Slash/HeckeMonoid`, `Slash/HeckeMatrix`, `Slash/Quaternionic` | The same theory in the sources' right-handed convention: `Σ₀'` (Buzzard's `Mₜ`), `RightSlashAction Δ A` with `a ∣ₛ δ`, Buzzard's slash on `L_{n,ν}`, `levelSubmoduleSlash`, right-coset Hecke operators, `SpaceSlash`, and the **seam theorems** identifying each with its left-handed original through the adjugate dictionary. |
| **General weights** | `Weight/Series`, `Weight/SlashAction`, `Weight/Char`, `Weight/Forms`, `Weight/Algebraic`, `Weight/Compact`, `Weight/Fredholm`, `Weight/BaseChange`, `Weight/Pr`, `Weight/Quaternionic` | Jacobs Def 1.27–1.32 for an *arbitrary* analytic weight: the `WeightSeries` engine and the weight-κ action on the Tate algebra `c(ℕ, K)` (Prop 2.6 by construction), honest characters (`ExpansionData`, **`AnalyticWeight`**), the headline space **`Forms Γ θ κ U hU (χ := 1)`** and its Hecke operators, the classical bridge (`polyEmbed`, `algWeight`, `classicalForms`, *classical = polynomial-valued overconvergent*), the **compactness theorem** (`Weight/Compact`: the block model `evalAtReps`, **Buzzard's decomposition at a neat level** `bijective_evalAtReps`/`formsModelEquiv`, the certificate blocks `heckeBlock`, the transport `evalAtReps_heckeOperator`, and `isCompactoid_heckeBlockOp` — Jacobs Lemma 2.7 / Buzzard Lemma 12.2 at every analytic weight), the **Fredholm determinant** `det(1 − T·[UηU])` on `S_κ(U)` (`Weight/Fredholm`: `heckeCharPowerSeries`, the eigenform criterion `evalT_heckeCharPowerSeries_eq_zero_iff`, independence of the representatives `heckeCharPowerSeries_eq_of_reps`), the **quaternionic instantiation** (`Weight/Quaternionic`: `FormsQ` = Buzzard's `S^D_κ(U)`, `heckeUpiQ` = `U_ϖ`, `isCompactoid_heckeBlockOp_etaAdelic'` = Buzzard Lemma 12.2, Hecke finiteness at compact open level), **base change** (`Weight/BaseChange`: weight actions, Hecke blocks and `det(1 − T·[UηU])` commute with a homomorphism of the coefficient field — Buzzard Lemma 2.13) and **non-neat levels** (`Weight/Pr`: the averaging projectors `stabAvg`/`stabProj` onto `∏ A^{Γ_λ}`, the determinant `heckeCharPowerSeriesPr` on the (Pr) summand, its independence of the projector, and the eigenform criterion at any level — Buzzard §2 pp. 18–19, §10 p. 73). |
| **Slopes & Hecke algebra** | `Weight/Slopes`, `Weight/HeckeAlgebra`, `Weight/AdicLevel`, `Level` | (slopes-hecke board, complete 2026-08-20.)  **The slope bound at a general analytic weight** (`Weight/Slopes`: row decay of the certificate blocks, `norm_charCoeff_heckeCharPowerSeries_le`, and `isBelow_newtonPolygon_heckeCharPowerSeries` — the Newton polygon of `det(1 − T·[UηU])` lies on or above the polygon with unit slopes `⌊k/t⌋·(−log σ)`, `t` = the class number; the abstract engine is `PhD/Main/TateFredholm/06_Slopes.lean`, where the exact case landed 2026-09-01); **the Hecke algebra as data** (`Weight/HeckeAlgebra`, Buzzard §5: a commutative algebra `𝕋` acting on `Forms` with a distinguished compact `[UηU]`, everything in `𝕋` preserves the Riesz finite-slope subspace, which carries a system of eigenvalues); **the valuation ↔ norm level dictionary** (`Weight/AdicLevel`: `Σ₀(γ)`/`Σ₁(p^k)` stated by valuations on a `Valued` field, retiring the fork's hand-made lemmas); **compact open levels** (`Level`: the integral order is compact, unit groups of compact multiplicatively-closed sets are compact, Hecke finiteness at any compact open level — Buzzard §9). |

The block-operator calculus the compactness theorem assembles on (`blockOp`, `blockIncl`/
`blockProj`, `isCompactoid_blockOp`) is `PhD/Main/TateFredholm/06_BlockOp.lean` (moved there from
the Jacobs fork on 2026-08-19; `isCompactoid_zero`, `IsCompactoid.finset_sum`,
`isCompactoid_of_row_decay'`, `RowIntAt.mono` live next to their definitions in
`TateFredholm/`).

`NontriviallyNormedField (v.adicCompletion F)` — the typeclass pack `Forms` needs at a finite place —
is the global instance `PhD/Main/ForMathlib/NumberTheory/NumberField/Completion/FinitePlace.lean`
(mathlib's scoped `Valued.toNontriviallyNormedField`, `rfl`-compatible with mathlib's `NormedField`);
the fork's former hand-made `K₃` instance is gone.

Instances of `AnalyticWeight`: `algWeight hb n : AnalyticWeight ⊤ S ρ` (`Weight/Algebraic`,
`κ(u) = u^(n+2)`) and `JacobsSlash.jacobsWeight t ht : AnalyticWeight (oneUnits K₃ ‖3‖ …)
Sigma1₃ ‖3‖` (`PhD/Main/JacobsSlash/U3/5_KappaWeight.lean`, `κ(u) = uᵗ`, expansion = the
`p`-adic binomial series `κ(d)·(t choose n)·(c/d)ⁿ`; since 2026-08-20 it is the *field-generic*
`jacobsWeightOf` — any complete ultrametric `K` with `‖3‖ < 1`, at the norm-defined level
`sigma1Norm` — restricted to `Σ₁(3)`, so the same construction over `L ⊇ K₃` gives the
base-changed spaces `kappaFormsL` of `U3/«10_Eigenforms»`).  **The Jacobs fork is slim**: `kappaForms`
= `FormsQ ℚ D v₃ (jacobsWeight t ht) U₁(9)`, `heckeU3` = `heckeUpiQ … 3`, `blockEntry` =
`heckeBlock` at the `«5_Factorisations»` certificates, `evalU3` = `evalAtReps … classRep`,
`bijective_evalU3` = `bijective_evalAtReps_of_stabilizer_eq_bot` at Theorem 2.1
(`classRep_bijective`) and Lemma 2.2, `charPowerSeriesU3` = `heckeCharPowerSeries`, and
`evalU3_heckeU3`/`isCompactoid_blockOpU3` are the general transport/compactness theorems
applied (`U3/6_Matrix.lean`, `U3/7_Fredholm.lean`); the only Jacobs-specific analysis left is
`U3/4_KappaColumn.lean` (the `Σ₁(3)` bounds and the closed form of the κ-column) and the
class-set/certificate computations.

Import discipline: `Weight/` imports `Slash/` (never the left core directly, except through
`Slash/WeightModule` for the classical bridge); `JacobsSlash` imports `PhD.Main.QMF` and
`PhD.Main.QMF.Slash`/`Weight` and never the left-action original (moved to
`PhD/Main/LegacyCode/Jacobs/` on 2026-08-21).

---

## 2. Design decision A — left actions vs the right slash

**The core is left-handed because mathlib is.**  `Module`, `DistribMulAction`,
`SMulCommClass` are left-handed; a right module is an `Mᵐᵒᵖ`-module, which would put
`MulOpposite` into every statement and every instance search.  FLT makes the same choice.
Concretely the core uses the Pollack–Stevens monoid `Σ₀(γ) = {g ∈ M₂(𝒪) : g₀₀ a unit,
v(g₁₀) ≤ γ, det g ≠ 0}` (unit condition on `a`), the *transposed* substitution
`g • P = ν(g) • P(aX + cY, bX + dY)` (which is what makes it a left action), the
Loeffler-style `(δ • φ)(g) = δ • φ(g·δ)` on automorphic functions, `L(U, A)` as the
`U`-fixed points, and `[UgV] : L(V) → L(U)` via *left* cosets `xᵢV`.

**The right dialect exists because the sources are written in it.**  The classical slash
`f ∣ γ` is a right action essentially universally (Shimura, Diamond–Shurman, Buzzard,
Jacobs): `Mₜ` has the unit condition on `d`, `(f|u)(g) = f(gu⁻¹)·u_p`, `UηU = ∐ U·xᵢ`
with *right* cosets.  The Jacobs crux (the `U₃` matrix, the factorisations
`cᵢvₜ⁻¹ = d·c·u`, the block operators) reads verbatim only in that form.  So
`Slash/` provides `RightSlashAction Δ A` (a weight-free `SlashAction`, same axiom names),
`Σ₀'` (= Buzzard's `Mₜ` on the nose), Buzzard's own formula on `L_{n,ν}`
(`P(X,Y) ↦ det(δ)^v · P(aX + bY, cX + dY)`, *untransposed*), `levelSubmoduleSlash`
(`{φ : φ ∣ₛ u = φ}` verbatim), and right-coset Hecke operators `L(U) → L(V)`.

**Rule: state right, prove left.**  Nothing is re-proved in the right dialect; every
right-handed statement crosses a seam theorem (`slash_eq_adj_smul`,
`levelSubmoduleSlash_eq_levelSubmodule`, `spaceSlash_eq_space`) into the left library.

**The seam is the adjugate — forced, not chosen.**  Passing between the conventions needs
an *anti*-automorphism of the acting monoid.  Group inversion is unavailable: `Σ₀` is a
monoid, and `η = (1 0; 0 ϖ)` is not invertible in it — that non-invertibility *is* the
`U_ϖ` direction.  Transpose is an anti-automorphism but sends `πᵗ ∣ c` to `πᵗ ∣ b`, the
wrong congruence subgroup.  The adjugate `(a b; c d) ↦ (d −b; −c a)` swaps `a ↔ d` and
preserves the level entry (up to sign): it is *the* level-preserving anti-automorphism.
On `L_{n,ν}` the adjugate transport of the left action agrees with Buzzard's formula only
after the signed variable swap `jTwist` (`(adj δ)ᵀ = J δ J⁻¹`; the `Z = X/Y` vs `Y/X`
homogenisation seam); no determinant correction is needed since `det(adj δ) = det δ` in
dimension 2.  Design notes in `00_Sigma0.lean` and `Slash/WeightModule.lean`.

**The general-weight layer is natively right-handed.**  Jacobs's `‖_κ` *is* a right
action; `WeightSeries.kappaSlashAction : RightSlashAction S c(ℕ, K)` is proved directly
(the Möbius composition law + the κ-cocycle), so `Forms` sits on `levelSubmoduleSlash` /
`heckeOperatorSlash` and never touches the left core.  The classical `ν` enters the right
world through `detTwist ν` (ν read on `Σ₀'` via the adjugate) and `RightSlashAction.twist`.

---

## 3. Design decision B — classical vs locally analytic weights

**Classical (`01_WeightModule.lean`).**  A weight is a pair `(n, ν)`: `n : ℕ` is the `Symⁿ`
degree and `ν : Σ₀(γ) →* Rˣ` is an *arbitrary* character of the **whole monoid** — a
one-dimensional scalar twist, so `WeightModule R n ν = Symⁿ ⊗ ν` as a `Σ₀(γ)`-module
(Buzzard's `det^v` is `ν = detChar w`; classical weight `(k, w)` is
`(n, v) = (k − 2, w − n − 1)`).  The module is finite-dimensional polynomial, over any
`F_v`-algebra `R`; the action is polynomial, needs no analyticity, and extends to `M₂(K)`.
`QMF.Space` is finite-dimensional by Fujisaki.  Weight 2 (`n = 0`, `ν = 1`) is FLT's space.

**Locally analytic (`Weight/`).**  A weight is
```
structure AnalyticWeight (U : Subgroup Kˣ) (S : Submonoid (Matrix (Fin 2) (Fin 2) K)) (ρ : ℝ)
  toChar    : U →* Kˣ                  -- an honest character of a subgroup of units
  expansion : ExpansionData S ρ U toChar -- its expansion κ(cz + d) at wild level (S, ρ), as data
```
(the expansion is carried as *data* — Jacobs's "by κ(cz + d) we mean the power series
expansion", Buzzard's explicitly singled-out "thickening" — so the action is computable by
`rfl` from the column, with no `Classical.choice`; it is nevertheless unique on the level,
`ExpansionData.col_eq_of_mem`, so weights with the same character act identically,
`AnalyticWeight.kappaSlash_eq`).  The
module is the Tate algebra `c(ℕ, K)`, infinite-dimensional; the action is `ofGenFun` of
`κ(cx+d)/((cx+d)(cx+d − axy − by))` with Def 1.27's normalisation `κ(cz+d)/(cz+d)²`
(Jacobs Prop 2.6 by construction).  The headline definitions (`Weight/Forms.lean`):
```
Forms Γ θ (κ : AnalyticWeight UK S ρ) (U : Subgroup G) (hU : ↑U ⊆ levelMonoidOf θ S) (χ := 1)
mem_forms_iff_one : φ ∈ Forms Γ θ κ U hU ↔ ∀ u g, φ (g * u) = κ.kappaSlash ⟨θ u, _⟩ (φ g)
heckeOperator θ κ U hU hη h φ          -- Γ, χ read off φ
```
— Buzzard's `S^D_κ(U)`, Jacobs's `L(U, A_κ)`, with the compatibility "U of wild level
≥ p^α, κ α-analytic" as hypotheses; `Γ` is the global group (`Dˣ`), explicit because nothing
else determines it, and the optional `χ : S →* Kˣ` is Buzzard's second weight component
`v(det γ)` (Def 1.27 is `χ = 1`; the classical twist is `detTwist ν`).  `Forms` is the fixed
points of the single twisted action `kappaLevelSlashActionTwisted θ κ χ`
(`RightSlashAction.twist` of the pulled-back weight action), so `mem_forms_iff` /
`mem_forms_iff_one` are `rfl`-deep, and `heckeOperator` is `heckeOperatorSlash` for that
action.  The compactness theorem (`Weight/Compact.lean`) then reads, at a section
`c : ι → G` of `Γ\G/U` and right-coset certificates `(vRep, idx, d, u)` for `UηU`:
`evalAtReps c` is injective, `evalAtReps c ∘ [UηU] = heckeBlockOp ∘ evalAtReps c`, and
`heckeBlockOp` is compactoid whenever `‖det θ(η)‖ ≤ σ` for some `ρ ≤ σ < 1` — the
determinant certificate being exactly Jacobs's/Buzzard's "`U_ϖ` type" hypothesis
(`norm_det_toMatrix_certificate_le`: on a bounded level `‖det‖ ≤ σ` forces `‖g₀₀‖ ≤ σ`,
hence `RowIntAt σ` of the generating function, `WeightSeries.rowIntAt_genFun`).

**Neat levels, non-neat levels, and the Fredholm determinant** (forms-followups, forms-riesz).  Buzzard §9 p. 69 /
Jacobs Lemma 1.31: `φ ↦ (φ(c_λ))` is an isomorphism `S_κ(U) ≅ ⊕_λ A_κ^{Γ_λ}` with
`Γ_λ = {u ∈ U : c_λ u c_λ⁻¹ ∈ Γ}`.  The generic decomposition onto the invariants is
`AutomorphicFunction.bijective_evalAtRepsSlash` (used by the classical finite-dimensionality
proof together with Fujisaki, `QMF/FiniteDimensional.lean`); what the overconvergent theory
needs is the invariants *gone*, so that the block model is all of `c(ι × ℕ, K)` and the
compactoid block operator is conjugate to `[UηU]` itself.  `Weight.bijective_evalAtReps` states
this under "the stabilisers act trivially" (`stabilizerAtSlash Γ U (c i) = ⊥` as a corollary —
Jacobs Lemma 2.2), for any family `c : ι → G` bijective onto `Γ\G/U`; `ext_of_forall_rep`/
`evalAtReps_injective` only need `c` to meet every double coset.  Then `det(1 − T·[UηU]) :=
heckeCharPowerSeries` (Jacobs p. 21: the matrix of `U_p` w.r.t. the topological basis), the
zeros are the reciprocal eigenvalues on `S_κ(U)` itself (`evalT_heckeCharPowerSeries_eq_zero_iff`,
Serre §7 through the model isomorphism), and the series is independent of the representatives
and certificates (`heckeCharPowerSeries_eq_of_reps`: two neat families are related by a
transition block operator, a continuous linear equivalence conjugating the two block operators —
Buzzard Cor 2.6).  Non-neat levels (Buzzard's property-(Pr) route, p. 73) are not formalised.
Finiteness of the index set at a quaternionic level is Fujisaki (`finite_classSet`, packaged as
`classSetFintype`; `evalAtReps_out_injective` is then Buzzard p. 73 verbatim); the fork's
`classRep_bijective` is the explicit class-number-one version.

**Without neatness** (`Weight/Pr.lean`) the image of `evalAtReps` is exactly the block-model
invariants (`mem_range_evalAtReps_iff`), and when the stabilisers are finite of order invertible in
`K` the blockwise average `stabProj` is a continuous projector onto it (Buzzard p. 73: "`Γ_λ` acts on
`A_{κ,r}` via a finite quotient.  Hence `S^D_κ(U;r)` is a direct summand of an ONable Banach
module").  The determinant is then Buzzard's `det(1 − X(φ ⊕ 0))` (§2 pp. 18–19), formalised as
`heckeCharPowerSeriesPr … E := det(1 − T·(heckeBlockOp ∘ E))` for *any* continuous projector `E`
onto that image: independent of `E` (`heckeCharPowerSeriesPr_eq_of_proj`, via `charPowerSeries_comm`
= Buzzard Lemma 2.12), equal to `heckeCharPowerSeries` at a neat level (`heckeCharPowerSeriesPr_one`,
`E = 1`), with the same eigenform criterion (`evalT_heckeCharPowerSeriesPr_eq_zero_iff`) needing only
that the representatives meet every double coset.  Two definitions on purpose — the neat one takes
certificates only, and every neat-level statement (base change, Riesz) is stated for it.

**Riesz theory on `S_κ(U)`** (`Weight/Fredholm.lean`): `exists_riesz_decomposition_forms` transports
Serre §7 Prop 12 / Buzzard Prop 3.2 along `formsModelEquiv` — at a zero `a` of `det(1 − T·[UηU])`
over a discretely valued `K`, `S_κ(U) = N ⊕ F` with `N` the `h`-dimensional generalised
`a⁻¹`-eigenspace and `1 − a·[UηU]` bijective on `F`: the finite-slope decomposition.

**Base change** (`Weight/BaseChange.lean`): two weights whose expansions match along `ι : K →+* L`
(hypothesis `hcol`) have `ι`-related actions, blocks and — for bounded `ι` — determinants
(`heckeCharPowerSeries_map`).  There is deliberately no `AnalyticWeight.map`: a character on the
`L`-disc is not determined by its `K`-points, so the `L`-weight is supplied by the caller
(`JacobsSlash.jacobsWeightOf` at `ι t`).

**Why the wild level `(S, ρ)` is part of the weight, not only of the level `U`.**
(Also recorded as the design note in `Weight/Forms.lean` and on `AnalyticWeight`.)
1. *Analyticity is a joint condition on κ and α.*  The action of `(a b; c d)` evaluates κ
   at `c·z + d`, `‖z‖ ≤ 1`, i.e. on the disc of radius `‖c‖ ≤ ρ` about the unit `d`.  The
   datum the action and the compactness estimates consume — `κ(c·z + d) = ∑ aₘ zᵐ` with
   `‖aₘ‖ ≤ ρᵐ` — exists iff κ is analytic on that disc.  Over a general `K` there is no
   "continuous ⇒ locally analytic" (that is special to `ℤ_p^×`), so the expansion data
   *is* the analyticity, and it is radius-indexed.
2. *`A_κ` is a right-`Σ_α`-module.*  `Forms = L(U, A_κ)` needs `U_p ⊆ Σ_α` acting through
   it, so κ and `U` must reference the same `Σ_α`: `AnalyticWeight UK S ρ` is the
   `Σ_S`-module structure on the Tate algebra, `hU` is `U_p ⊆ Σ_S`.  This is verbatim
   Buzzard ("κ a *t*-analytic weight, U of wild level ≥ p^t") and Jacobs ("fix α and κ as
   in Def 1.27; U of wild level ≥ p^α").
3. *α is free above the threshold and there is no canonical `S` per κ.*  Hecke operators,
   `U_p` and classicality move between levels; Jacobs's weight acts through both `Σ₁(3)`
   and `Σ₁(9)`.  Deriving the monoid from κ would bake in a choice; carrying it in the
   weight and passing to finer levels by `AnalyticWeight.restrict` keeps it explicit.
   (Restriction is in `S` at fixed `ρ`; monotonicity in `ρ` is *not* automatic from the
   abstract datum — it needs integrality of the Taylor coefficients of κ on the unit disc,
   which honest characters have but `ExpansionData` does not record.  `restrictRadius`
   restricts to `(S', ρ')` *given* the finer decay as a hypothesis; the "saturation" theorem
   that derives it for `SigmaNorm`-type levels is not formalised.)

**Two tiers, and what each is for.**  `WeightSeries S ρ` (`Weight/Series.lean`) is the
**engine**: the expansion `col c d` plus the five facts the action laws consume
(normalisation, row decay, summability, the κ-cocycle, one-variable-ness), on which
`kappaSlash`, `kappaSlash_one/_mul`, Prop 2.6, the column identity and the compactoid
estimates (`rowIntAt_genFun`, `isCompactoid_kappaSlash_of_norm_det_le`) are proved *once*.
The cocycle is the only character-specific analysis, and since the forms-headline board
there is exactly one proof of it: multiplicativity + evaluation injectivity
(`ExpansionData.toWeightSeries`), which every honest character inherits — the fork's ODE +
p-adic-binomial cocycle (`4_KappaSlash`, retired) and the algebraic weight's polynomial
cocycle (`algWeightSeries`, retired) are gone.  `ExpansionData` is the **constructor/
computation interface** — how a weight is *built* (`AnalyticWeight := ⟨toChar, expansion⟩`)
and how one *computes* with it (`kappaSlash_toWeightSeries_eq`, `col_eq_of_mem`).
`AnalyticWeight` is the **API**: it re-exports `kappaSlash`, `_one`, `_mul`,
`matrixCoeff_kappaSlash`, `kappaSlashAction`, `smulSlashClass`, `isCompactoid_kappaSlash`,
`restrict`/`kappaSlash_restrict`, `restrictRadius`.  Downstream code should never need to name
`WeightSeries` (the headers of `00_Series.lean`/`03_SlashAction.lean` say so): `05_Forms.lean` builds the
level action from `κ.kappaSlashAction`, and the fork names `WeightSeries` only in
`genFun_jacobsWeight`, the one place the thesis's generating function is identified.

**How the two notions of weight relate — and why neither contains the other on the nose.**
Local analyticity is *invisible* on a polynomial module, so the ν-generality of the
classical layer is not what the analytic layer enlarges; it enlarges the *degree*: `Symⁿ`
becomes the Tate algebra and `n` becomes the character `κ = u^(n+2)` (`algWeight`), the
`+2` absorbing Def 1.27's `(cz+d)^(-2)` (classical weight `k = n + 2`).  Conversely `κ`
is a character of *units only* while `ν` is a character of the whole monoid — its values
on non-units such as `η` matter for the `U_ϖ` normalisation — so ν does not disappear
into κ; it survives as the scalar twist `RightSlashAction.twist` at `detTwist ν`
(Def 1.27 is the untwisted case χ = 1) — which is why `Forms` carries the optional `χ`.
The bridge (`Weight/Algebraic.lean`), now stated at the headline: `polyEmbed`
dehomogenises `L_{n,ν} ↪ c(ℕ, K)`; `polyEmbed_slash_level` says the classical right slash
equals the κ-action at `algWeight hb n` twisted by `detTwist ν`;
`classicalForms Γ θ n ν U hU = SpaceSlash` and `map_classicalForms_le_forms :
(classicalForms …).map (mapCoeff (polyEmbed n ν)) ≤ Forms Γ θ (algWeight hb n) U hU
(detTwist ν)` is Buzzard's "classical forms are overconvergent forms" (§9); the endpoint
`mem_map_classicalForms_iff` — **classical = polynomial-valued overconvergent** — makes it
two-sided, and `heckeOperator_mapCoeff_polyEmbed` is the Hecke equivariance of the
inclusion.

---

## 4. Dead-code audit (re-run 2026-08-20, after the forms-riesz board)

* **Deleted / moved by forms-riesz**: `MvPowerSeries.map_inv₀` → ForMathlib,
  `map_linSeries`/`map_quadSeries` → `TateFredholm/WeightGenFun.lean`, the fork's
  `charCoeff_map`/`charPowerSeries_map` → isometric corollaries in `TateFredholm/BaseChange.lean`;
  the seven `K₃`-specific Jacobs-weight declarations (`levelBounds_sigma1₃`, `jacobsCol_rowDecay`,
  `hasSum_jacobsCol_unitPow`, `isUnit_unitPow`, `jacobsChar`, `jacobsChar_apply`,
  `jacobsExpansionData`) → the generic `…Of` versions; `matrixCoeff_U3MatrixOp_map` extracted from
  `map_charPowerSeriesU3`'s proof (which is now its corollary).  All in `renames.jsonl`.
* **Zero-reference today, kept deliberately**: endpoint statements
  (`exists_eigenform_U3_halfIntegral`, `exists_riesz_decomposition_forms`,
  `evalT_heckeCharPowerSeriesPr_eq_zero_iff`, `heckeCharPowerSeriesPr_one`,
  `heckeCharPowerSeriesPr_eq_of_proj`, `mem_map_classicalForms_iff`, `formsModelEquiv`,
  `bijective_evalAtReps_out`, `isCompactoid_heckeBlockOp_etaAdelic'`), discharging lemmas and
  unfolding/`simp` API.
* `runLinter`: the whole board surface (`QMF/Weight/*`, `JacobsSlash/U3/*`,
  `TateFredholm/{BaseChange,WeightGenFun,BlockOp}`, the ForMathlib files added by these boards) is
  clean.  Pre-existing findings remain in the TateFredholm core (`Tate`, `Compact`, `Fredholm`,
  `Matrix`, `ModelSpace`, `Pr`, `Residue` — ~35 unused-argument/simpNF) and in unrelated ForMathlib
  files (`PowerBounded`, `NewtonPolygon`, `NegLogNorm`), plus the frozen FLT vendor.

---

## 5. Next steps

Done on forms-headline (2026-08-19): compactness of `U_ϖ` at general weight, the Jacobs endpoint at
the headline, the `Forms`-level classical inclusion.  Done on forms-followups (2026-08-19): the
neat-level model isomorphism, the Fredholm determinant + eigenform criterion, `FormsQ`/`heckeUpiQ`,
`restrictRadius`, 39 legacy linter findings.  Done on forms-riesz (2026-08-20): **base change**
(`Weight/BaseChange.lean`), the **Jacobs crux for eigenforms** (`U3/10_Eigenforms.lean`:
`exists_eigenform_U3_halfIntegral` — for every `j`, an eigenform of `U₃` over `ℂ₃` with
`v₃(a) = j + ½`), the **Riesz decomposition on `S_κ(U)`**, and **non-neat levels via (Pr)**
(`Weight/Pr.lean`).

Done on slopes-hecke (2026-08-20): the **slope theorem at a general analytic weight**
(`Weight/Slopes.lean`: `isBelow_newtonPolygon_heckeCharPowerSeries` — the Newton polygon of
`det(1 − T·[UηU])` lies on or above the polygon with unit slopes `⌊k/|ι|⌋·(−log σ)`, on top of the
σ-general Hadamard/minor machinery now in `TateFredholm/Slopes.lean`), the **Hecke-algebra layer**
(`Weight/HeckeAlgebra.lean`: the commutation criterion, kernel-stability, and
`exists_eigensystem_of_riesz` — a system of eigenvalues on the Riesz finite-slope subspace), the
**valuation ↔ norm level dictionary** (`Weight/AdicLevel.lean`, replacing the fork's hand-rolled
lemmas by mathlib's `Valued.toNormedField.norm_le_iff`), and the **compact-open level** route
(`QMF/Level.lean` + `JacobsSlash/U3/2_LevelTopology.lean`).

Open:

1. **Compact open standard levels** — DONE (slopes-hecke D1/D2/D3/D3b).  `QMF/Level.lean` has the
   general half (`Units.isCompact_of_isCompact`, `Units.isOpen_of_isOpen`,
   `isCompact_integralTensor`, `isOpen_integralAdeles`, `continuous_toLocal`, `continuous_toMatrix`,
   `toMatrix_det_ne_zero`, and the mixin `RigidificationAt.IsCompletionLinear` recording that the
   rigidification is `F_v`-linear); `JacobsSlash/U3/2_LevelTopology.lean` instantiates it:
   `U₀(1)` and `U₁(9)` are compact open and `finite_image_doubleCoset_U1_9` gives Hecke finiteness
   for every `η` without exhibiting representatives (the fork's explicit `finite_image_eta3` stays
   — it is what computes the matrix).
2. **Quaternionic instantiation — the local data.**  `FormsQ`/`heckeUpiQ` are general, but the
   concrete `(F, v)` data (`Sigma1₃`, the rigidification `theta`, `LevelBounds`) is still built by
   hand in `U3/1_Setting.lean`; a general `Sigma0' ↔ SigmaNorm` dictionary would make `S^D_κ(U)`
   literal for every totally definite `D`.
3. **Weight space / families.**  `AnalyticWeight` over an affinoid `R` (`κ : U →* Rˣ`, expansions in
   `R⟨z⟩`); `WeightSeries`/`SlashAction` assume a field.  The object that varies in the family is
   `heckeCharPowerSeries` at fixed certificates; `Weight/BaseChange.lean` is the specialisation half.
   *lwx-seam board (complete 2026-09-05):* the halo weight `κ_{T₀}` of [LWX] is the first
   `AnalyticWeight` coming from a family (`PhD/Main/LWX/06_HaloWeight.lean`: character `x ↦ x²·κ_{T₀}(x)` on
   `haloUnits`, column `(cz+d)²·κ_{T₀}(d)·∑ C(s,m)(c/d)^m z^m`, radius `‖T₀‖√p`, on the sub-annulus
   `p⁻¹ < ‖T₀‖`, `‖T₀‖² < p⁻¹`).  With `heckeCharPowerSeries_eq_of_reps`, [LWX, Prop 2.17] at
   `m = 1` (`PhD/Main/LWX/07_Seam.lean`, `specCharSeries_ofCerts_eq_heckeCharPowerSeries`) is the
   specialisation half of the family: `Char(P)(T₀) = det(1 − X·U_p)` on `S^D_{κ_{T₀}}(U)`, and
   `PhD/Main/LWX/08_Quaternionic.lean` reads it on `D/ℚ` with the spectral interpretation
   (`evalT_specCharSeries_eq_zero_iff`).
4. **Slope theory at general weight** — DONE 2026-08-20 (`Weight/Slopes.lean`); what is still open
   on this front is the *exact*-slope statement (the fork's unit-minor equality) at a general
   weight, i.e. a hypothesis under which the bound of `isBelow_newtonPolygon_heckeCharPowerSeries`
   is attained.
5. **Housekeeping.**  The ρ-saturation theorem behind `restrictRadius`; the ~35 pre-existing
   `runLinter` findings in the TateFredholm core; `Fact`-packaging of `hU`/`hη`/finiteness for fixed
   quaternionic levels; independence of `heckeCharPowerSeriesPr` from the representatives (the
   non-neat analogue of `heckeCharPowerSeries_eq_of_reps`); a verso-blueprint for the QMF folder.
