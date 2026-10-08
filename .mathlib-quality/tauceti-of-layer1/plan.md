# Development Plan: overconvergent automorphic forms, Layer 1 (weights and weight modules)

Board: `.mathlib-quality/tauceti-of-layer1/` (named; always pass the path — the default board and
the sibling boards `tauceti-of-layer0/`, `tauceti-rag-layer2/`, `tauceti-co-layer0/` belong to other
runs). Planned 2026-10-06. Specification: `PhD/TauCeti/Roadmaps/OverconvergentForms/README.md`,
Layer 1 (§1.1–§1.4, lines 500–684) and its Examples. Code:
`PhD/TauCeti/Code/OverconvergentForms/Weight/`, module prefix
`PhD.TauCeti.Code.OverconvergentForms.Weight`, never importing `PhD.Main.*` (CI-gated). Build one
module at a time with `~/.elan/bin/lake build PhD.TauCeti.Code.OverconvergentForms.Weight.<Module>`;
never `lake build PhD`; one Lean process at a time (this Mac swap-thrashes with two). The chain root
`PhD/TauCeti.lean` is touched only by the last ticket, so the chain stays sorry-free while the
board is worked.

## Goal

The weight-`κ` action of the wild-level monoid on the Tate algebra, with its laws and bounds, the
algebraic and classical weights with the bridge to `Sym^n`, and the several-place product — stated
for a local field `L` (Buzzard's `F_𝔭`) embedded into the coefficient field `K` along a finite
family of isometric embeddings `ι` (Buzzard's `I_𝔭`), on `A := MvPowerSeries.Restricted K (1 : ι → ℝ)`
(the Tau Ceti Tate algebra `K⟨z_i : i ∈ ι⟩` of the rigid-analytic-geometry chain):

```lean
-- §1.1 (Weight/Level.lean): the norm-form level monoid, the level bounds, the adjugate dictionary
def SigmaNorm (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) : Submonoid (Matrix (Fin 2) (Fin 2) L)
structure LevelBounds (S : Submonoid (Matrix (Fin 2) (Fin 2) L)) (ρ : ℝ) : Prop
theorem LevelBounds.norm_apply_zero_zero_le_of_norm_det_le           -- ‖det γ‖ ≤ σ → ‖a‖ ≤ σ
theorem isUnit_sigmaNorm_iff : IsUnit g ↔ ‖(g : Matrix _ _ L).det‖ = 1
def adjugateEquiv : (SigmaNorm L ρ hρ0 hρ)ᵐᵒᵖ ≃* Sigma0 L ρ hρ0 hρ       -- right ⇔ left, convention 2

-- §1.2 (Weight/{Mobius,Action,Identity,Expansion}.lean): the engine and the public weight
structure WeightData (S : Type*) [Monoid S] (K ι : Type*) (ρ : ℝ)          -- multi-matrix + automorphy cocycle
def WeightData.kappaSlash (W) (γ : S) : Restricted K 1 →L[K] Restricted K 1  -- f ↦ j_γ · (f ∘ w_γ)
theorem WeightData.kappaSlash_mul : W.kappaSlash (δ * γ) = (W.kappaSlash γ).comp (W.kappaSlash δ)
theorem WeightData.norm_coeff_kappaSlash_monomial_le  -- ‖a_i‖ ≤ σ, ρ ≤ σ ⊢ ‖coeff t (z^r ∣ γ)‖ ≤ σ^|t|
theorem Embeddings.eq_zero_of_forall_evalPoint_eq_zero [CharZero K]       -- the identity theorem on e(𝒪_L)
structure ExpansionData (e : Embeddings L K ι) (S) (ρ) (n : (unitClosedBall L)ˣ →* Kˣ)
structure AnalyticWeight (e) (S) (ρ)                                      -- κ = (n, v, col)
theorem AnalyticWeight.autFactor_cocycle [CharZero K]                     -- DERIVED, never assumed
theorem AnalyticWeight.evalPoint_kappaSlash                                -- Buzzard's definition on points
theorem AnalyticWeight.kappaSlash_eq_of_n_eq                               -- depends only on (n, v)

-- §1.3 (Weight/{Algebraic,Classical}.lean)
def Embeddings.algWeight (e) (hb : LevelBounds S ρ) (n : ι → ℤ) (v : Lˣ →* Kˣ) (hv) : AnalyticWeight e S ρ
def SymPow (K ι) (n : ι → ℕ) : Submodule K (MvPolynomial (ι × Fin 2) K)    -- ⊗ᵢ Sym^{nᵢ}, homogeneous model
theorem finrank_symPow : Module.finrank K (SymPow K ι n) = ∏ i, (n i + 1)
def symPowAction : DistribMulAction (ι → Matrix (Fin 2) (Fin 2) K)ᵐᵒᵖ (SymPow K ι n) -- every matrix
theorem toTate_symAct    -- THE BRIDGE: dehomogenisation intertwines Sym^n with kappaSlash (algWeight n 1)
theorem AnalyticWeight.kappaSlash_smul_one                                -- scalars act by n(u) v(u²)

-- §1.4 (Weight/Action.lean): several places
def WeightData.pi (W : ∀ p, WeightData (S p) K (ι p) ρ) : WeightData (∀ p, S p) K (Σ p, ι p) ρ
def WeightData.comap (W : WeightData S K ι ρ) (φ : S' →* S) : WeightData S' K ι ρ
```

## Scope boundary — what this board does NOT plan (user decision requested)

**§1.2.7 (existence of expansion data) and the `u ↦ u^s` example are FLOOR-PENDING.** Both need
the `p`-adic-functional-analysis roadmap's §4.5 (`padicExp`, `padicLog`, the binomial series on a
Banach `ℚ_p`-algebra, the sharp radius `r_p`) and §§5.4–5.5 (analyticity level of a character of
`ℤ_p^×`, the expansion `expansion κ c d` with its geometric decay), and §1.2.7(b) additionally needs
Buzzard's Proposition 8.3 for a general `F_𝔭` (continuous homomorphisms `𝒪 → K` are the `K`-span of
the embeddings). None of this exists in `PhD/TauCeti/Code/PadicFunctionalAnalysis/` (Layer 0 only:
sums, unit balls, Tate rings, gauge norms, orthonormal families). The sorry-free originals live in
`PhD/Main/LWX/{00_PadicExpLog,01_Binomial,06_HaloWeight,08_HaloWeightH}.lean` (odd `p`, smaller disc)
and cannot be imported. The options are the same three recorded for the compact-operators board
(`.mathlib-quality/tauceti-co-layer0/DEFERRED.md`): (A) a floor slice on this board porting PFA
§4.5 + §5.4–5.5 under PFA's names; (B) develop PFA Layers 4–5 as their own boards first and add
§1.2.7 to this board afterwards by `/develop --continue`; (C) leave §1.2.7 to a later board.
**This plan assumes (B)/(C)**: every consumer of Layer 1 takes an `AnalyticWeight` (expansion data
as hypothesis), which is exactly the roadmap's convention 3, and §1.2.7 is the construction of such
data from a continuous character. Nothing else in Layer 1 depends on it (the algebraic and
classical-shape weights of §1.3 have data at every level by direct construction).

## References

| Tag | Reference | Used for |
|---|---|---|
| [RM] | `PhD/TauCeti/Roadmaps/OverconvergentForms/README.md`, Layer 1 (lines 500–684), conventions 2–5 and 10 (lines 171–273), Examples (lines 667–678) | the specification; every leaf is a numbered clause there |
| [Buz07] | K. Buzzard, *Eigenvarieties*, §8 (pp. 59–64: `B_r`, Lemma 8.1, Proposition 8.3 with proof), §9 (p. 68: `L_{n,v}`, `M_t`), §10 (pp. 71–73: `A_{κ,r}`, the action on points, norm-decreasing), §11 (pp. 73–75: classical forms are overconvergent, loading the character); `references/buzzard.txt` lines 2190–2470, 2620–2700, 2800–2960, 2990–3060 | the weight action, the thickening, the identity theorem's route, `L_{n,v}`, the nebentypus loading |
| [Jac03] | D. Jacobs, *Slopes of compact Hecke operators*, Definition 1.27 (p. 19), Proposition 2.6 (p. 29), Lemma 2.7 (p. 30); `references/jacobs_thesis.txt` (font-damaged: `κ`, `Σ`, `α`, `∣`, `ε` dropped; restored by hand in quotes) | the normalisation dictionary, the generating function as the matrix, the row-decay compactness criterion |
| [RAG] | Tau Ceti rigid-analytic-geometry chain, `PhD/TauCeti/Code/RigidAnalyticGeometry/{Restricted/*, TateAlgebra/{Basic,Eval}}.lean` (Layers 0–1, sorry-free) | the Tate algebra `Restricted K 1`, Gauss norm, `aeval`, `renameHom`, units, Weierstrass preparation |
| [PFA] | Tau Ceti `PhD/TauCeti/Code/PadicFunctionalAnalysis/{UnitBall,Tate,Sums}.lean` (Layer 0, sorry-free) | `Subring.unitClosedBall`, `NormedRing.closedBallIdeal`, `isUnit_iff_norm_eq_one`, `PseudoUniformizer` |
| [L0] | Layer 0 of this roadmap, `PhD/TauCeti/Code/OverconvergentForms/Level/Local.lean` (`LocalLevel.monoidM`, `iwahori`, `iwahoriOne`, `mem_monoidM_iff_norm`) | the dictionary §1.1.1 and §1.1.3 only |
| [SRC] | `PhD/Main/QMF/Weight/{00_Series,03_SlashAction,04_Char,04_AdicLevel,06_Algebraic}.lean`, `PhD/Main/QMF/Slash/01_Sigma0.lean`, `PhD/Main/TateFredholm/{00_Compose,05_GenFun,06_WeightGenFun}.lean` at `7586051` | **read-only reference for proof ideas**; never imported |
| [Mathlib] | pin `bbc4475e` (lean4 v4.33.0-rc1): `RingTheory/MvPowerSeries/{Restricted,Substitution,Evaluation,GaussNorm}`, `RingTheory/MvPolynomial/WeightedHomogeneous`, `LinearAlgebra/Matrix/{Adjugate,GeneralLinearGroup/Defs,ToLinearEquiv}`, `Algebra/Polynomial/Roots`, `LinearAlgebra/LinearIndependent/Basic` (`linearIndependent_monoidHom`), `Data/Finsupp/Weight` (`degree`), `Data/Fintype/Option` (`Finite.induction_empty_option`) | library inputs; every name below was checked by `grep` against the pin and is re-checked by elaboration of the skeleton |

## Mathlib / Tau Ceti inventory

| Concept | Status at the pin | Our action |
|---|---|---|
| Tate algebra `K⟨z_i⟩` as a Banach `K`-algebra | **not Mathlib**; [RAG] `MvPowerSeries.Restricted K (1 : ι → ℝ)`: `NormedCommRing`, `NormedAlgebra K`, `NormMulClass`, `IsUltrametricDist`, `CompleteSpace`, `NormOneClass`, `C`, `X`, `monomial`, `norm_coeff_le`, `exists_norm_coeff_eq`, `norm_le_iff_forall_norm_coeff_le`, `hasSum_monomial`, `tendsto_norm_coeff_cofinite` | USE (decision D1) |
| Substitution / evaluation of restricted series | [RAG] `Restricted.aeval c x hx : Restricted K c →ₐ[K] B` for `‖x i‖ ≤ c i`, `norm_aeval_le`, `continuous_aeval`, `aeval_X`, `aeval_toRestricted`, `algHom_ext_of_continuous`, `ringHom_ext_of_continuous`; `renameHom`, `renameEquiv`, `norm_renameEquiv`; `sumEquiv` | USE; PROVE `aeval_aeval` (composition) and `coeff_renameHom` (seam lemmas, namespace `MvPowerSeries.Restricted`) |
| Units of the Tate algebra | [RAG] `Restricted.isUnit_of_norm_lt_norm_constantCoeff`, `constantCoeff`; Mathlib `Ring.inverse`, `NormedRing.inverse_one_sub`, `tsum_geometric_of_norm_lt_one` | USE for `lin γ i` |
| Identity theorem (Strassmann) | **absent** everywhere: [RAG] `MaxModulus.eq_zero_of_forall_mem` needs vanishing at *every* maximal ideal; PFA §4.1.5 owns it but is not built | PROVE (API gap AG1, `Weight/Identity.lean`): from [RAG] `weierstrassPreparation_exists_of_isMulDistinguished` + `exists_greatest_achievesGaussNorm` + Mathlib `Polynomial.eq_zero_of_infinite_isRoot` |
| `C₀(ℕ^ι, K)` model space, `matrixCoeff`, kernels (PFA §2.1, §2.6; CO §0.3.1) | **absent** from the chain | NOT USED (decision D1); the matrix of the action is the coefficient array `coeff t (z^r ∣ γ)` |
| `p`-adic exp/log/binomial, characters of `ℤ_p^×` (PFA §4.5, §5.4–5.5) | **absent** | FLOOR-PENDING (§1.2.7, `u^s` example) |
| Unit ball of a normed field, closed-ball ideals | [PFA] `Subring.unitClosedBall L`, `NormedRing.closedBallIdeal L ε`, `NormedRing.isUnit_iff_norm_eq_one`, `Subring.norm_le_one` | USE for `𝒪_L`, `𝒪_L^×`, `𝒪/𝔭^α` |
| Uniformiser, discrete valuation | [PFA] `NormedRing.PseudoUniformizer L` + the hypothesis shape `∀ x ≠ 0, ∃ n : ℤ, ‖x‖ = ‖ϖ‖ ^ n` of `Rescale.lean` | USE for `extendUnits` (Buzzard's `v(ϖ) = 1`) |
| Adjugate, `GL`, `det` | `Matrix.adjugate_fin_two`, `adjugate_fin_two_of`, `adjugate_mul_distrib`, `det_adjugate`, `adjugate_adjugate`, `mul_adjugate`, `det_fin_two`, `GL`, `Matrix.GeneralLinearGroup.mkOfDetNeZero`, `exists_mulVec_eq_zero_iff` | USE |
| Multi-homogeneous polynomials (`⊗ Sym^{n_i}`) | `MvPolynomial.weightedHomogeneousSubmodule`, `weightedHomogeneousSubmodule_eq_finsupp_supported`, `IsWeightedHomogeneous`, `weightedHomogeneousSubmodule_mul`; **no** `IsWeightedHomogeneous.aeval` | USE; PROVE `IsWeightedHomogeneous.aeval` and the scaling lemma |
| Multi-indices | `Finsupp.degree` (an `AddMonoidHom`), `degree_eq_sum`, `degree_mapDomain`, `Finsupp.antidiagonal`, `MvPowerSeries.coeff_mul`, `sigmaFinsuppEquivPiFinsupp` | USE |
| Finite-type induction, Dedekind, infinite roots | `Finite.induction_empty_option`, `Equiv.optionEquivSumPUnit`, `linearIndependent_monoidHom`, `Polynomial.eq_zero_of_infinite_isRoot`, `Set.infinite_range_of_injective` | USE |
| Opposite actions, twisted actions | `MulOpposite`, `DistribMulAction.compHom`, `Module.End.applyModule`, `LinearMap.mkContinuous`, `ContinuousLinearMap.opNorm_le_bound` | USE |

## File structure (Tau Ceti home in each module docstring)

| File (`…/OverconvergentForms/Weight/`) | Roadmap | Imports | Content |
|---|---|---|---|
| `Level.lean` | §1.1.1–1.1.4 | Mathlib only | `SigmaNorm`, `LevelBounds`, determinant bound, units, `eta`, `SigmaOne`, `Sigma0`, the adjugate dictionary `adjugateEquiv` |
| `Dictionary.lean` | §1.1.1, §1.1.3 (seam with [L0]) | `Level/Local`, `Weight/Level` | `monoidM = SigmaNorm ‖ϖ‖^t`, `iwahori ⊆ SigmaNorm`, `iwahoriOne(ϖ^{2t}) ⊆ SigmaOne(‖ϖ‖^t)` |
| `Mobius.lean` | §1.2.1, §1.2.4 (bounds) | [RAG] `TateAlgebra/Eval`, `Restricted/Units` | multi-matrices, `MultiBounds`, `lin`, `num`, `linInv`, `mobius`, `mobiusSubst`, `RowBound`, Möbius composition, pointwise formula, `aeval_aeval` |
| `Identity.lean` | §1.2.3 (AG1, pure Tate algebra) | [RAG] `Restricted/PowerSeries/MulWeierstrassPrep`, `Restricted/Sum`, `Mobius` | Strassmann in one variable, slices, the several-variable identity theorem for product sets, `norm_det_le_one` |
| `Action.lean` | §1.2.4–1.2.6 (engine), §1.2.8 (twist), §1.4 | `Mobius`, [RAG] `Restricted/Sum` | `WeightData`, `kappaSlash`, laws, row bound, `kappaSlashAction`, `twist`, `comap`, `pi` |
| `Expansion.lean` | §1.2.2–1.2.3, §1.2.5–1.2.6, §1.2.8 | `Action`, `Identity`, `Level`, [PFA] `UnitBall` | `Embeddings` (+ `self`, `ofAlgHom`), the identity theorem on `e(𝒪_L)`, `ExpansionData`, uniqueness, `AnalyticWeight`, derived cocycle, `toWeightData`, public `kappaSlash` API, pointwise formula, `restrict`, `continuous_n` |
| `Algebraic.lean` | §1.3.1, §1.3.4, §1.3.5 | `Expansion`, [PFA] `Tate` | `algChar`, `extendUnits`, `algExpansionData`, `algWeight`, `lowerRightResidue`, `twistResidue`, `classicalShape`, scalars |
| `Classical.lean` | §1.3.2–1.3.3 | `Algebraic` | `SymPow`, `symAct`, `symPowAction`, `classicalAction`, `finrank_symPow`, `toTate`, `polySubmodule`, `toTateEquiv`, the bridge |
| `Examples.lean` | Examples | everything above | the acceptance examples of Layer 1 (minus the FLOOR-PENDING `u^s`) |

The chain root `PhD/TauCeti.lean` gets `import PhD.TauCeti.Code.OverconvergentForms.Weight.Examples`
at the final ticket. `Weight/Identity.lean`'s general lemmas are in the namespaces
`MvPowerSeries.Restricted` / `PowerSeries.Restricted` / `Matrix` (they are PFA §4.1.5's seam, like
Layer 0's `Adelic/FiniteAdeles.lean` was the global-number-fields seam); everything else is in the
namespace `AutomorphicForm` (decision D8).

## Dependency graph

```text
Level ──→ Dictionary                     (Layer 0 seam, leaf)
Mobius ──→ Action ──┐
Mobius ──→ Identity ├──→ Expansion ──→ Algebraic ──→ Classical ──→ Examples
Level ──────────────┘
```

## Binding decisions (with reasons; an implementor who does not know them reintroduces the problem)

**D1 — The carrier is the Tate algebra `MvPowerSeries.Restricted K (1 : ι → ℝ)`, not `C₀`.** The
roadmap writes `A = K⟨z_i⟩ = c₀(ℕ^{I_𝔭}, K)` and defines the action "by its kernel" (convention 5,
CO §0.3.1). Neither the model space `C₀` with its operator calculus (PFA §2.1, §2.6) nor the kernel
presentation (CO §0.3.1) exists in the Tau Ceti chain, while the Tate algebra with Gauss norm and
substitution does ([RAG]). The action is therefore *defined* as the substitution operator
`f ↦ j_κ(γ) · (f ∘ w_γ)` (CO §0.3.2's "substitution operator", whose kernel is `j(x)/(1 − w(x) y)`),
and "the matrix is the coefficient array of the kernel" is the theorem `kappaSlash_monomial`:
`z^r ∣ γ = j_κ(γ) ∏ w_i^{r_i}`, with `coeff_kappaSlash_monomial` giving the array. Jacobs's
Proposition 2.6 then holds by this theorem rather than "by construction"; the content (operator,
array, bounds, action laws) is identical. The isometry `Restricted K 1 ≃ₗᵢ C₀(ι →₀ ℕ, K)` is PFA
§4.1.1 and is Layer 2's to cross (the block model `c₀(ι × ℕ^I, K)`), not Layer 1's.

**D2 — The series algebra is developed for multi-matrices `γ : ι → Matrix (Fin 2) (Fin 2) K`.** The
single place feeds `fun i => (e.emb i).mapMatrix γ` (Buzzard's `γ_i := i(γ)`), the several places of
§1.4 feed the sigma type `Σ p, ι p` with `γ ⟨p, i⟩ := e_{p,i}(γ_p)`, and the classical module's
`GL₂`-action is the same multi-matrix acting on `MvPolynomial (ι × Fin 2) K`. Nothing is proved
twice for one and several places.

**D3 — Engine record `WeightData`, public record `AnalyticWeight`.** `WeightData S K ι ρ` carries a
monoid hom `S →* (ι → M₂(K))` with level bounds and an automorphy factor `j : S → A` with
`RowBound ρ (j γ)`, `j 1 = 1` and the cocycle `j (δγ) = j γ · (j δ ∘ w_γ)` as *fields*; the action
`kappaSlash`, its laws, its norm and row bounds, `twist`, `comap` and `pi` are proved once from it.
`AnalyticWeight e S ρ` is the roadmap's `κ = (n, v, col)`; its `toWeightData` *proves* the cocycle
from multiplicativity of `n`, `v` and the identity theorem (`autFactor_cocycle`), and the public
`AnalyticWeight.kappaSlash` is the engine's. This is the only place a character is analysed
(roadmap §1.2.6 ⚠); no character-specific cocycle proof exists anywhere (the algebraic and
classical-shape weights get theirs from `autFactor_cocycle` too). [SRC]'s `WeightSeries`/`AnalyticWeight`
split is the same architecture.

**D4 — `v : Lˣ →* Kˣ` with `‖v x‖ = 1`, and Buzzard's normalisation is a construction.** Buzzard's `v`
is a character of `𝒪^×` extended by `v(ϖ) := 1`; the roadmap repeats this. The extension needs a
uniformiser and a discrete valuation, which are properties of `L`, not of the weight; carrying them
in `AnalyticWeight` would make every weight depend on a choice of `ϖ`. The structure therefore
carries any norm-one character `v` of `Lˣ` (strictly more general: `v(ϖ)` may be any norm-one
scalar), and `extendUnits ϖ hϖ v₀` builds Buzzard's extension from `v₀ : 𝒪^× →* K^×` and a
`PseudoUniformizer` with `‖L^×‖ = ‖ϖ‖^ℤ`. The norm-one condition is what makes the action
norm-decreasing (Buzzard p. 71: "the supremum semi-norm of every element in the image of `n` or `v`
is `1`"); Buzzard's *literal* `det^v = ∏ i(det γ)^{v_i}` of §9 has `‖det η‖^{Σ v_i} ≠ 1` and is
**not** admissible — see erratum E3.

**D5 — `n` is a character of `(Subring.unitClosedBall L)ˣ`; continuity is a theorem, not a field.**
The roadmap says "continuous character"; nothing in Layer 1 consumes continuity, and it follows from
the expansion data whenever the level contains a lower unipotent `((1 0), (c 1))`, `c ≠ 0`
(`continuous_n_of_lowerUnip_mem`). A redundant field is a mathlib defect.

**D6 — The identity theorem is stated with a Prop field `exists_integralBasis` on `Embeddings`.**
Buzzard's proof of Proposition 8.3 uses a `ℤ_p`-basis `e_1, …, e_d` of `𝒪` and "linear independence of
distinct field embeddings" to get the invertible matrix `(i(e_β))`, then "a determinant calculation"
to see that `e(𝒪)` contains a small polydisc. The theorem `eq_zero_of_forall_evalPoint_eq_zero`
needs exactly: integral elements `b : ι → L` with `det (e_i (b_β)) ≠ 0`, and `[CharZero K]` (so that
`ℕ ⊆ 𝒪_K` is an infinite set on which the one-variable theorem applies). `Embeddings` carries this
as a Prop, `Embeddings.self K : Embeddings K K Unit` discharges it trivially (the `F = ℚ` case of
every acceptance example), and `Embeddings.ofAlgHom` discharges it for `[L : k] = |ι|` embeddings
over a nontrivially normed base field `k` by Dedekind's lemma (`linearIndependent_monoidHom`) — the
general-`F_𝔭` case. No `ℤ_p` appears: the roadmap's "`ℤ_p`-basis" is replaced by "integral basis
whose embedding matrix is invertible", which is what the proof uses.

**D7 — `ExpansionData` has two analytic fields, not three.** The roadmap asks for
`‖coeff_m col‖ ≤ ρ^{|m|}` **and** `‖coeff_m col‖ ρ^{−|m|} → 0`, adding "(for `ρ < 1` the first
implies the second)". The implication is false (`coeff_m = ρ^m` has ratio `1`), and the second
condition is consumed nowhere in Layers 1–5 (the action's norm uses `≤ 1`, restrictedness at
radius `1` and the row bounds use `≤ ρ^{|m|}`). It is dropped (erratum E1).

**D8 — Namespace `AutomorphicForm`.** Convention 10 puts the abstract layer in `AutomorphicForm`,
"the weights in `AnalyticWeight`", and nothing in the root namespace. `AnalyticWeight` is the
structure `AutomorphicForm.AnalyticWeight` with its API under it; `SigmaNorm`, `LevelBounds`,
`ExpansionData`, `WeightData`, `SymPow`, `Embeddings` are siblings in `AutomorphicForm`. The pure
Tate-algebra lemmas of `Identity.lean` and `aeval_aeval`, `coeff_renameHom` are in
`MvPowerSeries.Restricted` / `PowerSeries.Restricted`; two `2 × 2` adjugate facts and the ultrametric
determinant bound are in `Matrix`.

**D9 — `SigmaNorm L ρ hρ0 hρ` takes its two real hypotheses explicitly** (`1 ∈` needs `0 ≤ ρ`,
closure under products needs `ρ < 1`), as [L0]'s `monoidM K γ hγ` and [SRC] do; `LevelBounds S ρ`
bundles them with the four conditions (integral, `‖c‖ ≤ ρ`, `‖d‖ = 1`, `det ≠ 0`), so that every
theorem about a level takes one hypothesis `hb : LevelBounds S ρ`. `LevelBounds S ρ ↔ S ≤ SigmaNorm`
is the pair `LevelBounds.le_sigmaNorm` / `LevelBounds.of_le`.

**D10 — `Sym^n` is the homogeneous model.** `SymPow K ι n := weightedHomogeneousSubmodule K w n` in
`MvPolynomial (ι × Fin 2) K` with `w (i, _) = Pi.single i 1`, and the action of *every* multi-matrix
is `aeval` of `X_{(i,j)} ↦ Σ_k γ_i j k X_{(i,k)}` (i.e. `(X_i, Y_i) ↦ (a X + b Y, c X + d Y)`), a right
action by composition of `aeval`s with no analysis and no determinant condition. The roadmap's primary
realisation "polynomials in `A` of degree `≤ n_i` in each `z_i`" is `polySubmodule K ι n`, the image
of `SymPow` under the dehomogenisation `toTate` (`X_i ↦ z_i`, `Y_i ↦ 1`), and the roadmap's formula
`∏ (c_i z_i + d_i)^{n_i} f(w_γ z)` is the bridge theorem `toTate_symAct`: for `γ` in the level,
dehomogenisation intertwines `symAct` with `kappaSlash (algWeight n 1)`. The `v`-part is a twist by
the character `γ ↦ v(det γ)` on both sides (`classicalAction`, `WeightData.twist`), never a second
formula. Reason: `f(w_γ)` is not a restricted series for `γ ∉ Σ`, so the `GL₂`-action of §1.3.2 can
only live on the homogeneous model; `aeval` makes its laws free.

**D11 — Row bounds are the predicate `RowBound σ f := ∀ t, ‖coeff t f‖ ≤ σ ^ t.degree`.** It is
closed under products (ultrametric convolution with `degree` additive), holds for `w_{γ,i}` when
`‖a_i‖ ≤ σ` and `ρ ≤ σ` (the degree-`0` coefficient `b/d` only needs `≤ 1 = σ^0`), and for `col` by
the expansion field; the row bound of §1.2.4 is `RowBound.mul` applied to `j_κ(γ) ∏ w_i^{r_i}`. Layer
3 consumes it as "`‖matrixCoeff ε_{ij} m r‖ ≤ σ^{|m|}`" (Jacobs's Lemma 2.7).

**D12 — Right actions are `DistribMulAction Sᵐᵒᵖ A` with `SMulCommClass K Sᵐᵒᵖ A`, built by
`DistribMulAction.compHom` from the monoid hom `Sᵐᵒᵖ →* Module.End K A`, as *definitions* (several
weights act on the same `A`), never instances. `kappaSlash_mul : kappaSlash (δ * γ) =
(kappaSlash γ).comp (kappaSlash δ)` is the statement `(f ∣ δ) ∣ γ = f ∣ (δγ)` in the sources' order.

## Roadmap errata and looseness found while planning (recorded, not edited)

- **E1** §1.2.2: "`‖coeff_m col(c,d)‖ ρ^{−|m|} → 0` (for `ρ < 1` the first implies the second)" — the
  implication is false; the condition is unused (D7). Also "`ρ = 1` is Buzzard's minimal good `t`" is
  unreachable: `SigmaNorm` requires `ρ < 1` (§1.1.1) and Buzzard's `r|π^t|` is `< 1` for `t ≥ 1`.
- **E2** §1.2.3: the identity theorem's `ℤ_p`-basis is more than the proof uses (D6).
- **E3** §1.3.1–1.3.3: with `v : 𝒪^× → K^×` extended by `v(ϖ) = 1` (§1.2.2) the classical action
  `∏ i(det γ)^{v_i}` of §1.3.2 (Buzzard §9, literal) and the weight action of `algWeight (n, v)`
  agree only on `det γ ∈ 𝒪^×`; on `η` they differ by `∏ i(ϖ)^{v_i}`. Buzzard's §11 "`M_1`-equivariant
  inclusion `L_{n,v} → A_{κ,r}`" has the same gap. This board states both sides with the *same*
  normalised character (`v ∘ det` as a twist); the literal `det^v` is not norm-one on `η` and is not
  admissible as a weight at all (D4). The user may want to fix the roadmap's §1.3.2 formula.
- **E4** §1.3.1: "the product of `i(d)^{n_i}(1 + (i(c)/i(d)) z_i)^{n_i}` with the binomial series of
  a negative integer exponent, whose coefficients are integers" — the formalisation uses the
  geometric series `linInv` (the inverse of `c z + d`) and `RowBound.pow`; no binomial coefficients
  are needed. Same leaves, less machinery.
- **E5** §1.3.4 asks for `n` algebraic; the nebentypus twist `twistResidue` works for every `n` with
  expansion data (the proof never uses algebraicity). Stated in general; `classicalShape` is the
  algebraic instance.
- **E6** §1.1.1: `LevelBounds Σ ρ` "its elements satisfy the four conditions" — [SRC]'s `LevelBounds`
  omitted `det ≠ 0`; this board includes it (needed for `detChar`).

## Generality decisions

- `L` is any `[NormedField L] [IsUltrametricDist L]` (no completeness, no discreteness) for §1.1,
  §1.2, §1.3.4; `K` is `[NormedField K] [IsUltrametricDist K] [CompleteSpace K]` (completeness for
  `aeval` and the Banach-algebra structure of `A`); `[CharZero K]` only where the identity theorem is
  used (the cocycle, uniqueness, scalars, the bridge). `ι` is `[Fintype ι] [DecidableEq ι]` where
  determinants or products over `ι` occur, `[Finite ι]` elsewhere.
- The engine `WeightData` is over an arbitrary monoid `S` (not a submonoid of matrices) so that `pi`
  and `comap` are instances of one construction.
- `SymPow`'s action is of the full multiplicative monoid `ι → Matrix (Fin 2) (Fin 2) K` (no `det ≠ 0`,
  no level); the determinant twist is stated for `ι → GL (Fin 2) K` and, through `e`, for `GL (Fin 2) L`.
- Universe polymorphism: `L K ι : Type*` throughout; `Finite.induction_empty_option` forces the
  identity theorem's induction to run on `Type u` with transport along `renameEquiv`.

## Milestones

- **M1** `WeightData.kappaSlash_mul` + `WeightData.norm_coeff_kappaSlash_monomial_le` (§1.2.5–6, §1.2.4
  at the engine level).
- **M2** `Embeddings.eq_zero_of_forall_evalPoint_eq_zero` (§1.2.3, AG1 closed).
- **M3** `AnalyticWeight.autFactor_cocycle` and `AnalyticWeight.kappaSlash_eq_of_n_eq` (§1.2.6, §1.2.3):
  the weight action is a right action depending only on `(n, v)`.
- **M4** `toTate_symAct` + `finrank_symPow` (§1.3.2–3, the bridge).
- **M5** `WeightData.pi` with its row bound (§1.4.1) and the chain root importing `Weight/Examples`.

## Ticket statistics (see `tickets.md`)

See the Summary block of `tickets.md`. Cleanup cadence: one `/cleanup` per three proof tickets per
file, a final `/cleanup` per file, `CLEANUP-ALL` before each milestone ticket, `CLEANUP-FINAL` last.
