# Development Plan: p-adic functional analysis, Layer 2 (the model space and orthonormal bases)

Board: `.mathlib-quality/tauceti-pfa-layer2/` (named; the default board path belongs to another
project, and the other `tauceti-*` boards are parallel boards — never touch them or a sentinel that
names another board). Specification: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`,
Layer 2 (§2.1–§2.7) and its Examples, README lines 585–758. Code:
`PhD/TauCeti/Code/PadicFunctionalAnalysis/{ModelSpace/*, Orthogonal, ONable, Serre, CountableType,
Unitriangular}.lean`, module prefix `PhD.TauCeti.Code.PadicFunctionalAnalysis`, importing **Mathlib,
Layer 0, Layer 1 and the Newton-polygons `AddVal` files only** — never `PhD.Main.*` (CI-gated
two-chain rule). Planned 2026-10-06, on top of the completed Layer 1 board (`tauceti-pfa-layer1`,
2026-10-06). Status: **APPROVED 2026-10-06; T001 executed at plan review (shared file + README errata applied); T002 next.**

## Goal

The model space `C₀(I, R)` on a discrete `I` with the instances Mathlib lacks, its universal
property, reindexing and block decompositions; orthogonal, `t`-orthogonal and orthonormal families;
orthonormalisable modules (`IsONable`), potentially orthonormalisable modules and property (Pr) with
the lifting characterisation; Serre's theorem in ring and field form and the invariance of the index;
Banach spaces of countable type (Schneider §10); the dual `ℓ^∞`; matrices of operators, truncations,
closedness of finitely generated submodules over Noetherian rings; and the unitriangular-perturbation
criterion. `R` is a nonarchimedean normed ring (`[NormedRing R] [IsUltrametricDist R]`), Banach–Tate
(`[CompleteSpace R] [NormedRing.IsTate R]`) where the operator norm of Layer 1 is used.

```lean
-- §2.1  (ModelSpace/Basic, Universal, Reindex, Map)
instance ZeroAtInftyContinuousMap.instIsUltrametricDist [IsUltrametricDist E] : IsUltrametricDist C₀(I, E)
instance ZeroAtInftyContinuousMap.instIsBoundedSMul [IsBoundedSMul R E] : IsBoundedSMul R C₀(I, E)
def ZeroAtInftyContinuousMap.single (i : I) (x : E) : C₀(I, E)
theorem ZeroAtInftyContinuousMap.hasSum_smul_single_one (f : C₀(I, R)) : HasSum (fun i ↦ f i • single i 1) f
noncomputable def ZeroAtInftyContinuousMap.ofBounded (R) (m : I → M) (hm : ∃ C, ∀ i, ‖m i‖ ≤ C) : C₀(I, R) →L[R] M
theorem ZeroAtInftyContinuousMap.norm_ofBounded [NormOneClass R] : ‖ofBounded R m hm‖ = ⨆ i, ‖m i‖
theorem ZeroAtInftyContinuousMap.eq_ofBounded [IsTate R] (u : C₀(I, R) →L[R] M) : u = ofBounded R (fun i ↦ u (single i 1)) _
noncomputable def ZeroAtInftyContinuousMap.reindex (e : I ≃ J) : C₀(I, E) ≃ₗᵢ[R] C₀(J, E)   -- + sumEquiv, prodEquiv, piEquiv, blockEquiv
noncomputable def ZeroAtInftyContinuousMap.map (φ : R →+* S) (C) (hφ) : C₀(I, R) →SL[φ] C₀(I, S)
-- §2.2  (Orthonormal (shared, redefined in T001), Orthogonal, ONable)
def IsOrthonormalFamily R e := (∀ i, ‖e i‖ = 1) ∧ ∀ s a, ‖∑ i ∈ s, a i • e i‖₊ = s.sup fun i ↦ ‖a i‖₊   -- T001 (E19)
def IsOrthogonalFamily R e := ∀ s a, ‖∑ i ∈ s, a i • e i‖₊ = s.sup fun i ↦ ‖a i • e i‖₊
def IsTOrthogonalFamily R t e := ∀ s a, ∀ i ∈ s, t * ‖a i • e i‖ ≤ ‖∑ j ∈ s, a j • e j‖
def Module.IsONable (R : Type u) (M : Type v) := ∃ (I : Type v) (_ : TopologicalSpace I) (_ : DiscreteTopology I), Nonempty (M ≃ₗᵢ[R] C₀(I, R))
def Module.IsPotentiallyONable R M := ∃ I …, Nonempty (M ≃L[R] C₀(I, R))
def Module.HasPr R M := ∃ I … (ι : M →L[R] C₀(I, R)) (π : C₀(I, R) →L[R] M), π.comp ι = id
theorem Module.isONable_iff_exists_isOrthonormalBasis : IsONable R M ↔ ∃ (I : Type v) (e : I → M), IsOrthonormalBasis R e   -- MILESTONE M1
theorem Module.hasPr_iff_forall_exists_lift : HasPr R M ↔ ∀ N N' …, Surjective u → ∀ v, ∃ w, u.comp w = v   -- Bellaïche II.1.19
theorem Module.HasPr.projective [Module.Finite R M] : Module.Projective R M                                   -- Bellaïche II.1.20
-- §2.3  (Serre)
theorem PseudoUniformizer.isOrthonormalBasis_iff_residueFamily (hR hM) (he : ∀ i, ‖e i‖ ≤ 1) :
    IsOrthonormalBasis R e ↔ LinearIndependent ϖ.ResidueRing (ϖ.residueFamily e he) ∧ span … = ⊤   -- Bellaïche II.1.12
theorem PseudoUniformizer.isONable_iff_free_residueModule (hR hM) : IsONable R M ↔ Module.Free ϖ.ResidueRing (ϖ.ResidueModule M)
theorem Module.isPotentiallyONable_of_isRankOneDiscrete : IsPotentiallyONable K M                             -- MILESTONE M2
theorem Module.isONable_iff_forall_exists_norm_eq : IsONable K M ↔ ∀ m : M, ∃ k : K, ‖m‖ = ‖k‖
theorem ZeroAtInftyContinuousMap.nonempty_continuousLinearEquiv_iff : Nonempty (C₀(I, K) ≃L[K] C₀(J, K)) ↔ Nonempty (I ≃ J)
-- §2.4  (CountableType)
theorem Module.IsCountableType.exists_continuousLinearEquiv_nat (hV) (hfin) : Nonempty (V ≃L[K] C₀(ℕ, K))   -- Schneider 10.4, MILESTONE M3
theorem Submodule.closedComplemented_of_isCountableType (hV) (U) [IsClosed U] : U.ClosedComplemented      -- Schneider 10.5
-- §2.5  (ModelSpace/Dual)
noncomputable def ZeroAtInftyContinuousMap.dualEquivLp (R I) [IsTate R] : (C₀(I, R) →L[R] R) ≃ₗᵢ[R] lp (fun _ : I ↦ R) ∞
-- §2.6  (ModelSpace/Matrix, Truncation, Closed)
noncomputable def ZeroAtInftyContinuousMap.matrixCoeff (u : C₀(J, R) →L[R] C₀(I, R)) (i : I) (j : J) : R := u (single j 1) i
theorem ZeroAtInftyContinuousMap.opNorm_eq_iSup_matrixCoeff : ‖u‖ = ⨆ p : I × J, ‖matrixCoeff u p.1 p.2‖
noncomputable def ZeroAtInftyContinuousMap.truncation (S : Set I) : C₀(I, R) →L[R] C₀(I, R)
theorem ZeroAtInftyContinuousMap.exists_truncation_near (P) (hP : P.FG) (hclosed) : ∃ S : Finset I, ∀ p ∈ P, ‖truncation S p - p‖ ≤ ε * ‖p‖
theorem ZeroAtInftyContinuousMap.isClosed_of_fg [IsNoetherianRing R] (P) (hP : P.FG) : IsClosed (P : Set C₀(I, R))   -- MILESTONE M4
-- §2.7  (Unitriangular)
structure ZeroAtInftyContinuousMap.IsUnitriangularPerturbation (a : ℕ → ℕ → R) (q : ℝ) : Prop
noncomputable def IsUnitriangularPerturbation.linearIsometryEquiv (ha) : C₀(ℕ, R) ≃ₗᵢ[R] C₀(ℕ, R)       -- MILESTONE M5
theorem IsOrthonormalBasis.of_isUnitriangularPerturbation (he) (ha) (hf : ∀ j, HasSum (fun i ↦ a i j • e i) (f j)) : IsOrthonormalBasis R f
```

plus the roadmap's worked examples (`ModelSpace/Examples.lean`): the canonical basis and the dual of
`C₀(ℕ, ℚ_p)`, `C(ℤ_p, ℚ_p)` orthonormalisable by Serre, the doubled norm on `ℚ_p` (odd `p`) and on
`ℂ_p` (value-group fact as a hypothesis, E23), the shift, the two unitriangular perturbations, and
the §2.6.4 counterexample over `ℓ^∞(ℕ, ℚ_p)`.

## References

| Tag | Reference | Used for |
|---|---|---|
| [RM] | `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, Layer 2 (README lines 585–758), conventions 3–5, 7, 8, 12 (lines 158–270) | the specification; every leaf discharges a numbered clause |
| [Sch] | Schneider, *Nonarchimedean Functional Analysis* — `references/schneider.txt`: Lemma 1.4 l. 291–312, Lemma 1.6 l. 315–321, §3 `c₀`/`ℓ^∞` and the dual example l. 495–520 and l. 617–700, universal property of `c₀(X)` l. 2905–2947, Prop 10.1 l. 2948–3001, Remark 10.2 l. 3003–3006, Lemma 10.3 l. 3007–3028, Prop 10.4 l. 3029–3103, complemented subspaces and Prop 10.5 l. 3104–3140, Prop 9.2 (Hahn–Banach) l. 2486–2521, Cor 9.5 l. 2542–2563 | §2.1.3, §2.3.3–2.3.4, §2.4, §2.5 |
| [Bel] | Bellaïche, *The Eigenbook*, draft §II.1 — `references/bellaiche.txt`: Def II.1.5–Ex II.1.7 l. 2010–2030, Lemma II.1.8 l. 2043–2056, Hyp II.1.11 l. 2074–2081, Lemma II.1.12 l. 2082–2105, Thm II.1.13 l. 2108–2114, (Pr) + Exercise II.1.19 + Prop II.1.20 l. 2223–2235 | §2.2 definitions, §2.3.1–2.3.3, §2.2.4, §2.6.4 (II.1.8 = Lemma 3.1.12 in the published numbering) |
| [Buz07] | Buzzard, *Eigenvarieties*, §2 — `references/buzzard.txt`: ONable l. 222–236, `c_A(I)` and the universal property l. 238–254, matrices l. 272–300, Lemma 2.3 l. 335–392 | §2.1.3, §2.6.1, §2.6.5 |
| [JN] | Johansson–Newton, arXiv:1604.07739v4, §2.1 — `references/jn.txt`: Def 2.1.5 l. 532–545, Prop 2.1.8 l. 655–660 | convention 4, §2.6.6 |
| [Col] | Colmez, *Fonctions d'une variable p-adique* — `references/colmez.txt`: Déf 1.1.3 l. 95–112, Prop 1.1.5 + proof l. 113–172 | §2.2.2, §2.3.1, §2.7.3 |
| [Lud] | Ludwig, arXiv:2407.18073 — `references/ludwig.txt`: Lemma 2.26 l. 371–395 | §2.6.5 |
| [Mathlib] | pinned Mathlib (`lean4 v4.33.0-rc1`): `Topology/ContinuousMap/ZeroAtInfty.lean`, `Analysis/Normed/Lp/lpSpace.lean`, `Topology/Algebra/Module/Complement.lean`, `RingTheory/Valuation/Discrete/Basic.lean`, `Topology/Algebra/Valued/NormedValued.lean`, `Algebra/Module/Projective.lean`, `SetTheory/Cardinal/Arithmetic.lean`, `Topology/Algebra/Module/FiniteDimension.lean`, `Analysis/Normed/Group/Quotient.lean` | the inventory below |
| [L0] | Layer 0, `PhD/TauCeti/Code/PadicFunctionalAnalysis/{Tate,Multiplicative,Module,UnitBall,Sums,Residue,Rescale,Orthonormal}.lean` | `PseudoUniformizer`, `IsTate`, `IsMultiplicative`, `existsUnique_zpow_norm_smul_mem_Ioc`, `Filter.Tendsto.exists_norm_eq_iSup`, `tendsto_cofinite_prod_of_norm_le_mul`, `ResidueRing`/`ResidueModule`, `mem_ideal_smul_top_iff_norm_lt_one`, `ideal_eq_openUnitBallIdeal`, `maximalIdeal_unitClosedBall`, `Rescaled`, `isBoundedSMul_rescaled`, `norm_toRescaled*`, `IsOrthonormalBasis.exists_hasSum` |
| [L1] | Layer 1, `PhD/TauCeti/Code/PadicFunctionalAnalysis/Operator/{Norm,Banach,OpenMapping,Pi,Finite,Examples}.lean` | the scoped operator norm, `le_opNorm`, `opNorm_le_bound`, `le_opNorm_of_bound`, `exists_bound`, `exists_preimage_norm_le`, `continuousLinearEquivOfBijective`, `quotKerEquivRangeL`, `continuous_pi`, `exists_bound_of_finite`, `Submodule.isClosed_of_isNoetherianRing`, `lp.instIsUltrametricDist` |
| [NP] | `PhD/TauCeti/Code/NewtonPolygons/AddVal/{Discrete,Padic}.lean` | `IsRankOneDiscrete.exists_zpow_generator_eq`, `Padic.isRankOneDiscrete_valuation` |
| [RAG] | `PhD/TauCeti/Code/RigidAnalyticGeometry/{OrthonormalLift,TateAlgebra/StrictlyClosed}.lean` (in-chain consumers of `Orthonormal.lean`) | the three proof sites repaired by T001 |
| [SRC] | `PhD/Main/TateFredholm/{03_ModelSpace,04_Matrix,05_Noetherian,06_Pr,06_Unitriangular,07_Residue,08_BaseChange,06_BlockOp}.lean` at `747bb77` | **read-only reference for proof ideas** (sorry-free, different presentation: `cSpace`, field scalars in 06/07); never imported |

## Mathlib inventory (every name verified by elaboration: `scratch/names.lean` … `names5.lean`, ≈ 420 names)

| Concept | Mathlib status | Our action |
|---|---|---|
| `C₀(I, E)`: `NormedAddCommGroup`, `Module R` (needs `ContinuousConstSMul R E`), `CompleteSpace` (needs `[CompleteSpace E]`), `NormedSpace 𝕜`, `toBCF`, `isometry_toBCF`, `norm_toBCF_eq_norm`, `comp (g : β →co γ)`, `zero_at_infty'`, `cocompact_eq_cofinite`, `continuous_of_discreteTopology` | present | USE; our instances `IsUltrametricDist`, `IsBoundedSMul R`, `NormSMulClass R` are **absent** (`#synth` fails) — §2.1.1 |
| `BoundedContinuousFunction.{norm_eq_iSup_norm, norm_coe_le_norm, norm_le, instIsBoundedSMul, evalCLM}` | present | USE through `toBCF` |
| `lp (fun _ : I ↦ R) ∞`: `Module 𝕜` + `IsBoundedSMul 𝕜` over a `NormedRing`, `norm_eq_ciSup`, `isLUB_norm`, `norm_apply_le_norm`, `norm_le_of_forall_le`, `single`, `single_apply`, `memℓp_infty`, `Memℓp.bddAbove`, `inftyNormedRing`, `NormedCommRing`/`NormOneClass` for `lp (fun _ : ℕ ↦ ℚ_[p]) ∞` | present | USE (§2.5, Examples) |
| `Submodule.ClosedComplemented` (`∃ f : E →L[R] p, ∀ x : p, f x = x`), `.isClosed`, `ContinuousLinearMap.closedComplemented_ker_of_rightInverse`, `projKerOfRightInverse` | present (`Topology/Algebra/Module/Complement.lean`) | USE (§2.2.3, §2.2.5, §2.4.3) |
| `Module.Projective.of_split (i : P →ₗ M) (s : M →ₗ P) (h : s ∘ₗ i = id) [Projective M]`, `Module.Free.of_divisionRing`, `Module.Free.chooseBasis`, `Module.Basis.{mk, ofVectorSpace, reindex}`, `IsField.toField`, `Ideal.Quotient.maximal_ideal_iff_isField_quotient` | present | USE (§2.2.4, §2.3) |
| `Valuation.IsRankOneDiscrete`, `.exists_generator_lt_one`, `.generator_mem_range`, `.generator_zpowers_eq_range`, `Valuation.IsUniformizer`, `NormedField.valuation` (`Topology/Algebra/Valued/NormedValued.lean`, `valuation_apply`) | present | USE with [NP] `exists_zpow_generator_eq` (§2.3.3) |
| `Cardinal.{mk_iUnion_le_sum_mk, mk_biUnion_le, mul_eq_left, mk_le_of_injective, mk_le_of_surjective, eq, mk_le_aleph0, aleph0_le_mk}`, `Set.countable_iUnion`, `Set.Finite.countable`, `LinearIndependent.cardinal_le_rank`, `Module.finrank_pi`, `LinearEquiv.finrank_eq` | present | USE (§2.3.4) |
| `Submodule.closed_of_finiteDimensional`, `ContinuousLinearEquiv.ofFinrankEq`, `exists_linearIndependent`, `Set.countable_infinite_iff_nonempty_denumerable`, `Metric.infDist_lt_iff`, `IsClosed.notMem_iff_infDist_pos`, `Metric.infDist_le_dist_of_mem`, `LinearIndependent.notMem_span_image` | present | USE (§2.4) |
| `Submodule.Quotient.normedAddCommGroup (S) [IsClosed ↑S]`, `.normedSpace`, `.completeSpace`, `Submodule.mkQ`, `Submodule.Quotient.mk_surjective`, [L0] `Submodule.Quotient.instIsUltrametricDist` | present | USE (§2.4.3) |
| `LinearIsometryEquiv.{ofSurjective, ofBounds, trans, symm, toContinuousLinearEquiv}`, `LinearIsometry.{mk, isometry, toContinuousLinearMap}`, `ContinuousLinearEquiv.{equivOfInverse, ofBijective}`, `LinearMap.mkContinuous(_apply, _norm_le)` (ring scalars), `AddMonoidHomClass.continuous_of_bound`, `Equiv.{ulift, Set.sumCompl, toHomeomorphOfDiscrete}`, `Homeomorph.toCocompactMap` | present | USE |
| `hasSum_single`, `hasSum_sum_of_ne_finset_zero`, `HasSum.mapL`, `ContinuousLinearMap.map_tsum`, `HasSum.unique`, `Summable.tsum_eq_add_tsum_ite`, `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `IsUltrametricDist.{norm_tsum_le, norm_tsum_le_of_forall_le, norm_add_eq_max_of_norm_ne_norm, nnnorm_add_le_max}`, [L0] `IsUltrametricDist.norm_tsum_eq_of_forall_lt`, `tendsto_cofinite_prod_of_norm_le_mul`, `Filter.Tendsto.iSup_norm_cofinite_left/right` | present | USE |
| `Finset.nnnorm_sum_le_sup_nnnorm`, `Finset.{sup_le, le_sup, exists_mem_eq_sup, sup_const}`, `Real.{iSup_le, mul_iSup_of_nonneg, iSup_of_isEmpty}`, `ciSup_le`, `le_ciSup_of_le`, `Filter.Tendsto.bddAbove_range_norm` [L0] | present | USE |
| the ultrametric instance on `C(ℤ_[p], ℚ_[p])`, `CompactSpace ℤ_[p]` (`NumberTheory/Padics/ProperSpace.lean`), `ContinuousMap.norm_eq_iSup_norm`, `IsCompact.exists_isMaxOn`, `PadicComplex` with `ℂ_[p]`, `Padic.norm_eq_zpow_neg_valuation`, `PadicInt.isUnit_iff`, `PadicInt.norm_lt_one_iff_dvd` | present | USE (Examples) |
| the value group of `ℂ_p` (`‖ℂ_p^×‖ = p^ℚ`) | **absent** | hypothesis in the `ℂ_p` example (E23) |
| names that do **not** exist (checked): `ZeroAtInftyContinuousMap.{zero_at_infty, coe_toBCF, eval, coe_sum, coeFnAddMonoidHom}`, `BoundedContinuousFunction.{norm_smul_le, instIsUltrametricDist}`, `ContinuousMap.{liftZeroAtInfty, instIsUltrametricDist}`, `lp.{instModule, memℓp_infty_iff}`, `Submodule.closedComplemented_of_finiteDimensional`, `LinearIsometryEquiv.ofBijective`, `ContinuousLinearMap.{ker, range, mem_ker}`, `Valuation.IsRankOneDiscrete.exists_isUniformizer`, `Padic.isUniformizer_p` (lives in [NP]), `ContinuousLinearMap.Ultra.ofBounded` | — | the sketches use the verified alternatives |

## Generality and design decisions

1. **Model space = Mathlib's `C₀(I, E)`** (convention 3), index `[TopologicalSpace I] [DiscreteTopology I]`;
   the sup-norm lemmas and the two instances `IsUltrametricDist`, `IsBoundedSMul`/`NormSMulClass` are
   stated for any topological `I` (they need no discreteness); `ofTendsto`, `single`, the expansion
   and everything after need `DiscreteTopology I`. `single` needs `[DecidableEq I]` (it is `Pi.single`).
2. **Namespaces.** Model-space material lives in `ZeroAtInftyContinuousMap` (Mathlib's namespace for
   `C₀`); `matrixCoeff`, `ofMatrix`, `truncation`, `diagonal`, `baseChange`, `IsUnitriangularPerturbation`
   too, since they are operators between model spaces. The module predicates are `Module.IsONable`,
   `Module.IsPotentiallyONable`, `Module.HasPr`, `Module.IsCountableType` (next to `Module.Free`,
   `Module.Projective`, `Module.Finite`), satisfying convention 12's "nothing in the root namespace".
   The family predicates `IsOrthogonalFamily`, `IsTOrthogonalFamily` are in the root namespace next to
   the existing `IsOrthonormalFamily`/`IsOrthonormalBasis` of the shared `Orthonormal.lean` (and to
   Mathlib's root-level `Orthonormal`): see E20.
3. **Universe of the index set.** `IsONable (R : Type u) (M : Type v)` quantifies over `I : Type v`;
   the model space `C₀(J, R)` (any `J : Type w`) is orthonormalisable by reindexing along `ULift`, and a
   basis `e : I → M` with `I` in any universe gives `IsONable R M` by reindexing along `Set.range e`
   (`IsOrthonormalFamily.injective`). Transport lemmas (`of_linearIsometryEquiv`, `prod`, `zeroAtInfty`)
   keep the target in universe `v`; the lifting characterisation quantifies over Banach modules in
   `Type (max u v)` so that `C₀(I, R)` with `I : Type v` is admissible (E29).
4. **`HasPr` is the retract form** `π ∘ ι = id` with `ι : M →L[R] C₀(I, R)`, `π : C₀(I, R) →L[R] M` —
   Bellaïche's/JN's "direct summand of a potentially ON-able module" by `Submodule.ClosedComplemented.hasPr`
   and `HasPr.exists_closedComplemented`; the retract form is what the lifting proofs compose.
5. **`t`-orthogonality is stated termwise**: `∀ i ∈ s, t * ‖a i • e i‖ ≤ ‖∑ j ∈ s, a j • e j‖`, which is
   `‖∑‖ ≥ t · max` without a `Finset.sup` over `ℝ` (no `⊥`). `IsOrthogonalFamily` keeps Schneider's
   `‖a i • e i‖₊` form (it is scaling-closed); `IsOrthonormalFamily` becomes Bellaïche's `‖a i‖₊` form
   (E19, T001).
6. **Commutative scalars for matrix products** (§2.6.1 `hasSum_matrixCoeff_mul`, `ofMatrix_apply`,
   `matrixCoeff_comp`, §2.6.2, §2.6.6, §2.7): over a noncommutative `R` the coefficients multiply in the
   order `f j * a i j`; nothing downstream (Layers 3–5 are over `ℚ_p`-algebras) needs it. `matrixCoeff`,
   `tendsto_matrixCoeff_column`, `norm_matrixCoeff_le`, `ext_matrixCoeff` stay over `NormedRing`.
7. **Explicit bounds, explicit ring.** `map φ C hφ` and `diagonal d C hd` take the bound `C` explicitly
   (the def must not depend on `Classical.choose`); `ofBounded R m hm` takes the ring explicitly
   (nothing else determines it); `dualEquivLp R I`, `toBidual R I` likewise.
8. **Hypotheses as weak as the source allows.** `ofBounded` needs `M` ultrametric and complete and
   nothing on `R`; `ext_single`, `hasSum_single_apply`, `dense_span_range_single` need neither
   completeness nor ultrametricity; `[IsTate R]` appears exactly where `le_opNorm` is used (bounded
   values on the `single i 1`, `eq_ofBounded`, `norm_matrixCoeff_le`, `compL`, the dual) — the roadmap's
   "Banach–Tate is assumed where the operator norm of Layer 1 is used" (E26). Serre's theorem takes
   Bellaïche's Hypothesis II.1.11 as the explicit hypotheses `hR : ∀ r ≠ 0, ∃ n : ℤ, ‖r‖ = ‖ϖ‖ ^ n` and
   `hM : ∀ m ≠ 0, ∃ n : ℤ, ‖m‖ = ‖ϖ‖ ^ n`, as Layer 0's `Residue.lean` and `Rescale.lean` do.
9. **The scoped operator norm.** `open scoped ContinuousLinearMap.Ultra` wherever `‖u‖` is used; over a
   field the two norms agree definitionally (`norm_eq_opNorm`) but the `NormedAddCommGroup` instances
   are different terms, so the `ℚ_p` dual example is stated as `Nonempty (… ≃ₗᵢ …)` for Mathlib's
   instance and proved by transporting `dualEquivLp` (E28).
10. **Defs carry their proof obligations as `sorry` fields**, so that `_apply` lemmas are `rfl` now and
    stay `rfl`; instance arguments a sorried proof will need are written explicitly in the signature
    (`compL`, `congrRightL`, `toBidual`, the Dual file) so the signatures do not change when the proofs
    are filled. One expected skeleton warning: `toBidual_apply` "unused section variables
    `[DiscreteTopology I] [DecidableEq I]`", which disappears once `toBidual`'s proofs use them (T044).

## File layout (module prefix `PhD.TauCeti.Code.PadicFunctionalAnalysis`)

| File | § | Tau Ceti home |
|---|---|---|
| `ModelSpace/Basic.lean` | 2.1.1–2.1.2 | `TauCeti/Analysis/Normed/Module/Ultra/ModelSpace/Basic.lean` |
| `ModelSpace/Universal.lean` | 2.1.3 | `…/ModelSpace/Universal.lean` |
| `ModelSpace/Reindex.lean` | 2.1.4, §2.2.3 (`congrRight`), §2.2.5 (`setSumComplEquiv`) | `…/ModelSpace/Reindex.lean` |
| `ModelSpace/Map.lean` | 2.1.5 | `…/ModelSpace/Map.lean` |
| `ModelSpace/Truncation.lean` | 2.6.3, 2.2.5 (model-space half) | `…/ModelSpace/Truncation.lean` |
| `Orthogonal.lean` | 2.2.1–2.2.2 (with the shared `Orthonormal.lean`) | `…/Ultra/Orthogonal.lean` |
| `ONable.lean` | 2.2.3–2.2.5 | `…/Ultra/ONable.lean` |
| `Serre.lean` | 2.3 | `…/Ultra/Serre.lean` |
| `CountableType.lean` | 2.4 | `…/Ultra/CountableType.lean` |
| `ModelSpace/Matrix.lean` | 2.6.1, 2.6.2, 2.6.6 | `…/ModelSpace/Matrix.lean` |
| `ModelSpace/Dual.lean` | 2.5 | `…/ModelSpace/Dual.lean` |
| `ModelSpace/Closed.lean` | 2.6.4–2.6.5 | `…/ModelSpace/Closed.lean` |
| `Unitriangular.lean` | 2.7 | `…/Ultra/Unitriangular.lean` |
| `ModelSpace/Examples.lean` | Examples (leaf; `PhD/TauCeti.lean` imports it in T056) | — |

```text
Basic ← Universal ← {Reindex, Map(←Reindex), Truncation}
Orthonormal (T001) + Universal → Orthogonal → ONable (+Reindex, Truncation, L1 OpenMapping/Finite)
ONable + L0 Residue/Rescale + NP Discrete → Serre → CountableType (+Mathlib FiniteDimension, Quotient)
Universal + Map + L1 Banach → Matrix → {Dual (+ONable), Closed (+Truncation, L1 Finite), Unitriangular (+ONable)}
Examples ← {CountableType, Dual, Closed, Unitriangular, L1 Examples, NP Padic}
```

Skeleton gate (verified 2026-10-06, 2 688 jobs, 0 errors, the one expected warning):
`lake build PhD.TauCeti.Code.PadicFunctionalAnalysis.ModelSpace.Examples`. 256 declarations, 262 `sorry`s.

## Roadmap errata and seams (numbering continues Layer 1's E1–E18)

| # | Where | Finding | Action |
|---|---|---|---|
| E19 (applied: T001 done 2026-10-06) | convention 5, §2.2.3 | "orthonormal" with the sup-norm identity `‖∑ aᵢ eᵢ‖ = max ‖aᵢ • eᵢ‖` makes "ON-able ⟺ has an orthonormal basis" **false over rings**: `R = ℚ_p⟨X⟩` (Gauss norm), `M = ℚ_p` with `X` acting as `0`, `e = {1}` is such a basis, but `M` is `R`-torsion and `C₀(I, R)` is torsion-free. Bellaïche's/Buzzard's/JN's form `‖∑ aᵢ eᵢ‖ = max ‖aᵢ‖` is the right one (equivalent over fields) | **T001**: redefine the second conjunct of `IsOrthonormalFamily` as `s.sup fun i ↦ ‖a i‖₊`, generalise `Orthonormal.lean` to normed rings, repair the three RAG proof sites; edit convention 5 |
| E20 | convention 12 | "Nothing from this roadmap is placed in the root namespace" is already contradicted by the shared `Orthonormal.lean` (RAG board, done): `IsOrthonormalFamily`, `IsOrthonormalBasis` are root-level, as Mathlib's `Orthonormal` is | keep the family predicates root-level (add `IsOrthogonalFamily`, `IsTOrthogonalFamily` beside them); the module predicates go to `Module.*`; edit convention 12 |
| E21 | §2.2.1 | "an orthogonal family with nonzero members is linearly independent" needs a multiplicative action over a ring (`a • e = 0` with `e ≠ 0` does not force `a = 0`) | `IsOrthogonalFamily.linearIndependent [NormSMulClass R M]`; orthonormal families are LI over any ring |
| E22 | §2.6.2 | "injective with dense range when every `dᵢ` is a non-zero-divisor": dense range needs the `dᵢ` to be **units** (`diag(p, p, …)` on `C₀(ℕ, ℤ_p)` has range `p C₀`, not dense); `diag(⌊n/pʰ⌋!)` in §4.4 is over `ℚ_p` where they are units with unbounded inverses | `injective_diagonal` (non-zero-divisors), `denseRange_diagonal` (units) |
| E23 | §2.3.5, Examples | the value group of `ℂ_p` is not in Mathlib | `NormedField.Doubled K` + `not_isONable (hK : ∀ x, ‖x‖ ≠ 2⁻¹)`; the `ℂ_p` instance takes `hK` as a hypothesis, the `ℚ_p` instance (odd `p`) is proved |
| E24 | §2.4.2 | "an orthogonal basis when `K` is discretely valued (van Rooij; Perez-Garcia–Schikhof)": no source text is in the references (Schneider §10 has only the `t`-orthogonal construction; the discrete case needs Ingleton's norm-preserving Hahn–Banach = Schneider Prop 9.2 for the spherically complete `K` of Lemma 1.6, orthocomplemented finite-dimensional subspaces, and an orthogonalisation induction) | **off the board** (quote-or-delete); the `t`-orthogonal half is on the board (T035); the proposed route is recorded here for a later board once the PGS text is supplied |
| E25 | §2.4.3 | "a closed subspace of a space of countable type is of countable type" is not stated in Schneider; it follows from Prop 10.5 (the subspace is complemented, hence a quotient by its complement) and the quotient remark in 10.5's proof | T037 derives it that way (seam, not an erratum) |
| E26 | §2.1.3 | the universal property needs `M` ultrametric and complete for `ofBounded` (summability) and `[IsTate R]` only for "every map comes from a bounded family" | hypotheses as in decision 8 |
| E27 | §2.6.1 | the matrix formulas presuppose commutative scalars | decision 6 |
| E28 | §2.5.1, Examples | over a field the dual isometry is for the scoped norm; Mathlib's instance differs as a term | decision 9 |
| E29 | §2.2.4 | the lifting characterisation must quantify over Banach modules in a universe containing `C₀(I, R)` | `Type (max u v)` (decision 3) |

README edits applied 2026-10-06 at plan review: convention 5 (E19), convention 12 (E20), §2.2.1 (E21), §2.6.2
(E22), §2.4.2 (E24, the discrete case marked as potential future work), §2.3.5 (E23), §2.6.1 (E27). The user's
decisions: E24 stays off the board until the van Rooij / Perez-Garcia–Schikhof text is available; the `Module.*`
namespaces and the index-universe convention stand; E23's hypothesis form stands.

Seams: **S1** T001 edits the shared `Orthonormal.lean` and two RAG files — rebuild `lake build
PhD.TauCeti` after it (the RAG Tate-algebra chain depends on it) and keep the RAG statements unchanged.
**S2** `Serre.lean` imports `PhD.TauCeti.Code.NewtonPolygons.AddVal.Discrete` for
`IsRankOneDiscrete.exists_zpow_generator_eq` (same chain, allowed). **S3** `IsPotentiallyONable.zeroAtInfty`
and `HasPr.zeroAtInfty` need `[IsTate R]` (a continuous linear equivalence of the values is bounded only
over a Tate ring; Layer 1 §1.1.2). **S4** `CountableType.lean` uses Mathlib's quotient norm
`Submodule.Quotient.normedAddCommGroup` (instance argument `[IsClosed ↑U]`) and Layer 0's quotient
ultrametric instance.

## Milestones

- **M1** = T023 `Module.isONable_iff_exists_isOrthonormalBasis` (§2.2.3).
- **M2** = T032 `Module.isPotentiallyONable_of_isRankOneDiscrete` + `isONable_iff_forall_exists_norm_eq` (§2.3.3, Serre).
- **M3** = T036 `Module.IsCountableType.exists_continuousLinearEquiv_nat` (§2.4.1, Schneider 10.4).
- **M4** = T047 `ZeroAtInftyContinuousMap.isClosed_of_fg` (§2.6.5, Buzzard 2.3; discharges §1.4.3's deferral).
- **M5** = T051 `IsUnitriangularPerturbation.exists_linearIsometryEquiv` + `IsOrthonormalBasis.of_isUnitriangularPerturbation` (§2.7).

## Prior B2 log

`.mathlib-quality/b2_log.jsonl` has 8 entries (NewtonPolygon₀ 2026-08-03, LWX 2026-09-03/09); none names a
declaration of this board.

## Execution

Run `/beastmode on .mathlib-quality/tauceti-pfa-layer2/` after approval. Worker protocol, dependency
order and the 86 tickets: `tickets.md`. Verbatim source quotes, attack logs and the provability check per
leaf: `decomposition.md`.
