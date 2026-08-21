# Decomposition — forms-followups (`.mathlib-quality/forms-followups/`)

## Skeleton location
Every new statement exists as a declaration (`:= by sorry` for theorems; real bodies for the
definitions) — `lake build PhD.QMF.Weight.Fredholm PhD.QMF.Weight.Quaternionic
PhD.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace` green (sorries only), 2026-08-19:
- `PhD/QMF/Weight/Compact.lean` (item 1: `ext_of_forall_rep`, `bijective_evalAtReps`,
  `bijective_evalAtReps_of_stabilizer_eq_bot`, `formsModelEquiv`) — 3 sorries
- `PhD/QMF/Weight/Fredholm.lean` (item 3) — 3 sorries
- `PhD/QMF/Weight/Quaternionic.lean` (item 4) — 4 sorries
- `PhD/QMF/Weight/Char.lean` (item 6: `restrictRadius`, `kappaSlash_restrictRadius`) — 1 sorry
- `PhD/ForMathlib/NumberTheory/NumberField/Completion/FinitePlace.lean` (item 4 instance) — DONE, 0 sorries
Refactor items (T003, T007-fork part, T008) and cleanup items have no skeleton.

Prior-B2 log (`.mathlib-quality/b2_log.jsonl`) consulted: no name/shape match for any leaf below.

---

## Result R1 (item 1): `S_κ(U) ≅ ⊕_λ A_κ` at a neat level

### Plain-English proof (Buzzard §9 p. 69; Jacobs Lemma 1.31 p. 19)
Write `G = ∐_λ Γ c_λ U` (a complete family of representatives `c : ι → G`).  A form `φ` is
left-`Γ`-invariant and satisfies `φ(g u) = φ(g) ∣ u` for `u ∈ U`, so `φ(γ c_λ u) = φ(c_λ) ∣ u`: `φ` is
determined by the values `φ(c_λ)` (injectivity), and conversely a tuple `(a_λ)` defines a form
`φ(γ c_λ u) := a_λ ∣ u` provided this is well defined, i.e. provided `a_λ ∣ w = a_λ` for every
`w ∈ Γ_λ = {u ∈ U : c_λ u c_λ⁻¹ ∈ Γ}` — the tuple must lie in `∏ A^{Γ_λ}`.  If each `Γ_λ` acts
trivially on `A`, `∏ A^{Γ_λ} = ∏ A` and evaluation is a bijection onto the block model.

### Leaves
- **L1.1** (leaf, project): `QMF.Weight.ext_of_forall_rep` — `Compact.lean` (skeleton)
  - Statement: `(c : ι → G) (hc : Function.Surjective (fun i => (Quotient.mk'' (c i) : DoubleCoset.Quotient ↑Γ ↑U))) {φ ψ : Forms Γ θ κ U hU χ} (h : ∀ i, φ (c i) = ψ (c i)) : φ = ψ`
  - Source: [Buz07, §9 p. 69] > "Note that f ∈ L(U,A) is determined by f(τ_λ) for 1 ≤ λ ≤ µ"; [Jac03, Lemma 1.31 p. 19] > "It is an easy check that the map L(U,A) → ⊕ A^{Γ_i} given by φ ↦ (φ(c_i))_{i∈I} is an isomorphism."
  - Lean ↔ source: our `c` meets every double coset (surjectivity of `mk'' ∘ c`) — exactly "D_f^× = ∐ D^× c_i U" minus the disjointness, which injectivity does not need.
  - Discharged by: `Quotient.eq''`, `DoubleCoset.rel_iff` (`g = a * c i * b`), `AutomorphicFunction.left_invt'`, `AutomorphicFunction.slash_apply_mul` (project, Slash/AutomorphicFunction) — the template is the fork's `eval_classRep_injective` (6_Matrix.lean:197–228) and `bijective_evalAtRepsSlash.1` (Slash/HeckeMatrix.lean:181–190), both sorry-free.
  - Attacks: [1] negation search — none (`evalAtReps_injective` at a section is already proved, this generalises it). [2] edge: `ι` empty forces `G` empty quotient — `hc` then says the quotient is empty, i.e. `G` empty (impossible, `1 ∈ G`), so vacuous; `U = ⊤`: one double coset, `c` any single element — fine. [3] hypotheses: `hc` surjective only (bijective not needed); no `Fintype`; `hU` needed to slash. [4] source drift: Buzzard's `τ_λ` is a full set of reps; we weaken to "meets every coset" — still true (proof only uses existence of a decomposition `g = γ c_i u`). [5] discharge: the 4 lemmas exist (verified in the two template proofs). SURVIVED.
- **L1.2** (leaf, project): `QMF.Weight.bijective_evalAtReps` — `Compact.lean` (skeleton)
  - Source: [Buz07, §9 p. 69] > "one checks easily that the map f ↦ (f(τ_λ))_{1≤λ≤µ} induces an isomorphism L(U,A) → ⊕_{λ=1}^{µ} A^{Γ_λ}"; [Buz07, p. 68] > "Say D_f^× = ∐_{λ=1}^{µ} D^× τ_λ U. Then the groups Γ_λ := τ_λ⁻¹ D^× τ_λ ∩ U".
  - Lean ↔ source: `hstab` = "`Γ_λ` acts trivially on `A_κ`", so `A^{Γ_λ} = A`; then the source's isomorphism is a bijection onto `⊕ A = c(ι × ℕ, K)`.  Buzzard's `Γ_λ` is `stabilizerAtSlash Γ U (c i)` (docstring in Slash/HeckeMatrix.lean:98 "Buzzard's Γ_λ at a representative τ").
  - Discharged by: L1.1 (injectivity) + `AutomorphicFunction.bijective_evalAtRepsSlash` (.2, surjectivity onto invariants) + `cSpace.blockProj_apply`, `blockProj_evalAtReps`; template `bijective_evalU3` (7_Fredholm.lean:75–103, sorry-free).
  - Attacks: [1] none. [2] edge: `hstab` at `w = 1` is `kappaSlash_one`/`one_smul` — consistent. [3] hypotheses: `hc` bijective is needed for surjectivity (a non-injective family would make the target too big); `hstab` necessary (otherwise the image is `∏ A^{Γ_λ}` ⊊ `∏ A`, Buzzard p. 73). [4] source: matches with `A^{Γ_λ} = A`. [5] `bijective_evalAtRepsSlash` has the stated type (read at HeckeMatrix.lean:181–189). SURVIVED.
- **L1.3** (leaf, project): `bijective_evalAtReps_of_stabilizer_eq_bot` — from L1.2 with `w = 1`; source [Jac03, Lemma 2.2] > "Γ_i = {1} for all i = 0, 1, 2." (the fork's `stabilizerAt_classRep`). Attacks: composition only; SURVIVED.
- **L1.4** (def): `formsModelEquiv := LinearEquiv.ofBijective _ (bijective_evalAtReps …)` — [Jac03, (2.1.1)]/[Buz07 p. 69].
- **L1.5** (leaf, project — fork): `JacobsSlash.classRep_bijective (hcn : HClassNumberOne) : Function.Bijective (fun i : Fin 3 => (Quotient.mk'' (classRep i) : DoubleCoset.Quotient ↑(globalUnits ℚ D) ↑U1_9))` — discharged by `exists_classRep_factorisation hcn` (surjective; 3_ClassSet.lean:1178) and `classRep_index_unique` (injective; 3_ClassSet.lean:1304), both sorry-free on `hcn`. Attacks: [5] both lemmas have the needed shapes (read above). SURVIVED.

## Result R3 (item 3): the Fredholm determinant of `[UηU]` on `S_κ(U)` and its zeros

### Plain-English proof (Jacobs pp. 20–21; Buzzard §13; Serre §7)
Through the model isomorphism (R1) the operator `[UηU]` is the block operator `heckeBlockOp`
(`evalAtReps_heckeOperator`), compactoid for `η` of `U_ϖ` type (`isCompactoid_heckeBlockOp`), so
`det(1 − T·[UηU]) := charPowerSeries (heckeBlockOp)` makes sense — this is Jacobs's "matrix of
`U_p` with respect to the topological basis".  Serre's Riesz theory says `a` is a zero of
`det(1 − Tu)` iff `a⁻¹` is an eigenvalue of `u`; transporting eigenvectors along the model
isomorphism (which intertwines `[UηU]` and `heckeBlockOp`) gives the eigen**form** statement.
Independence from the representatives/certificates: two block operators are conjugate by the
transition operator (a continuous linear equivalence), and `det(1 − Tu)` is conjugation invariant
(Buzzard Cor 2.6 = `charPowerSeries_conj`).

### Leaves
- **L3.1** (def): `heckeCharPowerSeries := charPowerSeries (heckeBlockOp …)` — `Fredholm.lean`.
  Source: [Jac03, p. 21] > "Hence we obtain the matrix of U_p with respect to the topological basis {e_k : k ∈ K}."; [Buz07, §13 p. 79] > "let φ denote the operator U_π … M_X = S^D_κ(U;r)" (the determinant of `φ` on `M_X` is the eigenvariety input).
- **L3.2** (leaf, project): `evalT_heckeCharPowerSeries_eq_zero_iff` — `Fredholm.lean` (skeleton)
  - Source: [Ser62, §7 Props 11–12] as formalised: `TateFredholm.evalT_charPowerSeries_eq_zero_iff (u) (hu : IsCompactoid u) (ha0 : a ≠ 0) : evalT a (charPowerSeries u) = 0 ↔ ∃ x, x ≠ 0 ∧ u x = a⁻¹ • x` (Riesz.lean:2233, sorry-free); Riesz.lean header > "Serre's Proposition 11: 1 − a•u is invertible iff H(a) is a unit".
  - Lean ↔ source: the statement is the block-model criterion transported along `evalAtReps` (bijective by R1, intertwining by `evalAtReps_heckeOperator`): `∃ φ ≠ 0, [UηU]φ = a⁻¹ • φ`.
  - Discharged by: `evalT_charPowerSeries_eq_zero_iff`, `isCompactoid_heckeBlockOp`, `bijective_evalAtReps`, `evalAtReps_heckeOperator`, `map_smul`, injectivity (≤ 3 lemmas per direction).
  - Attacks: [1] none. [2] `a = 0` excluded by `ha0` (as in Serre). [3] needs neatness (`hstab`) — without it `heckeBlockOp` on the whole model is not conjugate to `[UηU]`; needs the determinant certificate for compactoidness (Serre's theory needs compactness). [4] matches Serre Prop 12 read through the model. [5] all cited decls exist and are sorry-free. SURVIVED.
- **L3.3** (leaf, project — fork): `charPowerSeriesU3 := heckeCharPowerSeries … etaRep … sigmaTable uTable` — `rfl` with the current definition (`charPowerSeries (blockOp (blockEntry t ht))`, `blockEntry` an abbrev of `heckeBlock`).
- **L3.4** (leaf, project, OPTIONAL): `evalAtReps_eq_transitionOp` — `Fredholm.lean` (skeleton). Source: [Jac03, p. 21] > "we decompose c_i v_t⁻¹ as d(i,t) c(i,t) u(i,t) with d(i,t) ∈ D, c(i,t) ∈ {c_0,c_1,c_2} and u(i,t) ∈ U" (the same factorisation device, now between two families). Discharged by: `mem_forms_iff` (`φ (g u) = χ • kappaSlash (φ g)`), `left_invt'`, `cSpace.blockProj_blockIncl`, `Finset.sum_ite_eq` — template `evalAtReps_heckeOperator` (Compact.lean:172). Attacks: [3] `hd`/`hfact` are exactly the certificate shape; [5] template exists. SURVIVED.
- **L3.5** (leaf, project, OPTIONAL): `heckeCharPowerSeries_eq_of_reps` — `Fredholm.lean` (skeleton)
  - Source: [Buz07, Cor 2.6 p. 14] > "if {e_i : i ∈ I} and {f_j : j ∈ J} are ON bases for (M,|.|₁) and (M,|.|₂) respectively, then the definitions of det(1 − Xφ) with respect to these bases coincide." and p. 14 > "the notion of a characteristic power series only depends on the topology on M … it does not depend on the choice of an orthonormal basis for M."
  - Discharged by: `TateFredholm.charPowerSeries_conj (φ : c(I,R) ≃L[R] c(J,R)) (u) (hu : IsCompactoid u) : charPowerSeries (φ ∘ u ∘ φ.symm) = charPowerSeries u` (Fredholm.lean:953, sorry-free), L3.4 both ways, R1 both families (surjectivity gives `T₂ ∘ T₁ = id`), `evalAtReps_heckeOperator` both families; the equivalence is built by `LinearEquiv.ofLinear` + continuity of both transition operators (no open-mapping theorem needed).
  - Attacks: [1] none. [3] both families must be neat (else the block operators are not conjugate on the whole model); compactoidness of one block operator needed (`charPowerSeries_conj`'s hypothesis). [4] Buzzard's statement is about bases of one module; ours is about two models of the same space — the same content. [5] `charPowerSeries_conj` signature read at Fredholm.lean:953–960. SURVIVED.

## Result R4 (item 4): `S^D_κ(U)` and `U_ϖ` for a quaternion algebra

- **L4.1** (leaf, mathlib): `instNontriviallyNormedFieldAdicCompletion : NontriviallyNormedField (v.adicCompletion K) := Valued.toNontriviallyNormedField _ ℤᵐ⁰` — DONE in the skeleton, and `example : (…).toNormedField = instNormedFieldValuedAdicCompletion K v := rfl` passes (no diamond with mathlib's `NormedField`). Attacks: [2] nontriviality witness = uniformizer (mathlib's `RankOne.nontrivial`); [5] verified by build. SURVIVED.
- **L4.2** (def): `FormsQ := Weight.Forms (globalUnits F D) (toMatrix F D v) κ U hU χ`; source [Buz07, §10 p. 72] > "define the space of r-overconvergent automorphic forms of weight κ and level U to be the O(X)-module S^D_κ(U;r) := L(U, A_{κ,r})."
- **L4.3** (def): `heckeUpiQ := Weight.heckeOperator (toMatrix F D v) κ U hU hη h` at `η = etaAdelic' ϖ`; source [Buz07, Lemma 12.2 proof p. 78] > "One checks easily that U_π is the Hecke operator [UηU] associated to the matrix η"; [Jac03, Def 1.33 p. 20] > "T_l := [U η_l U] … If l = p, it is traditional to write U_p for T_p."
- **L4.4** (leaf, project): `etaAdelic'_mem_levelMonoidOf_sigma0'` — `exact etaAdelic'_mem_levelMonoid' F D v γ hγ ϖ hϖ hϖ0` (`levelMonoidOf θ (Sigma0' …) = levelMonoid' F D v γ hγ` by `rfl`, both `Submonoid.comap (toMatrix F D v)`). Attacks: [5] defeq checked by reading both definitions (Forms.lean `levelMonoidOf θ S := S.comap θ`; Slash/Quaternionic.lean:48). SURVIVED.
- **L4.5** (leaf, project): `norm_det_toMatrix_etaAdelic' : ‖det (toMatrix (etaAdelic' ϖ))‖ = ‖ϖ‖` — `toMatrix_etaAdelic'` (Slash/Quaternionic.lean:125, needs a `γ < 1` witness, any) + `Sigma0'.eta` matrix `!![ϖ,0;0,1]` + `Matrix.det_fin_two_of` + `norm` simp; template `JacobsSlash.norm_det_toMatrix_eta3_le` (7_Fredholm.lean). Attacks: [2] `ϖ = 0` excluded; [5] template exists. SURVIVED.
- **L4.6** (leaf, project): `isCompactoid_heckeBlockOp_etaAdelic'` — `Weight.isCompactoid_heckeBlockOp … hρ hϖ1 (L4.5).le hvΔ hv idx u`; source [Buz07, Lemma 12.2 p. 78] > "The inclusion S^D_κ(U;r) → S^D_κ(U;r|π|) is norm-decreasing and compact, and hence U_π, considered as an endomorphism of S^D_κ(U;r), is also norm-decreasing and compact."  Lean ↔ source: our `ρ ≤ ‖ϖ‖ < 1` is Buzzard's "t good for (κ,r)" with `r|π|`-analyticity; the compactness is the general theorem's determinant certificate `‖det η_v‖ = ‖ϖ‖`. Attacks: [3] `ρ ≤ ‖ϖ‖` necessary (Jacobs's `ρ = ‖3‖`, `ϖ = 3` is the boundary case); [5] `isCompactoid_heckeBlockOp` signature read (Compact.lean:253). SURVIVED.
- **L4.7** (leaf, project): `finite_image_etaAdelic'_of_isOpen_of_isCompact := finite_image_doubleCoset_of_isOpen_of_isCompact hUo hUc _` (Slash/HeckeMonoid.lean:231; needs `IsTopologicalGroup (Dfx F D)`, found under `open scoped TensorProduct.RightActions` with `[DivisionRing D] [FiniteDimensional F D]` — verified in the skeleton build). Source [Buz07, §9 p. 69] > "decompose UηU = ∐_i U x_i (a finite union)". SURVIVED.
- **L4.8** (refactor): delete the fork's `instance : NontriviallyNormedField K₃` (1_Setting.lean:143) in favour of L4.1 (defeq: both are `⟨instNormedFieldValuedAdicCompletion, _⟩`); `kappaForms := FormsQ ℚ D v₃ …`, `heckeU3 := heckeUpiQ ℚ D v₃ … pi3 …` (cosmetic, `rfl`).

## Result R6 (item 6)
- **L6.1** (leaf, project): `kappaSlash_restrictRadius := WeightSeries.kappaSlash_congr rfl rfl` (SlashAction.lean:376, general in `(S, ρ)`). Source [Buz07, §13 p. 79] > "the inclusion B_{r(κ)} → B_{r(κ')} induces an injection A_{κ',r(κ')} → A_{κ',r(κ)}". Attacks: [3] `hdecay` is genuinely needed — counterexample to dropping it: a datum on `S = {c : ‖c‖ ≤ ρ/2}` declared at radius `ρ` satisfies `‖aₘ‖ ≤ ρ^m` but need not satisfy `‖aₘ‖ ≤ (ρ/2)^m` unless the Taylor coefficients are integral (the "saturation" theorem would derive it for `SigmaNorm`-type `S`; NOT ticketed). SURVIVED.
- **L6.2** (refactor): `kappaLevelSlashAction (κ : AnalyticWeight UK S ρ) := RightSlashAction.comap (levelMonoidOfToS θ S) κ.kappaSlashAction` (currently takes a `WeightSeries`); `kappaLevelSlashActionTwisted` through `κ.kappaSlash`; all `rfl` lemmas preserved (`AnalyticWeight.kappaSlash`/`kappaSlashAction` are `def`s over `κ.toWeightSeries`). Delete `Sigma0'.adjEquiv` (Slash/Sigma0.lean:189, no users).

## Item 5 — cleanup leaves
39 `runLinter` findings (list in tickets CLEANUP-6…11; `scratchpad/linter_legacy.txt`): unused
arguments (drop the hypothesis + fix call sites, or `omit … in`), one `simpNF` (LHS of
`matrixCoeff_inclSubtype` simplifies), one `defsWithUnderscore` (`U1_9`, thesis name → `@[nolint]`).

## Confidence gate
1. every leaf discharged from project/mathlib (cited) ✓  2. skeleton builds (sorries only) ✓
3. source quotes + match paragraphs ✓  4. attack blocks ✓  5. prior-B2 log: no matches ✓
6. trees mirror the sources (Buzzard §9 two-line proof → two leaves; Serre/Riesz already formalised) ✓
7. single-conclusion statements ✓ (bijectivity is one predicate; the `↔` is one statement).
