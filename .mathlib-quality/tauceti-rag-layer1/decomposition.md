# Decomposition: rigid analytic geometry, Layer 1 (affinoid algebras)

Companion to `plan.md`. Every leaf below is a declaration of the skeleton, stated with `sorry`; the
pointer is `File.lean · declaration name` (names are stable, line numbers are not; `scratch/sorries.py`
prints the current line of every open declaration, `scratch/signatures.txt` their elaborated
signatures). Sources:

- **[RM]** the roadmap `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, Layer 1, cited by clause
  (§1.1.1 … §1.5.2);
- **[BGR]** Bosch–Güntzer–Remmert, *Non-Archimedean Analysis* (1984), hand-transcribed from the scan into
  `references/bgr-6.1.1.md`, `bgr-6.1.2.md`, `bgr-6.1.3-6.1.5.md`, `bgr-3.7.md` (§3.7, §1.2.4–1.2.5, §7.2.5);
  a locator `bgr-6.1.1.md:45` is a line of the transcription, which records the book page;
- **[Bo]** Bosch, *Lectures on Formal and Rigid Geometry*, text layer `references/bosch-lectures.txt`
  (ligatures and broken spacing normalised in quotes, nothing else);
- **[L0]** Layer 0 of this roadmap (`.mathlib-quality/tauceti-rag-layer0/`, complete, sorry-free): the
  floor `Restricted/**`, `TateAlgebra/**`, `Rueckert.lean`, `Japanese.lean`, …;
- **[PFA]** the chain's `PhD/TauCeti/Code/PadicFunctionalAnalysis/{UnitBall, PowerBounded, Sums}.lean`.

Discharge lines (D) name the lemmas a worker will call. Every Mathlib name was checked by elaboration
against the pin (`scratch/names_tickets_mathlib.lean`, generated from the tickets' "Mathlib lemmas
needed" blocks) and every floor, chain and board name by `scratch/names_tickets_chain.lean`; see
`plan.md`, "Name check". Attack categories: **[1]** counterexample search, **[2]** edge cases,
**[3]** hypothesis strength, **[4]** source drift, **[5]** discharge, **[6]** composition.

## Skeleton location

`PhD/TauCeti/Code/RigidAnalyticGeometry/` — `NormedQuotient.lean`, `Restricted/Sum.lean`,
`Affinoid/{Basic, Extend, Noether, Continuity, Tensor, Fractions, BaseChange, Polydisc, Examples}.lean`,
`BanachAlgebra/{Noetherian, Continuity}.lean`; plus three Layer 0 / PFA files generalised in place:
`Restricted/Algebra.lean` (the `K`-module and `K`-algebra structure of `Restricted S c` for every
`K`-algebra `S`), `TateAlgebra/Eval.lean` (evaluation along a *bounded* coefficient map at a tuple with
*bounded monomials*, BGR 6.1.1/4), `PadicFunctionalAnalysis/PowerBounded.lean` (power-boundedness in
normed algebras). 16 files, 153 open declarations, 153 `sorry`s.

Gate: `lake build PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Examples` (the leaf imports the whole
board) — `Build completed successfully (2764 jobs)`, `sorry` warnings only, verified 2026-10-05 after
the last statement change. Note that the three generalised files are in Layer 0's cone, so Layer 0 is
*temporarily* sorry-bearing again (ten declarations): they are the first tickets of this board.

## Prior-B2 consultation (Step 4.6), once for the whole tree

All B2 logs under `.mathlib-quality/` were read (default log, `jacobs`, `lwx-conductor`, `lwx-h1`,
`lwx-halo`, `lwx-seam-m`, `lwx-theta`, `tauceti-of-layer0`). **No leaf matches by name.** The defect
shapes were applied to every leaf as edge-case attacks:

| Prior defect shape | Log entry | Where it was tested here | Outcome |
|---|---|---|---|
| section variable dropped from the elaborated statement | `lwx-h1` W5, `lwx-conductor` R13–R17, `tauceti-of-layer0` T023 | every declaration, by reading `scratch/signatures.txt` (153 entries, 0 errors) | **one hit**, fixed: `renameEquiv` had lost its bijection `e` (D5). All theorems carry their sections' instances (Lean includes an instance variable whenever its carrier is mentioned); the `omit`s only remove instances unused by proved (`rfl`-level) statements |
| statement generalised beyond the source's hypotheses | default log C3 | every leaf more general than its source: L0.* (bounded instead of contractive evaluation), L4.* (`A⟨X⟩` over any normed algebra), L5.*/L6.* (abstract Banach algebras), L12.1 (any `ρ`) | each re-derived by hand; **one hit**, fixed: `IsPowerBounded.map` is false for a merely *continuous* ring map of non-normed rings — the statement takes a norm bound (L0.10) |
| normalisation silently assumed (`‖p‖ = 1/p`) | `lwx-seam-m` X-4 | L13.4–L13.5 (`Padic.norm_p_lt_one` is a Mathlib theorem, no value used) | clean |
| unconstrained parameter | `lwx-theta` T-AG1a, `jacobs` J015 | L12.2–L12.5 (`s i = 0` would make the rescaling non-injective: hypothesis `hs`), L7.2 (`s = 0` makes `Tₙ → T_{n+1}/(g)` the zero map: hypothesis `hs`), L10.* (`hgen`) | **two hits**, fixed (D6, D7) |
| junk values | `jacobs` W001–W003 | L3.4 (`‖x‖` of the zero ring), L7.13 (`ringKrullDim` of the zero ring is `⊥`), L9.* / L10.* (the zero algebra as a tensor product or ring of fractions) | clean; each junk case is stated in the leaf |
| statement not instantiable by its consumer | `lwx-h1` W/I15 | the universe of the `C` in the two universal-property predicates: the uniqueness theorems instantiate it with the two candidates, which must therefore live in the predicate's universe | **two hits**, fixed (D2, D3) |
| the topology/instance in the statement is not the expected one | `tauceti-of-layer0` T039 | L3.1 (quotient completeness through the opaque `Restricted`: shortcut instance), L9.*/L10.* (residue *seminorm* on a quotient by a possibly non-closed ideal) | clean, recorded in the plan ("Seam") |

## Statement defects found by the adversarial pass (all repaired in the skeleton)

| # | Declaration | Defect | Repair |
|---|---|---|---|
| D1 | `Submodule.exists_forall_exists_eq_sum_mul_norm_le` | stated for a `K`-submodule `J` with `x i ∈ J`: the map `(aᵢ) ↦ Σ aᵢ xᵢ` need not land in `J`, so the open-mapping argument does not even start | restated as `Ideal.exists_forall_exists_eq_sum_mul_norm_le` for a closed ideal `J = span (range x)` |
| D2 | `IsAffinoidTensorProduct.exists_algEquiv` | `T` in an arbitrary universe while the universal property quantifies over `C : Type v`: the proof applies the property of `h'` with `C := T` | `T T' : Type v` |
| D3 | `IsAffinoidTensorProduct.surjective_ι₂_of_surjective` | same universe defect for `B₂ ⧸ 𝔞B₂` and `T`; `hT : IsAffinoidAlgebra K T` unused; `ker α₁` closed needs `α₁` continuous, which the predicate does not record | `B₂ T : Type v`, `hT` dropped, hypothesis `hα₁ : Continuous α₁` added |
| D4 | `IsGeneralisedFractions.exists_algEquiv` | universe defect as D2 | `A' A'' : Type v` |
| D5 | `Restricted.renameEquiv` | the bijection `e` was a section variable not mentioned in the type, hence dropped by elaboration (the def had no `e`) | explicit binder; the equivalence is now stated at the unit polyradius only (`c ∘ e.symm` is not syntactically `1`, a seam the consumers would have had to cross) |
| D6 | `injective_mk_comp_ofTail_of_isMulDistinguishedX0` | false for `s = 0`: a series distinguished of order `0` is a unit, the quotient is zero | hypothesis `hs : s ≠ 0` |
| D7 | `injective_rescaleAlgHom`, `isRestricted_shiftCoeff`, `finite_rescaleAlgHom` | `s i = 0` makes `μ ↦ μ s` non-injective and the coefficient extraction wrong | hypothesis `hs : ∀ i, s i ≠ 0` (BGR has `sᵢ ∈ ℕ` with `ϱᵢ^{sᵢ} ∈ |k^×|`, implicitly `sᵢ ≥ 1`) |
| D8 | `exists_sum_smul_mapBase` | stated with a `Finset K'` of scalars and a function on `K'`: not provable from a basis without an inverse of the basis map | stated for a given `Module.Basis ι K K'` |
| D9 | `isPowerBounded_X` | carried `[NormOneClass A]`, unnecessary: `‖X i ^ k‖ = ‖1‖` for `k ≥ 1` | hypothesis removed (the consumers `inlAlgHom`, `mapAlgHom` over a possibly-zero `A` need it removed) |
| D10 | `exists_forall_norm_le_mul_of_continuous`, the `Extend` section | carried `[IsUltrametricDist K]`, never used | removed from the section |
| D11 | `IsAffinoidAlgebra.of_subsingleton`, `tateAlgebra`, `ofTailAlgHom_apply` | `[CompleteSpace K]` included by the section, unused | `omit … in` |

## Statement-shape check (gate condition 7)

`scratch/sorries.json` was scanned for `∧` in conclusions. No open declaration has a top-level
conjunction except the allowed shapes: shared-witness existentials (`exists_norm_quotient_mk_eq`,
`exists_algEquiv_quotient` (a `Nonempty`), `existsUnique_extend`, `exists_forall_norm_smul_le_one`,
`exists_isAffinoidGeneratingSystem_of_finite`, `exists_finite_injective_comp` (both),
`exists_finite_injective`, `exists_forall_exists_eq_sum_mul_norm_le`,
`exists_forall_norm_le_mul_of_isNoetherianRing`, `exists_forall_norm_le_mul_of_isAffinoidAlgebra`,
`exists_algEquiv_quotient_norm_comp_le`, `IsAffinoidTensorProduct.exists_algEquiv`,
`IsGeneralisedFractions.exists_algEquiv`, `exists_algEquiv_quotient_X_norm_eq`,
`exists_summable_not_isRestricted`), characterisations (`isPowerBounded_map_iff_…`,
`isTopologicallyNilpotent_map_iff_…`), and the one explicit assembly `Examples.finite_injective_cusp`,
which is already proved as `⟨_, _⟩` of two leaves. Multi-part source statements are split: BGR 6.1.1/4
into `extendAlgHom`, `extendAlgHom_C`, `extendAlgHom_X`, `continuous_extendAlgHom`,
`extendAlgHom_unique`; BGR 6.1.2/1 (i), (ii) into the two `exists_finite_injective_comp`; BGR 3.7.5/3
into `continuous_of_…`, `continuous_symm_of_…`, `exists_forall_norm_le_mul_of_…`; BGR 6.1.4/1 into the
four data leaves and `isGeneralisedFractions_toFractions`; BGR 6.1.5/4 into `injective_rescaleAlgHom`,
`finite_rescaleAlgHom`, `isAffinoidAlgebra_of_forall_exists_pow_eq_norm`.

---

## G0 — The floor generalised in place (`Restricted/Algebra.lean`, `TateAlgebra/Eval.lean`, `PadicFunctionalAnalysis/PowerBounded.lean`), [RM] §1.1.3

### Source and prose proof

[BGR] 6.1.1/4 (`bgr-6.1.1.md:45–54`): *"Let `φ : B → A` be a continuous homomorphism between
`k`-Banach algebras `A`, `B`. Let `f₁, …, fₙ` be power-bounded elements in `A` … Then there exists a
unique continuous homomorphism `Φ : B⟨X₁, …, Xₙ⟩ → A` such that `Φ | B = φ`, `Φ(Xᵢ) = fᵢ`. Proof. For
`h = Σ a_ν X^ν ∈ B⟨X⟩`, we set `Φ(h) := Σ φ(a_ν) f^ν`. Since `fᵢ ∈ Å` and `lim a_ν = 0`, the series on the
right-hand side represents a well-defined element of `A`."* [BGR] 3.7.1 (`bgr-3.7.md:10–11`): *"such a
map `φ` is continuous if and only if it is bounded."* [BGR] 1.2.5/1–2 (`bgr-3.7.md:155–162`): *"An
element `a ∈ A` is called power-bounded if the set `{|aⁿ| ; n ∈ ℕ} ⊂ ℝ₊` is bounded … The set `Å` is a
subring of `A`."*

Layer 0's `eval₂` evaluated along a *contractive* coefficient map at a tuple with `‖x i‖ ≤ c i`. BGR
6.1.1/4 needs a *bounded* (continuous) `φ` and *power-bounded* `fᵢ`: the terms `φ(a_ν) f^ν` are then
bounded by `Cφ · Cx · ‖a_ν‖ c^ν`, which tends to zero, so the series converges (ultrametrically) and
the sum is a ring homomorphism, bounded by `Cφ Cx`. The contractive case is the case `Cφ = Cx = 1`.
Power-boundedness in a normed algebra over a nontrivially normed field is boundedness of the norms of
the powers (`TopologicalRing.IsBounded` is defined through neighbourhoods of `0`; a scalar of small
norm multiplies a bounded set into the unit ball). The `K`-module structure of `Restricted S c` for a
`K`-algebra `S` (coefficientwise scalars) is needed for `A⟨X⟩` to be a `K`-algebra at all.

### Leaves

- **L0.1** `isRestricted.smul'` (`Restricted/Algebra.lean`) — Q: [RM] §1.1.3 *"Define `A⟨X₁, …, Xₘ⟩`
  for a `K`-Banach algebra `A` as the restricted series over `A` at the unit polyradius"* (to be a
  `K`-algebra it must carry `K`-scalars). M: `IsRestricted c (k • f)` for `k : K` acting through
  `R`. D: `coeff t (k • f) = k • coeff t f` (`MvPowerSeries.coeff_smul`), `‖k • r‖ = ‖(k • 1) * r‖ ≤
  ‖k • 1‖ ‖r‖` (`IsScalarTower.smul_one_mul`? no — `smul_mul_assoc` with `one_mul`: `k • r = (k • 1) * r`
  by `smul_mul_assoc`, `one_mul`), so the Gauss terms of `k • f` are bounded by a constant multiple
  of those of `f`: `IsRestricted` is `Tendsto (‖coeff‖ * c^t) cofinite (𝓝 0)`, closed under constant
  multiples (`Filter.Tendsto.const_mul` and `squeeze_zero`). A: [2] `k = 0` ✓ (zero series). [3] the
  `IsScalarTower K R R` hypothesis is what makes `k • r = (k • 1) * r`; without it the bound fails
  (an arbitrary `Module K R` need not interact with the norm). [5] the floor proves the `R`-scalar case
  by the same bound. SURVIVED.
- **L0.2** `algebraMap_eq_C_comp` — Q: as L0.1. M: `algebraMap K (Restricted S c) = (C c).comp
  (algebraMap K S)`. D: `Algebra.ofModule`'s `algebraMap` is `k ↦ k • 1`; `Restricted.ext`, `val_smul`
  (general scalar version is `rfl`), `MvPowerSeries.smul_eq_C_mul`, `Algebra.algebraMap_eq_smul_one`
  — the floor's `algebraMap_apply` is the case `K = S`. A: [2] `K = S` recovers `algebraMap_apply` ✓
  (the instance is the same one). [5] `RingHom.ext`, three lemmas. SURVIVED.
- **L0.3** `norm_prod_pow_le_of_norm_le` (`Eval.lean`) — Q: [BGR] 5.1.4 (Layer 0's leaf L3.1) at the
  unit bound: *"`|a_ν x^ν| ≤ |a_ν|`"*; the general form is the case `Cx = 1` of 6.1.1/4. M:
  `‖Π xᵢ^{tᵢ}‖ ≤ 1 * Π cᵢ^{tᵢ}`. D: `Finsupp.prod`, `norm_prod_le` (needs `NormOneClass`),
  `norm_pow_le` and `pow_le_pow_left₀` with `norm_nonneg`. A: [2] `t = 0`: `‖1‖ = 1 ≤ 1` — this is why
  `NormOneClass` is assumed (over the zero ring `‖1‖ = 0 ≤ 1` too) ✓. [3] `c i < 0` makes `hx` false;
  no further hypothesis. [5] `norm_prod_le` signature verified. SURVIVED.
- **L0.4** `exists_forall_norm_prod_pow_le` — Q: [BGR] `bgr-6.1.1.md:51` *"Since `fᵢ ∈ Å` …
  represents a well-defined element"*; 1.2.5/2 `bgr-3.7.md:159–160` *"Choose `M > 0` such that
  `|aⁿ| ≤ M`, `|bⁿ| ≤ M`. We conclude `|(ab)ⁿ| ≤ M²`"*. M: a uniform bound on all monomials of a finite
  power-bounded tuple. D: choose `Cᵢ ≥ 0` for each `i` (`k = 0` forces `Cᵢ ≥ ‖1‖ ≥ 0`), set
  `Cx := max ‖1‖ (∏ i, max 1 (Cᵢ))` (`Fintype.ofFinite`); for `t ≠ 0` use `Finset.norm_prod_le'`
  on the support (nonempty) and `∏_{supp} Cᵢ ≤ ∏_{all} max 1 Cᵢ` (`Finset.prod_le_prod_of_subset_of_one_le'`);
  for `t = 0` the bound is `‖1‖`. A: [2] `σ` empty: `t = 0` only ✓; `x i = 0`: `Cᵢ ≥ ‖1‖` still ✓. [3]
  `Finite σ` is necessary (infinitely many `x i` of norm `2` have unbounded monomials). [5] three
  Mathlib lemmas, verified. SURVIVED.
- **L0.5** `norm_map_mul_prod_pow_le` — Q: `bgr-6.1.1.md:50–51` (the terms `φ(a_ν) f^ν`). M: the term
  bound with the product of constants. D: `norm_mul_le`, `mul_le_mul` (both factors nonnegative:
  `0 ≤ Cφ * ‖a‖` from `‖φ a‖ ≤ Cφ * ‖a‖` and `norm_nonneg`), `mul_mul_mul_comm`. A: [2] `Cφ < 0`
  (only over the zero ring `R`): then `‖φ a‖ ≤ Cφ ‖a‖ = 0`, product `0 ≤ 0` ✓. [3] none. SURVIVED.
- **L0.6** `tendsto_map_coeff_mul_prod_pow` — Q: `bgr-6.1.1.md:51` *"`lim a_ν = 0`"*. M: the terms tend
  to `0` along cofinite. D: `squeeze_zero_norm'`-style: `f.2` (restrictedness) gives
  `‖a_t‖ c^t → 0`, `Tendsto.const_mul (Cφ * Cx)`, L0.5, `tendsto_zero_iff_norm_tendsto_zero`. A: [2]
  negative constants: the squeeze only needs `‖term‖ ≤ RHS → 0` ✓. [5] verified. SURVIVED.
- **L0.7** `norm_eval₂_le_mul` — Q: [BGR] 5.1.4/2 (Layer 0 L3.6) and `bgr-6.1.1.md:51`. M:
  `‖Σ φ(a_ν) x^ν‖ ≤ |Cφ Cx| ‖f‖`. D: [PFA] `norm_tsum_le_of_forall_le`-type bound for ultrametric sums
  (Layer 0 used `Sums.lean`'s lemma in `norm_eval₂_le`; name recorded in the ticket), L0.5 and
  `norm_coeff_mul_prod_le`, `le_abs_self`. A: [2] **attack succeeded before repair**: with `Cφ Cx < 0`
  (possible only over the zero ring `B`) the old right-hand side `Cφ Cx ‖f‖` is negative while the
  left-hand side is `0` — the statement was false; now `|Cφ Cx|` (the gate's `norm_eval₂_le` still
  follows by `simpa`). [3] `Fact (∀ i, 0 < c i)` needed for the norm instance only. SURVIVED after repair.
- **L0.8** `TopologicalRing.IsBounded.exists_norm_le_of_normedAlgebra` (`PowerBounded.lean`) — Q:
  [BGR] 1.2.5/1 `bgr-3.7.md:155` (power-bounded = `{|aⁿ|}` bounded); [RM] §0.2.1 (the chain's
  `IsPowerBounded` is `TopologicalRing.IsBounded (range (a ^ ·))`). M: a bounded set of a normed
  algebra over a nontrivially normed field is norm-bounded. D: unfold `TopologicalRing.IsBounded`
  (for `U := ball 0 1 ∈ 𝓝 0` there is `V ∈ 𝓝 0` with `V • S ⊆ U`, in the chain's spelling), take
  `c : K` with `0 < ‖c‖` and `c • 1 ∈ V` (`NormedField.exists_norm_lt`, `Metric.mem_nhds_iff`), then
  `‖c • s‖ < 1` gives `‖s‖ < ‖c‖⁻¹` (`norm_smul`, `inv_mul_lt_iff₀`). A: [2] `S = ∅` ✓. [3]
  `NontriviallyNormedField` is necessary (over a trivially normed field every set is bounded in the
  chain's sense but not in norm — the trivially normed `K` acting on `ℝ`-normed `A`? the definition is
  over `K`-scalars, so this is the genuine counterexample shape). [5] the chain's definition is in
  `PowerBounded.lean`, `TopologicalRing.IsBounded`, verified by reading it. SURVIVED.
- **L0.9** `IsPowerBounded.exists_norm_pow_le` — Q: as L0.8. M: literal. D: L0.8 applied to
  `range (a ^ ·)`. A: [2] `a = 0` ✓. [5] one lemma. SURVIVED.
- **L0.10** `IsPowerBounded.map` — Q: [BGR] `bgr-6.1.1.md:43` *"Morphisms of `𝔄` map power-bounded
  elements into power-bounded elements."* M: for a ring homomorphism `φ` with `‖φ r‖ ≤ C ‖r‖`. D:
  `(φ a)^n = φ (a^n)` (`map_pow`), L0.9 gives `M`, so `‖(φ a)^n‖ ≤ C M`, then
  `isPowerBounded_of_norm_pow_le`. A: [1] without the bound (a merely additive, discontinuous `φ`) the
  statement is false; with continuity of a `K`-linear `φ` the bound exists (L4.3), which is how the
  consumers call it. [2] `C < 0` ✓ (then `φ = 0`). SURVIVED.

### Internal nodes

- **N0.1** `eval₂`, `eval₂_C`, `eval₂_X`, `eval₂_toRestricted`, `norm_eval₂_le`, `continuous_eval₂`
  (complete in the skeleton) — [6] the ring-homomorphism proofs `eval₂Fun_add/mul` were kept from Layer
  0 and only consume L0.6 through `summable_map_coeff_mul_prod_pow`; the gate compiles them. [2] the
  contractive case is `Cφ = Cx = 1` and `norm_eval₂_le` is `simpa` from L0.7 ✓. SURVIVED.
- **N0.2** `aeval` and its lemmas (complete) — built from `eval₂` with `norm_algebraMap_le_one_mul` and
  L0.3; Layer 0's consumers (`Chart.lean`, `MaxModulus.lean`, …) were rebuilt by the gate (`2764`
  jobs, 0 errors) ✓. SURVIVED.

---

## G1 — Quotient norms of ultrametric normed rings (`NormedQuotient.lean`), [RM] §1.1.1

### Source and prose proof

[BGR] 6.1.1 (`bgr-6.1.1.md:6–12`): *"Each residue algebra `Tₙ/𝔞` of `Tₙ` by a (closed) ideal `𝔞 ⊂ Tₙ`
becomes a `k`-Banach algebra if one defines the residue norm of the residue class `f̄` of an element
`f ∈ Tₙ` by `|f̄| := |f, 𝔞| := inf {|h| ; h ∈ f̄}`. The residue epimorphism `Tₙ → Tₙ/𝔞` is contractive
(hence continuous) and open."* [BGR] 3.7.1 (`bgr-3.7.md:11–13`): *"If `𝔞` is a closed ideal in a
`k`-Banach algebra `A`, it is easy to see that the residue algebra `A/𝔞` provided with the residue norm is
again a `k`-Banach algebra."* [Bo] 1.4/4 (`bosch-lectures.txt:1027–1041`): *"`|·|_α` is a `K`-algebra
norm … `Tₙ/𝔞` is complete under `|·|_α`."*

Mathlib supplies `Ideal.Quotient.normedCommRing` (closed ideal), `Ideal.Quotient.normedAlgebra`,
`Submodule.Quotient.completeSpace`. Two facts are missing. The quotient seminorm of an ultrametric
seminorm is ultrametric: `‖x + y‖ = inf_{m ↦ x + y} ‖m‖ ≤ inf ‖m₁ + m₂‖ ≤ max (inf ‖m₁‖, inf ‖m₂‖)`.
And for a proper closed ideal of a complete ring with `‖1‖ = 1`, `‖1̄‖ = 1`: an element `a ∈ I`
with `‖1 − a‖ < 1` would be `1 − (1 − a)`, a unit by the geometric series, so `I = ⊤`; hence
`‖1 − a‖ ≥ 1` for all `a ∈ I` and the infimum is attained at `a = 0`.

### Leaves

- **L1.1** `QuotientAddGroup.isUltrametricDist` — Q: [BGR] 1.1.6 (cited in the module docstring; the
  residue norm of a quotient group is the infimum over the coset), the ultrametric inequality is BGR's
  standing assumption *"non-Archimedean"* `bgr-3.7.md:8`. M: `IsUltrametricDist (M ⧸ S)` for any
  `AddSubgroup S`. D: `IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm` (the
  constructor from the norm inequality), `QuotientAddGroup.norm_mk`? — better `le_norm_iff` /
  `norm_lt_iff`: for `ε > max ‖x‖ ‖y‖` pick `m₁, m₂` with `‖mᵢ‖ < ε` (`QuotientAddGroup.norm_lt_iff`),
  then `‖m₁ + m₂‖ ≤ max < ε` and `mk (m₁ + m₂) = x + y`, so `‖x + y‖ < ε`; conclude by
  `le_of_forall_lt`. A: [2] `S = ⊤` (norm `0`) ✓; `S = ⊥` ✓. [3] no closedness needed (seminorm). [5]
  `QuotientAddGroup.norm_lt_iff`, `le_norm_iff` verified (Mathlib names, `Quotient.lean:144,148`).
  SURVIVED.
- **L1.2** `Ideal.Quotient.norm_mk_eq_norm_of_forall_le` — Q: [Bo] `bosch-lectures.txt:1032–1033`
  *"For any `f̄ ∈ Tₙ/𝔞`, there is an inverse image `f ∈ Tₙ` such that `|f̄|_α = |f|`"* (the nearest
  representative). M: if `f` is a nearest point of its coset, its class has norm `‖f‖`. D:
  `QuotientAddGroup.norm_mk` (`= infDist f S`), `le_antisymm`: `infDist_le_dist_of_mem` with `0 ∈ I`
  and `dist f 0 = ‖f‖`; `Metric.le_infDist` with `dist f a = ‖f − a‖ ≥ ‖f‖`. A: [2] `f = 0` ✓. [3] a
  seminormed ring suffices (no closedness). SURVIVED.
- **L1.3** `Ideal.Quotient.normOneClass_of_ne_top` — Q: [BGR] `bgr-6.1.1.md:6–9` (the residue norm
  is a `k`-algebra norm, which in BGR includes `|1| = 1` for `A ≠ 0`); [BGR] 1.2.4/4
  `bgr-3.7.md:135–136` *"each element of the form `e = 1 − y`, `y ∈ Ǎ`, is a unit."* M: `‖(1 : R ⧸ I)‖ = 1`
  for a proper closed ideal. D: L1.2 with `h : ∀ a ∈ I, ‖1‖ ≤ ‖1 − a‖`: if `‖1 − a‖ < ‖1‖ = 1`
  (`norm_one`) then `isUnit_one_sub_of_norm_lt_one` gives `IsUnit (1 − (1 − a)) = IsUnit a`, so
  `I = ⊤` (`Ideal.eq_top_of_isUnit_mem`), contradiction; then `norm_one`. A: [1] `I = ⊤`: `‖1̄‖ = 0`,
  which is why `hI` is needed ✓. [2] `R` zero ring: every ideal is `⊤` ✓ vacuous. [3] completeness is
  needed for the unit (`ℚ` with the `p`-adic norm and `I = (p)`? not closed there — the hypothesis
  `IsClosed` is in the instance; the statement is about the closed case). [4] BGR assumes `|1| = 1`
  for normed rings; we state `NormOneClass R`. SURVIVED.

---

## G2 — `R⟨X ⊕ Y⟩ ≅ R⟨Y⟩⟨X⟩`, renaming, and `Tₙ⟨Y_m⟩ ≅ T_{m+n}` (`Restricted/Sum.lean`), [RM] §1.1.3

### Source and prose proof

[BGR] 6.1.1/7–8 (`bgr-6.1.1.md:91–108`): *"If in particular `B = k⟨X₁, …, Xₙ⟩`, there exists by
Proposition 4 a unique continuous homomorphism `σ : A⟨X₁, …, Xₙ⟩ → A ⊗̂_k k⟨X₁, …, Xₙ⟩` such that
`Xᵢ ↦ 1 ⊗̂ Xᵢ`, `a ↦ a ⊗̂ 1` … one concludes that `σ` is an isomorphism. Furthermore, `σ` is obviously
contractive. Also `σ⁻¹` is contractive … **Corollary 8.** There are canonical isometric isomorphisms
`T_m ⊗̂_k Tₙ ≅ T_{m+n}`."* [RM] §1.1.3: *"`A⟨X⟩⟨Y⟩ ≅ A⟨X, Y⟩`"*.

Without complete tensor products the statement is the iteration isomorphism of restricted power
series: a series in `X ⊕ Y` is a series in `X` whose coefficients are series in `Y`. Both directions
are evaluation homomorphisms (BGR 6.1.1/4 as `eval₂`): `R⟨X ⊕ Y⟩ → R⟨Y⟩⟨X⟩` sends `X i ↦ X i`,
`Y j ↦ C (Y j)` along the constants `C ∘ C`; `R⟨Y⟩⟨X⟩ → R⟨X ⊕ Y⟩` sends the coefficients by the
evaluation `R⟨Y⟩ → R⟨X ⊕ Y⟩`, `Y j ↦ X (inr j)`, and `X i ↦ X (inl i)`. Both are contractive, both
compositions are continuous ring homomorphisms agreeing with the identity on constants and variables,
hence the identity by density of polynomials (Layer 0's `ringHom_ext_of_continuous`); two contractive
mutually inverse maps are isometries. Renaming variables along a bijection is the analogous pair of
evaluations (or the restriction of Mathlib's `MvPowerSeries.renameEquiv`). The Tate corollary
`Tₙ⟨Y₁, …, Y_m⟩ ≅ T_{m+n}` is built the same way at the unit polyradius, `Y j ↦ X (castAdd n j)`,
`X i ↦ X (natAdd m i)`, as a `K`-algebra isomorphism.

### Leaves

- **L2.1** `norm_sumTuple_le` — Q: `bgr-6.1.1.md:98` *"`σ` is obviously contractive"*. M: the images of
  the variables satisfy the bound `‖·‖ ≤ c i` needed by `eval₂`. D: `Sum.elim` cases; `norm_X` gives
  `‖1‖ * c i` with `norm_one` (`NormOneClass R` passes to `Restricted` by the floor's instance), and
  `norm_C`. A: [2] `σ` or `τ` empty ✓. [3] `NormOneClass R` is used (`‖X‖ = ‖1‖ c`); without it the
  bound `‖1‖ c i ≤ c i` can fail (`‖1‖ = 2`). SURVIVED.
- **L2.2** `iterToSum_comp_sumToIter` — Q: `bgr-6.1.1.md:96–98` *"the inclusions `σ₁`, `σ₂` satisfy
  the universal property … Thus one concludes that `σ` is an isomorphism."* M: `iterToSum ∘ sumToIter =
  id` on `R⟨X ⊕ Y⟩`. D: `ringHom_ext_of_continuous` (both sides continuous: `continuous_eval₂`
  composed; `hC`: `eval₂_C` twice; `hX`: by cases on `Sum`, `eval₂_X`, `Sum.elim_inl/inr`, and for
  `inr j` the inner `eval₂_X`). A: [6] the ext lemma needs `Fact (∀ i, 0 < c i)` on `σ ⊕ τ` ✓ and
  `T2Space` of the target ✓ (normed). [2] both index types empty: the ring is `R` ✓. SURVIVED.
- **L2.3** `sumToIter_comp_iterToSum` — Q: as L2.2. M: `= id` on `R⟨Y⟩⟨X⟩`. D: outer
  `ringHom_ext_of_continuous`: on `X i` by `eval₂_X` twice; on constants `C g` (`g ∈ R⟨Y⟩`) a second
  `ringHom_ext_of_continuous` in `g` for the two continuous homomorphisms `sumToIter ∘ (inner eval₂)`
  and `C (c ∘ inl)` (agree on `C r` and on `Y j ↦ X (inr j) ↦ C (Y j)`). A: [6] the inner ext is on
  `R⟨Y⟩` with `Fact` on `τ` (instance declared) ✓. [5] `RingHom.congr_fun` to pass from equality of
  homomorphisms to values. SURVIVED.
- **L2.4** `sumEquiv_C`, **L2.5** `sumEquiv_X_inl`, **L2.6** `sumEquiv_X_inr` — Q: `bgr-6.1.1.md:95`
  *"`Xᵢ ↦ 1 ⊗̂ Xᵢ`, `a ↦ a ⊗̂ 1`"*. M: the values of the isomorphism on constants and variables. D:
  `RingEquiv.ofRingHom_apply`, `eval₂_C` (composite `(C _).comp (C _)`, `RingHom.comp_apply`),
  `eval₂_X`, `sumTuple`, `Sum.elim_inl/inr`. A: [5] `RingEquiv.ofRingHom_apply` is `rfl`-level. SURVIVED.
- **L2.7** `norm_sumEquiv` — Q: `bgr-6.1.1.md:98–99` *"`σ` is obviously contractive. Also `σ⁻¹` is
  contractive."* M: isometry. D: `le_antisymm`: `norm_eval₂_le` (constants `1`) for `sumToIter`, and
  for `iterToSum` applied to `sumEquiv f` with `iterToSum_comp_sumToIter` (`RingHom.congr_fun`). No
  coefficient bookkeeping. A: [2] `f = 0` ✓. [3] `NormOneClass` enters only through L2.1. SURVIVED.
- **L2.8** `continuous_sumEquiv`, **L2.9** `continuous_sumEquiv_symm` — D: `continuous_eval₂` (the
  underlying maps are `eval₂`s; `RingEquiv.ofRingHom` coerces to them, `RingEquiv.ofRingHom_symm_apply`).
  A: [5] verified by the gate for the definitions. SURVIVED.
- **L2.10** `renameEquiv` (def), **L2.11** `renameEquiv_C`, **L2.12** `renameEquiv_X`, **L2.13**
  `norm_renameEquiv` — Q: [BGR] 5.1.3 (a chart; Layer 0's G9) and [RM] §1.1.3 (`Tₙ⟨Y⟩ ≅ T_{m+n}`
  needs `Fin m ⊕ Fin n ≃ Fin (m + n)`). M: the equivalence at the unit polyradius with its values and
  isometry. D: either the pair of evaluations `X i ↦ X (e i)`, `X j ↦ X (e.symm j)` with
  `ringHom_ext_of_continuous` (as L2.2–L2.7), or the restriction of Mathlib's
  `MvPowerSeries.renameEquiv e` to the subrings (restrictedness is preserved: the Gauss terms are
  permuted, `Finsupp.mapDomain` along `e`; then `norm_renameEquiv` is a reindexed supremum). The
  evaluation route reuses the proved `sumEquiv` pattern and is the planned one. A: [2] `σ` empty ✓.
  [3] stated at `1` only (D5): the general polyradius `c ∘ e.symm` is not syntactically a value the
  consumers have; nobody needs it. SURVIVED.
- **L2.14** `Affinoid.TateAlgebra.sumEquiv` (def) — Q: [BGR] 6.1.1/8 `bgr-6.1.1.md:107–108`
  *"`T_m ⊗̂_k Tₙ ≅ T_{m+n}`"*. M: `Tₙ⟨Y_m⟩ ≃ₐ[K] T_{m+n}`. D: `AlgEquiv.ofAlgHom` with forward
  `eval₂ (Cφ := 1) (Cx := 1) 1 (eval₂ 1 (C 1) (X ∘ Fin.natAdd m) … ) (X ∘ Fin.castAdd n) …`
  turned into a `K`-algebra homomorphism (`commutes'` by `algebraMap_eq_C_comp` and `eval₂_C`), inverse
  `aeval 1 (Fin.append (X _ 1) (C 1 ∘ X K 1)) hx`, and the two compositions by
  `algHom_ext_of_continuous` (the inner one for the constants as in L2.3; `Fin.append_left/right`,
  `Fin.castAdd`, `Fin.natAdd` with `Fin.addCases`). A: [6] both maps are contractive, which L2.15 uses.
  [2] `m = 0` or `n = 0` ✓ (degenerate `Fin.append`). [5] `Fin.append_left`, `Fin.append_right`,
  `finSumFinEquiv` not needed. SURVIVED.
- **L2.15** `Affinoid.TateAlgebra.norm_sumEquiv` — Q: `bgr-6.1.1.md:107` *"isometric"*. D:
  `norm_eval₂_le` both ways as in L2.7 (`norm_aeval_le` for the inverse). SURVIVED.
- **L2.16** `Affinoid.TateAlgebra.sumEquiv_C`, **L2.17** `sumEquiv_X` — D: `eval₂_C`, `eval₂_X` on the
  forward map; the statement of `sumEquiv_C` names the inner evaluation explicitly so that the
  consumer (`IsAffinoidAlgebra.restricted`, L8.10) can rewrite with it. A: [4] the roles of `castAdd`
  (the new variables first) and `natAdd` (the old ones last) follow BGR's `T_m ⊗̂ Tₙ ≅ T_{m+n}` with
  the `m` new variables first; any convention works, this one is fixed. SURVIVED.

### Internal node

- **N2** `sumEquiv` (ring equivalence, complete in the skeleton as `RingEquiv.ofRingHom`) — [6] the
  children L2.2–L2.3 are exactly its two obligations; the `Fact` instances for `c ∘ inl`, `c ∘ inr` are
  declared above it and are what the evaluations need. SURVIVED.

---

## G3 — Affinoid algebras and residue norms (`Affinoid/Basic.lean`), [RM] §1.1.1–1.1.2

### Source and prose proof

[BGR] 6.1.1/1 (`bgr-6.1.1.md:14–15`): *"A `k`-Banach algebra `A` is called affinoid (more precisely,
`k`-affinoid) if there exists an integer `n ≥ 0` and a continuous epimorphism `α : Tₙ → A`."* [Bo] 1.4/1
(`bosch-lectures.txt:1005–1006`): *"A `K`-algebra `A` is called an affinoid `K`-algebra if there is an
epimorphism `α : Tₙ → A` for some `n ∈ ℕ`."* The roadmap's convention 3 takes Bosch's ring-theoretic
form; BGR's topology is recovered in G8 (every presentation is continuous for every Banach norm).
[BGR] 6.1.1/2 (`bgr-6.1.1.md:23–25`): *"Let `A` be `k`-affinoid and let `|·|_α` be a residue norm on
`A`. Then `|A|_α ⊂ |k|`. In particular, each vector `≠ 0` in `A` can be normed to length 1 by
multiplication with a scalar. The assertion follows directly from Corollary 5.2.7/8."* [BGR] 6.1.1/3
(`bgr-6.1.1.md:31–36`): *"Let `A` be a `k`-affinoid algebra. Then `A` is a Noetherian Jacobson ring.
Each ideal `𝔞 ⊂ A` is closed, and each quotient `A/𝔞` (provided with the residue norm) is `k`-affinoid.
Proof. Let `α : Tₙ → A` be a continuous epimorphism. Then `A ≅ Tₙ/ker α` is a Noetherian Jacobson ring
since `Tₙ` is such a ring (Theorems 5.2.6/1 and 5.2.6/3). The closedness of any ideal `𝔞 ⊂ A` follows
from Proposition 3.7.2/2 (or simply from the closedness of ideals in `Tₙ`), and `A/𝔞` is `k`-affinoid,
since `Tₙ →α A → A/𝔞` is a continuous epimorphism."* [Bo] 1.4/2 (`bosch-lectures.txt:1008–1012`).

The residue norm on `Tₙ ⧸ I` is Mathlib's quotient norm, a norm because `I` is closed (Layer 0's
`isClosed_ideal`, now an instance); Mathlib's `Ideal.Quotient.normedAlgebra`, the quotient's
completeness (through the opaque `Restricted`: a shortcut instance), and G1 give the Banach algebra
with `‖1‖ = 1` when `I ≠ ⊤`. The residue norm is attained at a nearest point of the ideal (Layer 0's
strict closedness), takes values in `|K|` (Layer 0), and scalars normalise nonzero classes. Ideals of
`Tₙ ⧸ I` are closed because their preimages are and the residue map is a quotient map. Noetherian and
Jacobson pass through surjections (Mathlib), affinoidness through surjections and quotients by
composing presentations.

### Leaves

- **L3.1** `exists_norm_quotient_mk_eq` — Q: `bgr-6.1.1.md:25` *"follows directly from Corollary
  5.2.7/8"*; [Bo] `bosch-lectures.txt:1032–1033`. M: `‖f̄‖ = ‖f − a₀‖` at a nearest `a₀ ∈ I`. D: [L0]
  `exists_forall_norm_sub_le_ideal I f` gives `a₀`; `QuotientAddGroup.norm_mk` and the `infDist`
  computation of Layer 0's `norm_quotient_mk_mem_range_norm` (same four lines), or L1.2 applied to
  `f − a₀` with `mk (f − a₀) = mk f`. A: [2] `f ∈ I` ✓ (`a₀ = f`). [5] Layer 0 lemma verified.
  SURVIVED.
- **L3.2** `isClosed_ideal_quotient` — Q: `bgr-6.1.1.md:34–35` *"The closedness of any ideal `𝔞 ⊂ A`
  follows … simply from the closedness of ideals in `Tₙ`"*. M: ideals of `Tₙ ⧸ I` are closed. D:
  `J = (J.comap (mk I)).map (mk I)` (`Ideal.map_comap_of_surjective`), `IsClosed (J.comap mk)` by
  [L0] `isClosed_ideal`, and `(QuotientAddGroup.isQuotientMap_mk I.toAddSubgroup).isClosed_preimage`
  with `mk ⁻¹' J = J.comap mk` as sets (`Ideal.coe_comap`). A: [6] the topology of `Tₙ ⧸ I` as a
  `NormedCommRing` is the quotient topology — Mathlib's quotient-norm file states this ("the underlying
  topology is the quotient topology") and the `IsQuotientMap` lemma lives in
  `Topology/Algebra/Group/Quotient.lean` for the `QuotientAddGroup` topology instance; the two
  instances are the same by Mathlib's construction (`Submodule.Quotient.seminormedAddCommGroup` is
  `inferInstanceAs` the group quotient). [2] `J = ⊥` ✓. SURVIVED.
- **L3.3** `norm_quotient_mem_range_norm` — Q: `bgr-6.1.1.md:23–24` *"`|A|_α ⊂ |k|`"*. D:
  `Ideal.Quotient.mk_surjective` and [L0] `norm_quotient_mk_mem_range_norm`. SURVIVED.
- **L3.4** `exists_norm_smul_quotient_eq_one` — Q: `bgr-6.1.1.md:24–25` *"each vector `≠ 0` in `A` can
  be normed to length 1 by multiplication with a scalar"*. D: L3.3 gives `a` with `‖x‖ = ‖a‖`; `a ≠ 0`
  since `‖x‖ ≠ 0` (`norm_ne_zero_iff`, the quotient is a *normed* group as `I` is closed); take
  `a⁻¹`: `norm_smul`, `norm_inv`, `inv_mul_cancel₀`. A: [1] `x = 0` excluded ✓. [2] `I = ⊤`: no
  `x ≠ 0` ✓ vacuous. [3] the normed (not seminormed) structure is essential (`‖x‖ = 0 → x = 0`).
  SURVIVED.
- **L3.5** `IsAffinoidAlgebra.of_surjective` — Q: `bgr-6.1.1.md:35–36` *"`A/𝔞` is `k`-affinoid, since
  `Tₙ →α A → A/𝔞` is a continuous epimorphism"*. M: surjective images (the quotient is the special
  case `quotient`). D: `⟨n, φ.comp α, hφ.comp hα⟩`. A: [2] `B` zero ✓. SURVIVED.
- **L3.6** `exists_algEquiv_quotient` — Q: `bgr-6.1.1.md:17–18` *"`A` is isomorphic as a `k`-Banach
  algebra to the residue algebra `Tₙ/ker α`"* (the ring-theoretic half; the Banach half is G8). D:
  `Ideal.quotientKerAlgEquivOfSurjective`. A: [2] `A` zero: `I = ⊤` ✓. SURVIVED.
- **L3.7** `isNoetherianRing`, **L3.8** `isJacobsonRing` — Q: `bgr-6.1.1.md:33–34` *"`A ≅ Tₙ/ker α`
  is a Noetherian Jacobson ring since `Tₙ` is such a ring"*; [Bo] 1.4/2 (i), (ii). D:
  `isNoetherianRing_of_surjective _ _ α.toRingHom hα` with [L0] `instIsNoetherianRing`;
  `isJacobsonRing_of_surjective ⟨α.toRingHom, hα⟩` with [L0] `instIsJacobsonRing` (its argument
  shape — `(hf : ∃ f, Surjective f)`-like — is recorded in the ticket). A: [3] `[CompleteSpace K]` is
  carried and needed (Layer 0's instances need it, defect D5 of Layer 0). SURVIVED.

### Internal nodes

- **N3.1** the instances `instIsClosed`, `instCompleteSpaceQuotient`, `normOneClass_quotient` and the
  four `example`s (complete in the skeleton) — [6] `IsClosed` is a class in this Mathlib, so Layer 0's
  theorem becomes an instance verbatim; completeness needed the shortcut (plan, "Seam"). SURVIVED.
- **N3.2** `IsAffinoidAlgebra`, `tateAlgebra`, `quotient`, `of_algEquiv`, `tateAlgebra_quotient`,
  `of_subsingleton` (complete) — [4] the definition is Bosch's; BGR's continuity requirement is a
  theorem of G8, as the roadmap's convention 3 prescribes. [2] the zero algebra is affinoid
  (`of_subsingleton`; BGR's `A ≠ 0` appears only in 6.1.2/1). SURVIVED.

---

## G4 — The universal property of `A⟨X⟩` and affinoid generating systems (`Affinoid/Extend.lean`), [RM] §1.1.3

### Source and prose proof

[BGR] 6.1.1/4 (`bgr-6.1.1.md:45–54`, quoted in G0) and `bgr-6.1.1.md:52–54`: *"It is clear that this
is the only way to extend `φ` to the polynomial algebra `B[X₁, …, Xₙ]` and that `Φ` is a homomorphism
of `B[X₁, …, Xₙ]` into `A`. As `B[X₁, …, Xₙ]` is dense in `B⟨X₁, …, Xₙ⟩`, it follows that `Φ` is the
unique continuous extension of `φ`."* [BGR] `bgr-6.1.1.md:56–59`: *"for each set `f₁, …, fₙ ∈ Å` …
there exists exactly one continuous homomorphism `Φ : Tₙ → A` such that `Φ(Xᵢ) = fᵢ`. If `Φ` is
surjective, we call the elements `f₁, …, fₙ` a system of affinoid generators of `A`. In particular, `A`
is a `k`-affinoid algebra."* [BGR] 7.2.5 (`bgr-3.7.md:166–171`): *"A system `b = (b₁, …, bₙ)` of
power-bounded elements in `B` is called an affinoid generating system of `B` over `A` if the continuous
homomorphism `σ₁ : A⟨ζ₁, …, ζₙ⟩ → B` extending `σ` and mapping `ζᵢ` onto `bᵢ` … is surjective."*
[BGR] 6.1.1/5 (`bgr-6.1.1.md:66–70`): *"Let `B` be an object of `𝔄`, and let `φ : B → A` be a
continuous finite homomorphism into a `k`-Banach algebra `A`. Then `A ∈ 𝔄`. Proof. We may assume
`B = Tₙ` for some `n`. By assumption there are elements `a₁, …, a_m ∈ A` such that `A = Σ φ(Tₙ) aᵢ`. We
may assume `aᵢ ∈ Å`. By Proposition 4, the map `φ` extends to a continuous homomorphism
`Φ : Tₙ⟨Y₁, …, Y_m⟩ → A` such that `Φ(Yᵢ) = aᵢ`. Then `Φ` is surjective, and hence `A ∈ 𝔄`."* [BGR]
6.1.1/9 (`bgr-6.1.1.md:113–115`): *"By BANACH's Theorem, `φ` is open … we get continuous epimorphisms
`id_A ⊗̂ φ : A ⊗̂_k k⟨X⟩ → A ⊗̂_k B`"* — in our terms, `A⟨X⟩ → B⟨X⟩` is surjective for a surjective
continuous `A → B`.

`A⟨X⟩` is a normed `K`-algebra (scalars scale the Gauss norm by at most their norm). A continuous
`K`-algebra map is bounded (Mathlib), finitely many power-bounded elements have uniformly bounded
monomials (G0), so `eval₂` of G0 gives `extendAlgHom` with its values on constants and variables,
continuity, and the bound; uniqueness is Layer 0's density ext. "We may assume `aᵢ ∈ Å`" is the
rescaling by a scalar of small norm (nontrivially normed `K`), and "`Φ` is surjective" is the identity
`Σ φ(qᵢ) aᵢ = Φ(Σ C(qᵢ) Yᵢ)`. The reduction "we may assume `B = Tₙ`" needs the continuity of
presentations and is postponed to G8; here BGR 6.1.1/5 is proved for the source `Tₙ` and the
isomorphism `Tₙ⟨Y⟩ ≅ T_{m+n}` of G2. Functoriality `A⟨X⟩ → B⟨X⟩` is `extendAlgHom` along the
constants; its surjectivity for surjective `α` is the open mapping theorem applied to the coefficients.

### Leaves

- **L4.1** `norm_smul_le_of_normedAlgebra` — Q: [BGR] 3.7.1 `bgr-3.7.md:15–16` *"for every `k`-Banach
  algebra `A`, the algebra `A⟨X⟩` … is a `k`-Banach algebra"*. M: `‖k • f‖ ≤ ‖k‖ ‖f‖` (the `K`-algebra
  norm axiom). D: `norm_le_iff` on the Gauss terms; `(k • f).1 = k • f.1` (`rfl` for the general
  instance), `MvPowerSeries.coeff_smul`, `norm_smul_le` in `A`, `mul_assoc`, `norm_coeff_mul_prod_le`.
  A: [2] `k = 0` ✓. [3] equality fails over a normed ring `A` with `‖k • a‖ < ‖k‖ ‖a‖`; the inequality is
  what `NormedAlgebra` asks. [5] Layer 0's `norm_smul_eq` is the special case `A = K` and uses the
  same first half. SURVIVED.
- **L4.2** `isPowerBounded_X` — Q: `bgr-6.1.1.md:94–95` (`Xᵢ ↦ 1 ⊗̂ Xᵢ`, the variables are power-bounded
  in `A⟨X⟩`). D: `X ^ k = monomial (single i k) 1` (`X_pow_eq`-type floor lemma or
  `MvPowerSeries.X_pow_eq` through `Restricted.ext`), `norm_monomial` gives `‖1‖ * 1 = ‖1‖`;
  `isPowerBounded_of_norm_pow_le (C := ‖1‖)`. A: [2] `k = 0`: `‖1‖ ≤ ‖1‖` ✓; `A` zero ✓. [3] no
  `NormOneClass` (D9). SURVIVED.
- **L4.3** `exists_forall_norm_prod_pow_le_of_isPowerBounded` — Q: `bgr-6.1.1.md:51`. D: L0.9 for each
  `i` then L0.4. SURVIVED.
- **L4.4** `extendAlgHom` (the `commutes'` field) — Q: `bgr-6.1.1.md:47–48` *"`Φ | B = φ`"*. D:
  `algebraMap_eq_C_comp` (L0.2), `eval₂_C`, `φ.commutes`. A: [6] the `Classical.choose` bounds are
  fixed by `choose_spec` inside the definition; the lemmas below never unfold them. SURVIVED.
- **L4.5** `extendAlgHom_C`, **L4.6** `extendAlgHom_X` — Q: `bgr-6.1.1.md:48`. D: `eval₂_C`,
  `eval₂_X` (through `AlgHom.coe_mk`/`rfl`). SURVIVED.
- **L4.7** `extendAlgHom_comp_toAlgHom` — D: `AlgHom.ext`, `IsScalarTower.toAlgHom_apply`,
  `algebraMap_apply` (the floor: `algebraMap A (Restricted A 1) a = C 1 a`), L4.5. SURVIVED.
- **L4.8** `continuous_extendAlgHom`, **L4.9** `exists_forall_norm_extendAlgHom_le` — D:
  `continuous_eval₂`; `norm_eval₂_le_mul` with `C := |Cφ * Cx|`. SURVIVED.
- **L4.10** `extendAlgHom_unique` — Q: `bgr-6.1.1.md:53–54` *"`Φ` is the unique continuous
  extension of `φ`"*. D: `algHom_ext_of_continuous hψ (continuous_extendAlgHom …)` with `hX` from
  L4.6; the constants are automatic for `K`-algebra homomorphisms? — no: `algHom_ext_of_continuous`
  only needs the variables because both sides are `K`-algebra maps; the hypothesis `hC` (values on
  `C a`, `a ∈ A`) is **needed** since `A`-constants are not `K`-scalars. So the ext is the ring-level
  `ringHom_ext_of_continuous` with `hC` and `hX`, then `AlgHom.coe_ringHom_injective`. A: [3] without
  `hC` the statement is false (`A = K⟨T⟩`, `ψ` twisting `T`). The hypothesis is in the statement ✓.
  SURVIVED.
- **L4.11** `existsUnique_extend` — D: `⟨extendAlgHom …, ⟨L4.8, L4.5, L4.6⟩, fun ψ ⟨h₁, h₂, h₃⟩ ↦
  L4.10⟩`. SURVIVED.
- **L4.12** `extendAlgHom_ofId_eq_aeval` — Q: [RM] §1.1.3 (the case `A = K` is Layer 0's `aeval`). D:
  `algHom_ext_of_continuous` (both continuous: L4.8, `continuous_aeval`), `extendAlgHom_X`, `aeval_X`.
  A: [3] needs `IsUltrametricDist K` for `aeval` (added, D10's complement). SURVIVED.
- **L4.13** `isAffinoidGeneratingSystem_of_forall_exists_sum` — Q: `bgr-6.1.1.md:70` *"Then `Φ` is
  surjective"*. D: for `y` take `q`; `y = Φ (Σ i, C 1 (q i) * X A 1 i)` by `map_sum`, `map_mul`, L4.5,
  L4.6. A: [2] `σ` empty: `y = 0`? then `hgen` says every `y` is the empty sum `0`, so `B` is zero ✓
  consistent. SURVIVED.
- **L4.14** `exists_forall_norm_smul_le_one` — Q: `bgr-6.1.1.md:69` *"We may assume `aᵢ ∈ Å`"*. D:
  `NormedField.exists_norm_lt_one` gives `x`, `0 < ‖x‖ < 1`; `M := Finset.univ.sup' _ (‖a i‖)` or
  `∑ i, ‖a i‖` as a crude bound; `exists_pow_lt_of_lt_one` gives `N` with `‖x‖^N * M < 1`… simpler:
  `exists_pow_lt_of_lt_one (hM : 0 < 1 / (M + 1))`; `c := x ^ N`, `c ≠ 0` (`pow_ne_zero`),
  `‖c • a i‖ ≤ ‖c‖ ‖a i‖ ≤ ‖x‖^N (M + 1) ≤ 1` (`norm_smul_le`, `norm_pow`). A: [2] `σ` empty: `c = 1`
  ✓. [3] `NontriviallyNormedField` is necessary (trivial norm, `‖a‖ = 2`). SURVIVED.
- **L4.15** `exists_isAffinoidGeneratingSystem_of_finite` — Q: `bgr-6.1.1.md:68–70`. D: `hfin` is
  `Module.Finite A B` for `φ.toRingHom.toAlgebra`; `Module.Finite.exists_fin` gives `a : Fin m → B`
  spanning; L4.14 gives `c`; `b i := c • a i`, power-bounded by `isPowerBounded_of_norm_le_one`;
  `hgen`: `mem_span_range_iff_exists_fun` writes `y = Σ qᵢ • aᵢ` with `qᵢ • aᵢ = φ qᵢ * aᵢ`
  (`RingHom.smul_toAlgebra`/`Algebra.smul_def`), and `φ qᵢ * aᵢ = φ (c⁻¹ • qᵢ) * (c • aᵢ)`
  (`map_smul`, `smul_mul_smul_comm`, `inv_mul_cancel₀`, `one_smul`); conclude by L4.13. A: [2] `m = 0`
  (`B` zero) ✓. [6] the two module structures on `B` (over `A` via `φ`, over `K`) interact only
  through `map_smul` ✓. SURVIVED.
- **L4.16** `continuous_algebraMap_restricted` — D: `funext` with `algebraMap_apply` then
  `continuous_C`. SURVIVED.
- **L4.17** `mapAlgHom_C`, **L4.18** `mapAlgHom_X` — D: L4.5 with `IsScalarTower.toAlgHom_apply`,
  `algebraMap_apply`; L4.6. SURVIVED.
- **L4.19** `coeff_mapAlgHom` — Q: `bgr-6.1.1.md:115` (`id_A ⊗̂ φ` acts on coefficients). D:
  `hasSum_eval₂` for `mapAlgHom`, mapped by the continuous additive map `g ↦ coeff t g.1`
  (`AddMonoidHomClass.continuous_of_bound` with `norm_coeff_le`), giving
  `HasSum (fun ν ↦ coeff t (C (α a_ν) * X^ν)) (coeff t (Φ f))`; the summand is `if ν = t then α a_t
  else 0` (`coeff_C_mul`, `coeff_X_pow`/`coeff_monomial`), so `hasSum_ite_eq` and `HasSum.unique`.
  A: [2] `t` outside the support ✓ (`0`). [5] `hasSum_ite_eq`, `HasSum.unique`, `HasSum.map`
  verified. SURVIVED.
- **L4.20** `surjective_mapAlgHom_of_surjective` — Q: `bgr-6.1.1.md:113–115` (Banach's theorem).
  D: `ContinuousLinearMap.exists_preimage_norm_le` for `α` as `A →L[K] B` (`LinearMap.toContinuousLinearMap`
  needs the bound: `AlgHom.toLinearMap` + `continuous_of_bound`); choose lifts `a_ν` of `coeff ν g`
  with `‖a_ν‖ ≤ C ‖coeff ν g‖`; `IsRestricted 1 (fun ν ↦ a_ν)` by `squeeze_zero` from `g.2`; the
  series `f := ⟨…, _⟩` satisfies `Φ f = g` by `Restricted.ext`, `MvPowerSeries.ext`, L4.19. A: [3]
  `CompleteSpace A` necessary (open mapping). [2] `g = 0` ✓. SURVIVED.
- **L4.21** `IsAffinoidAlgebra.of_isAffinoidGeneratingSystem` — Q: `bgr-6.1.1.md:58–59` *"In
  particular, `A` is a `k`-affinoid algebra"*. D: `⟨n, extendAlgHom …, hsurj⟩` — `Restricted K
  (1 : Fin n → ℝ)` *is* `TateAlgebra K n` by the abbreviation. SURVIVED.
- **L4.22** `of_isAffinoidGeneratingSystem_tateAlgebra` — Q: `bgr-6.1.1.md:70`. D: `⟨m + n, Φ.comp
  (TateAlgebra.sumEquiv K n m).symm.toAlgHom, hsurj.comp (sumEquiv …).symm.surjective⟩`. SURVIVED.
- **L4.23** `of_finite_tateAlgebra` — D: L4.15 then L4.22. SURVIVED.

### Internal nodes

- **N4.1** `instNormedAlgebraOfNormedAlgebra` (complete, from L4.1) — [6] its `toAlgebra` is the
  floor's general `Algebra K (Restricted A c)` instance, the same one `IsScalarTower.toAlgHom`
  uses; for `A = K` it coincides with Layer 0's `instNormedAlgebra` (same `Algebra`, `Prop` field).
  SURVIVED.
- **N4.2** `mapAlgHom`, `inlAlgHom`, `inrAlgHom` (definitions by `extendAlgHom`, complete) — [6] they
  need `isPowerBounded_X` without `NormOneClass` (D9) so that the zero algebra is allowed. SURVIVED.

---

## G5 — Ideals of a noetherian Banach algebra are closed (`BanachAlgebra/Noetherian.lean`), [RM] §1.3 (input to BGR 3.7.5/2)

### Source and prose proof

[BGR] 3.7.2/1 (`bgr-3.7.md:27–33`): *"Let `A` be a `k`-Banach algebra and let `M` be a normed
`A`-module such that the completion `M̂` of `M` is a finite `A`-module. Then `M` is complete. Proof.
There are elements `x₁, …, xₙ ∈ M̂` such that the homomorphism `π : Aⁿ → M̂` defined by `π(a₁, …, aₙ)
:= Σ aᵢ xᵢ` is surjective. By BANACH's Theorem, `π` is open, and therefore `Σ Ǎ xᵢ = π(Ǎⁿ)` is a
neighborhood of `0` in `M̂`. Since `M` is dense in `M̂`, we have `x_ν ∈ M + Σ Ǎ x_μ` for `ν = 1, …, n`.
Now NAKAYAMA's Lemma 1.2.4/6 yields `M = M̂`."* [BGR] 3.7.2/2 (`bgr-3.7.md:39–41`): *"the ring `A` is
Noetherian if and only if all ideals in `A` are closed."* [BGR] 1.2.4/6 (`bgr-3.7.md:142–151`): *"Let `A`
be complete and let `M` be an `A`-module. Let `N` be a submodule of `M` such that there are elements
`x₁, …, xₙ` in `M` with the property: `M ⊂ N + Σ Ǎ x_μ`. Then `N = M`. Proof. … `y = (I − C) x` … it is
enough to show that `det(I − C)` is a unit in `A`. But clearly `det(I − C)` is of the form `1 − c` with
`c ∈ Ǎ` … Hence Proposition 4 gives `det(I − C) ∈ E(A)`."*

For an ideal `I` of a noetherian Banach algebra, `M := I` with completion `M̂ = J := closure I`, a
finitely generated ideal: BGR's argument becomes: generators `x` of `J`, the open map `Aⁿ → J`
(Mathlib's open mapping theorem gives coefficients bounded by `C‖y‖`), density of `I` in `J` gives
`xᵢ = yᵢ + Σ c_{iμ} x_μ` with `yᵢ ∈ I`, `‖c_{iμ}‖ < 1`, and the nonarchimedean Nakayama lemma gives
`xᵢ ∈ I`, so `J = I`. The Nakayama lemma itself is Mathlib's (`Submodule.le_of_le_smul_of_le_jacobson_bot`)
over the unit-ball subring `A°` with its ideal `𝔫 = {‖c‖ < 1} ≤ jacobson ⊥` (PFA), applied to the
`A°`-span of the generators: BGR's determinant argument is inside Mathlib's proof.

### Leaves

- **L5.1** `Ideal.forall_mem_of_forall_exists_eq_add_sum_mul_of_norm_lt_one` — Q: `bgr-3.7.md:142–143`
  (Lemma 1.2.4/6, with `Ǎ` replaced by the open unit ball, which BGR's own Proposition 1.2.4/4 remark
  `bgr-3.7.md:137` allows: *"Proposition 4 remains true if one replaces `Ǎ` by `A^∨`"*). M: `M = A`,
  `N = I`, generators `x`, conclusion `xᵢ ∈ I`. D: `letI := (unitClosedBall A).toAlgebra`?
  (`Subring` acts on `A`: the instance `Algebra ↥S A` for a subring is `Subring.toAlgebra`? — in
  Mathlib it is `Algebra.ofSubring`… the ticket records `Subalgebra.toAlgebra`-style name after a
  `#synth`; fallback: `Module (unitClosedBall A) A` by `Submonoid.smul`/`Subring.module`? — a
  `#synth Module ↥(unitClosedBall A) A` is the first step of the ticket); `N' := Submodule.span A°
  (range x)`, `N := I.restrictScalars A°`; hypothesis `N' ≤ N ⊔ 𝔫 • N'` by `Submodule.span_le` and the
  decomposition `x i = y + Σ c_μ * x_μ` with `⟨c_μ, _⟩ ∈ openUnitBallIdeal` (`mem_openUnitBallIdeal`)
  and `Submodule.smul_mem_smul`; `Submodule.le_of_le_smul_of_le_jacobson_bot (fg_span (finite_range x))
  openUnitBallIdeal_le_jacobson_bot`; then `subset_span` ∘ `mem_range_self`. A: [1] the `A°`-span is
  the right module: over `A` the ideal `𝔫 A` would be everything. [2] `n = 0` ✓ vacuous. [3]
  `NormOneClass`, `IsUltrametricDist`, `CompleteSpace` are what make `A°` a subring with
  `𝔫 ≤ jacobson ⊥` ([PFA] `openUnitBallIdeal_le_jacobson_bot` needs all three) ✓ carried. [4] BGR's
  statement is for arbitrary modules; ours is the ring case BGR 3.7.2/1 uses. SURVIVED.
- **L5.2** `Ideal.exists_forall_exists_eq_sum_mul_norm_le` — Q: `bgr-3.7.md:29–31` *"By BANACH's
  Theorem, `π` is open"*. M: bounded coefficients (D1 repaired the carrier to an ideal). D: `J` as a
  closed `K`-subspace `Jₖ := (J.restrictScalars K)` with `IsClosed` ✓ hence `CompleteSpace ↥Jₖ`
  (`IsClosed.completeSpace_coe`); `π : (Fin n → A) →L[K] ↥Jₖ`, `π a := ⟨Σ aᵢ xᵢ, J.sum_mem …⟩`
  (`LinearMap.codRestrict`, continuity by `continuous_finset_sum`); surjective by `hx ▸
  Ideal.mem_span_range_iff_exists_fun`; `ContinuousLinearMap.exists_preimage_norm_le π hsurj` gives
  `C > 0` and preimages with `‖a‖ ≤ C ‖y‖`, and `‖a i‖ ≤ ‖a‖` (`norm_le_pi_norm`). A: [2] `n = 0`:
  `J = ⊥`, `y = 0` ✓. [3] `CompleteSpace A` needed; `NontriviallyNormedField K` needed (open mapping).
  [5] `ContinuousLinearMap.exists_preimage_norm_le` (`Banach.lean:162`) verified. SURVIVED.
- **L5.3** `Ideal.isClosed_coe_closure_restrictScalars` — D: `Ideal.coe_closure`, `isClosed_closure`.
  SURVIVED.
- **L5.4** `Ideal.isClosed_of_fg_closure` — Q: `bgr-3.7.md:27–33`. D: `hfg : I.closure.FG` gives
  `x : Fin n → A` with `span (range x) = I.closure` (`Submodule.fg_iff_exists_fin_generating_family`);
  L5.2 with `hJ := isClosed_closure` (through L5.3 / `Ideal.coe_closure`) gives `C`; for each `i`,
  `x i ∈ closure I` so (`Metric.mem_closure_iff`) there is `yᵢ ∈ I` with `‖x i − yᵢ‖ < C⁻¹`; then
  `x i − yᵢ ∈ I.closure` and L5.2 writes it as `Σ c_μ x_μ` with `‖c_μ‖ ≤ C ‖x i − yᵢ‖ < 1`; L5.1 gives
  `x i ∈ I`, so `I.closure = span ≤ I`, i.e. `closure I ⊆ I`, `isClosed_of_closure_subset`. A: [6]
  `C > 0` is needed to divide ✓ provided by L5.2. [2] `I = ⊥`: closure `⊥` ✓. SURVIVED.

### Internal node

- **N5** `Ideal.isClosed_of_isNoetherianRing` (complete: `I.isClosed_of_fg_closure
  (IsNoetherian.noetherian _)`) — [6] `Ideal.closure` is an ideal of the noetherian ring ✓. SURVIVED.

---

## G6 — Automatic continuity for Banach algebras (`BanachAlgebra/Continuity.lean`), [RM] §1.3.2–1.3.3

### Source and prose proof

[BGR] 3.7.5/1 (`bgr-3.7.md:97–111`): *"Let `A`, `B` be `k`-Banach algebras, and let `Φ : A → B` be a
`k`-algebra homomorphism. Assume that there is a family `𝔅` of ideals in `B` such that (i) each
`𝔟 ∈ 𝔅` is closed in `B` and each inverse image `Φ⁻¹(𝔟)` is closed in `A`, (ii) for each `𝔟 ∈ 𝔅` one
has `dim_k B/𝔟 < ∞`, (iii) `⋂ 𝔟 = (0)`. Then `Φ` is continuous. Proof. … `A/ker ψ` and `B/𝔟` provided
with the residue norms are finite-dimensional weakly cartesian `k`-vector spaces. Therefore `ψ̄` and
hence `ψ` are continuous. Now we get the continuity of `Φ` from the Closed Graph Theorem; namely,
assume there is given a sequence `aₙ ∈ A` with `lim aₙ = 0` and `lim Φ(aₙ) = b`. … `β(b) = … = 0`, i.e.
`b ∈ 𝔟`. Since this holds for all `𝔟 ∈ 𝔅`, we deduce `b = 0` from (iii)."* [BGR] 3.7.5/2
(`bgr-3.7.md:113–116`): *"Let `B` be a Noetherian `k`-Banach algebra with a family `𝔅` of ideals of `B`
such that (i) `dim_k B/𝔟 < ∞`, (ii) `⋂ 𝔟 = (0)`. Then each `k`-algebra homomorphism of a Noetherian
`k`-Banach algebra `A` into `B` is continuous."* [BGR] 3.7.5/3 (`bgr-3.7.md:118–121`): *"All complete
`k`-algebra norms (if there exist any) on a Noetherian `k`-algebra `B` with a family `𝔅` of ideals
satisfying conditions (i) and (ii) … are equivalent."*

"Weakly cartesian" is Mathlib's: a linear map out of a finite-dimensional normed space over a complete
field is continuous. The map `A → B/𝔟` factors through `A/ker ψ`, finite-dimensional (it injects into
`B/𝔟`) and Hausdorff (`ker ψ = Φ⁻¹𝔟` closed), so it is continuous. Mathlib's sequential closed graph
theorem then gives continuity of `Φ`. For noetherian algebras all ideals are closed (G5), which is
3.7.5/2; 3.7.5/3 is 3.7.5/2 for an isomorphism, whose inverse is continuous by the open mapping
theorem, and the norms are equivalent by boundedness of continuous linear maps.

### Leaves

- **L6.1** `LinearMap.continuous_of_isClosed_ker_of_finiteDimensional` — Q: `bgr-3.7.md:105–107`
  *"the residue spaces `A/ker ψ` and `B/𝔟` provided with the residue norms are finite-dimensional
  weakly cartesian `k`-vector spaces. Therefore `ψ̄` and hence `ψ` are continuous."* M: a linear map
  into a finite-dimensional normed space with closed kernel is continuous. D: `haveI :=
  Fact.mk hf`? no — the quotient's `NormedAddCommGroup` instance takes `[IsClosed (ker f : Set E)]`
  (`Submodule.Quotient.normedAddCommGroup`), supplied by `haveI`; `FiniteDimensional K (E ⧸ ker f)` from
  `(LinearMap.quotKerEquivRange f).finiteDimensional` and the instance for `range f ≤ F`
  (`Submodule.finiteDimensional_of_le`/`FiniteDimensional.finiteDimensional_submodule`);
  `f = (ker f).liftQ f le_rfl ∘ mkQ` (`Submodule.liftQ_mkQ`); `LinearMap.continuous_of_finiteDimensional`
  for the lift (domain `E ⧸ ker f` is `T2` because normed) and `continuous_quot_mk` for `mkQ`. A: [1]
  without closedness the kernel of a discontinuous functional is dense, not closed ✓ hypothesis
  needed. [2] `F` zero ✓. [3] `CompleteSpace K` is needed by Mathlib's finite-dimensional continuity.
  [5] `LinearMap.quotKerEquivRange`, `Submodule.liftQ_mkQ`, `LinearMap.continuous_of_finiteDimensional`
  verified. SURVIVED.
- **L6.2** `AlgHom.continuous_quotient_mk_comp_of_isClosed` — Q: `bgr-3.7.md:103–105` *"Define
  `ψ : A → B/𝔟` by `ψ := β ∘ Φ` … Obviously `ker ψ = Φ⁻¹(𝔟)`."* D: `RingHom.ker ((mkₐ K 𝔟).comp Φ) =
  𝔟.comap Φ` (`Ideal.comap_comap`, `Ideal.mk_ker`), L6.1 on `.toLinearMap` (the `NormedAlgebra K
  (B ⧸ 𝔟)` instance from the `IsClosed` instance argument). A: [6] the kernel as an `Ideal` versus
  `LinearMap.ker`: `AlgHom.ker_toLinearMap`-type coercion, `Ideal.coe_comap`. SURVIVED.
- **L6.3** `AlgHom.continuous_of_forall_isClosed_of_finiteDimensional` — Q: `bgr-3.7.md:107–111`.
  D: `LinearMap.continuous_of_seq_closed_graph Φ.toLinearMap`: given `u → x`, `Φ ∘ u → y`; for `𝔟 ∈ 𝔅`
  (with `haveI` for closedness and finite-dimensionality), L6.2 gives `mk (Φ (u n)) → mk (Φ x)`
  (`Continuous.tendsto` composed with `Tendsto`), and `mk (Φ (u n)) → mk y` (`continuous_quot_mk`);
  `tendsto_nhds_unique` (`T2Space` of the normed quotient) gives `mk y = mk (Φ x)`, i.e.
  `y − Φ x ∈ 𝔟` (`Ideal.Quotient.eq`); so `y − Φ x ∈ sInf 𝔅 = ⊥` (`Ideal.mem_sInf`), `sub_eq_zero`.
  A: [2] `𝔅 = ∅`: `sInf ∅ = ⊤ ≠ ⊥` unless `B` is zero ✓ (then everything is continuous). [3] completeness
  of both `A` and `B` is needed by the closed graph theorem ✓. [5] `tendsto_nhds_unique`,
  `Ideal.mem_sInf`, `Ideal.Quotient.eq` verified. SURVIVED.
- **L6.4** `AlgHom.continuous_of_isNoetherianRing` — Q: `bgr-3.7.md:113`. D: L6.3 with
  `hB := fun 𝔟 _ ↦ 𝔟.isClosed_of_isNoetherianRing`, `hA := fun 𝔟 _ ↦ (𝔟.comap Φ).isClosed_of_isNoetherianRing`.
  A: [3] `NormOneClass`, `IsUltrametricDist` on both sides are G5's hypotheses (plan, "Banach algebra
  conventions"). SURVIVED.
- **L6.5** `AlgEquiv.continuous_symm_of_isNoetherianRing` — Q: `bgr-3.7.md:118–121`. D: `e` is
  continuous (`continuous_of_isNoetherianRing`); `LinearEquiv.continuous_symm e.toLinearEquiv h`
  (Mathlib, `Banach.lean:313`, needs `CompleteSpace` on both sides ✓). A: [2] `A` zero ✓. SURVIVED.
- **L6.6** `AlgEquiv.exists_forall_norm_le_mul_of_isNoetherianRing` — D: L6.4/L6.5 and
  `SemilinearMapClass.bound_of_continuous` twice (`e.toAlgHom`, `e.symm.toAlgHom`). SURVIVED.

### Internal node

- **N6** `AlgEquiv.continuous_of_isNoetherianRing` (complete: L6.4 applied to `e.toAlgHom`). SURVIVED.

---

## G7 — Noether normalisation and its consequences (`Affinoid/Noether.lean`), [RM] §1.2

### Source and prose proof

[BGR] 6.1.2/1 (`bgr-6.1.2.md:20–41`): *"(i) Let `A` be a non-zero `k`-affinoid algebra. For every
finite homomorphism `α : Tₙ → A`, there exist a chart `{X₁, …, Xₙ}` of `Tₙ` and an integer `d ≥ 0` such
that `α | k⟨X₁, …, X_d⟩` is finite and injective. (ii) Let `φ : B → A` be a finite homomorphism between
non-zero `k`-affinoid algebras. Then there exists a homomorphism `ψ : T_d → B` for some `d ≥ 0` such that
`φ ∘ ψ : T_d → B → A` is finite and injective. Proof. … By choosing an epimorphism `α : Tₙ → B` and
applying the first statement to the map `φ ∘ α : Tₙ → A`, one gets a subalgebra `T_d ⊂ Tₙ` such that
`(φ ∘ α) | T_d` is finite and injective. Then `ψ := α | T_d` has the required properties. Now let us
prove the first assertion. We proceed by induction on `n`. The case `n = 0` is trivial. Let `n ≥ 1`. If
`ker α = 0`, there is nothing to prove. Otherwise we can find a chart `{X₁, …, Xₙ}` of `Tₙ` and a
Weierstrass polynomial `ω ∈ T_{n−1}[Xₙ]` such that `ω ∈ ker α`. Then `α` induces a finite homomorphism
`ᾱ : Tₙ/ωTₙ → A`. By the WEIERSTRASS Finiteness Theorem 5.2.3/4, the natural injection `T_{n−1} → Tₙ`
induces a finite monomorphism `β : T_{n−1} → Tₙ/ωTₙ`. Obviously, `ᾱ ∘ β` is finite, and one has
`ᾱ ∘ β = α | k⟨X₁, …, X_{n−1}⟩`. Applying the induction hypothesis to `T_{n−1}` and `ᾱ ∘ β`, we get the
theorem."* [BGR] 6.1.2/2 (`:46–47`), Remark (`:49–57`): *"`dim A = dim T_d` (for example, use NAGATA
Corollary 10.10), and `dim T_d = d`"*; 6.1.2/3 (`:59–65`): *"let `𝔮` be an ideal in `A` such that its
nilradical `rad 𝔮` is a maximal ideal in `A`. Then `A/𝔮` is finite over `k`. Proof. By the theorem, there
exists a finite monomorphism `φ : T_d → A/𝔮` for some `d ≥ 0`. We claim `d = 0`, i.e., `T_d = k`. The
composition of `φ` with the canonical epimorphism `ϱ : A/𝔮 → A/rad 𝔮` is finite and injective (because
`T_d` is reduced). The ideal `rad 𝔮` being maximal, we see that `T_d` has a finite extension which is a
field. But then `T_d` must itself be a field so that `d = 0` and `T_d = k`."*; 6.1.2/4 (`:69–75`): *"Every
`k`-affinoid algebra `A` which is an integral domain is Japanese. Proof. Let `A′` be an integral extension
of `A` such that its field of fractions `Q(A′)` is a finite extension of `Q(A)`. We have to show `A′` is a
finite `A`-module. By the theorem, there is a normalization map `φ : T_d → A` for a suitable `d ≥ 0`.
Then `A′` is an integral extension of `T_d`, and `Q(A′)` is finite over `Q(T_d)`. Since `T_d` is Japanese
by Theorem 5.3.1/3, we see that `A′` is a finite `T_d`-module and a fortiori a finite `A`-module."*
[Bo] 1.4/2 (iii), 1.4/3 (`bosch-lectures.txt:1011–1019`).

Our distinguished variable is `X 0` (roadmap convention 2), so the chart is Layer 0's `shear` and the
"Weierstrass polynomial in the kernel" is an `X 0`-distinguished series (Layer 0's `exists_shear_isMulDistinguishedX0`
and `finite_mk_comp_ofTail_of_isMulDistinguishedX0`, which hides the Weierstrass polynomial). The induction
is on `n` for finite `β : Tₙ →ₐ[K] A`, and the chart followed by the inclusion of the last `d` variables is the
map `ψ : T_d → Tₙ` of the statement. The dimension equality is Layer 0's `ringKrullDim_le_of_isIntegral`
(integral maps do not raise the dimension) together with going-up for injective integral maps (Mathlib's
`exists_ltSeries_of_hasGoingUp`), and `dim T_d = d` (Layer 0). Finite residue rings: `T_d` injects
integrally into the field `A/rad 𝔮`, so it is a field (Mathlib), so `d = 0` by the dimension, and
"finite over `T₀ = K`" is finite-dimensionality. Japaneseness transports along `T_d → A` because
integrality is transitive and `Q(A)` is finite over `Q(T_d)` (the fraction field of a finite extension of
domains is the localisation at the nonzero elements of the base, Mathlib's `Module.Finite.of_isLocalization`).

### Leaves

- **L7.1** `finite_comp_ofTail_of_isMulDistinguishedX0` — Q: `bgr-6.1.2.md:37–40` *"`α` induces a
  finite homomorphism `ᾱ : Tₙ/ωTₙ → A` … `β : T_{n−1} → Tₙ/ωTₙ` [finite] … `ᾱ ∘ β` is finite"*. M: the
  Weierstrass polynomial replaced by any distinguished `g` in the kernel. D: `hle : span {g} ≤ ker φ`,
  `φ' := Ideal.Quotient.lift _ φ`, `φ = φ'.comp (mk _)` (`Ideal.Quotient.lift_comp_mk`),
  `RingHom.Finite.of_comp_finite` gives `φ'.Finite`, and `(φ'.comp ((mk _).comp (ofTail K n))).Finite`
  by `RingHom.Finite.comp` with [L0] `finite_mk_comp_ofTail_of_isMulDistinguishedX0`; rewrite by
  `RingHom.comp_assoc`. The proof is Layer 0's `IsWeierstrassPolynomial.finite_comp_ofTail` with `g` for
  `ofPolynomial ω`. A: [2] `s = 0` (`g` a unit): the quotient is zero, `φ = 0`, `A` zero ✓ consistent.
  SURVIVED.
- **L7.2** `injective_mk_comp_ofTail_of_isMulDistinguishedX0` — Q: `bgr-6.1.2.md:38–39` *"a finite
  monomorphism `β : T_{n−1} → Tₙ/ωTₙ`"*. D: if `mk (ofTail f) = 0` then `ofTail f = q * g`
  (`Ideal.Quotient.eq_zero_iff_mem`, `Ideal.mem_span_singleton'`); two Weierstrass divisions of
  `ofTail f` by `g`: `q * g + ofPolynomial 0` and `0 * g + ofPolynomial (Polynomial.C f)` (the latter has
  `degree (C f) ≤ 0 < s`); [L0] `weierstrassDivision_r_unique` gives `Polynomial.C f = 0`
  (`ofPolynomial_injective`), so `f = 0` (`Polynomial.C_eq_zero`). A: [1] `s = 0` is a counterexample
  (D6) ✓ excluded. [5] the exact argument order of `weierstrassDivision_r_unique` is recorded in the
  ticket (`signatures.txt` / `#check`). SURVIVED.
- **L7.3** `exists_finite_comp_shear_symm_comp_ofTail` — Q: `bgr-6.1.2.md:32–34` *"we can find a chart
  … and a Weierstrass polynomial `ω` … such that `ω ∈ ker α`"*. D: [L0] `exists_shear_isMulDistinguishedX0
  hf` gives `e, s, hs`; `β' := β.comp (shear K n e).symm.toAlgHom` is finite
  (`RingHom.Finite.comp hβ (RingHom.Finite.of_surjective _ (shear …).symm.surjective)`) and kills
  `shear K n e f` (`AlgEquiv.symm_apply_apply`); L7.1 with `g := shear K n e f`. A: [6] `AlgHom.comp`
  versus `RingHom.comp` coercions: `AlgHom.comp_toRingHom`. SURVIVED.
- **L7.4** `injective_of_nontrivial` — Q: `bgr-6.1.2.md:31` *"The case `n = 0` is trivial."* D:
  `T₀ ≃+* K` ([L0] `isEmptyEquiv`); `(β.toRingHom.comp (isEmptyEquiv K 1).symm.toRingHom).injective`
  (`RingHom.injective` for a division ring source into a nontrivial ring), then `Function.Injective.of_comp`
  with the bijection. A: [1] `A` zero: not injective ✓ hypothesis needed. SURVIVED.
- **L7.5** `Affinoid.TateAlgebra.exists_finite_injective_comp` — Q: `bgr-6.1.2.md:31–41` (the
  induction). D: `induction n` generalising `β`; base: `⟨0, le_rfl, AlgHom.id _ _, by simpa, L7.4 β⟩`;
  step: `by_cases hker : RingHom.ker β = ⊥`: then `⟨n + 1, le_rfl, AlgHom.id, hβ, (RingHom.injective_iff_ker_eq_bot _).2 hker⟩`;
  else `Submodule.exists_mem_ne_zero_of_ne_bot hker` gives `f ≠ 0` in the kernel; L7.3 gives `e`; the
  induction hypothesis on `β'' := (β.comp (shear K n e).symm.toAlgHom).comp (ofTailAlgHom K n)` gives
  `d ≤ n`, `ψ'`; take `ψ := ((shear K n e).symm.toAlgHom.comp (ofTailAlgHom K n)).comp ψ'` with
  `β.comp ψ = β''.comp ψ'` (`AlgHom.comp_assoc`), `d ≤ n + 1`. A: [2] `A` zero: excluded by
  `Nontrivial A` (then no injective map from `T_d`) ✓. [6] the induction hypothesis is used for an
  arbitrary finite `β''`, which is why the statement quantifies over all finite `β` and not only over
  presentations (BGR's (i) is stated for finite `α` for this reason). SURVIVED.
- **L7.6** `IsAffinoidAlgebra.exists_finite_injective_comp` — Q: `bgr-6.1.2.md:27–30` (the
  reduction (ii) → (i)). D: `hB` gives `α`; `(φ.comp α).toRingHom.Finite` by `RingHom.Finite.comp hφ
  (RingHom.Finite.of_surjective _ hα)`; L7.5 gives `d, ψ`; `⟨d, α.comp ψ, by rwa [← AlgHom.comp_assoc], …⟩`.
  SURVIVED.
- **L7.7** `IsAffinoidAlgebra.exists_finite_injective` — Q: `bgr-6.1.2.md:46–47`. D: L7.6 with
  `φ := AlgHom.id`, `RingHom.Finite.id`. SURVIVED.
- **L7.8** `ringKrullDim_le_of_isIntegral_of_injective` — Q: `bgr-6.1.2.md:50–51` *"`dim A = dim T_d`
  (for example, use NAGATA Corollary 10.10)"* — the going-up half; Layer 0 proved the other half
  (`ringKrullDim_le_of_isIntegral`). D: `letI := f.toAlgebra`; `Algebra.IsIntegral R S` from `hf`
  (`RingHom.IsIntegral` is definitionally `∀ x, IsIntegral R x`); `Algebra.HasGoingUp.of_isIntegral`;
  `ringKrullDim = Order.krullDim (PrimeSpectrum _)`; `Order.krullDim_le_iff`-style: for every
  `l : LTSeries (PrimeSpectrum R)`, a prime `P` over `l.head.asIdeal` exists
  (`Ideal.exists_ideal_over_prime_of_isIntegral _ ⊥ (by simpa [← RingHom.ker_eq_comap_bot] using
  (RingHom.injective_iff_ker_eq_bot f).1 hinj ▸ bot_le)`), `P.LiesOver` from `comap = P`;
  `Ideal.exists_ltSeries_of_hasGoingUp l P` gives `L` of the same length, so
  `l.length ≤ krullDim (PrimeSpectrum S)` (`Order.LTSeries.length_le_krullDim`); conclude by
  `Order.krullDim_le_iSup`/`iSup_le`. A: [2] `R` zero: `krullDim = ⊥ ≤ _` ✓ (no `LTSeries`); `S` zero
  with `R` nonzero: impossible by injectivity ✓. [3] injectivity is necessary (`ℤ → ℤ/2`). [5]
  `Ideal.exists_ltSeries_of_hasGoingUp`, `Ideal.exists_ideal_over_prime_of_isIntegral`,
  `Algebra.HasGoingUp.of_isIntegral` verified. SURVIVED.
- **L7.9** `IsAffinoidAlgebra.ringKrullDim_eq_of_finite_injective` — Q: `bgr-6.1.2.md:50–51`. D:
  `le_antisymm ([L0] ringKrullDim_le_of_isIntegral φ.toRingHom hφ.to_isIntegral ▸ …) (L7.8 …)` with
  [L0] `ringKrullDim_eq K d`. A: [2] `d = 0`: `A` finite over `K`, nonzero (injective), dimension `0` ✓.
  SURVIVED.
- **L7.10** `exists_ringKrullDim_eq` — D: L7.7 and L7.9. SURVIVED.
- **L7.11** `finiteDimensional_of_finite_zero` — Q: `bgr-6.1.2.md:64–65` *"`d = 0` and `T_d = k`"*
  (finite over `T₀` is finite-dimensional over `k`). D: `letI := φ.toRingHom.toAlgebra`;
  `Module.Finite T₀ A := hφ`; `IsScalarTower K T₀ A` by `IsScalarTower.of_algebraMap_eq` (`φ.commutes`);
  `Module.Finite K T₀` from `(isEmptyEquiv K 1)` as a `K`-linear equivalence to `K`
  (`LinearEquiv.finiteDimensional`, `Module.Finite.self`); `Module.Finite.trans T₀ A`. A: [6] the
  `K`-module structure on `A` from `Algebra K A` must be the one the tower uses ✓ (`IsScalarTower`
  proof). [5] `Module.Finite.trans` verified. SURVIVED.
- **L7.12** `injective_factor_comp_of_injective` — Q: `bgr-6.1.2.md:62–63` *"finite and injective
  (because `T_d` is reduced)"*. D: for `r` with `factor (φ r) = 0`: write `φ r = mk a`
  (`Ideal.Quotient.mk_surjective`), `factor (mk a) = mk a` in `A ⧸ rad` (`Ideal.Quotient.factor_mk`),
  so `a ∈ 𝔮.radical` (`Ideal.Quotient.eq_zero_iff_mem`), `a ^ m ∈ 𝔮` (`Ideal.mem_radical_iff`), hence
  `(φ r) ^ m = mk (a ^ m) = 0`, `φ (r ^ m) = 0`, `r ^ m = 0` (`hφ` with `map_zero`), `r = 0`
  (`IsReduced.pow_eq_zero_iff`/`pow_eq_zero_iff` for reduced rings). A: [3] reducedness of the source
  is necessary (`k[ε] → k[ε]/(ε)`). SURVIVED.
- **L7.13** `Affinoid.TateAlgebra.eq_zero_of_isField` — Q: `bgr-6.1.2.md:64–65` *"`T_d` must itself
  be a field so that `d = 0`"*. D: `ringKrullDim_eq_zero_of_isField h`, [L0] `ringKrullDim_eq K d`,
  so `(d : WithBot ℕ∞) = 0`; `Nat.cast_eq_zero` through `WithBot.coe_eq_zero`/`ENat.coe_eq_zero`
  (`exact_mod_cast`). A: [2] `d = 0`: `T₀ = K` is a field ✓ consistent. SURVIVED.
- **L7.14** `finiteDimensional_quotient_of_radical_isMaximal` — Q: `bgr-6.1.2.md:59–65`. D:
  `Nontrivial (A ⧸ 𝔮)` from `𝔮 ≠ ⊤` (`Ideal.Quotient.nontrivial`, `𝔮 ≤ radical 𝔮 ≠ ⊤`); L7.7 on
  `hA.quotient 𝔮` gives `d, φ`; `ψ := (Ideal.Quotient.factor 𝔮.le_radical).comp φ.toRingHom` injective
  (L7.12, `T_d` a domain hence reduced) and integral (`(hφ.comp_surjective? )` — `RingHom.Finite.comp
  (of_surjective factor_surjective) hφ` then `.to_isIntegral`); `letI := ψ.toAlgebra`; `A ⧸ 𝔮.radical`
  is a field (`Ideal.Quotient.field`), so `(Algebra.IsIntegral.isField_iff_isField hinj).2
  (Field.toIsField _)` gives `IsField (T_d)`; L7.13 gives `d = 0`; `subst`; L7.11. A: [2] `𝔮 = ⊤`:
  `radical ⊤ = ⊤` is not maximal ✓ excluded by `h`. [6] the two algebra structures (`φ` and `ψ`) are
  introduced by `letI` in separate `have`s. SURVIVED.
- **L7.15** `Ideal.isMaximal_comap_of_isAffinoidAlgebra` — Q: [RM] §1.2.4 *"the preimage of a maximal
  ideal under a `K`-algebra map of affinoid algebras is maximal"*; the argument is BGR 6.1.2/3's
  consequence (Layer 0 used the same for `Tₙ` in `isMaximal_ker_of_isAlgebraic`). D:
  `Ideal.quotientMapₐ 𝔪 φ le_rfl : A ⧸ 𝔪.comap φ →ₐ[K] B ⧸ 𝔪` is injective
  (`Ideal.quotientMap_injective`); `FiniteDimensional K (A ⧸ 𝔪.comap φ)` by
  `FiniteDimensional.of_injective (…).toLinearMap` from L7.14 on `hB`; the quotient is a domain
  (`Ideal.IsPrime.comap`, `Ideal.Quotient.isDomain`); `isField_of_isIntegral_of_isField'
  (Field.toIsField K)` with `Algebra.IsIntegral.of_finite`; `Ideal.Quotient.maximal_of_isField`. A:
  [3] `hA` is not needed (any `K`-algebra `A`) ✓ stated without it. [2] `A` zero: `comap = ⊤`, but
  then `A ⧸ ⊤` is not a domain — `Ideal.IsPrime.comap` still holds? `comap φ 𝔪 = ⊤` is not prime;
  **check**: for `A` the zero ring, `𝔪.comap φ = ⊤` and `⊤.IsMaximal` is false, so the statement would
  be FALSE for the zero ring `A`. Is `𝔪.comap φ` prime for `A = 0`? `Ideal.IsPrime.comap` requires
  nothing of `A`… `comap φ 𝔪 ≠ ⊤` iff `φ 1 ∉ 𝔪` iff `1 ∉ 𝔪` ✓ always true since `𝔪 ≠ ⊤` and `φ 1 = 1`
  — so `comap φ 𝔪 ≠ ⊤` even for `A` zero? For `A` zero, `φ 1 = φ 0 = 0 ∈ 𝔪` and also `= 1 ∈ B`, so
  `1 ∈ 𝔪` — contradiction: `B` would be zero, impossible for a maximal ideal. Hence `A` zero forces
  `B` zero which has no maximal ideal: vacuous ✓. SURVIVED.
- **L7.16** `IsFractionRing.isLocalization_algebraMapSubmonoid_of_isIntegral` — Q:
  `bgr-6.1.2.md:72–73` *"`Q(A′)` is finite over `Q(T_d)`"* (its identification). D:
  `IsLocalization.of_le (Algebra.algebraMapSubmonoid S R⁰) (nonZeroDivisors S)`? — the direction: we
  know `IsLocalization S⁰ (FractionRing S)` and want it for the smaller submonoid `M :=
  algebraMapSubmonoid S R⁰ ≤ S⁰` (injectivity + domain: `algebraMap R S r ≠ 0`); Mathlib's
  `IsLocalization.of_le` goes from a smaller to a larger submonoid, so instead use the characterisation
  `IsLocalization.isLocalization_iff`/`IsLocalization.mk'_surjective`-style: (i) elements of `M` are
  units (`IsLocalization.map_units` for `S⁰`, `M ≤ S⁰`), (ii) every `z = mk' s t` with `t ∈ S⁰`: `t` is
  integral, `t * u = algebraMap r₀` with `r₀ ≠ 0` (from a monic equation of minimal degree: the
  constant term is nonzero since `S` is a domain — `IsIntegral.exists_mul_eq_algebraMap_of_ne_zero`?
  Mathlib has `exists_dvd_... `: the ticket proves it from `minpoly`/`IsIntegral.isUnit`-free: take
  `p` monic with `p(t) = 0`, divide by the largest power of `X` (`Polynomial.X_pow_dvd_iff`), get `q`
  with `q(t) = 0`, `q(0) ≠ 0`, and `t * (q − q(0))/X evaluated = −q(0)`), so `z = mk' (s * u)
  ⟨algebraMap r₀, _⟩`; (iii) `exists_of_eq` from injectivity of `algebraMap S (FractionRing S)`.
  A: [1] without injectivity (`ℤ → ℤ/2`) the submonoid contains `0` ✓ hypothesis needed. [2] `R`
  a field ✓. [3] `IsDomain S` needed for the nonzero constant term. [5] `IsLocalization.of_le`
  verified to exist but goes the wrong way; the constructor route is `IsLocalization.mk'`-based. This
  is the most technical leaf of G7 (estimate 60 lines). SURVIVED.
- **L7.17** `FractionRing.finiteDimensional_of_finite` — Q: `bgr-6.1.2.md:72–73`. D:
  `Module.Finite.of_isLocalization R S (nonZeroDivisors R)` with L7.16 (as a `haveI`), the given
  `Algebra (FractionRing R) (FractionRing S)` and tower, and `IsLocalization R⁰ (FractionRing R)` ✓.
  A: [3] the algebra structure between the fraction fields is an instance argument (Mathlib's
  `FractionRing.liftAlgebra` is a local instance to avoid a diamond; the caller supplies it and the
  tower). [5] `Module.Finite.of_isLocalization` (`Localization/Finiteness.lean:142`, needs the import)
  verified. SURVIVED.
- **L7.18** `IsAffinoidAlgebra.isJapaneseRing` — Q: `bgr-6.1.2.md:69–75`. D: unfold `IsJapaneseRing`;
  given `L` with `[FiniteDimensional (FractionRing A) L]`; L7.7 gives `φ : T_d → A` finite injective;
  `letI := φ.toRingHom.toAlgebra`; `Algebra T_d L` through `A` (`(algebraMap A L).comp φ`), tower
  `T_d → A → L`; `Algebra (FractionRing T_d) L` by `FractionRing.liftAlgebra` (injective `T_d → L`),
  tower `T_d → Frac T_d → L` (`FractionRing.isScalarTower_liftAlgebra`); `Algebra (FractionRing T_d)
  (FractionRing A)` by `liftAlgebra` too, with `IsScalarTower (Frac T_d) (Frac A) L` by
  `IsFractionRing.lift` uniqueness (`IsLocalization.ringHom_ext`); `FiniteDimensional (Frac T_d)
  (Frac A)` by L7.17 and then `Module.Finite.trans (FractionRing A) L`; [L0]
  `TateAlgebra.isJapaneseRing d L` gives `Module.Finite T_d (integralClosure T_d L)`;
  `integralClosure T_d L = integralClosure A L` as subalgebras over `T_d`? — as *sets*:
  `isIntegral_trans` (`T_d → A` integral) and `IsIntegral.tower_top`; transport finiteness along the
  equality (`Subalgebra.equivOfEq`-style `LinearEquiv`), then `Module.Finite.of_restrictScalars_finite
  T_d A _`. A: [3] `CharZero K` is needed because Layer 0's Japaneseness of `T_d` is proved in
  characteristic zero only (its char-`p` half is off the board); the statement carries `[CharZero K]`.
  [6] universes: `K A : Type u` as in Layer 0's `isJapaneseRing` (the definition quantifies over
  `L : Type u`) ✓ matches. This is the longest leaf of the board (instance plumbing, estimate 150
  lines); the roadmap's §1.2.5 asks for exactly it. SURVIVED.

### Internal nodes

- **N7.1** `ofTailAlgHom` (complete) — [6] the `commutes'` field uses the floor's `algebraMap_apply`
  twice and `ofTail_C` ✓ compiled. SURVIVED.
- **N7.2** `finiteDimensional_quotient_of_isMaximal`, `finiteDimensional_quotient_pow` (complete from
  L7.14) — [2] `ν = 0` is excluded by `hν` here; G8 handles `𝔪 ^ 0 = ⊤` separately. SURVIVED.

---

## G8 — Continuity for affinoid algebras (`Affinoid/Continuity.lean`), [RM] §1.1.3–1.1.4, §1.3

### Source and prose proof

[BGR] 6.1.3 (`bgr-6.1.3-6.1.5.md:7–17`): *"For each `k`-affinoid algebra `B ∈ 𝔄`, the set `𝔅 :=
{𝔪^ν ; 𝔪 maximal ideal in `B`, `ν ∈ ℕ`}` fulfills conditions (i) and (ii) of Proposition 3.7.5/2.
Namely, (i) `dim_k B/𝔟 < ∞` for each `𝔟 ∈ 𝔅`, (ii) `⋂ 𝔟 = (0)`. Proof. We have `dim_k B/𝔟 < ∞` for all
`𝔟 ∈ 𝔅` by Corollary 6.1.2/3. In order to show `⋂ 𝔟 = (0)`, take any `f ∈ B` such that `f ∈ ⋂ 𝔪^ν`
for all maximal ideals `𝔪 ⊂ B`. KRULL's Intersection Theorem implies that for each `𝔪` there is an
element `m ∈ 𝔪` such that `(1 − m) f = 0`. Hence the annihilator of `f` is contained in no maximal
ideal in `B`. Therefore, `f = 0` and (ii) holds."* [BGR] 6.1.3/1 (`:21–22`): *"Each `k`-algebra
homomorphism of a Noetherian `k`-Banach algebra into a `k`-affinoid algebra is continuous."*; `:24–27`:
*"a `k`-algebra can carry at most one `k`-affinoid structure, since the identity map must be continuous
in both directions."*; 6.1.3/2 (`:29–31`); 6.1.3/3 (`:35–42`): *"Let `φ : B → A` be a homomorphism of
`k`-affinoid algebras. Then the algebra norm on `A` can be replaced by an equivalent one such that `φ`
becomes contractive … Let `a₁, …, aₙ ∈ A` denote affinoid generators of `A`. Then according to
Proposition 6.1.1/4, the map `φ` extends uniquely to a continuous homomorphism `ψ : B⟨X₁, …, Xₙ⟩ → A`
such that `ψ(Xᵢ) = aᵢ`. The map `ψ` is obviously surjective and hence open by BANACH's Theorem.
Therefore, the residue norm via `ψ` is equivalent to the original norm on `A`; thus `ψ` and, in
particular, `φ` are contractive with respect to this norm on `A`."* [Bo] 1.4/19
(`bosch-lectures.txt:1426–1431`). [BGR] 6.1.4 (`bgr-6.1.3-6.1.5.md:64–66`): *"If `A` is a `k`-affinoid
algebra … then the ring `A⟨X⟩` of strictly convergent power series over `A` is `k`-affinoid."*

Krull's intersection theorem in Mathlib's form `Ideal.mem_iInf_smul_pow_eq_bot_iff` (`f ∈ ⋂ 𝔪^ν ↔
∃ m ∈ 𝔪, m f = f`) gives (ii) exactly as BGR argues; (i) is G7. BGR 3.7.5/2 (G6) then gives 6.1.3/1,
whose consequences are formal: presentations are continuous for every Banach norm, ideals are closed
for every Banach norm (G5), isomorphisms are homeomorphisms (G6), norms are equivalent, power-bounded
and topologically nilpotent elements are the same for all norms, a homomorphism is determined by its
values on an affinoid generating system (G4's uniqueness), every affinoid Banach algebra has an
affinoid generating system (the images of the variables under a presentation, which is continuous),
BGR 6.1.1/5 holds for an arbitrary affinoid source, `A⟨X⟩` is affinoid (G4's surjectivity of
`Tₙ⟨X⟩ → A⟨X⟩` and G2), and the contractive renorming is the residue norm of `ψ : B⟨X⟩ ↠ A`.

### Leaves

- **L8.1** `Ideal.sInf_maximalPowers_eq_bot` — Q: `bgr-6.1.3-6.1.5.md:14–17`. D: `eq_bot_iff`; for
  `f ∈ sInf 𝔅` (`Ideal.mem_sInf`), by contradiction `f ≠ 0`: `Ann f := Module.annihilator`-free
  spelling `{r | r * f = 0}` as `Ideal.span`?? — use `Submodule.annihilator (span {f})` or directly:
  the ideal `(LinearMap.lsmul? )`… simplest: `I₀ := RingHom.ker (LinearMap.toSpanSingleton A A f)`-type
  ideal `{r | r • f = 0}` (`Submodule.annihilator`), `I₀ ≠ ⊤` since `1 • f = f ≠ 0`;
  `Ideal.exists_le_maximal I₀ h` gives `𝔪`; `f ∈ 𝔪 ^ ν` for all `ν` (membership in `sInf`, with
  `𝔪 ^ ν ∈ 𝔅`); `Ideal.mem_iInf_smul_pow_eq_bot_iff (M := A)` (after rewriting `𝔪^ν • ⊤ = 𝔪^ν`,
  `Ideal.smul_top_eq`-style `smul_eq_mul, mul_top`) gives `r ∈ 𝔪` with `r • f = f`, so `1 − r ∈ I₀ ≤ 𝔪`,
  so `1 ∈ 𝔪`, contradiction (`𝔪.IsMaximal.ne_top`, `Ideal.add_mem`). A: [2] `A` zero: `sInf = ⊥`
  trivially ✓ (`f = 0`). [3] no Jacobson property needed (BGR uses only Krull); noetherian is
  needed by Krull ✓. [5] `Ideal.mem_iInf_smul_pow_eq_bot_iff` (`Filtration.lean:393`, import needed)
  verified. SURVIVED.
- **L8.2** `IsAffinoidAlgebra.finiteDimensional_of_mem_maximalPowers` — Q: `:14` *"by Corollary
  6.1.2/3"*. D: `obtain ⟨𝔪, ν, h𝔪, rfl⟩`; `rcases ν`: `𝔪 ^ 0 = ⊤` (`pow_zero`, `Ideal.one_eq_top`),
  `A ⧸ ⊤` subsingleton (`Ideal.Quotient.subsingleton_iff`), `Module.Finite.of_finite`; otherwise
  `hA.finiteDimensional_quotient_pow 𝔪 (Nat.succ_ne_zero _)`. SURVIVED.
- **L8.3** `AlgHom.continuous_of_isAffinoidAlgebra` — Q: `:19–22`. D: `haveI := hB.isNoetherianRing`;
  `AlgHom.continuous_of_isNoetherianRing (Ideal.maximalPowers B) (fun _ h ↦ hB.finiteDimensional_of_mem_maximalPowers h)
  hB.sInf_maximalPowers_eq_bot Φ`. A: [3] `[NormOneClass A] [IsUltrametricDist A]` (source) and the
  same on `B` are G6's hypotheses; for residue norms they hold (N3.1) when the algebra is nonzero. For
  a *zero* target or source the statement is trivially true but `NormOneClass` fails — the zero
  affinoid algebra with its (zero) residue norm is excluded from this theorem; plan, "Banach algebra
  conventions". SURVIVED.
- **L8.4** `AlgEquiv.exists_forall_norm_le_mul_of_isAffinoidAlgebra` — D: `continuous_of_isAffinoidAlgebra'`
  on `e.toAlgHom` and `e.symm.toAlgHom`, `SemilinearMapClass.bound_of_continuous`. SURVIVED.
- **L8.5** `AlgEquiv.isPowerBounded_map_iff_of_isAffinoidAlgebra` — Q: [RM] §1.3.3; [Bo]
  `bosch-lectures.txt:1335–1336` *"the notion of power boundedness is independent of the residue norm
  under consideration"*. D: `isPowerBounded_iff_exists_norm_pow_le` (L0) both sides; L8.4 gives
  `C, C'`; `(e a)^n = e (a^n)` (`map_pow`), `‖e (a^n)‖ ≤ C ‖a^n‖ ≤ C M` and conversely with `e.symm`.
  A: [2] `C < 0` cannot occur for nonzero `A` ✓ (and `max 0 C` otherwise). SURVIVED.
- **L8.6** `AlgEquiv.isTopologicallyNilpotent_map_iff_of_isAffinoidAlgebra` — D: `IsTopologicallyNilpotent`
  is `Tendsto (a ^ ·) atTop (𝓝 0)`; `(e a)^n = e (a^n)`; `(continuous_e).tendsto 0` composed, with
  `map_zero`, and back with `e.symm` (`e.symm_apply_apply`). SURVIVED.
- **L8.7** `AlgHom.ext_of_isAffinoidGeneratingSystem` — Q: `bgr-6.1.1.md:52–54` with 6.1.3/1; [RM]
  §1.1.4. D: `obtain ⟨hb, hsurj⟩ := ha`; `Φ := extendAlgHom (Algebra.ofId K A) _ a hb`;
  `ψ₁.comp Φ = ψ₂.comp Φ` by `algHom_ext_of_continuous` (continuity: L8.3 for `ψᵢ` composed with
  `continuous_extendAlgHom`; on `X i`: `extendAlgHom_X` and `h i`) — here the coefficient ring is `K`,
  so the `K`-algebra ext applies; then `AlgHom.ext` with `hsurj`. SURVIVED.
- **L8.8** `IsAffinoidAlgebra.exists_isAffinoidGeneratingSystem` — Q: `bgr-6.1.1.md:56–59`. D:
  `obtain ⟨n, α, hα⟩ := hA`; `hcont := hA.continuous_presentation α`; `a i := α (X K 1 i)`;
  `hb i := IsPowerBounded.map (C := …) (bound from exists_forall_norm_le_mul_of_continuous) (isPowerBounded_X i)`
  (`X K 1 i` is power-bounded by `isPowerBounded_of_norm_le_one` with `norm_X`);
  `extendAlgHom (ofId K A) _ a hb = α` by `extendAlgHom_unique α hcont (fun c ↦ by rw [← algebraMap_apply]; exact α.commutes c) (fun i ↦ rfl)`
  — `C 1 c = algebraMap K Tₙ c` by the floor's `algebraMap_apply`; conclude `⟨n, a, hb, by rwa [this]⟩`.
  A: [6] `extendAlgHom_unique` has `hC : ∀ a : A, ψ (C 1 a) = φ a` with `A := K` and `φ := ofId K A`
  ✓. SURVIVED.
- **L8.9** `IsAffinoidAlgebra.of_finite_of_continuous` — Q: `bgr-6.1.1.md:68` *"We may assume
  `B = Tₙ`"*. D: `obtain ⟨n, α, hα⟩ := hA`; `of_finite_tateAlgebra (φ.comp α) (hφ.comp
  (hA.continuous_presentation α)) (RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ hα))`.
  SURVIVED.
- **L8.10** `IsAffinoidAlgebra.restricted` — Q: `bgr-6.1.3-6.1.5.md:64–66`; `bgr-6.1.1.md:113–117`.
  D: `obtain ⟨n, α, hα⟩ := hA`; `hsurj := surjective_mapAlgHom_of_surjective α (hA.continuous_presentation α) hα`
  (`Restricted Tₙ 1_σ → Restricted A 1_σ`); `Fintype.ofFinite σ`, `e := Fintype.equivFin σ`;
  `Restricted Tₙ 1_σ ≃+* Restricted Tₙ 1_{Fin m}` (L2.10), upgraded to `≃ₐ[K]` by
  `AlgEquiv.ofRingEquiv` with `renameEquiv_C` and `algebraMap_eq_C_comp`; then `TateAlgebra.sumEquiv K n m`;
  `(tateAlgebra (m + n)).of_algEquiv (…).symm` then `.of_surjective (mapAlgHom …) hsurj`. A: [6] the
  composite equivalence's `K`-linearity is the only seam (constants `C (C c)`). SURVIVED.
- **L8.11** `IsAffinoidAlgebra.exists_algEquiv_quotient_norm_comp_le` — Q: `:38–42`. D: L8.8 for `A`
  gives `a : Fin n → A`, `hb`, `hsurj₀ : Surjective (extendAlgHom (ofId K A) _ a hb)`; `hφ :=
  φ.continuous_of_isAffinoidAlgebra' hB hA`; `ψ := extendAlgHom φ hφ a hb : Restricted B 1_{Fin n} →ₐ[K] A`;
  `ψ.comp (mapAlgHom (Algebra.ofId K B) (continuous_algebraMap K B)) = extendAlgHom (ofId K A) _ a hb`
  by `extendAlgHom_unique` (continuity, `C c ↦ φ (algebraMap c) = algebraMap c`, `X ↦ a`), so `ψ` is
  surjective; `I := RingHom.ker ψ`; `e := Ideal.quotientKerAlgEquivOfSurjective hψ`; `Continuous e`
  from `(QuotientAddGroup.isQuotientMap_mk _).continuous_iff` and `e ∘ mk = ψ`
  (`Ideal.quotientKerAlgEquivOfSurjective_apply`? — `rfl` on `mk`); `Continuous e.symm`: if `A` is
  nontrivial, `I ≠ ⊤`, `NormOneClass (B⟨X⟩ ⧸ I)` (`normOneClass_of_ne_top`, `I` closed by
  `hB.restricted.isClosed_ideal`), both sides affinoid (`hB.restricted.quotient`, `hA`) and L8.3 on
  `e.symm.toAlgHom`; if `A` is trivial, `e.symm` is continuous into a subsingleton
  (`continuous_of_discreteTopology`/`Subsingleton` ⟹ constant). The bound: `e.symm (φ b) = mk (C 1 b)`
  since `ψ (C 1 b) = φ b` (`extendAlgHom_C`) and `e.symm_apply_eq`; `Ideal.Quotient.norm_mk_le` and
  `norm_C`. A: [2] `n = 0`: `B⟨⟩ = B`, `ψ = φ` surjective ✓ consistent. [3] `[NormOneClass A]` enters
  through L8.3 (both directions); the zero case is handled. [6] the instance `IsClosed I` is a `haveI`
  inside the proof; the statement uses only the seminormed quotient. SURVIVED.

### Internal nodes

- **N8.1** `sInf_maximalPowers_eq_bot`, `continuous_of_isAffinoidAlgebra'`, `continuous_presentation`,
  `isClosed_ideal`, `continuous_symm_of_isAffinoidAlgebra` (complete in the skeleton) — [6] each is one
  application of a leaf with `hA.isNoetherianRing`. SURVIVED.

---

## G9 — The affinoid tensor product by presentations (`Affinoid/Tensor.lean`), [RM] §1.1.4–1.1.5

### Source and prose proof

[BGR] 6.1.1/10–11 (`bgr-6.1.1.md:127–156`): *"Let `B₁, B₂ ∈ 𝔄` be normed algebras over some algebra
`A ∈ 𝔄` via contractive homomorphisms `A → Bᵢ`. Then also `B₁ ⊗̂_A B₂`, viewed as a `k`-algebra,
belongs to `𝔄` … **Proposition 11.** … let `𝔟ᵢ ⊂ Bᵢ` be ideals, and denote by `(𝔟₁, 𝔟₂) ⊂ B₁ ⊗̂_A B₂`
the ideal generated by the images of `𝔟₁` and `𝔟₂`. Then the canonical map `π : B₁ ⊗̂_A B₂ →
B₁/𝔟₁ ⊗̂_A B₂/𝔟₂` is surjective and satisfies `ker π = (𝔟₁, 𝔟₂)` … the canonical maps `Bᵢ → B₁ ⊗̂_A B₂`
induce maps `Bᵢ/𝔟ᵢ → B₁ ⊗̂_A B₂/(𝔟₁, 𝔟₂)`. Just as in the preceding proof, it is not hard to see that
these induced maps satisfy the universal property characterizing the complete tensor product
`B₁/𝔟₁ ⊗̂_A B₂/𝔟₂`. Thus `(B₁ ⊗̂_A B₂)/(𝔟₁, 𝔟₂)` is `k`-affinoid … for `T_m/𝔞, Tₙ/𝔟 ∈ 𝔄`, it follows
that `T_m/𝔞 ⊗̂_k Tₙ/𝔟 = T_{m+n}/(𝔞, 𝔟)`."* [BGR] 3.1.1/2 is the universal property of the complete
tensor product (cited, not transcribed: for `B₁ ← A → B₂` and contractive `fᵢ : Bᵢ → C` agreeing on
`A` there is a unique contractive `B₁ ⊗̂_A B₂ → C`). [RM] §1.1.5.

With `B₁ = A⟨X⟩/𝔟₁`, `B₂ = A⟨Y⟩/𝔟₂`, the object is defined as `A⟨X ⊕ Y⟩/(𝔟₁, 𝔟₂)` (BGR's last
display). Its universal property among Banach algebras with *continuous* maps is BGR 6.1.1/4: given
`f₁, f₂` agreeing on `A`, the extension `A⟨X ⊕ Y⟩ → C`, `X i ↦ f₁(X̄ i)`, `Y j ↦ f₂(Ȳ j)` along
`f₁ ∘ (A → B₁)`, kills `(𝔟₁, 𝔟₂)` because its restriction to `A⟨X⟩` is `f₁ ∘ mk` (uniqueness of
extensions) and descends; uniqueness is again the density ext. Two objects with the universal property
are uniquely isomorphic; the predicate transports along isomorphisms of a factor; `B₂/𝔞B₂` is the tensor
product of `A/𝔞` and `B₂`; hence `ι₂` is surjective when `α₁` is (BGR 6.1.1/11 for `𝔟₂ = 0`). The
algebraic tensor product maps in with dense image because its image contains the classes of all
polynomials.

### Leaves

- **L9.1** `inlAlgHom_C`, **L9.2** `inrAlgHom_C`, **L9.3** `inlAlgHom_comp_toAlgHom`, **L9.4**
  `inrAlgHom_comp_toAlgHom` — Q: `bgr-6.1.1.md:96` (the inclusions `σ₁, σ₂`). D: `extendAlgHom_C`,
  `IsScalarTower.toAlgHom_apply`, `algebraMap_apply`; `AlgHom.ext`. SURVIVED.
- **L9.5** `IsAffinoidTensorProduct.exists_algEquiv` — Q: `bgr-6.1.1.md:137–139` *"satisfy the
  universal property … Hence … is an isomorphism"*. D: `obtain ⟨F, ⟨hF, hF₁, hF₂⟩, _⟩ :=
  h.existsUnique_lift ι₁' ι₂' h'.continuous_ι₁ h'.continuous_ι₂ h'.comp_eq` and symmetrically `G`;
  `G.comp F = AlgHom.id` by the uniqueness part of `h.existsUnique_lift ι₁ ι₂ …` applied to both
  (`AlgHom.comp_assoc`, `AlgHom.id_comp`); same for `F.comp G`; `AlgEquiv.ofAlgHom F G h₁ h₂`;
  continuity of `e`, `e.symm` is `hF`, `hG`. A: [6] universes: `T, T' : Type v` (D2) so that
  `existsUnique_lift` applies with `C := T'` and `C := T` ✓. [2] `T` zero: then `B₁, B₂` map to zero…
  the UP forces `T'` zero too ✓ consistent. SURVIVED.
- **L9.6** `IsAffinoidTensorProduct.of_algEquiv_left` — Q: implicit in `bgr-6.1.1.md:137` ("`A/𝔞`" is
  `B₁` up to isomorphism). D: `constructor`; `continuous_ι₁ := h.continuous_ι₁.comp he`;
  `comp_eq`: `ι₁ ∘ e ∘ e.symm ∘ α₁ = ι₁ ∘ α₁ = ι₂ ∘ α₂` (`AlgEquiv.comp_symm`); lift: for `f₁ : B₁' → C`
  continuous, apply `h` to `f₁.comp e.symm.toAlgHom` (continuous by `he'`) and `f₂`, with the
  compatibility `f₁ ∘ e.symm ∘ α₁ = f₂ ∘ α₂` ⟸ `f₁ ∘ (e.symm ∘ α₁) = f₂ ∘ α₂` ✓; uniqueness
  likewise. SURVIVED.
- **L9.7** `isAffinoidTensorProduct_quotient_map` — Q: `bgr-6.1.1.md:142–151` with `B₁ = A`,
  `𝔟₁ = 𝔞`, `𝔟₂ = 0`: *"`A/𝔞 ⊗̂_A B₂ = B₂/𝔞B₂`"* (BGR 6.1.1/11 reading). D: `constructor`;
  `ι₁ := Ideal.quotientMapₐ`: continuity by `(QuotientAddGroup.isQuotientMap_mk _).continuous_iff.2`
  with `ι₁ ∘ mk = mk ∘ α₂` (`Ideal.quotientMap_mk`) continuous; `ι₂ := mkₐ` continuous
  (`continuous_quot_mk`); `comp_eq` by `Ideal.quotientMap_comp_mk`; lift: `F := Ideal.Quotient.liftₐ
  (𝔞.map α₂) f₂ hker` with `hker : ∀ b ∈ 𝔞.map α₂, f₂ b = 0` from `Ideal.map_le_iff_le_comap` and
  `f₂ (α₂ a) = f₁ (mk a) = 0` for `a ∈ 𝔞` (`AlgHom.congr_fun hcomp`); `F.comp mkₐ = f₂` (`liftₐ_comp`);
  `F.comp ι₁ = f₁` by `Ideal.Quotient.algHom_ext`-style on `mk a`; `Continuous F` via the quotient map
  and `F ∘ mk = f₂`; uniqueness: `F'` with `F'.comp mkₐ = f₂` equals `F` by `Ideal.Quotient.algHom_ext`.
  A: [2] `𝔞 = ⊤`: everything zero ✓. [3] `IsClosed 𝔞` is an instance argument so that `A ⧸ 𝔞` is a
  Banach algebra (a `B₁` of the predicate), `hB₂` gives closedness of `𝔞.map α₂` (G8) so that the
  target is Banach; `NormOneClass B₂` only for that. SURVIVED.
- **L9.8** `IsAffinoidTensorProduct.surjective_ι₂_of_surjective` — Q: `bgr-6.1.1.md:144–146`
  *"the canonical map `π` is surjective"*; [RM] §1.1.5 *"if `A → B₁` is surjective so is
  `B₂ → B₁ ⊗̂_A B₂`"*. D: `𝔞 := RingHom.ker α₁`, closed (`hα₁.isClosed_preimage`/`IsClosed.preimage`
  of `{0}`), `haveI`; `e := Ideal.quotientKerAlgEquivOfSurjective hα₁' : A ⧸ 𝔞 ≃ₐ[K] B₁`, continuous
  (quotient map) with continuous inverse (`e.symm = mk ∘ (section)`? — no: `e.symm` is continuous by
  the open mapping theorem, `LinearEquiv.continuous_symm`, both complete ✓); L9.6 transports `h` to
  `(mkₐ 𝔞, α₂, ι₁ ∘ e, ι₂)` (note `e.symm ∘ α₁ = mkₐ 𝔞` by `quotientKerAlgEquivOfSurjective_symm_apply`);
  L9.7 gives the quotient model `T'`; L9.5 gives `ε : T ≃ₐ[K] T'` with `ε ∘ ι₂ = mkₐ (𝔞.map α₂)`
  surjective; hence `ι₂ = ε.symm ∘ mkₐ …` is surjective (`Function.Surjective.of_comp`-style:
  `ε.symm.surjective.comp mk_surjective`). A: [6] universes `B₂ T : Type v` (D3) ✓; `hα₁` needed for
  closedness of the kernel (D3) ✓. [2] `B₁` zero: `𝔞 = ⊤`, `T' = 0`, `T ≅ 0`, `ι₂` surjective ✓.
  SURVIVED.
- **L9.9** `tensorInl` (obligation `𝔟₁ ≤ comap`), **L9.10** `tensorInr` — D: `fun f hf ↦ by
  simp [Ideal.Quotient.eq_zero_iff_mem]; exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)`.
  SURVIVED.
- **L9.11** `continuous_tensorInl`, **L9.12** `continuous_tensorInr` — D: quotient map on the source:
  `(QuotientAddGroup.isQuotientMap_mk 𝔟₁.toAddSubgroup).continuous_iff.2` with `tensorInl ∘ mk = mk ∘
  inlAlgHom` (`tensorInl_mk`), `continuous_quot_mk.comp (continuous_inlAlgHom _ _)`. SURVIVED.
- **L9.13** `tensorInl_comp_eq_tensorInr_comp` — D: `AlgHom.ext`; both sides send `a` to
  `mk (C 1 a)`: `IsScalarTower.toAlgHom_apply`, `Ideal.Quotient.algebraMap_eq`? — unfold: `algebraMap A
  (A⟨X⟩ ⧸ 𝔟₁) a = mk (algebraMap A A⟨X⟩ a)` (`Ideal.Quotient.algebraMap_eq`), `tensorInl_mk`,
  `inlAlgHom_C`, `algebraMap_apply`. SURVIVED.
- **L9.14** `isAffinoidTensorProduct_tensorQuotient` — Q: `bgr-6.1.1.md:147–150`. D: `constructor`;
  continuity L9.11–L9.12; `comp_eq` L9.13; lift: `F₀ := extendAlgHom (f₁.comp (IsScalarTower.toAlgHom
  K A _)) (hf₁.comp (continuous_algebraMap_restricted? composed with continuous_quot_mk)) (Sum.elim
  (fun i ↦ f₁ (mk (X i))) (fun j ↦ f₂ (mk (X j)))) (power-bounded: `IsPowerBounded.map` with the
  bounds of `f₁ ∘ mk`, `f₂ ∘ mk` on `isPowerBounded_X`)` : `A⟨X ⊕ Y⟩ →ₐ[K] C`; `F₀.comp (inlAlgHom …)
  = f₁.comp (mkₐ 𝔟₁)` by `ringHom_ext_of_continuous` on `A⟨X⟩` (constants: `F₀ (C a) = f₁ (mk (C a))`
  ✓ both equal `f₁ (algebraMap a)`; variables ✓), so `F₀` kills `𝔟₁.map inl` (`Ideal.map_le_iff_le_comap`,
  `mk` kills `𝔟₁`), likewise `𝔟₂.map inr` (using `hcomp` to see `F₀ (C a) = f₂ (mk (C a))`), hence
  `tensorIdeal ≤ ker F₀` (`sup_le`); `F := Ideal.Quotient.liftₐ _ F₀ _`; `F.comp tensorInl = f₁`
  (`Ideal.Quotient.algHom_ext`, `tensorInl_mk`, the ext above), same for `ι₂`; continuity via the
  quotient map; uniqueness: for `F'` with the two equations, `F'.comp (mkₐ _) = F₀` by
  `ringHom_ext_of_continuous` on `A⟨X ⊕ Y⟩` (constants and both kinds of variables are determined
  through `tensorInl`/`tensorInr`), then `Ideal.Quotient.algHom_ext`. A: [6] the index type of the UP
  variables is `σ ⊕ τ` with `Finite (σ ⊕ τ)` ✓ instance. [2] `𝔟₁ = ⊤`: `B₁ = 0`, UP forces `C = 0`…
  then `F` is the zero map ✓ consistent. [3] `NormOneClass A` is only for the `IsClosed` instances in
  the statement (so that `B₁, B₂, T` are *normed*); the UP proof itself does not use it. SURVIVED.
- **L9.15** `tensorInlₐ`, **L9.16** `tensorInrₐ` (`commutes'`) — D: `tensorInl_mk`, `inlAlgHom_C`,
  `Ideal.Quotient.algebraMap_eq`, `algebraMap_apply`. SURVIVED.
- **L9.17** `denseRange_tensorLift` — Q: [RM] §1.1.5. D: the range is a subalgebra containing
  `mk (C a)` (`tensorLift (mk (C a) ⊗ₜ 1) = tensorInlₐ (mk (C a))`), `mk (X (inl i))`
  (`tensorLift (mk (X i) ⊗ₜ 1)`) and `mk (X (inr j))`, hence `Set.range (mk ∘ MvPolynomial.toRestricted 1)
  ⊆ range` by `MvPolynomial.induction_on` (`map_add`, `map_mul`); `mk ∘ toRestricted` has dense range
  (`(denseRange_toRestricted _).comp`? — `DenseRange.comp (hg : DenseRange g) (hf : DenseRange f)
  (cg : Continuous g)` with `g := mk` surjective (`Function.Surjective.denseRange`) and `f :=
  toRestricted`); `DenseRange.mono`. A: [2] both index types empty ✓. SURVIVED.

### Internal nodes

- **N9.1** `IsAffinoidTensorProduct` (structure), `tensorIdeal`, `TensorQuotient` (abbrev), `tensorInl_mk`,
  `tensorInr_mk`, `isAffinoidAlgebra_tensorQuotient`, `isClosed_tensorIdeal`, `tensorLift` (complete) —
  [4] the predicate is BGR 3.1.1/2 with "contractive" replaced by "continuous" and norms dropped: the
  roadmap's warning (§1.1.5) that the completed tensor product with its norm is not claimed is honoured
  by stating only this. [6] the `abbrev` gives the quotient all of Mathlib's instances; closedness of
  `tensorIdeal` for affinoid `A` makes it a normed algebra. SURVIVED.

---

## G10 — Generalised rings of fractions (`Affinoid/Fractions.lean`), [RM] §1.4.1–1.4.2

### Source and prose proof

[BGR] 6.1.4/1 (`bgr-6.1.3-6.1.5.md:93–96`, quoted in the skeleton docstring), `:103–114`: *"Let `X` and
`Y` denote systems of indeterminates. Then `A′ := A⟨X, Y⟩/(X − f, gY − 1)` is obviously a `k`-Banach and
even a `k`-affinoid algebra over `A` such that the `gⱼ` become units and the `fᵢ, gⱼ⁻¹` are
power-bounded in `A′`. Furthermore, the canonical map `A → A⟨X, Y⟩/(X − f, gY − 1)` also satisfies the
universal property stated in Proposition 1. Namely, let `φ : A → B` be a continuous homomorphism as in
Proposition 1. Then `φ` extends to a continuous homomorphism `φ″ : A⟨X, Y⟩ → B`, `X ↦ φ(f)`,
`Y ↦ φ(g)⁻¹`, with `(X − f, gY − 1) ⊂ ker φ″`. Thus `φ″` gives rise to a continuous homomorphism
`φ′ : A⟨X, Y⟩/(X − f, gY − 1) → B` such that the diagram commutes, and `φ′` is uniquely determined by
this diagram since the residue classes of `X` and `Y` must be mapped by `φ′` onto `φ(f)` and `φ(g)⁻¹`
respectively."* 6.1.4/2 (`:116–117`), `:119–126` (associativity, `A⟨h⁻¹⟩` for a unit); 6.1.4/3
(`:140–143`); `:145–151`: *"consider the `k`-affinoid algebra `A′ = A⟨X⟩/(gX − f)`. With `X̄ᵢ` denoting
the residue class of `Xᵢ` in `A′`, we get `(a + Σ aᵢ X̄ᵢ) g = a g + Σ aᵢ fᵢ = 1` which shows that `g` is a
unit in `A′`. Moreover, `X̄ᵢ = fᵢ/g` in `A′`; hence, the elements `fᵢ/g` must be power-bounded in `A′`. It
is now a straightforward verification to see that also `A′ = A⟨X⟩/(gX − f)` satisfies the universal
property stated in Proposition 3."*; 6.1.4/4 (`:153–154`); `:75–77` (`A⟨X⟩[X⁻¹]` dense).

The models are the quotients by the displayed ideals; their universal properties are BGR 6.1.1/4 plus
descent, as transcribed; uniqueness up to isomorphism and associativity follow from the universal
properties alone (BGR: "both algebras satisfy the same universal property", "it follows from Proposition
2 that we have associativity"). The density of `A[g⁻¹]` is the density of polynomials.

### Leaves

- **L10.1** `IsGeneralisedFractions.exists_algEquiv` — Q: `:100–101` *"both algebras satisfy the same
  universal property"*. D: as L9.5 with one structure map. SURVIVED (universes D4).
- **L10.2** `IsGeneralisedFractions.trans` — Q: `:124–126`. D: `constructor`; continuity
  `h'.continuous.comp h.continuous`; units: `Fin.append` cases (`Fin.addCases`), `h.isUnit j` mapped by
  `φ₁` (`IsUnit.map`) and `h'.isUnit j'`; power-boundedness of `f`-images: `IsPowerBounded.map` with
  the bound of `φ₁` (`exists_forall_norm_le_mul_of_continuous`) on `h.isPowerBounded_f i`, and
  `h'.isPowerBounded_f`; of inverses: `(φ₁ u)⁻¹ = φ₁ u⁻¹` as units (`Units.map`), then as before; UP:
  given `φ : A → B` with the conditions on `f ++ f'`, `g ++ g'`: `h.existsUnique_lift φ …` (the
  `Fin.append_left` cases) gives `φ' : A' → B`; then `h'.existsUnique_lift φ' …` (conditions on
  `φ₀ ∘ f'`: `φ' (φ₀ (f' i)) = φ (f' i)` by the equation `φ'.comp φ₀ = φ`, `Fin.append_right`) gives
  `φ'' : A'' → B`; uniqueness: a lift `χ` of `φ` through `φ₁ ∘ φ₀` restricts to a lift `χ ∘ φ₁` of `φ`
  through `φ₀`, equal to `φ'` by uniqueness in `h`, then `χ = φ''` by uniqueness in `h'`. A: [6] the
  universe of `B` is `v` throughout ✓. [2] `m' = n' = 0` ✓ (`Fin.append` with empty). SURVIVED.
- **L10.3** `IsGeneralisedFractions.of_isUnit` — Q: `:122–124`. D: `constructor`; `continuous_id`;
  the data hypotheses; UP: `⟨φ, ⟨hφ, AlgHom.comp_id⟩, fun χ ⟨_, hχ⟩ ↦ by simpa using hχ⟩`. SURVIVED.
- **L10.4** `IsRationalFractions.isGeneralisedFractions_of_one` — Q: `:157–158`. D: `h.isUnit.unit = 1`
  (`Units.ext`, `map_one`); `h.isPowerBounded_div` simplifies to `φ₀ (f i)`; UP: for `φ` with
  `hf`, apply `h.existsUnique_lift φ hφ (by simpa using isUnit_one) (by simpa using hf)`. A: [2] the
  empty `g` makes `isUnit`/`isPowerBounded_inv` vacuous (`Fin.elim0`). SURVIVED.
- **L10.5** `continuous_toFractions`, **L10.11** `continuous_toRational` — D: `continuous_quot_mk.comp
  (continuous_algebraMap_restricted _)`. SURVIVED.
- **L10.6** `toFractions_mul_mk_X_inr` — Q: `:105–106` *"the `gⱼ` become units"*. D: `← map_mul`,
  `Ideal.Quotient.eq`/`sub_mem`: `C (g j) * X (inr j) − 1 ∈ fractionIdeal` (`Ideal.subset_span`,
  `Set.mem_union_right`, `Set.mem_range_self`). SURVIVED.
- **L10.7** `toFractions_f` — D: `X (inl i) − C (f i) ∈ fractionIdeal` similarly. SURVIVED.
- **L10.8** `isPowerBounded_toFractions_f`, **L10.9** `isPowerBounded_inv_toFractions` — Q: `:106`
  *"the `fᵢ, gⱼ⁻¹` are power-bounded in `A′`"*. D: L10.7 / the inverse is `mk (X (inr j))`
  (`Units.inv_eq_of_mul_eq_one_right`-style from L10.6, `IsUnit.unit_spec`), and `IsPowerBounded.map`
  along `mk` (bound `1`, `Ideal.Quotient.norm_mk_le`) of `isPowerBounded_X`. SURVIVED.
- **L10.10** `isGeneralisedFractions_toFractions` — Q: `:107–114`. D: `constructor` with L10.5–L10.9;
  UP: `φ'' := extendAlgHom φ hφ (Sum.elim (φ ∘ f) (fun j ↦ ↑(hg j).unit⁻¹)) (Sum.rec hf hg')`; kills
  the generators (`extendAlgHom_X`, `extendAlgHom_C`, `Units.mul_inv`), so `fractionIdeal ≤ ker`
  (`Ideal.span_le`, `Set.union_subset`); `φ' := liftₐ`; `φ'.comp toFractions = φ` (`liftₐ_comp`,
  `extendAlgHom_comp_toAlgHom`); continuity via the quotient map; uniqueness: for `χ` with
  `χ.comp toFractions = φ`, `χ.comp (mkₐ _) = φ''` by `ringHom_ext_of_continuous` (constants: `χ (mk (C a))
  = χ (toFractions a) = φ a`; `X (inl i)`: `mk (X (inl i)) = toFractions (f i)` (L10.7) so
  `χ … = φ (f i)`; `X (inr j)`: `mk (X (inr j))` is the inverse of `toFractions (g j)` (L10.6), and a
  ring homomorphism sends inverses to inverses: `χ (mk (X_j)) * φ (g j) = 1` so `χ (mk X_j) =
  ↑(hg j).unit⁻¹` (`Units.eq_inv_of_mul_eq_one_left`)); then `Ideal.Quotient.algHom_ext`. A: [3]
  `hA` gives closedness so the quotient is a Banach algebra (a `B` of the predicate requires nothing
  of `A'` beyond the instances in the statement, which exist through the `haveI`). [2] the zero
  algebra `A⟨f, g⁻¹⟩` (e.g. `A = K`, `g = p`): the UP holds vacuously-consistently (no `φ` can make
  `p` a unit with power-bounded inverse into a nonzero `B`? it can — `B = 0`) ✓. SURVIVED.
- **L10.12** `isUnit_toRational` — Q: `:147–149`. D: `IsUnit.of_mul_eq_one (mk (C a + Σ C (a' i) *
  X i))`: `mk (C a + Σ …) * mk (C g) = mk (C (a g) + Σ C (a' i) * (C g * X i)) = mk (C (a g) + Σ C (a' i)
  * C (f i)) = mk (C 1) = 1`, using `C g * X i − C (f i) ∈ rationalIdeal` termwise (`Ideal.Quotient.eq`,
  `Finset.sum_mem`, `Ideal.mul_mem_left`), `map_sum`, `map_add`, `map_mul`, `hgen`. SURVIVED.
- **L10.13** `toRational_mul_inv` — Q: `:149` *"`X̄ᵢ = fᵢ/g`"*. D: `mk (C (f i)) = mk (C g * X i)`
  (`Ideal.Quotient.eq`, generator), then `mul_assoc`, `Units.mul_inv_cancel_right`-style with
  `toRational g = ↑unit`. SURVIVED.
- **L10.14** `isPowerBounded_toRational_div` — D: L10.13 and `IsPowerBounded.map` of `isPowerBounded_X`.
  SURVIVED.
- **L10.15** `isRationalFractions_toRational` — Q: `:150–151`. D: as L10.10 with `extendAlgHom φ hφ
  (fun i ↦ φ (f i) * ↑hg.unit⁻¹)`; kills `C g * X i − C (f i)` (`Units.mul_inv_cancel_right`);
  uniqueness: `χ (mk (X i)) * φ g = χ (mk (C g * X i)) = χ (mk (C (f i))) = φ (f i)` determines
  `χ (mk (X i)) = φ (f i) * (φ g)⁻¹` (`Units.eq_mul_inv_iff_mul_eq`). SURVIVED.
- **L10.16** `denseRange_awayLift` — Q: `:75–77` *"`A⟨X⟩[X⁻¹]` is dense in `A⟨X, X⁻¹⟩`"* (the analogous
  statement for `A⟨f/g⟩`, [RM] §1.4.2). D: the range of `awayLift` contains `mk (C a)`
  (`IsLocalization.Away.lift_eq`, `Algebra.ofId_apply`) and `mk (X i) = toRational (f i) * g⁻¹ =
  awayLift (mk' (f i) ⟨g, _⟩)` (L10.13, `IsLocalization.lift_mk'`); as a subalgebra it contains the
  classes of all polynomials; density as L9.17. SURVIVED.

### Internal nodes

- **N10.1** `IsGeneralisedFractions`, `IsRationalFractions` (structures) — [4] BGR 6.1.4/1 and 6.1.4/3
  verbatim, with "continuous" as in BGR; the power-bounded inverse in `IsGeneralisedFractions` is
  spelled with `(isUnit j).unit⁻¹`, a dependent field (the structure elaborates ✓). [6] the predicates
  carry a universe `v` for the test algebras `B`; the models satisfy them for every `v`. SURVIVED.
- **N10.2** `fractionIdeal`, `GeneralisedFractions`, `toFractions`, `isUnit_toFractions`,
  `isAffinoidAlgebra_generalisedFractions`, `rationalIdeal`, `RationalFractions`, `toRational`,
  `awayLift`, `isAffinoidAlgebra_rationalFractions` (complete) — [2] `A⟨f, g⁻¹⟩` can be the zero ring
  (BGR's `K⟨X⟩/(pX − 1) = 0` is `K⟨p⁻¹⟩`), consistent with the roadmap's example. SURVIVED.

---

## G11 — Extension of the ground field (`Affinoid/BaseChange.lean`), [RM] §1.1.6

### Source and prose proof

[BGR] 6.1.1/8 (`bgr-6.1.1.md:104–108`): *"The proposition applies in particular to the cases where
`A` is a TATE algebra `Tₙ(k)` or where `A` is an extension field `k′` of `k` with a complete valuation on
`k′` extending the valuation on `k`. Thus, we have **Corollary 8.** There are canonical isometric
isomorphisms `T_m ⊗̂_k Tₙ ≅ T_{m+n}` and `k′ ⊗̂_k Tₙ(k) ≅ Tₙ(k′)`."* 6.1.1/9 (`:110–117`): *"`k′ ⊗̂_k B`
is `k′`-affinoid … `id_{k′} ⊗̂ φ : k′ ⊗̂_k k⟨X₁, …, Xₙ⟩ → k′ ⊗̂_k B`"*; 6.1.1/12 (`:158–161`). [BGR] 3.7.1
(`bgr-3.7.md:17–19`): *"finite extensions of `k` provided with the spectral valuation … carry always the
product topology and … all subspaces are closed."* [RM] §1.1.6: *"for a finite extension `K'/K` with its
spectral norm, `A ⊗̂_K K' := A ⊗_K K'` (already complete)"*.

For a finite extension the complete tensor product is the algebraic one (finite-dimensional over the
Banach algebra `Tₙ(K)`): with a `K`-basis `b` of `K'`, every series over `K'` is `Σ_k b_k • g_k` with
`g_k` over `K` — the coordinates of the coefficients tend to zero because the coordinate functionals
of a finite-dimensional normed space are continuous (BGR's "product topology") — and the representation
is unique because `b` is a basis coefficientwise. Hence `K' ⊗_K Tₙ(K) → Tₙ(K')`, `c ⊗ f ↦ c • f`, is
bijective. Affinoidness of `K' ⊗ A` follows by tensoring a presentation (Mathlib's
`Algebra.TensorProduct.map_surjective`); 6.1.1/12 is Mathlib's `tensorQuotientEquiv`.

### Leaves

- **L11.1** `mapBase` (`commutes'`) — D: `Restricted.ext`, `val_map`, `MvPowerSeries.map_C`,
  `algebraMap_apply`, `Algebra.algebraMap_eq_smul_one`? — the `K`-algebra structure on `Tₙ(K')` is the
  general instance: `algebraMap K (Tₙ(K')) c = C 1 (algebraMap K K' c)` (L0.2). SURVIVED.
- **L11.2** `norm_mapBase` — Q: `bgr-6.1.1.md:107` *"isometric"*. D: `norm_def` on both sides,
  `MvPowerSeries.gaussNorm` with `coeff_map` and `norm_algebraMap'` (`NormOneClass K'`): the Gauss terms
  are equal termwise, so the suprema agree (`congrArg` after `funext`). A: [3] `NormOneClass K'` is
  needed for `‖algebraMap c‖ = ‖c‖` (`norm_algebraMap'`); for a normed field extension it holds.
  SURVIVED.
- **L11.3** `baseChangeAlgHom_tmul` — D: `Algebra.TensorProduct.lift_tmul`, `Algebra.ofId_apply`,
  `Algebra.smul_def`. SURVIVED.
- **L11.4** `exists_sum_smul_mapBase` — Q: `bgr-3.7.md:17–19` (the product topology of a finite
  extension), `bgr-6.1.1.md:107–108`. D: `h k := ⟨fun ν ↦ b.coord k (coeff ν g), _⟩` where
  restrictedness: `‖b.coord k x‖ ≤ C_k ‖x‖` (`LinearMap.continuous_of_finiteDimensional` for
  `b.coord k : K' →ₗ[K] K`, `[CompleteSpace K]`, then `SemilinearMapClass.bound_of_continuous`), so
  `‖coord k (coeff ν g)‖ ≤ C_k ‖coeff ν g‖ → 0` (`squeeze_zero`, `g.2`); the identity: `Restricted.ext`,
  `MvPowerSeries.ext fun ν ↦ ?_`, coefficient of `Σ_k b_k • map (h k)` is `Σ_k b_k • coord k (coeff ν g)
  = coeff ν g` (`Module.Basis.sum_repr`, `coeff_map`, `coeff_smul`, `Finset.sum_apply`-type lemmas
  `MvPowerSeries.coeff_sum`? — `map_sum` for `coeff ν`). A: [2] `K' = K` (`ι` a singleton) ✓. [3]
  `CompleteSpace K` is used for the continuity of coordinates (Mathlib needs it); `FiniteDimensional K
  K'` through `Fintype ι`. SURVIVED.
- **L11.5** `bijective_baseChangeAlgHom` — D: surjectivity from L11.4 (`Σ b k ⊗ₜ h k ↦ Σ b k • map (h k)`
  by `map_sum`, L11.3); injectivity: every `x : K' ⊗[K] Tₙ(K)` is `Σ_k b k ⊗ₜ h k` for a unique `h`
  (`Module.Basis.baseChange`? — use the basis `b.map?`: Mathlib's `Algebra.TensorProduct.basis`
  / `Basis.baseChange` gives a `Tₙ(K)`-basis `(b k ⊗ₜ 1)` of `K' ⊗[K] Tₙ(K)` after `TensorProduct.comm`;
  the ticket records the exact name after a search (`Basis.baseChange` is for `A ⊗[R] M` with `M`'s
  basis — here `M := K'` with basis `b` and `A := Tₙ(K)`, giving `Basis ι Tₙ (Tₙ ⊗[K] K')`, composed
  with `Algebra.TensorProduct.comm`)); then `Σ b k • map (h k) = 0` gives coefficientwise
  `Σ_k coeff ν (h k) • b k = 0` so all `coeff ν (h k) = 0` (`b.linearIndependent`, `Fintype.linearIndependent_iff`),
  so `h = 0` and `x = 0` (`injective_iff_map_eq_zero`). A: [2] `n = 0`: `K' ⊗ K ≅ K'` ✓. [5] the
  basis-of-tensor-product name is the one uncertainty, recorded as a search step. SURVIVED.
- **L11.6** `IsAffinoidAlgebra.baseChange` — Q: `bgr-6.1.1.md:113–117`. D: `obtain ⟨n, α, hα⟩ := hA`;
  `Algebra.TensorProduct.map (AlgHom.id K' K') α : K' ⊗[K] Tₙ(K) →ₐ[K'] K' ⊗[K] A` surjective
  (`Algebra.TensorProduct.map_surjective Function.surjective_id hα`); compose with
  `(baseChangeEquiv K K' n).symm.toAlgHom`; `⟨n, _, hsurj.comp (…).surjective⟩`. A: [6] the
  `K'`-algebra structure on `K' ⊗[K] A` is `Algebra.TensorProduct.leftAlgebra` ✓ (the statement
  elaborates with it). SURVIVED.

### Internal nodes

- **N11.1** `baseChangeAlgHom`, `baseChangeEquiv`, `completeSpace_of_finiteDimensional`,
  `baseChange_quotient` (complete) — [4] 6.1.1/12 is Mathlib's `Algebra.TensorProduct.tensorQuotientEquiv`
  verbatim (verified by the gate). [2] `baseChange_quotient` is stated with `Nonempty` since the
  equivalence is data from Mathlib. SURVIVED.

---

## G12 — Polydiscs of arbitrary polyradius (`Affinoid/Polydisc.lean`), [RM] §1.5

### Source and prose proof

[BGR] 6.1.5/4 (`bgr-6.1.3-6.1.5.md:199–213`): *"The algebra `T_{n,ϱ}` is `k`-affinoid if and only if
all components `ϱᵢ` of `ϱ` belong to `|k_a^*|`. Proof. First assume that there are `s₁, …, sₙ ∈ ℕ` and
`c₁, …, cₙ ∈ k^*` such that `ϱᵢ^{sᵢ} = |cᵢ⁻¹|` for `i = 1, …, n`. Then `|cᵢ Xᵢ^{sᵢ}|_ϱ = 1`, and we can
define a monomorphism `φ : Tₙ → T_{n,ϱ}` by setting `φ(Xᵢ) := cᵢ Xᵢ^{sᵢ}` (see Proposition 6.1.1/4). We
claim that `φ` is finite. Take `f = Σ a_ν X^ν ∈ T_{n,ϱ}` and write `f = Σ_{λ, 0 ≤ λᵢ < sᵢ} X^λ (Σ_μ
a_{μs+λ} c^{−μ} (c X^s)^μ)` … For each `λ` with `0 ≤ λᵢ < sᵢ`, define `g_λ := Σ_μ (a_{μs+λ} c^{−μ}) X^μ ∈
k⟦X⟧`. Then `g_λ ∈ Tₙ`, since `|a_{μs+λ} c^{−μ}| = |a_{μs+λ}| ϱ^{μs} = |a_{μs+λ}| ϱ^{μs+λ} ϱ^{−λ} → 0`
as `|μ| → ∞`. We have `f = Σ_λ φ(g_λ) X^λ` so that `T_{n,ϱ}` is a finite `Tₙ`-module via `φ`; the
monomials `X^λ`, `0 ≤ λᵢ < sᵢ`, are generators. Thus, `T_{n,ϱ}` is `k`-affinoid by Proposition 6.1.1/5,
and half of the theorem is proved."* `:180–185` (the open-disc example). [RM] §1.5.1–1.5.2.

`T_{n,ρ}` is Layer 0's `Restricted K ρ` with all its structure (§1.5.1 is the floor at every
polyradius). The first half of 6.1.5/4 is transcribed: the rescaling is Layer 0's `aeval` (BGR's
6.1.1/4 at `A = K`), injective because it acts on coefficients by `a_μ ↦ a_μ c^μ` placed at `μ s`, finite
with the stated generators, and `of_finite_tateAlgebra` (G4, BGR 6.1.1/5) concludes. The open-disc
example is explicit: `Σ aₙ Xⁿ` with `‖aₙ‖ ρⁿ ∈ [‖π‖⁻¹, 1]` converges for `‖x‖ < ρ` by comparison with a
geometric series and is not restricted.

### Leaves

- **L12.1** `norm_smul_X_pow` — Q: `:202` *"Then `|cᵢ Xᵢ^{sᵢ}|_ϱ = 1`"*. D: `norm_smul` (the Layer 0
  `NormedAlgebra K (Restricted K ρ)` instance), `norm_pow` (`NormMulClass`), `norm_X`, `norm_one`,
  `one_mul`, `mul_comm`, `hc i`. SURVIVED.
- **L12.2** `injective_rescaleAlgHom` — Q: `:202–203` *"a monomorphism"*. D: coefficient formula via
  `hasSum_eval₂` mapped by the continuous `coeff t` (as L4.19): `coeff t (φ f) = Σ_μ a_μ c^μ [t = μ s]`
  — with `hs`, `μ ↦ μ s` (`Finsupp` pointwise product) is injective, so the sum is `a_μ c^μ` at `t = μ s`
  and `0` elsewhere (`hasSum_ite_eq` after `Function.Injective`-reindexing); `φ f = 0` gives `a_μ c^μ = 0`,
  `c^μ ≠ 0` (`Finset.prod_ne_zero_iff`, `pow_ne_zero`, `hc0` from `hc`), so `f = 0`. A: [1] `s i = 0`:
  `X i ↦ c i • 1`, not injective ✓ excluded (D7). [5] `Finsupp.mapRange`/pointwise multiplication of
  finsupps: spelled with `Finsupp.ofSupportFinite (fun i ↦ μ i * s i)` as in L12.3. SURVIVED.
- **L12.3** `isRestricted_shiftCoeff` — Q: `:208–211`. D: unfold `IsRestricted` at `1`:
  `‖a_{μs+l} ∏ c_i^{-μ_i}‖ = ‖a_{μs+l}‖ ρ^{μ s} = (‖a_{μs+l}‖ ρ^{μs+l}) ρ^{−l}` (`norm_mul`,
  `norm_prod`, `norm_pow`, `norm_inv`, `hc`, `Finsupp.prod` manipulations); `f.2` composed with the
  injective map `μ ↦ μ s + l` (`Filter.Tendsto.comp` with `Function.Injective.tendsto_cofinite`), times
  the constant `ρ^{−l}` (`Tendsto.const_mul`). A: [2] `n = 0` ✓. SURVIVED.
- **L12.4** `finite_rescaleAlgHom` — Q: `:204–212`. D: `Module.Finite` via `φ.toRingHom.toAlgebra`;
  generators `X^λ` for `λ ∈ Fintype.piFinset (fun i ↦ Finset.range (s i))` (as `Finsupp`s through
  `Finsupp.equivFunOnFinite`); `Submodule.span = ⊤`: for `f`, the identity `f = Σ_λ φ (g_λ) * X^λ` where
  `g_λ := ⟨Σ_μ a_{μs+λ} c^{−μ} X^μ, L12.3⟩`; proof by `Restricted.ext` and coefficients: `coeff ν` of the
  right side is `a_ν` (the unique decomposition `ν = μ s + λ` by `Nat.div_add_mod`; `coeff` of
  `φ (g_λ)` by the formula of L12.2, times `X^λ` shifts by `λ`). A: [2] all `s i = 1`: `φ` is an
  isomorphism (`ρ = ‖c‖⁻¹`), generators `{1}` ✓. [3] `hc0` is implied by `hc` (`ρ^s ‖c‖ = 1`, so
  `c ≠ 0`) and is kept as a hypothesis for the statement's independence from `ρ > 0`. This is the
  longest leaf of G12 (estimate 120 lines of `Finsupp` arithmetic). SURVIVED.
- **L12.5** `isAffinoidAlgebra_of_forall_exists_pow_eq_norm` — Q: `:212–213`. D: `choose s c hs hc0 h
  using h`; `c' i := (c i)⁻¹` with `ρ i ^ s i * ‖c' i‖ = 1` (`norm_inv`, `mul_inv_cancel₀`);
  `IsAffinoidAlgebra.of_finite_tateAlgebra (rescaleAlgHom ρ s c' hc') (continuous_rescaleAlgHom _)
  (finite_rescaleAlgHom _ hs (inv_ne_zero ∘ hc0))`. A: [6] the target `Restricted K ρ` has all the
  instances `of_finite_tateAlgebra` needs (Layer 0 at every polyradius: `NormedCommRing`,
  `NormedAlgebra K`, `IsUltrametricDist`, `CompleteSpace`) ✓ (the statement elaborates). SURVIVED.
- **L12.6** `PowerSeries.exists_summable_not_isRestricted` — Q: `:182–185`. D: `π` with `1 < ‖π‖`
  (`NormedField.exists_one_lt_norm`); for each `ν`, `exists_mem_Ico_zpow (hρ' : 0 < ρ⁻¹ ^ ν) hπ` gives
  `k_ν` with `‖π‖^{k_ν} ≤ ρ^{−ν} < ‖π‖^{k_ν+1}`; `a_ν := π ^ k_ν` (`zpow`), `‖a_ν‖ ρ^ν ∈ (‖π‖⁻¹, 1]`;
  `f := PowerSeries.mk a`; summability at `‖x‖ < ρ`: `‖a_ν x^ν‖ ≤ (‖x‖/ρ)^ν`, geometric
  (`summable_geometric_of_lt_one`), `Summable.of_norm_bounded`; not restricted: `isRestricted_iff`
  (the floor's: `Tendsto (‖coeff‖ * ρ^ν) cofinite (𝓝 0)`) contradicts `‖π‖⁻¹ < ‖a_ν‖ ρ^ν` for all `ν`
  (`Filter.Tendsto.eventually_lt_const`, `Filter.eventually_cofinite`, a cofinite set of `ν` is
  nonempty). A: [2] `ρ ∉ |K^×|` is *not* needed for this statement (the series simply fails
  restrictedness at radius `ρ`); BGR's point is about `P_ρ(k) = B⁻(0, ρ)` when `ρ ∉ |k^×|`, which the
  roadmap records as the example's *meaning*, not as a hypothesis ✓. [3] `NontriviallyNormedField`
  needed for `π`. SURVIVED.

### Internal nodes

- **N12.1** `rescaleAlgHom`, `rescaleAlgHom_X`, `continuous_rescaleAlgHom` (complete) — [4] the roadmap's
  route through Weierstrass domains (`Tₙ⟨(cᵢ'^r cᵢ⁻¹) Zᵢ^r⟩`) is replaced by BGR's own finite
  monomorphism; recorded as deviation V4 in the plan. SURVIVED.

---

## G13 — Examples (`Affinoid/Examples.lean`), [RM] Layer 1, "Examples"

### Source and prose proof

[RM] Layer 1 Examples: *"`K⟨X⟩/(X² − p)` and `K⟨X⟩/(X − a)` for `|a| ≤ 1`; `K⟨X⟩/(pX − 1) = 0`;
`A⟨f⟩` for `f = X` in `A = K⟨X⟩` is `A` itself; `K⟨X, Y⟩/(XY − 1) = K⟨X, X⁻¹⟩`; Noether normalisation of
`K⟨X, Y⟩/(Y² − X³)` by `T₁ = K⟨X⟩`; the two presentations `K⟨X⟩ ⧸ (X)` and `K` of the same affinoid
algebra, with their residue norms equal; `ℚ_p⟨X⟩ ⊗_{ℚ_p} ℚ_p(√p) = ℚ_p(√p)⟨X⟩`."* [BGR]
`bgr-6.1.3-6.1.5.md:99–102` (`A⟨X⟩⟨X⁻¹⟩ ≅ A⟨X, X⁻¹⟩`).

Each example is an instance of a Layer 0 or Layer 1 theorem: Weierstrass division by `X − a` and
`X² − a` (Layer 0), units `aX − 1` for `‖a‖ < 1` (geometric series), `IsGeneralisedFractions.of_isUnit`,
the sum/rename isomorphisms, the distinguishedness of the cusp with G7's finiteness and injectivity,
the nearest-point description of the residue norm, and `baseChangeEquiv`.

### Leaves

- **L13.1** `finrank_quotient_X_sq_sub` — Q: [RM] (`K⟨X⟩/(X² − p)`); [L0] `isMaximal_span_X_sq_sub_p`
  is the `ℚ_p` instance. D: `ω := Polynomial.X ^ 2 − Polynomial.C (C 1 a)` over `T₀`, a Weierstrass
  polynomial ([L0] `isWeierstrassPolynomial_iff`, `‖a‖ < 1`); `IsWeierstrassPolynomial.bijective_quotientMap`
  gives `T₀[X] ⧸ (ω) ≃ T₁ ⧸ (ofPolynomial ω)` (ring equivalence, `RingEquiv.ofBijective`), and
  `ofPolynomial ω = X ^ 2 − C a` (`map_sub`, `map_pow`, `ofPolynomial_X`, `ofPolynomial_C`-type
  Layer 0 lemmas); `T₀[X] ⧸ (ω) ≃ₐ AdjoinRoot ω` with `(AdjoinRoot.powerBasis (monic.ne_zero)).finrank`
  `= natDegree ω = 2`; transport along `K`-linear equivalences (`T₀ ≃ₐ[K] K`, `isEmptyEquiv`). A: [3]
  `‖a‖ < 1` (not `≤ 1`) is needed for the Weierstrass polynomial (`‖X² − a‖ = max 1 ‖a‖ = 1` only needs
  `≤ 1`; but `isWeierstrassPolynomial` is "monic of Gauss norm one" (Layer 0's E1), so `‖a‖ ≤ 1`
  suffices!). **Attack [3] finds the hypothesis stronger than needed**: keep `‖a‖ < 1` (the roadmap's
  example has `a = p`), noted in the ticket as a possible generalisation; not a defect. SURVIVED.
- **L13.2** `ker_aeval_eq_span` — Q: [RM] (`K⟨X⟩/(X − a)`). D: `⊇`: `Ideal.span_le`, `aeval_X`,
  `aeval_C`, `sub_self`; `⊆`: `X − C a` is `X 0`-distinguished of order `1` ([L0]
  `isMulDistinguishedX0_iff`: `coeffX0 1 = 1`, `‖X − C a‖ = 1`, higher coefficients `0`);
  `weierstrassDivision_exists` writes `f = q * (X − C a) + ofPolynomial r` with `degree r < 1`, i.e.
  `r = C r₀` with `r₀ ∈ T₀ ≅ K`; applying `aeval` gives `0 = r₀` (as an element of `K`, via
  `aeval_toRestricted`/`ofPolynomial_C`), so `f = q * (X − C a) ∈ span`. A: [2] `a = 0` ✓. SURVIVED.
- **L13.3** `nonempty_algEquiv_quotient_X_sub` — D: `⟨(Ideal.quotientKerAlgEquivOfSurjective
  hsurj).trans? ⟩`: `aeval 1 (fun _ ↦ a)` is surjective (`aeval_C`-type: `c • 1 ↦ c`), then
  `Ideal.quotientKerAlgEquivOfSurjective` and `ker_aeval_eq_span ▸`. SURVIVED.
- **L13.4** `isUnit_C_mul_X_sub_one` — Q: [RM] (`K⟨X⟩/(pX − 1) = 0`); [L0] `isUnit_one_add_p_mul_X`
  is the same computation. D: `‖C a * X‖ = ‖a‖ < 1` (`norm_mul`, `norm_C`, `norm_X`), `isUnit_one_sub_of_norm_lt_one`,
  `IsUnit.neg` with `sub_eq_neg_add`-type rewriting. SURVIVED.
- **L13.5** `subsingleton_quotient_C_mul_X_sub_one` — D: `Ideal.span_singleton_eq_top.2 (L13.4)`,
  `Ideal.Quotient.subsingleton_iff`. SURVIVED.
- **L13.6** `nonempty_algEquiv_generalisedFractions_X` — Q: `bgr-6.1.3-6.1.5.md:99–102`. D:
  `e₁ := renameEquiv (T₁) (Equiv.sumEmpty? : Fin 0 ⊕ Fin 1 ≃ Fin 1)` upgraded to `≃ₐ[K]`, `e₂ :=
  TateAlgebra.sumEquiv K 1 1 : Restricted T₁ 1_{Fin 1} ≃ₐ[K] T₂`; `Ideal.quotientEquivAlg (fractionIdeal …)
  (span {X 0 * X 1 − 1}) (e₁.trans e₂) (map_eq : …)` where the ideal image is computed on the
  generators (`Ideal.map_span`, `Set.image`, `renameEquiv_C/X`, `sumEquiv_C/X`, `Fin.elim0`). A: [6]
  the `Fin.castAdd`/`natAdd` conventions of L2.17: `Y_0 ↦ X 0`, `C (X 0) ↦ X 1`, so the generator
  `C (X 0) * Y 0 − 1 ↦ X 1 * X 0 − 1 = X 0 * X 1 − 1` (`mul_comm`) ✓. SURVIVED.
- **L13.7** `isMulDistinguishedX0_cusp` — D: [L0] `isMulDistinguishedX0_iff` for `g = X 0 ^ 2 − X 1 ^ 3`:
  `coeffX0 g 2 = 1` (unit), `‖g‖ = 1 = ‖coeffX0 g 2‖`, `coeffX0 g ν = 0` for `ν > 2` and `‖·‖ < 1`
  there — computed from `X 1 ^ 3 = ofTail (X 0 ^ 3)` (`ofTail_X`) and `X 0 ^ 2 = ofPolynomial X^2`
  (`coeffX0_ofPolynomial`, `coeff_coeffX0`). A: [4] BGR's `Y² − X³` with `Y` the distinguished (last)
  variable is our `X 0 ^ 2 − X 1 ^ 3` by convention 2 ✓ docstring says so. SURVIVED.
- **L13.8** `exists_algEquiv_quotient_X_norm_eq` — Q: [RM] (two presentations of `K`). D: `e :=
  Ideal.quotientKerAlgEquivOfSurjective (aeval at 0)` with `ker = span {X}` (L13.2 at `a = 0`,
  `C 0 = 0`); norm: for `mk f`, `‖mk f‖ = ‖f − (f − C (coeff 0 f))‖ = ‖C (coeff 0 f)‖ = ‖coeff 0 f‖` by
  L1.2 (`norm_mk_eq_norm_of_forall_le` applied to the representative `C (coeff 0 f)` whose class is
  `mk f`: for `g ∈ span {X}`, `coeff 0 g = 0`, so `‖C c₀ − g‖ ≥ ‖coeff 0 (C c₀ − g)‖ = ‖c₀‖`
  (`norm_coeff_le`)), and `e (mk f) = aeval f = coeff 0 f` (`aeval_apply` at `x = 0`:
  `Σ' coeff t f * 0^t = coeff 0 f`, `tsum_ite_eq`-style). A: [2] `f ∈ (X)` ✓ both sides `0`. SURVIVED.

### Internal nodes

- **N13** `isAffinoidAlgebra_quotient_X_sq_sub`, `isGeneralisedFractions_id_X`, `finite_injective_cusp`,
  `isAffinoidAlgebra_polydisc`, `subsingleton_quotient_p_mul_X_sub_one`, `finrank_quotient_X_sq_sub_p`,
  the `baseChangeEquiv` example (complete) — [6] each is one application; `Padic.norm_p_lt_one` is
  Mathlib's. SURVIVED.

---

## Confidence gate (Step 5)

1. **Every leaf has a verbatim source quote with a locator**: 153 leaves, each with a Q line into
   `references/*.md`, `bosch-lectures.txt`, Layer 0 (`[L0]`) or the roadmap (`[RM]`, used only for
   the examples, the convention-driven packaging and the `notions independent of the norm` items of
   §1.3.3). ✓
2. **Every leaf has a Lean ↔ source match paragraph (M)** or the match is literal (then only D). ✓
3. **Every leaf is discharged** (D) from Mathlib, Layer 0, PFA, or earlier leaves; the Mathlib names
   are listed in the tickets and checked by elaboration (`plan.md`, "Name check"). Two names are
   recorded as *search steps* in their tickets: the basis of `K' ⊗[K] M` (L11.5) and the constant-term
   argument of L7.16. ✓
4. **Attacks**: every leaf has at least three attack categories; seven attacks succeeded and were
   repaired (D1–D9 above and the L0.7 edge case); no leaf was deleted. ✓
5. **No invented infrastructure**: the only general-purpose developments not in BGR's text are the
   quotient-norm facts of G1 (BGR cites them as "easy to see"), the nonarchimedean Nakayama lemma in
   Mathlib's form (BGR 1.2.4/6), and the two fraction-field lemmas of G7 (BGR: "`Q(A′)` is finite over
   `Q(T_d)`"); each is a one-ticket lemma with a source line. ✓
6. **No false leaf** survived: the degenerate cases found (zero ring, `s = 0`, universes) are repaired
   in the statements, not assumed away in proofs. ✓
7. **Statement shape**: no bundled conclusions (see above). ✓

## Unticketed sub-trees (not on this board)

- **BGR 6.1.1/6, 6.1.3/4 and the remark after it** (a finite homomorphism from an affinoid algebra into
  a `K`-algebra admits a Banach topology making it strict; a finite homomorphism into a Banach algebra
  is automatically continuous and strict): needs BGR 3.7.4/1, the construction of a ring norm on a
  finite module (`|x| := sup |xy|′/|y|′`); the roadmap does not list it, and §1.1.3 asks only for the
  continuous-finite form (BGR 6.1.1/5).
- **BGR 3.7.2/2, "only if"** (all ideals closed ⇒ noetherian, by Baire) and **3.7.3** (finite modules
  over a noetherian Banach algebra): not requested by the roadmap's Layer 1.
- **Direct sums `A ⊕ B`** (`bgr-6.1.1.md:80–89`): not in the roadmap; a one-ticket addition if a later
  layer needs it (`Prod` of Banach algebras with `Tₙ⟨Y⟩ → Tₙ × Tₙ`).
- **The seminorm-completion model of `A⟨f, g⁻¹⟩` and `A⟨f/g⟩`** (`bgr-6.1.3-6.1.5.md:79–91`, `:128–138`)
  and the isometry of the two models (BGR 6.1.4/2, 6.1.4/4 "isometric"): roadmap §1.4.2 asks for it;
  deferred (deviation V2 in the plan): only the density of `A[g⁻¹]` is proved. Building the completion
  needs the PFA roadmap's completion of seminormed algebras.
- **Roadmap §1.4.3–1.4.4** (identification with the adic-spaces roadmap's `A⟨T/s⟩`, flatness): that
  chain is not in this repository.
- **BGR 6.1.5/4, "only if", and 6.1.5/5** (`|·|_ρ` is the supremum norm; `T_{n,ρ}` affinoid forces
  `ρᵢ ∈ |k_a^×|`): need the supremum seminorm of Layer 2 (BGR 3.1.5, 6.2); roadmap §1.5.2 lists the
  "only if" as a ⚠ remark; deferred to Layer 2.
- **Characteristic `p` Japaneseness** of affinoid domains: Layer 0's `isJapaneseRing` is characteristic
  zero only (Layer 0's unticketed sub-tree), so `IsAffinoidAlgebra.isJapaneseRing` carries `[CharZero K]`.
- **BGR 6.1.1/9's strict monomorphism `B → k′ ⊗̂ B`** for an arbitrary complete extension `k′`: the
  roadmap sends it to §6.6; for finite `K'` the map `A → K' ⊗[K] A` is injective by Mathlib (free base
  change), not stated here.
