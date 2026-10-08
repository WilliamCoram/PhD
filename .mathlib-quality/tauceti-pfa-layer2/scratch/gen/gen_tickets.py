#!/usr/bin/env python3
"""Generate tickets.md for the tauceti-pfa-layer2 board.
Statement blocks are copied verbatim from the skeleton files (never typed by hand)."""
import re, pathlib

ROOT = pathlib.Path("/Users/nkw24xru/Desktop/Lean/PhD")
CODE = ROOT / "PhD/TauCeti/Code/PadicFunctionalAnalysis"
OUT = ROOT / ".mathlib-quality/tauceti-pfa-layer2/tickets.md"
KW = r"(?:(?:noncomputable|scoped|protected)\s+)*(?:theorem|def|instance|structure|abbrev)\s+"

def extract(fname, key):
    lines = (CODE / fname).read_text().split("\n")
    if key.startswith("instance"):
        pat = re.compile(r"^(?:noncomputable\s+)?" + re.escape(key))
    else:
        pat = re.compile("^" + KW + re.escape(key) + r"(?=\s|$|\()")
    idx = next((i for i, l in enumerate(lines) if pat.match(l)), None)
    assert idx is not None, (fname, key)
    start = idx
    while start > 0 and (lines[start-1].startswith("@[") or lines[start-1].startswith("omit ")
                         or lines[start-1].startswith("variable (") or lines[start-1].startswith("include ")):
        start -= 1
    end = idx
    while end + 1 < len(lines) and lines[end+1].strip() != "":
        end += 1
    return "\n".join(lines[start:end+1])

T = []
def ticket(id, title, file, deps, parallel, typ, leaves, decls, sketch, lemmas, sources, generality, extra=""):
    T.append(dict(id=id, title=title, file=file, deps=deps, parallel=parallel, typ=typ, leaves=leaves,
                  decls=decls, sketch=sketch, lemmas=lemmas, sources=sources, generality=generality, extra=extra))
def cleanup(id, file, deps, note):
    T.append(dict(id=id, cleanup=True, file=file, deps=deps, note=note))

BA = "ModelSpace/Basic.lean"; UN = "ModelSpace/Universal.lean"; RE = "ModelSpace/Reindex.lean"
MA = "ModelSpace/Map.lean"; TR = "ModelSpace/Truncation.lean"; OR = "Orthogonal.lean"; ON = "ONable.lean"
SE = "Serre.lean"; CT = "CountableType.lean"; MX = "ModelSpace/Matrix.lean"; DU = "ModelSpace/Dual.lean"
CL = "ModelSpace/Closed.lean"; UT = "Unitriangular.lean"; EX = "ModelSpace/Examples.lean"

# ---------------- T001: the shared redefinition ----------------
ticket("T001", "Redefine `IsOrthonormalFamily` (Bellaïche form) and generalise `Orthonormal.lean` to normed rings",
 "Orthonormal.lean", "none", "yes (edits only the shared file and two RAG files; run alone, then rebuild the chain)",
 "definition change + proof repairs", "L1.1–L1.4",
 [],
 """**Files**: `PhD/TauCeti/Code/PadicFunctionalAnalysis/Orthonormal.lean` (shared with the rigid-geometry board, done),
`PhD/TauCeti/Code/RigidAnalyticGeometry/OrthonormalLift.lean` (one proof site, l. 196–198),
`PhD/TauCeti/Code/RigidAnalyticGeometry/TateAlgebra/StrictlyClosed.lean` (two proof sites, l. 205–215 and l. 264–278).
Statements of the RAG files are **not** changed; only the three proofs and the one definition.
1. In `Orthonormal.lean` replace the second conjunct of `IsOrthonormalFamily` by
   `∀ (s : Finset I) (a : I → R), ‖∑ i ∈ s, a i • e i‖₊ = s.sup fun i ↦ ‖a i‖₊` (plan E19); update the two docstrings
   (Source: Bellaïche, Definition II.1.5; Buzzard §2; Colmez, Déf 1.1.3 (ii); roadmap convention 5 as corrected).
2. Generalise the `IsOrthonormalFamily`/`IsOrthonormalBasis` sections from `[NormedField K] [NormedSpace K V]` to
   `{R : Type*} [NormedRing R] {M : Type*} [NormedAddCommGroup M] [Module R M]`; `summable_smul` and `exists_hasSum`
   keep `[IsUltrametricDist M] [CompleteSpace M]` and `exists_hasSum` takes `[CompleteSpace R]` instead of
   `[CompleteSpace K]`. Lemma by lemma: `nnnorm_smul_eq` becomes `‖c • e i‖₊ = ‖c‖₊` from the identity at
   `s = {i}` (`Finset.sum_singleton`, `Finset.sup_singleton`); `norm_coeff_le_norm_sum` is the identity plus
   `Finset.le_sup (f := fun j ↦ ‖a j‖₊)`; `norm_sum_le` is the identity plus `Finset.sup_le`; `linearIndependent`,
   `norm_coeff_le_of_hasSum`, `norm_le_of_hasSum`, `eq_of_hasSum` keep their proofs; `tendsto_cofinite_of_hasSum`
   and `summable_smul` replace `norm_smul, he.1, mul_one` by the new `nnnorm_smul_eq`/its real form;
   `exists_hasSum` is unchanged except for the instance (its Cauchy argument runs in `R`).
3. `OrthonormalLift.lean:196`: the final `refine ⟨hy1, fun s a ↦ le_antisymm (Finset.nnnorm_sum_le_sup_nnnorm s _)
   (Finset.sup_le fun μ hμ ↦ ?_)⟩` now has goals `‖∑‖₊ ≤ s.sup ‖a μ‖₊` and `‖a μ‖₊ ≤ ‖∑‖₊`: for the first
   compose `Finset.nnnorm_sum_le_sup_nnnorm` with `Finset.sup_mono_fun fun μ _ ↦ by rw [nnnorm_smul, …hy1…, mul_one]`
   (`‖a μ • y μ‖₊ = ‖a μ‖₊`); for the second drop the `norm_smul, hy1, mul_one` rewrite and use `hkey s a μ hμ`.
4. `StrictlyClosed.lean:205` and `:264`: in the first bullet of each, the `hu` branch uses
   `Finset.le_sup (f := fun t ↦ ‖a t‖₊) hu` directly (no `← hsmul`); in the second bullet drop `rw [hsmul, …]`
   and keep the `coe_nnnorm` conversion; delete `hsmul` if it becomes unused.
5. Rebuild the dependents: `lake build PhD.TauCeti.Code.RigidAnalyticGeometry.TateAlgebra.Examples` and
   `lake build PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.Examples` (or the whole chain `lake build PhD.TauCeti`),
   then `lake exe runLinter PhD.TauCeti.Code.PadicFunctionalAnalysis.Orthonormal`.""",
 "`Finset.sum_singleton`, `Finset.sup_singleton`, `Finset.le_sup`, `Finset.sup_le`, `Finset.sup_mono_fun`, `Finset.nnnorm_sum_le_sup_nnnorm`, `nnnorm_smul`, `NNReal.coe_le_coe`, `coe_nnnorm`, `cauchySeq_tendsto_of_complete`.",
 "[Bel] Def II.1.5 l. 2010–2015 (\"`|m| = sup_i |a_i|`\"); [Buz07] l. 229–236; [Col] Déf 1.1.3 (ii) l. 108–109; E19 (plan) with the torsion counterexample; [RAG] the three proof sites.",
 "Normed-ring scalars everywhere; the field lemmas are instances. **Seam S1**: the only ticket touching files outside this board's new files; run it first and alone.")

# ---------------- Basic ----------------
ticket("T002", "The sup norm on `C₀(I, E)`", BA, "none", "yes (parallel with T001)", "lemmas", "L2.1–L2.7",
 ["norm_eq_iSup", "norm_apply_le", "norm_le_of_forall_le", "sum_apply", "tendsto_cofinite", "exists_norm_apply_eq_norm", "countable_support"],
 """1. `norm_eq_iSup`: `rw [← norm_toBCF_eq_norm, BoundedContinuousFunction.norm_eq_iSup_norm]; rfl` (`toBCF_apply`).
2. `norm_apply_le`: `rw [← norm_toBCF_eq_norm]; exact BoundedContinuousFunction.norm_coe_le_norm f.toBCF i`.
3. `norm_le_of_forall_le`: `rw [← norm_toBCF_eq_norm]; exact (BoundedContinuousFunction.norm_le hC).2 h`.
4. `sum_apply`: `Finset.cons_induction` with `Finset.sum_cons` and `add_apply` (there is no `coeFnAddMonoidHom` for `C₀`).
5. `tendsto_cofinite`: `have := f.zero_at_infty'; rwa [cocompact_eq_cofinite] at this`.
6. `exists_norm_apply_eq_norm`: `obtain ⟨i, hi⟩ := (tendsto_cofinite f).exists_norm_eq_iSup` (Layer 0 `Sums.lean`), then `⟨i, by rw [hi, norm_eq_iSup]⟩`.
7. `countable_support`: `{i | f i ≠ 0} = ⋃ n : ℕ, {i | (n + 1 : ℝ)⁻¹ < ‖f i‖}` (`Set.ext`, `norm_pos_iff`, `exists_nat_one_div_lt`);
   each set is finite by `Filter.eventually_cofinite.1 (Metric.tendsto_nhds.1 (tendsto_cofinite f) _ (by positivity))`
   (complement form, `dist_zero_right`), so `Set.countable_iUnion fun n ↦ (…).countable`.""",
 "`ZeroAtInftyContinuousMap.norm_toBCF_eq_norm`, `toBCF_apply`, `BoundedContinuousFunction.{norm_eq_iSup_norm, norm_coe_le_norm, norm_le}`, `Finset.cons_induction`, `Finset.sum_cons`, `ZeroAtInftyContinuousMap.add_apply`, `cocompact_eq_cofinite`, `Filter.Tendsto.exists_norm_eq_iSup` [L0], `Metric.tendsto_nhds`, `Filter.eventually_cofinite`, `Set.countable_iUnion`, `Set.Finite.countable`, `exists_nat_one_div_lt`, `norm_pos_iff`.",
 "[RM] §2.1.1 (\"the sup-norm formula `‖f‖ = ⨆ i, ‖f i‖`, that the supremum is attained when `f ≠ 0`, that `f → 0` cofinitely\"); [Sch] §3 l. 495–520 (`c₀(X)`), the dual example l. 617–700 (\"each `Y_x` is finite or countable\").",
 "Any topological `I` for L2.1–L2.4 (the formula is Mathlib's for `α →ᵇ β`); `DiscreteTopology I` only from L2.5 on; seminormed `E` throughout.")

ticket("T003", "The instances Mathlib lacks on `C₀(I, E)`", BA, "T002", "no", "instances", "L3.1–L3.3",
 ["instIsUltrametricDist", "instIsBoundedSMul", "instNormSMulClass"],
 """1. `instIsUltrametricDist`: `⟨fun f g h ↦ ?_⟩` with the field `dist_triangle_max`; rewrite the three distances with
   `dist_eq_norm`; `norm_le_of_forall_le (le_max_of_le_left dist_nonneg) fun i ↦ ?_`; `(f - h) i = (f - g) i + (g - h) i`
   (`sub_apply`, `sub_add_sub_cancel`), then `IsUltrametricDist.norm_add_le_max` and `max_le_max (norm_apply_le _ i) (norm_apply_le _ i)`.
2. `instIsBoundedSMul`: `IsBoundedSMul.of_norm_smul_le fun r f ↦ norm_le_of_forall_le (mul_nonneg (norm_nonneg r) (norm_nonneg f))
   fun i ↦ by rw [smul_apply]; exact (norm_smul_le r (f i)).trans (mul_le_mul_of_nonneg_left (norm_apply_le f i) (norm_nonneg r))`.
3. `instNormSMulClass`: `⟨fun r f ↦ by simp_rw [norm_eq_iSup, smul_apply, norm_smul, Real.mul_iSup_of_nonneg (norm_nonneg r)]⟩`.""",
 "`IsUltrametricDist.mk` (field `dist_triangle_max`), `dist_eq_norm`, `IsUltrametricDist.norm_add_le_max`, `max_le_max`, `IsBoundedSMul.of_norm_smul_le`, `norm_smul_le`, `ZeroAtInftyContinuousMap.smul_apply`, `norm_smul`, `Real.mul_iSup_of_nonneg`.",
 "[RM] §2.1.1 (\"Add to `C₀(I, E)` … the instances Mathlib lacks: `IsUltrametricDist`, and … `IsBoundedSMul R C₀(I, E)` (and `NormSMulClass` when `E` has it)\").",
 "Any topological `I`; `[SeminormedRing R] [Module R E] [IsBoundedSMul R E]` for the action (the `Module R C₀(I, E)` instance is Mathlib's, through `ContinuousConstSMul`).")

ticket("T004", "The coordinate vectors `single i x`", BA, "T002", "yes (parallel with T003)", "definition + lemmas", "L4.1–L4.6",
 ["single", "single_apply_self", "single_apply_of_ne", "single_zero", "norm_single", "smul_single"],
 """1. The `sorry` in `single`: `Tendsto (Pi.single i x) cofinite (𝓝 0)` is
   `tendsto_const_nhds.congr' (Filter.eventually_cofinite.2 ((Set.finite_singleton i).subset fun j hj ↦ by_contra fun h ↦ hj (Pi.single_eq_of_ne h x)))`
   (the set where `Pi.single i x j ≠ 0` is inside `{i}`).
2. `single_apply_self`: `Pi.single_eq_same`; `single_apply_of_ne`: `Pi.single_eq_of_ne h`.
3. `single_zero`: `ext j; simp [Pi.single_zero]`.
4. `norm_single`: `le_antisymm (norm_le_of_forall_le (norm_nonneg x) fun j ↦ ?_) ?_`; upper: `by_cases hj : j = i` with
   `Pi.single_eq_same`/`Pi.single_eq_of_ne` and `norm_zero`; lower: `(single_apply_self i x) ▸ norm_apply_le (single i x) i`.
5. `smul_single`: `ext j; rw [smul_apply, coe_single, coe_single, ← Pi.single_smul]`.""",
 "`tendsto_const_nhds`, `Filter.Tendsto.congr'`, `Filter.eventually_cofinite`, `Set.finite_singleton`, `Pi.single_eq_same`, `Pi.single_eq_of_ne`, `Pi.single_zero`, `Pi.single_smul`, `norm_zero`.",
 "[RM] §2.1.2 (\"The coordinate vectors `single i r`\"); [Sch] §3 (\"`1_x`\"); [Buz07] l. 238–243 (\"`e_i` … the function sending `j` to `0` if `i ≠ j`, and to `1` if `i = j`\").",
 "`single` is stated for any seminormed `E` (used with `E = R` and, in `IsONable.zeroAtInfty`, with `E = M`); `[DecidableEq I]` because it is `Pi.single`.")

cleanup("CLEANUP-1", BA, "T002, T003, T004", "Three proof tickets landed on `Basic.lean`")

ticket("T005", "The coordinate expansion and the density of finitely supported families", BA, "CLEANUP-1", "no", "lemmas", "L5.1–L5.5",
 ["hasSum_single_apply", "dense_span_range_single", "hasSum_smul_single_one", "dense_span_range_single_one", "norm_evalCLM"],
 """1. `hasSum_single_apply`: `HasSum` is `Tendsto (fun s : Finset I ↦ ∑ i ∈ s, single i (f i)) atTop (𝓝 f)`; use `Metric.tendsto_atTop.2 fun ε hε ↦ ?_`.
   From `Metric.tendsto_nhds.1 (tendsto_cofinite f) (ε / 2) (half_pos hε)` and `Filter.eventually_cofinite` the set
   `B := {i | ¬ ‖f i‖ < ε / 2}` is finite; take `N := B.toFinset`. For `s ≥ N`: pointwise
   `(∑ i ∈ s, single i (f i)) j = if j ∈ s then f j else 0` (`sum_apply`, `coe_single`, `Finset.sum_pi_single'`), so
   `‖(f - ∑ …) j‖ = if j ∈ s then 0 else ‖f j‖ ≤ ε / 2` (`j ∉ s ⟹ j ∉ B`), hence `dist (∑ …) f ≤ ε / 2 < ε` via
   `dist_eq_norm'`/`norm_le_of_forall_le`.
2. `dense_span_range_single`: `Metric.dense_iff`/`Metric.mem_closure_iff`: for `f` and `ε`, the partial sum
   `∑ i ∈ N, single i (f i)` lies in the span (`Submodule.sum_mem`, `Submodule.subset_span ⟨(i, f i), rfl⟩`) and is within
   `ε` by the tendsto of step 1 (`Metric.tendsto_atTop.1`).
3. `hasSum_smul_single_one`: `(hasSum_single_apply f).congr?` — show `f i • single i 1 = single i (f i)` by
   `smul_single, smul_eq_mul, mul_one` and rewrite (`funext`, `simpa only`).
4. `dense_span_range_single_one`: as 2 with `f i • single i 1` (`Submodule.smul_mem`), or from 2 with
   `Submodule.span_le`-monotonicity (`single i x = x • single i 1`) and `Dense.mono`.
5. `norm_evalCLM`: `le_antisymm (opNorm_le_bound _ zero_le_one fun f ↦ by rw [one_mul]; exact norm_apply_le f i) ?_`;
   lower: `have h := le_opNorm_of_bound (evalCLM R i) ⟨1, fun f ↦ by rw [one_mul]; exact norm_apply_le f i⟩ (single i 1)`,
   then `rw [evalCLM_apply, single_apply_self, norm_one, norm_single, norm_one, mul_one] at h`.""",
 "`Metric.tendsto_atTop`, `Metric.tendsto_nhds`, `Filter.eventually_cofinite`, `Set.Finite.toFinset`, `Finset.sum_pi_single'`, `dist_eq_norm'`, `Metric.mem_closure_iff`, `Submodule.sum_mem`, `Submodule.smul_mem`, `Submodule.subset_span`, `Dense.mono`, `ContinuousLinearMap.Ultra.{opNorm_le_bound, le_opNorm_of_bound}` [L1], `norm_one`.",
 "[RM] §2.1.2 (\"the coordinate functionals `eval i : C₀(I, R) →L[R] R` of norm `1`, and the expansion `f = ∑' i, f i • single i 1`, convergent in norm; finitely supported families are dense\"); [Bel] footnote l. 2022–2027 (the convergence of `∑ m_i` along finite subsets); [Buz07] l. 243–245 (\"the `e_i` are an ON basis for `c_A(I)`\").",
 "No completeness and no ultrametricity: the partial sums are truncations and converge for any seminormed `E` (plan decision 8). `norm_evalCLM` needs `[NormOneClass R]` (`‖single i 1‖ = ‖1‖`) and no Tate hypothesis (`le_opNorm_of_bound`).")

cleanup("CLEANUP-2", BA, "T005", "Final cleanup of `Basic.lean`")

# ---------------- Universal ----------------
ticket("T006", "Uniqueness: a map out of the model space is determined on the coordinate vectors", UN, "CLEANUP-2", "no", "lemmas", "L6.1–L6.3",
 ["hasSum_smul_apply_single", "ext_single", "exists_bound_single"],
 """1. `hasSum_smul_apply_single`: `have h := (hasSum_smul_single_one f).mapL u` gives `HasSum (fun i ↦ u (f i • single i 1)) (u f)`;
   `simpa only [map_smul] using h`.
2. `ext_single`: `ContinuousLinearMap.ext fun f ↦ (hasSum_smul_apply_single u f).unique (by simpa only [h] using hasSum_smul_apply_single v f)`.
3. `exists_bound_single`: `⟨‖u‖, fun i ↦ by simpa [norm_single, norm_one] using le_opNorm u (single i 1)⟩` (`[IsTate R]`, `[NormOneClass R]`).""",
 "`HasSum.mapL`, `ContinuousLinearMap.map_smul`, `HasSum.unique`, `ContinuousLinearMap.ext`, `ContinuousLinearMap.Ultra.le_opNorm` [L1], `norm_single`, `norm_one`.",
 "[Sch] universal property of `c₀(X)` l. 2905–2947 (\"`f` is uniquely determined by its values on the `1_x`\"); [Buz07] l. 274–280 (\"if `φ` is continuous and `φ(e_i) = n_i`, then the `n_i` are a bounded collection of elements of `N` which uniquely determine `φ`\").",
 "L6.1–L6.2 over any normed ring and any normed module (no completeness); L6.3 is the only Tate-dependent fact (plan E26).")

ticket("T007", "The universal property: `ofBounded`", UN, "T006", "no", "definition + lemmas", "L7.1–L7.5",
 ["summable_smul_of_bounded", "norm_tsum_smul_le", "ofBounded", "hasSum_ofBounded", "norm_ofBounded_le"],
 """1. `summable_smul_of_bounded`: `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero` (the `NonarchimedeanAddGroup M` instance comes
   from `IsUltrametricDist M`); the family tends to `0`: `tendsto_zero_iff_norm_tendsto_zero` and `squeeze_zero` with
   `‖f i • m i‖ ≤ ‖f i‖ * max C 0` (`norm_smul_le`, `hm.choose_spec`) and `((tendsto_cofinite f).norm.mul_const _)` (`norm_zero`, `zero_mul`).
2. `norm_tsum_smul_le`: `IsUltrametricDist.norm_tsum_le_of_forall_le (mul_nonneg (Real.iSup_nonneg fun _ ↦ norm_nonneg _) (norm_nonneg f)) fun i ↦ ?_`;
   `‖f i • m i‖ ≤ ‖f i‖ * ‖m i‖ ≤ ‖f‖ * ⨆ j, ‖m j‖` by `norm_smul_le`, `mul_le_mul (norm_apply_le f i) (le_ciSup ⟨C, …⟩ i) …`, `mul_comm`
   (`BddAbove (Set.range fun i ↦ ‖m i‖)` from `hm`: `⟨C, by rintro _ ⟨i, rfl⟩; exact hC i⟩`).
3. `ofBounded`'s `map_add'`: `simp_rw [add_apply, add_smul]; exact (summable_smul_of_bounded f m hm).tsum_add (summable_smul_of_bounded g m hm)`;
   `map_smul'`: `simp_rw [smul_apply, smul_eq_mul, mul_smul]; exact ((summable_smul_of_bounded f m hm).tsum_const_smul r).symm` (`RingHom.id_apply`).
4. `hasSum_ofBounded`: `(summable_smul_of_bounded f m hm).hasSum`.
5. `norm_ofBounded_le`: `opNorm_le_bound _ (Real.iSup_nonneg fun _ ↦ norm_nonneg _) (norm_ofBounded_apply_le m hm)`.""",
 "`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `tendsto_zero_iff_norm_tendsto_zero`, `squeeze_zero`, `Filter.Tendsto.mul_const`, `IsUltrametricDist.norm_tsum_le_of_forall_le`, `le_ciSup`, `Real.iSup_nonneg`, `Summable.tsum_add`, `Summable.tsum_const_smul`, `Summable.hasSum`, `ContinuousLinearMap.Ultra.opNorm_le_bound` [L1].",
 "[RM] §2.1.3 (\"bounded families `I → M` correspond to continuous linear maps `C₀(I, R) →L[R] M` by `m ↦ (f ↦ ∑' i, f i • m i)`, with `‖u‖ = sup ‖m i‖`\"); [Sch] l. 2905–2947 (\"for any map `x ↦ v_x` into a bounded subset of `V` there is a unique continuous linear map `f : c₀(X) → V` with `f(1_x) = v_x`\"); [Buz07] l. 280–283.",
 "`M` ultrametric and complete, `R` any normed ring (plan E26); the ring is explicit (`ofBounded R m hm`) because nothing else determines it.")

ticket("T008", "`ofBounded` on the coordinate vectors, its norm, and the converse", UN, "T007", "no", "lemmas", "L8.1–L8.3",
 ["ofBounded_single", "norm_ofBounded", "eq_ofBounded"],
 """1. `ofBounded_single`: `rw [ofBounded_apply, tsum_eq_single i (fun j hj ↦ by rw [single_apply_of_ne hj, zero_smul]), single_apply_self, one_smul]`.
2. `norm_ofBounded`: `le_antisymm (norm_ofBounded_le R m hm) (Real.iSup_le (fun i ↦ ?_) (opNorm_nonneg _))`; for each `i`:
   `have h := le_opNorm_of_bound (ofBounded R m hm) ⟨_, norm_ofBounded_apply_le m hm⟩ (single i 1)`, then
   `rw [ofBounded_single, norm_single, norm_one, mul_one] at h`.
3. `eq_ofBounded`: `ext_single fun i ↦ (ofBounded_single _ _ i).symm`.""",
 "`tsum_eq_single`, `zero_smul`, `one_smul`, `Real.iSup_le`, `ContinuousLinearMap.Ultra.{le_opNorm_of_bound, opNorm_nonneg}` [L1], `norm_single`, `norm_one`.",
 "[RM] §2.1.3 (\"with `‖u‖ = sup ‖m i‖`\"); [Sch] l. 2905–2947 (\"`f(1_x) = v_x`\"); [Buz07] l. 280–283 (\"there is a unique continuous map `φ : M → N` such that `φ(e_i) = n_i` for all `i`, and `|φ| = sup_{i∈I} |n_i|`\").",
 "`norm_ofBounded` needs `[NormOneClass R]`, no Tate hypothesis; `eq_ofBounded` needs `[IsTate R]` only through `exists_bound_single`.")

cleanup("CLEANUP-3", UN, "T008", "Final cleanup of `Universal.lean`")

# ---------------- Reindex ----------------
ticket("T009", "Reindexing along a bijection", RE, "CLEANUP-2", "yes (parallel with T006–T008)", "definition + lemma", "L9.1–L9.2",
 ["reindex", "reindex_single"],
 """1. The two `tendsto` fields: `(tendsto_cofinite f).comp e.symm.injective.tendsto_cofinite` and `(tendsto_cofinite g).comp e.injective.tendsto_cofinite`.
2. `map_add'`, `map_smul'`: `ext; rfl`. `left_inv`/`right_inv`: `fun f ↦ by ext; simp` (`Equiv.symm_apply_apply`, `Equiv.apply_symm_apply`).
3. `norm_map'`: `le_antisymm` with `norm_le_of_forall_le (norm_nonneg _)` in both directions and `norm_apply_le` (every value of
   `f ∘ e.symm` is a value of `f` and conversely), avoiding `iSup` lemmas.
4. `reindex_single`: `ext j; simp only [reindex_apply, coe_single, Pi.single_apply, Equiv.symm_apply_eq]`.""",
 "`Function.Injective.tendsto_cofinite`, `Equiv.symm_apply_apply`, `Equiv.apply_symm_apply`, `Equiv.symm_apply_eq`, `Pi.single_apply`.",
 "[RM] §2.1.4 (\"A bijection `I ≃ J` induces an isometry `C₀(I, R) ≃ₗᵢ[R] C₀(J, R)`\").",
 "Values in any normed module `E` over a normed ring (used with `E = R` and `E = M`).")

ticket("T010", "Disjoint unions and products of index sets", RE, "T009", "no", "definitions", "L10.1–L10.2",
 ["sumEquiv", "prodEquiv"],
 """1. `sumEquiv`: the two tendsto fields of `toFun` are `(tendsto_cofinite f).comp Sum.inl_injective.tendsto_cofinite` (resp. `inr`); for `invFun`,
   `Tendsto (Sum.elim p.1 p.2) cofinite (𝓝 0)`: by `Metric.tendsto_nhds` and `Filter.eventually_cofinite`, the bad set is
   `Sum.inl '' B₁ ∪ Sum.inr '' B₂` with `B₁, B₂` finite (`Set.Finite.image`, `Set.Finite.union`) — or `Filter.Tendsto.sum_elim`-type
   lemma if present. `map_add'`/`map_smul'`: `Prod.ext` + `ext; rfl`. Inverses: `ext x; cases x <;> rfl`. `norm_map'`: `Prod.norm_def`,
   then `le_antisymm` via `norm_le_of_forall_le`/`norm_apply_le` (a value at `inl i` is bounded by the first norm, …; `max_le`, `le_max_left`).
2. `prodEquiv`: inner tendsto `(tendsto_cofinite f).comp (Prod.mk.inj_left i).tendsto_cofinite`; outer tendsto is Layer 0's
   `Filter.Tendsto.iSup_norm_cofinite_left (tendsto_cofinite f)` after `norm_eq_iSup`; `invFun`'s tendsto is Layer 0's
   `tendsto_cofinite_prod_of_tendsto_iSup_norm` applied to `(tendsto_cofinite g).norm` rewritten with `norm_eq_iSup`.
   `map_add'`/`map_smul'`/inverses: `ext; rfl`. `norm_map'`: sandwich — `‖f (i, j)‖ ≤ ‖(prodEquiv f) i‖ ≤ ‖prodEquiv f‖` and
   `‖(prodEquiv f) i‖ ≤ ‖f‖` by `norm_le_of_forall_le`, hence equality by `le_antisymm`.""",
 "`Sum.inl_injective`, `Sum.inr_injective`, `Prod.mk.inj_left`, `Function.Injective.tendsto_cofinite`, `Metric.tendsto_nhds`, `Filter.eventually_cofinite`, `Set.Finite.image`, `Set.Finite.union`, `Prod.norm_def`, `Filter.Tendsto.iSup_norm_cofinite_left` [L0], `tendsto_cofinite_prod_of_tendsto_iSup_norm` [L0], `norm_eq_iSup`.",
 "[RM] §2.1.4 (\"`C₀(I ⊕ J, R) ≃ₗᵢ C₀(I, R) × C₀(J, R)` with the max norm; `C₀(I × J, R) ≃ₗᵢ C₀(I, C₀(J, R))`\").",
 "Mathlib's product norm is the max norm (`Prod.norm_def`), as the roadmap requires.")

ticket("T011", "Finite index sets, the block decomposition, and functoriality in the values (isometric case)", RE, "T010", "no", "definitions", "L11.1–L11.3",
 ["piEquiv", "congrRight"],
 """1. `piEquiv`: `invFun`'s tendsto: on a finite type `cofinite = ⊥` (`Filter.cofinite_eq_bot`), so `tendsto_bot`. `map_add'`/`map_smul'`: `rfl`;
   `left_inv`: `ext; rfl`; `right_inv`: `rfl`. `norm_map'`: `le_antisymm (norm_le_of_forall_le (norm_nonneg _) fun i ↦ norm_le_pi_norm _ i)
   ((pi_norm_le_iff_of_nonneg (norm_nonneg f)).2 (norm_apply_le f))`. `blockEquiv` and `setSumComplEquiv` are already terms.
2. `congrRight`: tendsto `((e.continuous.tendsto 0).comp (tendsto_cofinite f))` after `map_zero` (same for `e.symm`); `map_add'`/`map_smul'`:
   `ext; simp [map_add, map_smul]`; inverses: `ext; simp`; `norm_map'`: sandwich with `norm_le_of_forall_le`, `norm_apply_le` and `e.norm_map`.""",
 "`Filter.cofinite_eq_bot`, `tendsto_bot`, `norm_le_pi_norm`, `pi_norm_le_iff_of_nonneg`, `LinearIsometryEquiv.norm_map`, `LinearIsometryEquiv.continuous`, `map_zero`.",
 "[RM] §2.1.4 (\"for a finite `σ`, `C₀(σ × I, R) ≃ₗᵢ (σ → C₀(I, R))`, the block decomposition\"); §2.2.3 (stability under `C₀(J, −)`).",
 "`piEquiv` takes `[Fintype I]` because `Pi.normedAddCommGroup` does.")

cleanup("CLEANUP-4", RE, "T009, T010, T011", "Three proof tickets landed on `Reindex.lean`")

ticket("T012", "Functoriality in the values over a Tate ring: `compL`, `congrRightL`", RE, "CLEANUP-4", "no", "definitions", "L12.1–L12.2",
 ["compL", "congrRightL"],
 """1. `compL`: tendsto `((u.continuous.tendsto 0).comp (tendsto_cofinite f))` with `map_zero`; `map_add'`/`map_smul'`: `ext; simp`;
   the bound: `norm_le_of_forall_le (mul_nonneg (opNorm_nonneg u) (norm_nonneg f)) fun i ↦ (le_opNorm u (f i)).trans
   (mul_le_mul_of_nonneg_left (norm_apply_le f i) (opNorm_nonneg u))` (`[IsTate R]`).
2. `congrRightL`: the two inverse proofs `fun f ↦ by ext; simp [compL_apply, e.symm_apply_apply]` and `e.apply_symm_apply`.""",
 "`ContinuousLinearMap.Ultra.{le_opNorm, opNorm_nonneg}` [L1], `ContinuousLinearEquiv.{symm_apply_apply, apply_symm_apply}`, `ContinuousLinearEquiv.equivOfInverse`.",
 "[RM] §2.2.3 (stability of potential orthonormalisability and (Pr) under `C₀(J, −)`); [L1] §1.1.2 (continuous = bounded over a Tate ring, which is why `[IsTate R]` is needed — seam S3).",
 "`[NormOneClass R] [IsTate R]` written explicitly in the signatures (plan decision 10).")

cleanup("CLEANUP-5", RE, "T012", "Final cleanup of `Reindex.lean`")
