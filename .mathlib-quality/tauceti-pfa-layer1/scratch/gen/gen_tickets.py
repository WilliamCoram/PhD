#!/usr/bin/env python3
"""Generate tickets.md for the tauceti-pfa-layer1 board.
Statement blocks are copied verbatim from the skeleton files (never typed by hand)."""
import re, pathlib, datetime

ROOT = pathlib.Path("/Users/nkw24xru/Desktop/Lean/PhD")
CODE = ROOT / "PhD/TauCeti/Code/PadicFunctionalAnalysis/Operator"
OUT = ROOT / ".mathlib-quality/tauceti-pfa-layer1/tickets.md"
KW = r"(?:(?:noncomputable|scoped|protected)\s+)*(?:theorem|def|instance)\s+"

def extract(fname, key):
    lines = (CODE / fname).read_text().split("\n")
    if key.startswith("instance"):
        pat = re.compile(r"^(?:noncomputable\s+)?" + re.escape(key))
    else:
        pat = re.compile("^" + KW + re.escape(key) + r"(?=\s|$|\()")
    idx = next((i for i, l in enumerate(lines) if pat.match(l)), None)
    assert idx is not None, (fname, key)
    start = idx
    while start > 0 and (lines[start-1].startswith("@[") or lines[start-1].startswith("omit ")):
        start -= 1
    end = idx
    while end + 1 < len(lines) and lines[end+1].strip() != "":
        end += 1
    return "\n".join(lines[start:end+1])

T = []  # tickets in dependency order
def ticket(id, title, file, deps, parallel, typ, leaves, decls, sketch, lemmas, sources, generality, extra=""):
    T.append(dict(id=id, title=title, file=file, deps=deps, parallel=parallel, typ=typ, leaves=leaves,
                  decls=decls, sketch=sketch, lemmas=lemmas, sources=sources, generality=generality, extra=extra))
def cleanup(id, file, deps, note):
    T.append(dict(id=id, cleanup=True, file=file, deps=deps, note=note))

N = "Norm.lean"; B = "Banach.lean"; O = "OpenMapping.lean"; CG = "ClosedGraph.lean"; BS = "BanachSteinhaus.lean"
PI = "Pi.lean"; F = "Finite.lean"; E = "Examples.lean"

ticket("T001", "Order-theoretic lemmas of the operator norm", N, "none", "yes (no dependencies)", "lemmas",
 "L1.1–L1.7",
 ["bounds_bddBelow", "opNorm_nonneg", "opNorm_le_bound", "opNorm_zero", "le_opNorm_of_bound", "norm_id_le", "opNorm_neg"],
 """1. `bounds_bddBelow`: the bound set is bounded below by `0`: `⟨0, fun _ hc ↦ hc.1⟩`.
2. `opNorm_nonneg`: `Real.sInf_nonneg fun _ hc ↦ hc.1` (with `sInf ∅ = 0` no boundedness is needed).
3. `opNorm_le_bound`: `csInf_le bounds_bddBelow ⟨hC, h⟩`.
4. `opNorm_zero`: `le_antisymm (opNorm_le_bound _ le_rfl fun x ↦ by simp) (opNorm_nonneg _)`.
5. `le_opNorm_of_bound`: `obtain ⟨C, hC⟩ := h`. Case `‖x‖ = 0` (seminormed `M`!): `hC x` gives `‖u x‖ ≤ 0`, so both
   sides are `0` (`norm_nonneg`, `mul_zero`). Case `‖x‖ ≠ 0`: `‖u x‖ / ‖x‖` is a lower bound of the bound set
   (`div_le_iff₀ (lt_of_le_of_ne (norm_nonneg x) (Ne.symm hx))` on `hc.2 x`), and the set is nonempty (`max C 0`
   is in it: `le_max_right`, and `hC x` with `mul_le_mul_of_nonneg_right (le_max_left _ _)`), so
   `le_csInf ⟨_, _⟩ _ : ‖u x‖ / ‖x‖ ≤ ‖u‖`; finish with `div_mul_cancel₀`.
6. `norm_id_le`: `opNorm_le_bound _ zero_le_one fun x ↦ by simp` (`id_apply`, `one_mul`).
7. `opNorm_neg`: `simp only [norm_def, ContinuousLinearMap.neg_apply, norm_neg]`.""",
 "`Real.sInf_nonneg`, `csInf_le`, `le_csInf`, `div_le_iff₀`, `div_mul_cancel₀`, `norm_nonneg`, `le_max_left`, `le_max_right`, `mul_le_mul_of_nonneg_right`, `ContinuousLinearMap.id_apply`, `ContinuousLinearMap.neg_apply`, `norm_neg`.",
 "[Mathlib] `ContinuousLinearMap.{bounds_bddBelow, opNorm_nonneg, opNorm_le_bound, opNorm_zero, norm_id_le, opNorm_neg}` in `Mathlib/Analysis/Normed/Operator/Basic.lean:173–235` (their proofs transport verbatim); [RM] §1.1.1.",
 "Semiring scalars and seminormed modules — the formula needs nothing else (decision 3); `opNorm_neg` in a `Ring` section because `-u` needs it. `le_opNorm_of_bound` is stated with an existential bound so that it applies before any Tate hypothesis.")

ticket("T002", "The scaling trick for linear maps", N, "none", "yes (parallel with T001)", "lemma", "L1.8",
 ["norm_map_le_div_mul_of_forall_norm_le"],
 """1. `0 ≤ C`: from `h 0 (by simp [hε.le])` after `map_zero, norm_zero`.
2. Case `x = 0`: `simp` (both sides `0` after `map_zero`; the RHS is `_ * 0`).
3. Case `x ≠ 0`: `obtain ⟨n, ⟨h₁, h₂⟩, -⟩ := ϖ.existsUnique_zpow_norm_smul_mem_Ioc hε hx`, giving
   `ε * ‖ϖ‖ < ‖(ϖ.unit ^ n : R) • x‖ ≤ ε` (`Set.mem_Ioc`).
4. Bound on the scaled vector: `hfx := h _ h₂`; rewrite `f.map_smul` and `ϖ.norm_zpow_smul` to get
   `‖ϖ‖ ^ n * ‖f x‖ ≤ C`.
5. Rewrite `h₁` with `ϖ.norm_zpow_smul`: `ε * ‖ϖ‖ < ‖ϖ‖ ^ n * ‖x‖`. Put `t := ‖ϖ‖ ^ n > 0` (`zpow_pos ϖ.norm_pos`).
6. Conclude: `‖f x‖ ≤ C / t` (`le_div_iff₀`), and `C / t ≤ C / (ε * ‖ϖ‖) * ‖x‖` because
   `C * (ε * ‖ϖ‖) ≤ C * (t * ‖x‖)` (`mul_le_mul_of_nonneg_left h₁.le hC`), cleared with `div_le_iff₀`,
   `le_div_iff₀` (denominators `t`, `ε * ‖ϖ‖` positive) and `ring`-normalisation. Keep the identity explicit
   (readability over `nlinarith`).""",
 "`NormedRing.PseudoUniformizer.existsUnique_zpow_norm_smul_mem_Ioc` (L0), `NormedRing.PseudoUniformizer.norm_zpow_smul` (L0), `NormedRing.PseudoUniformizer.norm_pos` (L0), `LinearMap.map_smul`, `Set.mem_Ioc`, `zpow_pos`, `le_div_iff₀`, `div_le_iff₀`, `mul_le_mul_of_nonneg_left`, `map_zero`, `norm_zero`.",
 "[Sch] Prop 3.1 proof, `schneider.txt:541–546` (\"choose an integer `m` such that `|a|^{m+2} < ‖v‖ ≤ |a|^{m+1}`\"); [Buz07] `buzzard.txt:266–270`; [SRC] `01_OperatorNorm.le_opNorm` (the same computation inline).",
 "Explicit `ϖ` (the constant mentions `‖ϖ‖`), `[NormOneClass R]` for `0 < ‖ϖ‖`, a *linear* map `f` (continuity is irrelevant), closed ball `‖x‖ ≤ ε` so that `ε = 1` is literally the unit ball.")

ticket("T003", "Continuity is boundedness over a Tate normed ring", N, "T001, T002", "no", "lemmas", "L1.9–L1.12",
 ["exists_bound", "continuous_iff_exists_bound", "continuous_iff_exists_forall_norm_le", "le_opNorm"],
 """1. `exists_bound`: `obtain ⟨ϖ⟩ := NormedRing.IsTate.exists_pseudoUniformizer (R := R)`. Continuity at `0`:
   `obtain ⟨δ, hδ, H⟩ := Metric.continuousAt_iff.1 u.continuous.continuousAt 1 one_pos`; after `map_zero` and
   `dist_zero_right`, `H : ‖y‖ < δ → ‖u y‖ < 1`. Then `⟨1 / (δ / 2 * ‖(ϖ : R)‖), fun x ↦
   norm_map_le_div_mul_of_forall_norm_le ϖ (u : M →ₗ[R] N) (half_pos hδ) (fun y hy ↦ (H (by linarith)).le) x⟩`.
2. `continuous_iff_exists_bound`: `⟨fun hf ↦ exists_bound ⟨f, hf⟩, fun ⟨C, hC⟩ ↦ AddMonoidHomClass.continuous_of_bound f C hC⟩`
   (⚠ `LinearMap.continuous_of_bound` is not a name at this pin).
3. `continuous_iff_exists_forall_norm_le`: (⇒) from step 2 with `C' := max C 0`:
   `‖f x‖ ≤ C * ‖x‖ ≤ max C 0 * 1`. (⇐) `obtain ⟨ϖ⟩` again; `norm_map_le_div_mul_of_forall_norm_le ϖ f one_pos h`
   is a bound, then `AddMonoidHomClass.continuous_of_bound`.
4. `le_opNorm`: `le_opNorm_of_bound u (exists_bound u) x`.""",
 "`NormedRing.IsTate.exists_pseudoUniformizer`, `Metric.continuousAt_iff`, `Continuous.continuousAt`, `dist_zero_right`, `map_zero`, `half_pos`, `AddMonoidHomClass.continuous_of_bound`, `mul_le_of_le_one_right`, `le_max_left`, `le_max_right`.",
 "[JN] `jn.txt:522–523` (\"continuity of an `R`-linear map `φ` is equivalent to boundedness\"); [Sch] Prop 3.1 `schneider.txt:520–546`; [RM] §1.1.2.",
 "`[IsTate R]` as a Prop (existence only; no constant in the statements); `continuous_iff_*` stated for `LinearMap`s, `le_opNorm` for the continuous map. The unit-ball form uses the closed ball.")

cleanup("CLEANUP-1", N, "T003", "after the 3rd proof ticket on `Norm.lean` (cadence rule)")

ticket("T004", "The unit-ball comparison and the ratio supremum", N, "CLEANUP-1", "no", "lemmas", "L1.13–L1.15",
 ["opNorm_le_div_of_forall_norm_le", "norm_le_opNorm_of_norm_le_one", "opNorm_eq_iSup_div"],
 """1. `opNorm_le_div_of_forall_norm_le`: `hC : 0 ≤ C := by simpa using h 0 (by simp [hε.le])`; then
   `opNorm_le_bound u (div_nonneg hC (mul_pos hε ϖ.norm_pos).le) (norm_map_le_div_mul_of_forall_norm_le ϖ (u : M →ₗ[R] N) hε h)`.
2. `norm_le_opNorm_of_norm_le_one`: `(le_opNorm u x).trans (mul_le_of_le_one_right (opNorm_nonneg u) hx)`.
3. `opNorm_eq_iSup_div`: `hbdd : BddAbove (Set.range fun x ↦ ‖u x‖ / ‖x‖)` with bound `‖u‖`
   (`div_le_of_le_mul₀ (norm_nonneg _) (opNorm_nonneg _) (le_opNorm u x)`). `le_antisymm`:
   (≤) `opNorm_le_bound _ (Real.iSup_nonneg fun x ↦ div_nonneg (norm_nonneg _) (norm_nonneg _))`; for `x` with
   `‖x‖ = 0` both sides vanish (`le_opNorm` gives `‖u x‖ ≤ 0`); otherwise `‖u x‖ = ‖u x‖ / ‖x‖ * ‖x‖`
   (`div_mul_cancel₀`) and `le_ciSup hbdd x`. (≥) `ciSup_le fun x ↦ div_le_of_le_mul₀ … (le_opNorm u x)`
   (`Nonempty M` from `0`).""",
 "`div_nonneg`, `mul_pos`, `mul_le_of_le_one_right`, `div_le_of_le_mul₀`, `Real.iSup_nonneg`, `le_ciSup`, `ciSup_le`, `div_mul_cancel₀`, `norm_nonneg`.",
 "[Sch] Cor 3.2 and the warning `schneider.txt:538–550`; [JN] `jn.txt:523`; [RM] §1.1.2 corrected (erratum E9 in `plan.md`).",
 "The ratio supremum ranges over all `x` (the `x = 0` term is `0`); the two-sided unit-ball comparison is the honest replacement for the false `sup_{‖x‖ ≤ 1}` formula; explicit `ϖ` in the lemma whose constant mentions `‖ϖ‖`.")

cleanup("CLEANUP-2", N, "T004", "final per-file cleanup of `Norm.lean`")

ticket("T005", "The normed group of bounded operators", B, "CLEANUP-2", "no", "lemmas + instances", "L2.1–L2.5",
 ["opNorm_add_le", "opNorm_eq_zero_iff", "opNorm_add_le_max", "instIsUltrametricDist"],
 """1. `opNorm_add_le`: `opNorm_le_bound _ (add_nonneg (opNorm_nonneg u) (opNorm_nonneg v)) fun x ↦ by
   rw [ContinuousLinearMap.add_apply, add_mul]; exact norm_add_le_of_le (le_opNorm u x) (le_opNorm v x)`.
2. `opNorm_eq_zero_iff`: (→) `ext x; exact norm_le_zero_iff.1 (by simpa [h] using le_opNorm u x)`;
   (←) `rintro rfl; exact opNorm_zero`.
3. Check that `instNormedAddCommGroup` (already complete in the skeleton) still elaborates after steps 1–2 are
   proved; do not change its shape (`toNorm` must stay `instNorm`, decision 2).
4. `opNorm_add_le_max`: `opNorm_le_bound _ (le_max_of_le_left (opNorm_nonneg u)) fun x ↦ by
   rw [ContinuousLinearMap.add_apply, max_mul_of_nonneg _ _ (norm_nonneg x)];
   exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (le_opNorm u x) (le_opNorm v x))`.
5. `instIsUltrametricDist`: `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm opNorm_add_le_max`.""",
 "`norm_add_le_of_le`, `ContinuousLinearMap.add_apply`, `add_mul`, `norm_le_zero_iff`, `IsUltrametricDist.norm_add_le_max`, `max_le_max`, `max_mul_of_nonneg`, `le_max_of_le_left`, `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`.",
 "[Bel] `bellaiche.txt:1975–1981`; [RM] §1.1.3; [Mathlib] `ContinuousLinearMap.opNorm_add_le`, `opNorm_zero_iff`.",
 "Ultrametricity of `M →L[R] N` needs only ultrametric `N`; the normed-group instance needs `[NormedAddCommGroup N]` (separation) and `[IsTate R]` (through `le_opNorm`).")

ticket("T006", "Completeness of the operator space", B, "T005", "no", "instance", "L2.6",
 ["instCompleteSpace"],
 """Transcribe [SRC] `01_OperatorNorm.exists_lim_of_cauchySeq` (sorry-free) into `Metric.complete_of_cauchySeq_tendsto`:
1. `refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_`; `Metric.cauchySeq_iff.1 hu`.
2. Pointwise Cauchy: `dist (u m x) (u n x) = ‖(u m - u n) x‖ ≤ ‖u m - u n‖ * ‖x‖` (`dist_eq_norm`,
   `ContinuousLinearMap.sub_apply`, `le_opNorm`); use `ε / (‖x‖ + 1)`.
3. `choose v₀ hv₀ using fun x ↦ cauchySeq_tendsto_of_complete (hptwise x)`; additivity and `R`-linearity of `v₀`
   by `tendsto_nhds_unique` against `(hv₀ x).add (hv₀ y)` and `(hv₀ x).const_smul c` (`map_add`, `map_smul`).
4. Bound: `obtain ⟨N₀, hN₀⟩ := hu' 1 one_pos`; `‖v₀ x‖ ≤ (‖u N₀‖ + 1) * ‖x‖` by `le_of_tendsto (hv₀ x).norm`
   and `Filter.eventually_atTop` (`‖u n x‖ ≤ ‖u n - u N₀‖ * ‖x‖ + ‖u N₀‖ * ‖x‖`).
5. `v := LinearMap.mkContinuous { toFun := v₀, map_add' := _, map_smul' := _ } _ hbound`.
6. `Metric.tendsto_atTop`: for `ε`, take `N₁` from the Cauchy condition at `ε / 2`; `dist (u n) v = ‖u n - v‖ ≤ ε / 2`
   by `opNorm_le_bound` and, for each `x`, `le_of_tendsto` on `fun m ↦ ‖u n x - u m x‖ → ‖(u n - v) x‖`.""",
 "`Metric.complete_of_cauchySeq_tendsto`, `Metric.cauchySeq_iff`, `cauchySeq_tendsto_of_complete`, `tendsto_nhds_unique`, `Filter.Tendsto.add`, `Filter.Tendsto.const_smul`, `Filter.Tendsto.sub`, `Filter.Tendsto.norm`, `le_of_tendsto`, `Filter.eventually_atTop`, `LinearMap.mkContinuous`, `Metric.tendsto_atTop`, `dist_eq_norm`, `ContinuousLinearMap.sub_apply`, `map_add`, `map_smul`.",
 "[Sch] Prop 3.3 `schneider.txt:551–588`; [Bel] `bellaiche.txt:1981`; [Lud] `ludwig.txt:218–222`; [SRC] `01_OperatorNorm.exists_lim_of_cauchySeq`.",
 "`[CompleteSpace N]` only; completeness of `M` is not used and not assumed.")

ticket("T007", "The Banach ring of endomorphisms and the scalars", B, "T006", "no", "lemmas + instances", "L2.7–L2.12",
 ["opNorm_comp_le", "norm_id", "opNorm_smul_le", "instIsBoundedSMul", "opNorm_smul_of_isMultiplicative"],
 """1. `opNorm_comp_le`: `opNorm_le_bound _ (mul_nonneg (opNorm_nonneg v) (opNorm_nonneg u)) fun x ↦ by
   rw [ContinuousLinearMap.comp_apply, mul_assoc];
   exact (le_opNorm v _).trans (mul_le_mul_of_nonneg_left (le_opNorm u x) (opNorm_nonneg v))`.
2. `norm_id`: `le_antisymm norm_id_le`; `obtain ⟨x, hx⟩ := exists_ne (0 : M)`;
   `have h := le_opNorm (ContinuousLinearMap.id R M) x`; `rw [ContinuousLinearMap.id_apply] at h`;
   `exact le_of_mul_le_mul_right (by simpa using h) (norm_pos_iff.2 hx)`.
3. Check `instNormedRing` / `instNormOneClass` (complete in the skeleton) still elaborate.
4. `opNorm_smul_le`: `opNorm_le_bound _ (mul_nonneg (norm_nonneg a) (opNorm_nonneg u)) fun x ↦ by
   rw [ContinuousLinearMap.smul_apply, mul_assoc];
   exact (norm_smul_le a _).trans (mul_le_mul_of_nonneg_left (le_opNorm u x) (norm_nonneg a))`.
5. `instIsBoundedSMul`: `IsBoundedSMul.of_norm_smul_le opNorm_smul_le`.
6. `opNorm_smul_of_isMultiplicative`: `refine le_antisymm (opNorm_smul_le _ _) ?_`;
   `have h := opNorm_smul_le ((a⁻¹ : Rˣ) : R) ((a : R) • u)`; `rw [smul_smul, Units.inv_mul, one_smul, ha.norm_inv] at h`;
   `rwa [le_inv_mul_iff₀ ha.norm_pos] at h`.""",
 "`ContinuousLinearMap.comp_apply`, `ContinuousLinearMap.smul_apply`, `ContinuousLinearMap.id_apply`, `norm_smul_le`, `exists_ne`, `le_of_mul_le_mul_right`, `norm_pos_iff`, `IsBoundedSMul.of_norm_smul_le`, `smul_smul`, `Units.inv_mul`, `one_smul`, `le_inv_mul_iff₀`; Layer 0: `NormedRing.IsMultiplicative.norm_inv`, `NormedRing.IsMultiplicative.norm_pos`.",
 "[Bel] `bellaiche.txt:1978` (\"`|φ'φ| ≤ |φ'||φ|`\"); [RM] §1.1.3 (E11: equality for multiplicative *units*); [Mathlib] `opNorm_comp_le`, `norm_id`, `opNorm_smul_le`.",
 "The scalar statements live in a `[NormedCommRing R]` section because Mathlib's `ContinuousLinearMap.module` needs `SMulCommClass R R N` (inventory). `norm_id` takes `[Nontrivial M]`, the normed-group reading of Mathlib's `NontrivialTopology`.")

cleanup("CLEANUP-3", B, "T007", "after the 3rd proof ticket on `Banach.lean`")

ticket("T008", "Sums of operators", B, "CLEANUP-3", "no", "lemmas", "L2.13–L2.15",
 ["summable_of_tendsto_cofinite_zero", "hasSum_apply", "tsum_apply"],
 """1. `summable_of_tendsto_cofinite_zero`: `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hu`; the
   instances `NonarchimedeanAddGroup (M →L[R] N)` (via `IsUltrametricDist.nonarchimedeanAddGroup` from T005) and
   `CompleteSpace` (T006) must be found by unification — if not, `haveI` them.
2. `hasSum_apply`: `let e : (M →L[R] N) →+ N := AddMonoidHom.mk' (fun v ↦ v x) fun _ _ ↦ rfl`;
   `have he : Continuous e := AddMonoidHomClass.continuous_of_bound e ‖x‖ fun v ↦ by rw [mul_comm]; exact le_opNorm v x`;
   `exact hu.map e he`.
3. `tsum_apply`: `(hasSum_apply hu.hasSum x).tsum_eq.symm`.""",
 "`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, `IsUltrametricDist.nonarchimedeanAddGroup`, `AddMonoidHom.mk'`, `AddMonoidHomClass.continuous_of_bound`, `HasSum.map`, `Summable.hasSum`, `HasSum.tsum_eq`.",
 "[RM] §1.1.4 (\"`∑' uᵢ` converges in operator norm and pointwise, and `‖∑' uᵢ‖ ≤ sup ‖uᵢ‖`\" — the bound is Mathlib's `IsUltrametricDist.norm_tsum_le` on the ultrametric instance, no restatement).",
 "`hasSum_apply` needs neither completeness nor ultrametricity (only `le_opNorm`); if the linter flags the unused section variables, `omit` them at cleanup.")

ticket("T009", "The Neumann series in the endomorphism ring", B, "T008", "no", "lemmas", "L2.16–L2.19",
 ["isUnit_of_norm_one_sub_lt_one", "norm_eq_one_of_norm_one_sub_lt_one", "norm_inv_eq_one_of_norm_one_sub_lt_one", "isOpen_setOf_isUnit"],
 """All four are Mathlib's / Layer 0's facts about a complete normed ring, applied to `M →L[R] M` with the scoped
instances (`instNormedRing`, `instCompleteSpace` with `N := M`, `instIsUltrametricDist`, `instNormOneClass`).
`HasSummableGeomSeries (M →L[R] M)` comes from `CompleteSpace`; `haveI` it if unification stalls.
1. `isUnit_of_norm_one_sub_lt_one`: `⟨Units.oneSub (1 - u) hu, by rw [Units.val_oneSub, sub_sub_cancel]⟩`.
2. `norm_eq_one_of_norm_one_sub_lt_one`: `have h := NormedRing.norm_one_sub_of_norm_lt_one hu` (in the ring
   `M →L[R] M`; needs `NormOneClass` ⇐ `Nontrivial M`, `IsUltrametricDist` ⇐ ultrametric `M`); `rwa [sub_sub_cancel] at h`.
3. `norm_inv_eq_one_of_norm_one_sub_lt_one`: `have hval : ((u⁻¹ : (M →L[R] M)ˣ) : M →L[R] M) = ((Units.oneSub (1 - u) hu)⁻¹ : (M →L[R] M)ˣ) :=
   Units.inv_unique (by rw [Units.val_oneSub, sub_sub_cancel])`; the inverse of `Units.oneSub t h` is `∑' n, t ^ n`
   by definition (`rfl`; check with `#print Units.oneSub`); finish with `NormedRing.norm_tsum_geometric hu`.
4. `isOpen_setOf_isUnit`: `Units.isOpen`.""",
 "`Units.oneSub`, `Units.val_oneSub`, `Units.inv_unique`, `Units.isOpen`, `sub_sub_cancel`; Layer 0: `NormedRing.norm_one_sub_of_norm_lt_one`, `NormedRing.norm_tsum_geometric`.",
 "[RM] §1.1.5; [BGR] 1.2.4/4–5 `bgr-3.7.md:135–139`; Layer 0 §0.2.3.",
 "`[IsUltrametricDist M] [CompleteSpace M]` for the Banach ring; `[Nontrivial M]` exactly where `‖1‖ = 1` is used (the two norm equalities), not for `IsUnit` or openness.")

ticket("T010", "Agreement with Mathlib at the instance level", B, "T009", "no", "theorem", "L2.20",
 ["instNormedAddCommGroup_eq"],
 """1. Prove a private extensionality lemma (Mathlib has `MetricSpace.ext` but no `NormedAddCommGroup.ext` at this
   pin): for `i j : NormedAddCommGroup E`, if `i.toAddCommGroup = j.toAddCommGroup`, `∀ x, @norm E i.toNorm x =
   @norm E j.toNorm x` and `∀ x y, @dist E i.toDist x y = @dist E j.toDist x y`, then `i = j`:
   `cases i; cases j`, turn the three hypotheses into equalities of the `toNorm` (`funext`), `toAddCommGroup`
   and `toMetricSpace` (`MetricSpace.ext (funext₂ h)`) fields, `subst`, `rfl`.
2. Apply it: the additive groups are both `ContinuousLinearMap.addCommGroup` (`rfl`); the norms agree by
   `norm_eq_opNorm` (`rfl`); the distances agree because both instances satisfy `dist x y = ‖x - y‖`
   (`NormedAddCommGroup.dist_eq` on each side, with the norms already identified).
3. Mathlib's side carries the strong-topology uniformity through `replaceUniformity`
   (`Mathlib/Analysis/Normed/Operator/Basic.lean:379–383`); `MetricSpace.ext` only needs `dist`, so this is
   invisible to the proof.""",
 "`MetricSpace.ext`, `funext`, `NormedAddCommGroup.dist_eq`, `norm_eq_opNorm` (T001-level `rfl`).",
 "[RM] §1.1.6; [Mathlib] `ContinuousLinearMap.toNormedAddCommGroup` (`Operator/NormedSpace.lean:166`).",
 "Field scalars only (`NontriviallyNormedField K`, `NormedSpace`); the scoped instance's `IsTate K` is Layer 0's instance for fields.")

cleanup("CLEANUP-4", B, "T010", "final per-file cleanup of `Banach.lean` (also the 3rd proof ticket since CLEANUP-3)")

ticket("T011", "The Baire step of the open mapping theorem", O, "CLEANUP-2", "yes (with G2, G5, G6)", "lemma", "L3.1",
 ["exists_approx_preimage_norm_le"],
 """Transcribe `Mathlib/Analysis/Normed/Operator/Banach.lean:92–152` (`exists_approx_preimage_norm_le`) with
Layer 0's shell lemma in place of `rescale_to_shell`; [SRC] `01_OperatorNorm.exists_approx_preimage_norm_le` is
a sorry-free transcription to copy from.
1. `A : ⋃ n : ℕ, closure (u '' ball 0 n) = univ` from surjectivity and `exists_nat_gt ‖x‖`.
2. `nonempty_interior_of_iUnion_of_closed (fun n ↦ isClosed_closure) A` gives `n, a` with
   `a ∈ interior (closure (u '' ball 0 n))`; `mem_interior_iff_mem_nhds`, `Metric.mem_nhds_iff` give `ε > 0` with
   `ball a ε ⊆ closure (u '' ball 0 n)`.
3. `obtain ⟨ϖ⟩ := IsTate.exists_pseudoUniformizer`; `refine ⟨4 * n / (ε * ‖ϖ‖), by positivity, fun y ↦ ?_⟩`;
   `rcases eq_or_ne y 0 with rfl | hy`, the zero case by `simp`.
4. `obtain ⟨j, ⟨hj₁, hj₂⟩, -⟩ := ϖ.existsUnique_zpow_norm_smul_mem_Ioc (half_pos εpos) hy`; set
   `d := (ϖ.unit ^ j : R)`, `δ := ‖d • y‖ / 4 > 0`.
5. `a + d • y ∈ ball a ε` (`hj₂` and `half_lt_self`) and `a ∈ ball a ε`; `Metric.mem_closure_iff` gives
   `x₁ x₂ ∈ ball 0 n` with `dist (u x₁) (a + d • y) < δ`, `dist (u x₂) a < δ`.
6. `I : ‖u (x₁ - x₂) - d • y‖ ≤ 2 * δ` (`map_sub`, `abel`, `norm_sub_le`).
7. `x := (ϖ.unit ^ (-j) : R) • (x₁ - x₂)`: `J : ‖u x - y‖ ≤ 1 / 2 * ‖y‖` using `(ϖ.unit ^ (-j)) • d • y = y`
   (`smul_smul`, `← Units.val_mul`, `zpow_neg`, `inv_mul_cancel`), `ϖ.norm_zpow_smul`, and
   `‖ϖ‖ ^ (-j) * ‖d • y‖ = ‖y‖`; `K : ‖x‖ ≤ 4 * n / (ε * ‖ϖ‖) * ‖y‖` from `‖x₁ - x₂‖ ≤ 2 * n` and
   `‖ϖ‖ ^ (-j) * (ε * ‖ϖ‖) ≤ 2 * ‖y‖` (from `hj₁`). Keep the real-number identities explicit.""",
 "`nonempty_interior_of_iUnion_of_closed`, `isClosed_closure`, `mem_interior_iff_mem_nhds`, `Metric.mem_nhds_iff`, `Metric.mem_closure_iff`, `Metric.mem_ball`, `dist_eq_norm`, `exists_nat_gt`, `Set.mem_iUnion`, `subset_closure`, `half_pos`, `half_lt_self`, `norm_sub_le`, `smul_smul`, `Units.val_mul`, `zpow_neg`, `inv_mul_cancel`; Layer 0: `existsUnique_zpow_norm_smul_mem_Ioc`, `norm_zpow_smul`, `norm_pos`.",
 "[Mathlib] docstring of `ContinuousLinearMap.exists_approx_preimage_norm_le`; [Bel] `bellaiche.txt:1983–1989`; [SRC] `01_OperatorNorm.exists_approx_preimage_norm_le`.",
 "`[CompleteSpace N]` only (Baire on `N`); no `CompleteSpace M`, no `CompleteSpace R`, no ultrametricity (E16).")

cleanup("CLEANUP-ALL-1", "project", "T011, CLEANUP-2, CLEANUP-4", "pre-milestone sweep (`/cleanup-all` on the Layer 1 files so far) before M1")

ticket("T012", "The quantitative open mapping theorem (MILESTONE M1)", O, "CLEANUP-ALL-1", "no", "theorems", "L3.2–L3.4",
 ["exists_preimage_norm_le", "isOpenMap", "isQuotientMap"],
 """1. `exists_preimage_norm_le`: transcribe `Mathlib/Analysis/Normed/Operator/Banach.lean:162–225` verbatim
   (also [SRC] `exists_preimage_norm_le`): `obtain ⟨C, C0, hC⟩ := exists_approx_preimage_norm_le u hu`;
   `choose g hg using hC`; `h y := y - u (g y)` with `‖h y‖ ≤ 1 / 2 * ‖y‖`; `refine ⟨2 * C + 1, by linarith, fun y ↦ ?_⟩`;
   `‖h^[n] y‖ ≤ (1 / 2) ^ n * ‖y‖` by induction (`Function.iterate_succ'`); `u_n := g (h^[n] y)` with
   `‖u_n‖ ≤ (1 / 2) ^ n * (C * ‖y‖)`; `Summable (‖u_n‖)` by `Summable.of_nonneg_of_le` and
   `summable_geometric_of_lt_one`; `x := ∑' n, u_n`; `‖x‖ ≤ (2 * C + 1) * ‖y‖` via `norm_tsum_le_tsum_norm`,
   `Summable.tsum_le_tsum`, `tsum_mul_right`, `tsum_geometric_two`; `u (∑ i < n, u_i) = y - h^[n] y` by induction
   (`Finset.sum_range_succ`, `Function.iterate_succ_apply'`); pass to the limit with `HasSum.tendsto_sum_nat`,
   `tendsto_nhds_unique`, `squeeze_zero`, `tendsto_pow_atTop_nhds_zero_of_lt_one`.
2. `isOpenMap`: transcribe `Banach.lean:229–248`: `Metric.isOpen_iff`; for `y = u x ∈ u '' s` and the
   `ε`-ball around `x` inside `s`, the ball of radius `ε / C` around `y` is in the image (preimage `w` of
   `z - y` with `‖w‖ ≤ C * ‖z - y‖ < ε`).
3. `isQuotientMap`: `(Ultra.isOpenMap u hu).isQuotientMap u.continuous hu`.""",
 "`Function.iterate_succ'`, `Function.iterate_succ_apply'`, `Summable.of_nonneg_of_le`, `summable_geometric_of_lt_one`, `summable_geometric_two`, `Summable.of_norm`, `norm_tsum_le_tsum_norm`, `Summable.tsum_le_tsum`, `tsum_mul_right`, `tsum_geometric_two`, `Finset.sum_range_succ`, `HasSum.tendsto_sum_nat`, `tendsto_nhds_unique`, `squeeze_zero`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `tendsto_iff_norm_sub_tendsto_zero`, `Metric.isOpen_iff`, `Metric.mem_ball`, `dist_eq_norm`, `mul_div_cancel₀`, `IsOpenMap.isQuotientMap`.",
 "[Bel] `bellaiche.txt:1983–1989`; [JN] `jn.txt:525`; [Lud] `ludwig.txt:226–228`; [Sch] Prop 8.6 `schneider.txt:2357–2372`; [Mathlib] `ContinuousLinearMap.{exists_preimage_norm_le, isOpenMap, isQuotientMap}`; [RM] §1.2.1 (seam S1 recorded in the module docstring).",
 "`[CompleteSpace M] [CompleteSpace N]`, nothing on `R` beyond Tate; `isOpenMap` is `protected` as in Mathlib.")

ticket("T013", "Bijective operators are isomorphisms", O, "T012", "no", "lemma + defs", "L3.5–L3.6",
 ["continuous_symm", "toContinuousLinearEquivOfContinuous", "continuousLinearEquivOfBijective"],
 """1. `continuous_symm`: `let u : M →L[R] N := ⟨e, he⟩`; `obtain ⟨C, -, hC⟩ := exists_preimage_norm_le u e.surjective`;
   `refine AddMonoidHomClass.continuous_of_bound e.symm C fun y ↦ ?_`; `obtain ⟨x, hx, hle⟩ := hC y`;
   `e.symm y = x` because `e x = y` (`e.symm_apply_apply`, `hx`, or `e.injective`); `rwa` and conclude.
2. The two `def`s and their `coe` lemmas are complete; check they elaborate against the proved `continuous_symm`.""",
 "`AddMonoidHomClass.continuous_of_bound`, `LinearEquiv.surjective`, `LinearEquiv.injective`, `LinearEquiv.symm_apply_apply`, `LinearEquiv.apply_symm_apply`.",
 "[Sch] Cor 8.7 `schneider.txt:2373–2375`; [Mathlib] `LinearEquiv.continuous_symm`, `LinearEquiv.toContinuousLinearEquivOfContinuous`, `ContinuousLinearEquiv.ofBijective`; [RM] §1.2.2.",
 "Both modules Banach; `continuousLinearEquivOfBijective` takes `Function.Bijective u` (Mathlib's takes `ker = ⊥`, `range = ⊤`; the `Bijective` form is what `ClosedGraph.lean` and `Finite.lean` have).")

cleanup("CLEANUP-5", O, "T013", "after the 3rd proof ticket on `OpenMapping.lean`")

ticket("T014", "Strictness of operators with closed range", O, "CLEANUP-5", "no", "lemmas + def", "L3.7–L3.9",
 ["norm_quotKerEquivRange_apply_le", "exists_norm_quotKerEquivRange_symm_le", "quotKerEquivRangeL"],
 """1. `norm_quotKerEquivRange_apply_le`: `refine le_of_forall_pos_lt_add fun ε hε ↦ ?_`;
   `obtain ⟨m, rfl, hm⟩ := Submodule.Quotient.norm_mk_lt x (div_pos hε …)` (choose the slack so that
   `‖u‖ * (‖x‖ + slack) < ‖u‖ * ‖x‖ + ε`; if `‖u‖ = 0` handle directly); rewrite
   `LinearMap.quotKerEquivRange_apply_mk`; `(le_opNorm u m).trans` and `mul_lt_mul_of_pos_left`.
2. `exists_norm_quotKerEquivRange_symm_le`: `haveI : IsClosed (LinearMap.ker (u : M →ₗ[R] N) : Set M) := u.isClosed_ker`
   (so `Submodule.Quotient.normedAddCommGroup`, `Submodule.Quotient.completeSpace`,
   `Submodule.Quotient.instIsBoundedSMul` apply — the last needs `NormedCommRing R`);
   `haveI := hu.completeSpace_coe`; `ū : (M ⧸ ker u) →L[R] range u :=
   LinearMap.mkContinuous (LinearMap.quotKerEquivRange (u : M →ₗ[R] N)).toLinearMap ‖u‖ (by simpa using norm_quotKerEquivRange_apply_le u)`
   (the norm of a point of `range u` is the norm in `N`: `Submodule.coe_norm`);
   `obtain ⟨C, -, hC⟩ := exists_preimage_norm_le ū (LinearEquiv.surjective _)`; identify the preimage of `y` with
   `(quotKerEquivRange u).symm y` by injectivity; `⟨C, …⟩`.
3. `quotKerEquivRangeL`: the remaining `sorry` is `Continuous (quotKerEquivRange u)`:
   `AddMonoidHomClass.continuous_of_bound _ ‖u‖ (by simpa using norm_quotKerEquivRange_apply_le u)`.""",
 "`le_of_forall_pos_lt_add`, `Submodule.Quotient.norm_mk_lt`, `LinearMap.quotKerEquivRange_apply_mk`, `mul_lt_mul_of_pos_left`, `ContinuousLinearMap.isClosed_ker`, `IsClosed.completeSpace_coe`, `Submodule.Quotient.normedAddCommGroup`, `Submodule.Quotient.completeSpace`, `Submodule.Quotient.instIsBoundedSMul`, `LinearMap.mkContinuous`, `LinearEquiv.surjective`, `LinearEquiv.injective`, `Submodule.coe_norm`, `AddMonoidHomClass.continuous_of_bound`.",
 "[BGR] 3.7.3/4 `bgr-3.7.md:68`; [Sch] Prop 8.3 `schneider.txt:2281`; [RM] §1.2.2.",
 "`[NormedCommRing R]` because Mathlib's `IsBoundedSMul` on quotients needs commutative scalars (inventory); the first bound needs no completeness. `quotKerEquivRangeL` is the `def` that `/beastmode` must not restate.")

cleanup("CLEANUP-6", O, "T014", "final per-file cleanup of `OpenMapping.lean`")

ticket("T015", "The closed graph theorem", CG, "CLEANUP-6", "no", "theorems", "L4.1–L4.2",
 ["continuous_of_isClosed_graph", "continuous_of_seq_closed_graph"],
 """Transcribe `Mathlib/Analysis/Normed/Operator/Banach.lean:532–560` with the board's equivalence constructor.
1. `continuous_of_isClosed_graph`: `let : CompleteSpace f.graph := completeSpace_coe_iff_isComplete.mpr hf.isComplete`;
   `φ₀ : M →ₗ[R] M × N := LinearMap.id.prod f` with `Function.LeftInverse Prod.fst φ₀` (`fun x ↦ rfl`);
   `φ : M ≃ₗ[R] f.graph := (LinearEquiv.ofLeftInverse this).trans (LinearEquiv.ofEq _ _ f.graph_eq_range_prod.symm)`;
   `ψ : f.graph ≃L[R] M := toContinuousLinearEquivOfContinuous φ.symm continuous_subtype_val.fst`;
   `exact (continuous_subtype_val.comp ψ.symm.continuous).snd`. Instances: `IsBoundedSMul R (M × N)` (Mathlib),
   `IsBoundedSMul R f.graph` (Layer 0 `Submodule.instIsBoundedSMul`), `CompleteSpace (M × N)`.
2. `continuous_of_seq_closed_graph`: `refine continuous_of_isClosed_graph f (IsSeqClosed.isClosed ?_)`;
   `rintro φ ⟨x, y⟩ hφg hφ`; apply `hf (Prod.fst ∘ φ) x y ((continuous_fst.tendsto _).comp hφ)`; the second
   tendsto is `(continuous_snd.tendsto _).comp hφ` after `f ∘ Prod.fst ∘ φ = Prod.snd ∘ φ` (`hφg n`).""",
 "`completeSpace_coe_iff_isComplete`, `IsClosed.isComplete`, `LinearMap.id`, `LinearMap.prod`, `LinearEquiv.ofLeftInverse`, `LinearEquiv.ofEq`, `LinearMap.graph_eq_range_prod`, `continuous_subtype_val`, `Continuous.fst`, `Continuous.snd`, `IsSeqClosed.isClosed`, `continuous_fst`, `continuous_snd`, `Filter.Tendsto.comp`; Layer 0: `Submodule.instIsBoundedSMul`.",
 "[Sch] Prop 8.5 `schneider.txt:2322–2325`; [Mathlib] `LinearMap.continuous_of_isClosed_graph`, `continuous_of_seq_closed_graph`; [RM] §1.2.3.",
 "Both modules Banach; no ultrametricity, no `CompleteSpace R` (E16).")

cleanup("CLEANUP-7", CG, "T015", "final per-file cleanup of `ClosedGraph.lean`")

ticket("T016", "Banach–Steinhaus", BS, "CLEANUP-2", "yes (with G2, G3, G6)", "theorem", "L5.1",
 ["banach_steinhaus"],
 """1. `obtain ⟨ϖ⟩ := IsTate.exists_pseudoUniformizer (R := R)`.
2. `A n := ⋂ i, {x : M | ‖u i x‖ ≤ n}`; closed: `isClosed_iInter fun i ↦ isClosed_le (continuous_norm.comp (u i).continuous) continuous_const`;
   covering: for `x`, `obtain ⟨C, hC⟩ := h x`, `obtain ⟨n, hn⟩ := exists_nat_ge C`, so `x ∈ A n`.
3. `nonempty_interior_of_iUnion_of_closed` gives `n`, `x₀`, and (`mem_interior_iff_mem_nhds`, `Metric.mem_nhds_iff`)
   `ε > 0` with `ball x₀ ε ⊆ A n`.
4. For `‖y‖ ≤ ε / 2`: `x₀ + y ∈ ball x₀ ε` and `x₀ ∈ ball x₀ ε`, so `‖u i y‖ = ‖u i (x₀ + y) - u i x₀‖ ≤ n + n`
   (`map_add`, `add_sub_cancel_left`, `norm_sub_le`).
5. `refine ⟨2 * n / (ε / 2 * ‖(ϖ : R)‖), fun i ↦ opNorm_le_div_of_forall_norm_le ϖ (u i) (half_pos hε) fun y hy ↦ ?_⟩`
   with step 4.""",
 "`isClosed_iInter`, `isClosed_le`, `continuous_norm`, `continuous_const`, `exists_nat_ge`, `nonempty_interior_of_iUnion_of_closed`, `mem_interior_iff_mem_nhds`, `Metric.mem_nhds_iff`, `Metric.mem_ball`, `dist_eq_norm`, `map_add`, `add_sub_cancel_left`, `norm_sub_le`, `Set.mem_iInter`, `Set.mem_iUnion`.",
 "[Sch] Prop 6.15 `schneider.txt:1683–1690` with Example 2 `schneider.txt:1715–1718` (Baire); [Mathlib] `banach_steinhaus` (statement; its current proof goes through barrelled spaces); [RM] §1.2.4.",
 "`[CompleteSpace M]` only; `N` any normed module; no ultrametricity (it would only replace `2n` by `n`).")

ticket("T017", "Pointwise limits of bounded operators are bounded", BS, "T016", "no", "theorem", "L5.2",
 ["continuous_of_tendsto"],
 """1. Pointwise bounded: for each `x`, `(h x).norm.bddAbove_range` gives `C x` with `∀ n, ‖u n x‖ ≤ C x`
   (`Filter.Tendsto.bddAbove_range`, `mem_upperBounds`, `Set.mem_range_self`).
2. `obtain ⟨C, hC⟩ := banach_steinhaus u (fun x ↦ ⟨_, …⟩)`.
3. `‖f x‖ ≤ C * ‖x‖`: `le_of_tendsto (h x).norm (Filter.Eventually.of_forall fun n ↦ (le_opNorm (u n) x).trans
   (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg x)))`.
4. `AddMonoidHomClass.continuous_of_bound f C`.""",
 "`Filter.Tendsto.bddAbove_range`, `Filter.Tendsto.norm`, `le_of_tendsto`, `Filter.Eventually.of_forall`, `mul_le_mul_of_nonneg_right`, `AddMonoidHomClass.continuous_of_bound`, `mem_upperBounds`, `Set.mem_range_self`.",
 "[RM] §1.2.4 (\"a pointwise limit of continuous linear maps from a Banach module is continuous\"); [Mathlib] `continuousLinearMapOfTendsto`.",
 "Sequences (`atTop` on `ℕ`): a net convergent along a general filter need not be pointwise bounded; the limit `f` is given as a linear map, so the statement is one conclusion (continuity).")

cleanup("CLEANUP-8", BS, "T017", "final per-file cleanup of `BanachSteinhaus.lean`")

ticket("T018", "The bound for maps out of a finite free module", PI, "CLEANUP-2", "yes (with G2, G3, G5)", "lemmas", "L6.1–L6.2",
 ["norm_map_le_iSup_mul", "continuous_pi"],
 """1. `norm_map_le_iSup_mul`: write `x = ∑ i, x i • Pi.single i 1` (`Finset.univ_sum_single x` and
   `Pi.single_smul`/`smul_eq_mul`/`mul_one`, or `pi_eq_sum_univ` directly); `rw` it on the left only (`conv_lhs`),
   then `map_sum`, `map_smul`. Apply `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` with
   `C := (⨆ i, ‖f (Pi.single i 1)‖) * ‖x‖` (`mul_nonneg (Real.iSup_nonneg fun _ ↦ norm_nonneg _) (norm_nonneg _)`);
   termwise `‖x i • f (Pi.single i 1)‖ ≤ ‖x i‖ * ‖f (Pi.single i 1)‖ ≤ ‖x‖ * ⨆ …`
   (`norm_smul_le`, `norm_le_pi_norm`, `le_ciSup (Set.finite_range _).bddAbove i`, `mul_le_mul`), then `mul_comm`.
2. `continuous_pi`: `AddMonoidHomClass.continuous_of_bound f _ (norm_map_le_iSup_mul f)`.""",
 "`Finset.univ_sum_single`, `Pi.single_smul`, `pi_eq_sum_univ`, `map_sum`, `map_smul`, `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`, `Real.iSup_nonneg`, `norm_smul_le`, `norm_le_pi_norm`, `le_ciSup`, `Set.finite_range`, `Set.Finite.bddAbove`, `mul_le_mul`, `AddMonoidHomClass.continuous_of_bound`.",
 "[Sch] Prop 4.13 Step 1 `schneider.txt:909–913`; [BGR] 3.7.3/2 proof `bgr-3.7.md:57–59`; [RM] §1.2.5.",
 "`[IsUltrametricDist M]` on the target (E17); no `NormOneClass`, no Tate hypothesis; `[DecidableEq ι]` because `Pi.single` needs it.")

ticket("T019", "The operator norm of a map out of a finite free module", PI, "T018", "no", "lemma", "L6.3",
 ["opNorm_pi_eq"],
 """1. `refine le_antisymm (opNorm_le_bound _ (Real.iSup_nonneg fun _ ↦ norm_nonneg _) (norm_map_le_iSup_mul u)) ?_`.
2. `cases isEmpty_or_nonempty ι`: empty — `Real.iSup_of_isEmpty` and `opNorm_nonneg`; nonempty —
   `ciSup_le fun i ↦ ?_` with `‖u (Pi.single i 1)‖ ≤ ‖u‖ * ‖Pi.single i 1‖ = ‖u‖`
   (`le_opNorm_of_bound u ⟨_, norm_map_le_iSup_mul u⟩`, `Pi.norm_single`, `norm_one`, `mul_one`).""",
 "`Real.iSup_nonneg`, `Real.iSup_of_isEmpty`, `isEmpty_or_nonempty`, `ciSup_le`, `Pi.norm_single`, `norm_one`, `mul_one`.",
 "[RM] §1.2.5 (\"with norm the maximum of the norms of the images of the basis vectors\").",
 "`[NormOneClass R]` for `‖Pi.single i 1‖ = 1`; no `IsTate` (the bound of T018 feeds `le_opNorm_of_bound`).")

cleanup("CLEANUP-9", PI, "T019", "final per-file cleanup of `Pi.lean`")

ticket("T020", "Buzzard's Lemma 2.2", F, "CLEANUP-6, CLEANUP-9", "no", "lemmas", "L7.1–L7.2",
 ["exists_bound_of_finite", "continuous_of_finite"],
 """1. `exists_bound_of_finite`: `obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R P`;
   `let πL : (Fin n → R) →L[R] P := ⟨π, continuous_pi π⟩` (ultrametric `P`);
   `obtain ⟨C, hC0, hC⟩ := exists_preimage_norm_le πL hπ` (`CompleteSpace (Fin n → R)` from `CompleteSpace R`);
   `refine ⟨(⨆ i, ‖(φ ∘ₗ π) (Pi.single i 1)‖) * C, fun p ↦ ?_⟩`; `obtain ⟨a, rfl, ha⟩ := hC p`;
   `‖φ (π a)‖ = ‖(φ ∘ₗ π) a‖ ≤ (⨆ …) * ‖a‖` (`norm_map_le_iSup_mul`, ultrametric `M`) `≤ (⨆ …) * (C * ‖p‖)`
   (`mul_le_mul_of_nonneg_left ha (Real.iSup_nonneg …)`), `mul_assoc`.
2. `continuous_of_finite`: `obtain ⟨C, hC⟩ := exists_bound_of_finite φ; exact AddMonoidHomClass.continuous_of_bound φ C hC`.""",
 "`Module.Finite.exists_fin'`, `LinearMap.comp_apply`, `Real.iSup_nonneg`, `mul_le_mul_of_nonneg_left`, `mul_assoc`, `AddMonoidHomClass.continuous_of_bound`; board: `continuous_pi`, `norm_map_le_iSup_mul`, `exists_preimage_norm_le`.",
 "[Buz07] Lemma 2.2 `buzzard.txt:201–210`; [Lud] Lemma 2.14 `ludwig.txt:231–236`; [BGR] 3.7.3/2–3 `bgr-3.7.md:56–63` (uniqueness of the Banach norm is this lemma applied to the identity between two norms); [RM] §1.4.1.",
 "No Noetherian hypothesis. `[IsUltrametricDist P]` for `continuous_pi π`, `[IsUltrametricDist M]` for the bound on `φ ∘ π` (added to the skeleton during the adversarial pass), `[CompleteSpace R]` for the domain of the open mapping theorem, `[CompleteSpace P]` for its codomain.")

ticket("T021", "The nonarchimedean Nakayama lemma for submodules", F, "none (Layer 0 only)", "yes", "lemma", "L7.3",
 ["Submodule.forall_mem_of_forall_exists_eq_add_sum_smul_of_norm_lt_one"],
 """Transcribe [RAG] `Ideal.forall_mem_of_forall_exists_eq_add_sum_mul_of_norm_lt_one` (`RigidAnalyticGeometry/BanachAlgebra/Noetherian.lean:52–72`) from ideals to submodules:
1. `N' : Submodule (unitClosedBall R) M := Submodule.span _ (Set.range x)`;
   `N₀ : Submodule (unitClosedBall R) M := N.restrictScalars (unitClosedBall R)` (instances
   `Subsemiring.instModuleSubtypeMem`, `Submonoid.instIsScalarTowerSubtypeMem` — verified to synthesise).
2. `hle : N' ≤ N₀ ⊔ openUnitBallIdeal R • N'`: `Submodule.span_le.2`; `rintro _ ⟨i, rfl⟩`; `obtain ⟨y, hy, c, hc, hxi⟩ := h i`;
   `rw [SetLike.mem_coe, hxi]`; `Submodule.add_mem_sup hy (Submodule.sum_mem _ fun j _ ↦ ?_)`;
   `c j • x j = (⟨c j, mem_unitClosedBall.2 (hc j).le⟩ : unitClosedBall R) • x j` is `rfl`;
   `Submodule.smul_mem_smul (mem_openUnitBallIdeal.2 (hc j)) (Submodule.subset_span ⟨j, rfl⟩)`.
3. `Submodule.le_of_le_smul_of_le_jacobson_bot (Submodule.fg_span (Set.finite_range x)) openUnitBallIdeal_le_jacobson_bot hle`
   gives `N' ≤ N₀`; apply it to `Submodule.subset_span ⟨i, rfl⟩`.""",
 "`Submodule.span_le`, `SetLike.mem_coe`, `Submodule.add_mem_sup`, `Submodule.sum_mem`, `Submodule.smul_mem_smul`, `Submodule.subset_span`, `Submodule.fg_span`, `Set.finite_range`, `Submodule.le_of_le_smul_of_le_jacobson_bot`, `Submodule.restrictScalars`; Layer 0: `Subring.mem_unitClosedBall`, `NormedRing.mem_openUnitBallIdeal`, `NormedRing.openUnitBallIdeal_le_jacobson_bot`.",
 "[BGR] 1.2.4/6 `bgr-3.7.md:142–150`; [RAG] the ideal case (sorry-free, same proof); [RM] §1.4.2 (seam S3: Mathlib's Nakayama replaces the matrix lemma).",
 "`[NormedCommRing R] [NormOneClass R] [IsUltrametricDist R] [CompleteSpace R]` — the hypotheses of Layer 0's Jacobson-radical lemma; nothing on `M` beyond being a normed module (no completeness).")

ticket("T022", "Bounded coefficients on a closed finitely generated submodule", F, "T020", "no", "lemma", "L7.4",
 ["Submodule.exists_forall_exists_eq_sum_smul_norm_le"],
 """Transcribe [RAG] `Ideal.exists_forall_exists_eq_sum_mul_norm_le` (`BanachAlgebra/Noetherian.lean:85–115`) over the Tate ring:
1. `hmem : ∀ a : Fin n → R, ∑ i, a i • x i ∈ J` (`J.sum_mem`, `J.smul_mem`, `hx ▸ Submodule.subset_span ⟨i, rfl⟩`).
2. `πl : (Fin n → R) →ₗ[R] J := { toFun := fun a ↦ ⟨∑ i, a i • x i, hmem a⟩, map_add' := …, map_smul' := … }`
   (`Subtype.ext`, `add_smul`, `Finset.sum_add_distrib`, `Finset.smul_sum`, `smul_smul`).
3. `haveI : CompleteSpace J := hJ.completeSpace_coe`; `πL : (Fin n → R) →L[R] J := ⟨πl, continuous_pi πl⟩`
   (`J` is ultrametric as a subtype of `M`).
4. Surjective: `rintro ⟨y, hy⟩`; `hx ▸ hy` and `Submodule.mem_span_range_iff_exists_fun.1`.
5. `obtain ⟨C, hC0, hC⟩ := exists_preimage_norm_le πL hsurj`; for `y ∈ J`, `obtain ⟨a, ha, hna⟩ := hC ⟨y, hy⟩`;
   `⟨a, (congrArg Subtype.val ha).symm, fun i ↦ (norm_le_pi_norm a i).trans hna⟩`.""",
 "`Submodule.sum_mem`, `Submodule.smul_mem`, `Submodule.subset_span`, `Subtype.ext`, `add_smul`, `Finset.sum_add_distrib`, `Finset.smul_sum`, `smul_smul`, `IsClosed.completeSpace_coe`, `Submodule.mem_span_range_iff_exists_fun`, `norm_le_pi_norm`, `congrArg`; board: `continuous_pi`, `exists_preimage_norm_le`.",
 "[BGR] 3.7.2/1 proof `bgr-3.7.md:30–33` (\"By BANACH's Theorem, `π` is open\"); [RAG] the ideal case.",
 "`[CompleteSpace M]` (for `J`), `[CompleteSpace R]` (for `Fin n → R`), ultrametric `M` (for `continuous_pi`); the constant is positive so that `C⁻¹` can be used in T023.")

cleanup("CLEANUP-10", F, "T022", "after the 3rd proof ticket on `Finite.lean`")
cleanup("CLEANUP-ALL-2", "project", "CLEANUP-10, CLEANUP-6, CLEANUP-7, CLEANUP-8, CLEANUP-9, CLEANUP-4", "pre-milestone sweep (`/cleanup-all` on all Layer 1 files so far) before M2")

ticket("T023", "Closedness of submodules of finitely generated Banach modules (MILESTONE M2)", F, "CLEANUP-ALL-2", "no", "theorems", "L7.5–L7.6",
 ["Submodule.isClosed_of_fg_topologicalClosure", "Submodule.isClosed_of_isNoetherianRing"],
 """1. `isClosed_of_fg_topologicalClosure`: transcribe [RAG] `Ideal.isClosed_of_fg_closure` (`Noetherian.lean:130–162`):
   `obtain ⟨n, x, hx⟩ := Submodule.fg_iff_exists_fin_generating_family.1 hfg`; `J := N.topologicalClosure`, closed by
   `Submodule.isClosed_topologicalClosure`; `obtain ⟨C, hC0, hC⟩ := Submodule.exists_forall_exists_eq_sum_smul_norm_le x J hJ hx`;
   `hxN : ∀ i, x i ∈ N` by `Submodule.forall_mem_of_forall_exists_eq_add_sum_smul_of_norm_lt_one N x fun i ↦ ?_`:
   `x i ∈ closure (N : Set M)` (`Submodule.topologicalClosure_coe`, `hx ▸ Submodule.subset_span ⟨i, rfl⟩`),
   `Metric.mem_closure_iff.1 … C⁻¹ (inv_pos.2 hC0)` gives `y ∈ N`, `dist (x i) y < C⁻¹`;
   `hC _ (J.sub_mem hxi (N.le_topologicalClosure hy))` gives `c` with `x i - y = ∑ j, c j • x j` and
   `‖c j‖ ≤ C * ‖x i - y‖ < C * C⁻¹ = 1`; rearrange to `x i = y + ∑ …` (`sub_eq_iff_eq_add'`/`abel`).
   Finish: `isClosed_of_closure_subset`: `closure N ⊆ J = span (range x) ≤ N` (`Submodule.span_le.2`).
2. `isClosed_of_isNoetherianRing`: `haveI := isNoetherian_of_isNoetherianRing_of_finite R M`;
   `exact N.isClosed_of_fg_topologicalClosure (IsNoetherian.noetherian _)`.""",
 "`Submodule.fg_iff_exists_fin_generating_family`, `Submodule.isClosed_topologicalClosure`, `Submodule.topologicalClosure_coe`, `Submodule.le_topologicalClosure`, `Submodule.subset_span`, `Submodule.span_le`, `Submodule.sub_mem`, `Metric.mem_closure_iff`, `dist_eq_norm`, `inv_pos`, `mul_lt_mul_of_pos_left`, `mul_inv_cancel₀`, `isClosed_of_closure_subset`, `isNoetherian_of_isNoetherianRing_of_finite`, `IsNoetherian.noetherian`.",
 "[BGR] 3.7.2/1 `bgr-3.7.md:27–33` and `bgr-3.7.md:35–37`; [JN] `jn.txt:526–531`; Fresnel–van der Put Lemma 1.2.3 as cited by [RM] §1.4.2; [RAG] `Ideal.isClosed_of_fg_closure`, `Ideal.isClosed_of_isNoetherianRing`.",
 "BGR 3.7.2/1 proper (`isClosed_of_fg_topologicalClosure`) has **no** Noetherian hypothesis; `isClosed_of_isNoetherianRing` adds `[IsNoetherianRing R] [Module.Finite R M]`. Each hypothesis is necessary (T029–T030 exhibit the failure without Noetherianity).")

ticket("T024", "Closed ideals and the Banach norm of a finitely generated module", F, "T023", "no", "theorems", "L7.7–L7.8",
 ["Ideal.isClosed_of_isTate_of_isNoetherianRing", "Module.Finite.exists_surjective_isClosed_ker"],
 """1. `Ideal.isClosed_of_isTate_of_isNoetherianRing`: `Submodule.isClosed_of_isNoetherianRing (M := R) I`
   (`Module.Finite R R` is an instance).
2. `Module.Finite.exists_surjective_isClosed_ker`: `obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R P`;
   `exact ⟨n, π, hπ, Submodule.isClosed_of_isNoetherianRing (M := Fin n → R) (LinearMap.ker π)⟩`
   (`IsUltrametricDist (Fin n → R)` from `R`, `CompleteSpace (Fin n → R)`, `Module.Finite R (Fin n → R)` are instances).""",
 "`Module.Finite.exists_fin'`, `Module.Finite.self`, `Pi.instIsUltrametricDist`; board: `Submodule.isClosed_of_isNoetherianRing`.",
 "[Buz07] `buzzard.txt:173`; [BGR] 3.7.2/2 `bgr-3.7.md:39`, 3.7.3/3 `bgr-3.7.md:60–63`; [RM] §1.4.1.",
 "The ideal lemma's name avoids the in-chain field-scalar `Ideal.isClosed_of_isNoetherianRing` of `RigidAnalyticGeometry/BanachAlgebra/Noetherian.lean` (same chain root). `P` carries no norm: the statement produces the Banach structure.")

cleanup("CLEANUP-11", F, "T024", "final per-file cleanup of `Finite.lean`")

ticket("T025", "Multiplication by a ring element", E, "CLEANUP-11, CLEANUP-4, CLEANUP-7, CLEANUP-8", "no", "def + lemma", "L8.1",
 ["mulLeftL", "opNorm_mulLeftL"],
 """1. The bound in `mulLeftL`: `fun x ↦ by rw [LinearMap.mulLeft_apply]; exact norm_mul_le a x`.
2. `opNorm_mulLeftL`: `le_antisymm (opNorm_le_bound _ (norm_nonneg a) fun x ↦ by simpa using norm_mul_le a x)`;
   for `≥`: `have h := le_opNorm_of_bound (mulLeftL a) ⟨‖a‖, fun x ↦ by simpa using norm_mul_le a x⟩ 1`;
   `simpa [mulLeftL_apply, norm_one] using h`.""",
 "`LinearMap.mulLeft_apply`, `norm_mul_le`, `norm_one`, `mul_one`.",
 "[RM] Layer 1 Examples, corrected (erratum E10 in `plan.md`: `‖a‖ = ‖a · 1‖ ≤ ‖mulLeft a‖ ‖1‖`).",
 "`[NormedCommRing R] [NormOneClass R]`, no Tate hypothesis: the example shows equality holds for every `a` as soon as `‖1‖ = 1`.")

ticket("T026", "The open mapping constant of `(x, y) ↦ x + ϖ y`", E, "T025", "no", "def + lemmas", "L8.2–L8.4",
 ["addPseudoUniformizerSMul", "exists_preimage_norm_le_addPseudoUniformizerSMul", "one_le_of_forall_exists_preimage_norm_le_addPseudoUniformizerSMul"],
 """1. The bound `1` in `addPseudoUniformizerSMul`: `‖m.1 + ϖ * m.2‖ ≤ max ‖m.1‖ (‖ϖ‖ * ‖m.2‖) ≤ max ‖m.1‖ ‖m.2‖ = ‖m‖`
   (`LinearMap.add_apply`, `LinearMap.smul_apply`, `smul_eq_mul`, `IsUltrametricDist.norm_add_le_max`,
   `ϖ.isMultiplicative.norm_mul`, `mul_le_of_le_one_left (norm_nonneg _) ϖ.norm_lt_one.le`, `Prod.norm_def`, `one_mul`).
2. `exists_preimage_norm_le_addPseudoUniformizerSMul`: `⟨(n, 0), by simp, by simp [Prod.norm_def]⟩`.
3. `one_le_of_forall_exists_preimage_norm_le_addPseudoUniformizerSMul`: `obtain ⟨m, hm, hle⟩ := hC 1`;
   `calc 1 = ‖(1 : R)‖ := norm_one.symm; _ = ‖addPseudoUniformizerSMul ϖ m‖ := by rw [hm]; _ ≤ ‖m‖ := (step 1's bound);
   _ ≤ C * ‖(1 : R)‖ := hle; _ = C := by rw [norm_one, mul_one]`.""",
 "`LinearMap.add_apply`, `LinearMap.smul_apply`, `smul_eq_mul`, `IsUltrametricDist.norm_add_le_max`, `mul_le_of_le_one_left`, `Prod.norm_def`, `norm_fst_le`, `norm_snd_le`, `norm_one`, `mul_one`; Layer 0: `NormedRing.IsMultiplicative.norm_mul`, `PseudoUniformizer.norm_lt_one`.",
 "[RM] Layer 1 Examples (\"the open mapping constant for the quotient map `R ² → R`, `(x, y) ↦ x + ϖ y`\").",
 "`[IsUltrametricDist R]` for the constant `1`; `[NormOneClass R]` for the lower bound; explicit `ϖ`.")

ticket("T027", "A continuous bijection whose inverse has norm `p`", E, "T026", "no", "lemmas", "L8.5–L8.6",
 ["bijective_padic_smul_id", "norm_padic_inv_smul_id"],
 """These two use Mathlib's field-scalar instances on `ℚ_[p] →L[ℚ_[p]] ℚ_[p]` (do not open the scope in this section).
1. `bijective_padic_smul_id`: `hp0 : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero`;
   `Function.bijective_iff_has_inverse.2 ⟨fun y ↦ (p : ℚ_[p])⁻¹ * y, fun x ↦ by simp [hp0], fun y ↦ by simp [hp0]⟩`
   (`ContinuousLinearMap.smul_apply`, `ContinuousLinearMap.id_apply`, `smul_eq_mul`, `inv_mul_cancel_left₀`).
2. `norm_padic_inv_smul_id`: `rw [norm_smul, norm_inv, Padic.norm_p, inv_inv, ContinuousLinearMap.norm_id, mul_one]`;
   if the `NontrivialTopology ℚ_[p]` instance behind `norm_id` is not found, prove `‖id‖ = 1` with
   `ContinuousLinearMap.opNorm_eq_of_bounds` (bound `1`, and `‖id 1‖ = 1`).""",
 "`Function.bijective_iff_has_inverse`, `Nat.cast_ne_zero`, `inv_mul_cancel_left₀`, `mul_inv_cancel_left₀`, `norm_smul`, `norm_inv`, `Padic.norm_p`, `inv_inv`, `ContinuousLinearMap.norm_id`, `ContinuousLinearMap.opNorm_eq_of_bounds`.",
 "[RM] Layer 1 Examples (\"a continuous bijection of Banach `ℚ_p`-spaces whose inverse has norm `p`\"); the scoped norm agrees by `norm_eq_opNorm`.",
 "Field scalars, Mathlib's norm; the example is also a sanity check of §1.1.6.")

cleanup("CLEANUP-12", E, "T027", "after the 3rd proof ticket on `Examples.lean`")

ticket("T028", "`ℤ_p` with the squared norm: continuous, unbounded", E, "CLEANUP-12", "no", "instances + lemmas", "L8.7–L8.11",
 ["instance : NormedAddCommGroup (PadicIntSq p)", "instance : IsBoundedSMul ℤ_[p] (PadicIntSq p)", "instance : IsUltrametricDist (PadicIntSq p)", "continuous_symm_toPadicIntSq", "not_exists_bound_symm_toPadicIntSq"],
 """Throughout, `(toPadicIntSq p).symm x` is definitionally `x` as an element of `ℤ_[p]`; `norm_def` unfolds `‖x‖`.
1. Norm fields: `map_zero'`: `norm_zero`, `zero_pow two_ne_zero`; `add_le'`: `pow_le_pow_left (norm_nonneg _)
   (IsUltrametricDist.norm_add_le_max _ _) 2`, then `max_pow`-style `(max a b) ^ 2 = max (a ^ 2) (b ^ 2)`
   (`Monotone.map_max (pow_left_mono 2)`) and `max_le_add_of_nonneg`; `neg'`: `norm_neg`;
   `eq_zero_of_map_eq_zero'`: `pow_eq_zero_iff two_ne_zero`, `norm_eq_zero`.
2. `IsBoundedSMul`: `IsBoundedSMul.of_norm_smul_le fun r x ↦ ?_`: `‖r • x‖ = (‖r‖ * ‖x‖) ^ 2 = ‖r‖ ^ 2 * ‖x‖ ^ 2 ≤ ‖r‖ * ‖x‖ ^ 2`
   (`norm_def`, `smul_eq_mul`, `PadicInt.norm_mul` / `norm_mul`, `mul_pow`, `pow_le_of_le_one (norm_nonneg r) (PadicInt.norm_le_one r) two_ne_zero`).
3. `IsUltrametricDist`: `isUltrametricDist_of_isNonarchimedean_norm` with the `max` computation of step 1.
4. `continuous_symm_toPadicIntSq`: `Metric.continuous_iff.2 fun x ε hε ↦ ⟨ε ^ 2, by positivity, fun y hy ↦ ?_⟩`;
   `dist y x = ‖y - x‖ ^ 2 < ε ^ 2` gives `‖y - x‖ < ε` (`pow_lt_pow_iff_left₀`, `abs_lt_abs`-free: use
   `lt_of_pow_lt_pow_left₀ 2 hε.le`).
5. `not_exists_bound_symm_toPadicIntSq`: `rintro ⟨C, hC⟩`; `obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (Nat.one_lt_cast.2 hp.out.one_lt)`;
   `have := hC (toPadicIntSq p (p ^ n))`; `rw [norm_def, PadicInt.norm_p_pow, …]` to get `(p : ℝ) ^ (-n : ℤ) ≤ C * ((p : ℝ) ^ (-n : ℤ)) ^ 2`;
   multiply by `(p : ℝ) ^ (2 n) > 0` (`zpow_neg`, `zpow_natCast`, `inv_pow`) to get `p ^ n ≤ C`, contradicting `hn`.""",
 "`norm_zero`, `zero_pow`, `pow_le_pow_left`, `Monotone.map_max`, `pow_left_mono`, `max_le_add_of_nonneg`, `norm_neg`, `pow_eq_zero_iff`, `norm_eq_zero`, `IsBoundedSMul.of_norm_smul_le`, `norm_mul`, `mul_pow`, `pow_le_of_le_one`, `PadicInt.norm_le_one`, `IsUltrametricDist.norm_add_le_max`, `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`, `Metric.continuous_iff`, `dist_eq_norm`, `lt_of_pow_lt_pow_left₀`, `pow_unbounded_of_one_lt`, `Nat.one_lt_cast`, `PadicInt.norm_p_pow`, `zpow_neg`, `zpow_natCast`, `inv_pow`, `le_div_iff₀`.",
 "[RM] §1.1.2 (\"the identity map from `ℤ_p` with the norm `‖x‖²` (a normed `ℤ_p`-module) to `ℤ_p` with its norm is continuous and unbounded. The Tate hypothesis is exactly what is needed\"); Layer 0 `not_isTate_padicInt`.",
 "The scalars are `ℤ_p` (not `ℚ_p`): `‖r‖ ≤ 1` is what makes the squared norm a module norm; the synonym carries `toPadicIntSq` as its only interface.")

ticket("T029", "A non-closed principal ideal of `ℓ^∞(ℕ, ℚ_p)`", E, "T028", "no", "instance + def + theorem", "L8.12–L8.14",
 ["lp.instIsUltrametricDist", "padicGeomSeq", "not_isClosed_span_padicGeomSeq"],
 """1. `lp.instIsUltrametricDist`: `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm fun f g ↦
   lp.norm_le_of_forall_le (le_max_of_le_left (norm_nonneg f)) fun i ↦ ?_`; `rw [lp.coeFn_add, Pi.add_apply]`;
   `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le_max (lp.norm_apply_le_norm top_ne_zero f i) (lp.norm_apply_le_norm top_ne_zero g i))`.
2. `padicGeomSeq` bounded: `rintro _ ⟨n, rfl⟩; exact (norm_pow_le' _ …).trans (pow_le_one₀ (norm_nonneg _) Padic.norm_p_lt_one.le)`
   (or `Padic.norm_p_pow` with `zpow_le_one_of_nonpos₀`).
3. `not_isClosed_span_padicGeomSeq`: set `S := (Ideal.span {padicGeomSeq p} : Set _)`,
   `c : lp (fun _ : ℕ ↦ ℚ_[p]) ∞ := ⟨fun n ↦ (p : ℚ_[p]) ^ (n / 2), memℓp_infty ⟨1, …⟩⟩`.
   (i) `c ∈ closure S` (`Metric.mem_closure_iff`): given `ε > 0`, `obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.2 hp.out.one_lt))`
   for `(p : ℝ)⁻¹ ^ N < ε`; `b : lp _ ∞ := ⟨fun n ↦ if n < 2 * N then (p : ℚ_[p]) ^ (n / 2) * ((p : ℚ_[p]) ^ n)⁻¹ else 0, bounded (finitely many nonzero)⟩`;
   `b * padicGeomSeq p ∈ S` by `Ideal.mem_span_singleton'.2 ⟨b, rfl⟩`; `dist c (b * a) = ‖c - b * a‖ ≤ (p : ℝ)⁻¹ ^ N < ε`
   by `lp.norm_le_of_forall_le`: coordinate `n`: `lp.coeFn_sub`, `lp.infty_coeFn_mul`, `Pi.mul_apply`; for `n < 2N`
   the coordinate is `0` (`inv_mul_cancel_right₀`); for `n ≥ 2N` it is `p ^ (n / 2)` of norm `(p⁻¹) ^ (n / 2) ≤ (p⁻¹) ^ N`
   (`Padic.norm_p_pow`, `pow_le_pow_of_le_one`, `Nat.le_div_iff_mul_le`).
   (ii) `c ∉ S`: `rintro h`; `obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.1 h`; coordinatewise
   `b n * p ^ n = p ^ (n / 2)` (`congrFun (congrArg Subtype.val hb) n`, `lp.infty_coeFn_mul`); at `n = 2k`:
   `b (2k) = p ^ k * (p ^ (2k))⁻¹` has norm `(p : ℝ) ^ k` (`norm_mul`, `norm_inv`, `Padic.norm_p_pow`, `zpow_neg`,
   `Nat.mul_div_cancel_left`); `lp.norm_apply_le_norm top_ne_zero b (2 * k)` gives `(p : ℝ) ^ k ≤ ‖b‖` for every `k`,
   against `pow_unbounded_of_one_lt ‖b‖ (Nat.one_lt_cast.2 hp.out.one_lt)`.
   Conclude: `fun hS ↦ (hS.closure_eq ▸ hc_closure : c ∈ S)` contradicts (ii).""",
 "`IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`, `lp.norm_le_of_forall_le`, `lp.norm_apply_le_norm`, `lp.coeFn_add`, `lp.coeFn_sub`, `lp.infty_coeFn_mul`, `memℓp_infty`, `norm_pow_le'`, `pow_le_one₀`, `Padic.norm_p_lt_one`, `Padic.norm_p_pow`, `Metric.mem_closure_iff`, `exists_pow_lt_of_lt_one`, `inv_lt_one_of_one_lt₀`, `Nat.one_lt_cast`, `Ideal.mem_span_singleton'`, `inv_mul_cancel_right₀`, `pow_le_pow_of_le_one`, `Nat.le_div_iff_mul_le`, `Nat.mul_div_cancel_left`, `norm_mul`, `norm_inv`, `zpow_neg`, `pow_unbounded_of_one_lt`, `IsClosed.closure_eq`, `top_ne_zero`.",
 "[RM] §1.4.3 (\"Not every finitely generated submodule of a Banach module is closed. Record a counterexample over a non-Noetherian Banach–Tate ring\"); [Lud] Remark 2.25 `ludwig.txt:351–358` (Bellaïche's Hypothesis 3.1.8); erratum E18 in `plan.md` (the example is the planner's).",
 "The `lp` ultrametric instance is stated for every family `E` (§2.5 will reuse it); the counterexample is a *principal* ideal, the strongest form; `p` arbitrary.")

ticket("T030", "`ℓ^∞(ℕ, ℚ_p)` is not Noetherian", E, "T029", "no", "theorem", "L8.15",
 ["not_isNoetherianRing_lp_infty"],
 """1. `intro h`; `haveI : NormedRing.IsTate (lp (fun _ : ℕ ↦ ℚ_[p]) ∞) := NormedRing.isTate_of_normedAlgebra ℚ_[p] _`
   (`lp.inftyNormedAlgebra`, `NormOneClass` from `Nonempty ℕ`).
2. `exact not_isClosed_span_padicGeomSeq p (Submodule.isClosed_of_isNoetherianRing (R := lp _ ∞) (M := lp _ ∞) _)`
   — the remaining instances (`NormedCommRing`, ultrametric from T029, `CompleteSpace`, `IsBoundedSMul R R`,
   `Module.Finite R R`) are found by unification; `haveI` any that is not.""",
 "`lp.inftyNormedCommRing`, `lp.inftyNormedAlgebra`, `Module.Finite.self`; Layer 0: `NormedRing.isTate_of_normedAlgebra`; board: `Submodule.isClosed_of_isNoetherianRing`, `not_isClosed_span_padicGeomSeq`.",
 "[RM] §1.4.3 (\"a non-Noetherian Banach–Tate ring\"); [Buz07] `buzzard.txt:173` (closed ideals ⇔ Noetherian).",
 "This is M2 read backwards: every hypothesis of `Submodule.isClosed_of_isNoetherianRing` except Noetherianity holds for `ℓ^∞(ℕ, ℚ_p)`.")

cleanup("CLEANUP-13", E, "T030", "final per-file cleanup of `Examples.lean`")

ticket("T031", "Add Layer 1 to the chain root", "PhD/TauCeti.lean", "CLEANUP-13", "no", "integration", "—", [],
 """1. Append `import PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.Examples` to `PhD/TauCeti.lean`, in alphabetical
   position after `PhD.TauCeti.Code.PadicFunctionalAnalysis.NormComparison` (append-only edit; another board may be
   editing the file — re-read it first).
2. `lake build PhD.TauCeti` must succeed; then `#print axioms` on `exists_preimage_norm_le`,
   `Submodule.isClosed_of_isNoetherianRing`, `instNormedAddCommGroup_eq`, `not_isNoetherianRing_lp_infty`
   (only `propext`, `Classical.choice`, `Quot.sound`), and `grep -c sorry` over `Operator/` must be `0`.
3. Record the completion line in this board's header and in `plan.md`.""",
 "—", "[RM] \"Existing Lean work\" (the chain root lists leaf modules only).", "—")

cleanup("CLEANUP-FINAL", "project", "T031", "final `/cleanup-all` of the whole Layer 1 (per-file `runLinter`, no `sorry`, standard axioms)")

# ---------- render ----------
proof = [t for t in T if not t.get("cleanup")]
cleans = [t for t in T if t.get("cleanup")]
out = []
out.append(f"""# Ticket board: Tau Ceti `PadicFunctionalAnalysis`, Layer 1 (bounded linear maps)

**Board**: `.mathlib-quality/tauceti-pfa-layer1/` (a *named* board: always pass this path to `/beastmode`;
the default board belongs to another project, and the other `tauceti-*` boards are parallel boards).
**Plan**: `plan.md` · **Decomposition (quotes, attacks, gate)**: `decomposition.md` · **References**: `references/*`
**Roadmap**: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, Layer 1 (§1.1–§1.4) — cited as [RM].
**Code**: `PhD/TauCeti/Code/PadicFunctionalAnalysis/Operator/` — eight files, every declaration already stated with
`sorry`. Planned {datetime.date.today().isoformat()}. Status: **open** (0 / {len(T)} done).

## Summary

| | Count |
|---|---|
| Proof / definition / integration tickets | {len(proof)} (`T001`–`T{len(proof):03d}`) |
| Per-file cleanups | 13 (`CLEANUP-1`–`CLEANUP-13`) |
| Pre-milestone sweeps | 2 (`CLEANUP-ALL-1`, `CLEANUP-ALL-2`) |
| Final sweep | 1 (`CLEANUP-FINAL`) |
| **Total** | **{len(T)}** |

- **Milestone M1** = `T012`: the quantitative open mapping theorem over a Tate normed ring
  (`ContinuousLinearMap.Ultra.exists_preimage_norm_le`, `isOpenMap`) — [RM] §1.2.1.
- **Milestone M2** = `T023`: every submodule of a finitely generated Banach module over a Noetherian Banach–Tate
  ring is closed (`Submodule.isClosed_of_isNoetherianRing`) — [RM] §1.4.2.
- The agreement with Mathlib (§1.1.6) is `T010`; the layer's two counterexamples are `T028` and `T029`–`T030`.
- Skeleton: 99 declaration headers, 75 `sorry`s. Gate (verified 2026-10-06, 2 254 jobs, 0 errors):
  `lake build PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.Examples`.
- Tickets that can start immediately (no dependencies): `T001`, `T002`, `T021`.

## Worker protocol (binding)

1. **The statements are fixed.** Every ticket's Statement block is copied verbatim from the skeleton by
   `scratch/gen/gen_tickets.py`. Prove the statement as written. If a statement is false or unprovable as stated,
   that is a **B2 stop** with a concrete counterexample or obstruction — never silently change a hypothesis.
   Private helper lemmas are allowed and expected where a sketch says so; they follow the same conventions.
2. **Chain separation.** Never `import PhD.Main.*` here (CI-gated), and never the reverse. `PhD/Main/` files cited
   as [SRC] and the in-chain [RAG] file are read-only references for proof ideas. Never delete `PhD/PR'd/` or
   legacy files.
3. **Build** with `lake build PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.<Module>` — never `lake build PhD`.
   There is no `timeout` binary on this machine: use the tool timeout and check exit codes. Run one Lean process
   at a time (parallel builds swap-thrash).
4. **Imports stay minimal per file** (never `import Mathlib` in a `Code/` file). When a proof needs an unimported
   module, add exactly that module.
5. **The scope.** Everything lives in `namespace ContinuousLinearMap.Ultra`; outside it, `open scoped
   ContinuousLinearMap.Ultra` activates the operator norm. An unqualified `le_opNorm`, `opNorm_le_bound`, … inside
   the namespace is overloaded with Mathlib's field version — write `Ultra.le_opNorm` when the elaborator
   complains. Never open the scope for field scalars (`T010`, `T027` use Mathlib's instances on purpose).
6. **Done means**: the module builds with no `sorry` in the ticket's declarations, `#print axioms` on each shows
   only `propext`, `Classical.choice`, `Quot.sound`, and the ticket's Status line is updated here.
7. **Cleanup tickets are done inline by the main agent** (no Agent-dispatched cleanup workers), with
   `lake exe runLinter` on the module.
8. **Sentinel ownership.** `.mathlib-quality/beastmode_active` may belong to a parallel instance: `cat` it before
   acting, and delete it only if its `BOARD:` line names this board.
9. **Mathlib first.** Every Mathlib name in a "Mathlib lemmas needed" block was checked by elaboration against
   the pinned Mathlib (`scratch/names*.lean`, three files, about 250 names), except where a sketch says
   "if … is not found" and gives the fallback. `T0xx` refers to an earlier ticket of this board; "Layer 0" names
   are in `PhD/TauCeti/Code/PadicFunctionalAnalysis/*.lean`.
10. **Conventions** (plan §"Generality and design decisions"): Mathlib's formula verbatim; weakest hypotheses
    (no `CompleteSpace R`, no ultrametricity in §1.2 proper; commutative `R` only where Mathlib's instances force
    it); explicit `ϖ` when a constant mentions `‖ϖ‖`, `[IsTate R]` otherwise; one conclusion per declaration;
    one-line `Source:` docstrings; readable arithmetic (`ring` identity + `mul_le_mul` + `linarith` over `nlinarith`).
11. **Commit or push only when the user asks.**

## Roadmap errata (found while planning; see `plan.md` for the full table)

E9 `‖u‖` is the supremum of the ratios, not of `‖u x‖` over the unit ball · E10 multiplication by `a` has norm
exactly `‖a‖` once `‖1‖ = 1` · E11 equality in `‖a • u‖ ≤ ‖a‖‖u‖` needs a multiplicative *unit* · E12 the OMT is
proved by Baire, not from Henkel's theorem (seam S1) · E13 §1.3's orthogonal bases are deferred to Layer 2 ·
E14 §1.4.1's adic-spaces citations and §1.4.2's matrix lemma are replaced by Buzzard 2.2 and Nakayama (seams
S2, S3) · E15 the `C₀` examples move to Layer 2 · E16 §1.2 needs neither `CompleteSpace R` nor ultrametricity ·
E17 §1.2.5 needs an ultrametric target · E18 the §1.4.3 counterexample is `ℓ^∞(ℕ, ℚ_p)`. E9 and E10 are corrected
in the roadmap README (2026-10-06, uncommitted).

## Dependency order

```text
G1  Norm            T001 ∥ T002 → T003 → CLEANUP-1 → T004 → CLEANUP-2
G2  Banach          CLEANUP-2 → T005 → T006 → T007 → CLEANUP-3 → T008 → T009 → T010 → CLEANUP-4
G3  OpenMapping     CLEANUP-2 → T011 → CLEANUP-ALL-1 (needs CLEANUP-4) → T012 (M1) → T013 → CLEANUP-5 → T014 → CLEANUP-6
G4  ClosedGraph     CLEANUP-6 → T015 → CLEANUP-7
G5  BanachSteinhaus CLEANUP-2 → T016 → T017 → CLEANUP-8
G6  Pi              CLEANUP-2 → T018 → T019 → CLEANUP-9
G7  Finite          {{CLEANUP-6, CLEANUP-9}} → T020 ; T021 (free) ; T020 → T022 → CLEANUP-10 → CLEANUP-ALL-2 → T023 (M2) → T024 → CLEANUP-11
G8  Examples        {{CLEANUP-11, CLEANUP-4, CLEANUP-7, CLEANUP-8}} → T025 → T026 → T027 → CLEANUP-12 → T028 → T029 → T030 → CLEANUP-13
Root                CLEANUP-13 → T031 → CLEANUP-FINAL
```

## Tickets
""")
for t in T:
    if t.get("cleanup"):
        tgt = f"`{t['file']}`" if t['file'] != "project" else "the project"
        cmd = "/cleanup-all" if t['file'] == "project" else "/cleanup"
        out.append(f"""### [{t['id']}] Run `{cmd}` on {tgt}
- **Status**: open · **File**: {tgt} · **Depends on**: {t['deps']} · **Parallel**: no · **Type**: cleanup
- **Description**: {t['note']}. Audit + golf + style to mathlib standards; `lake exe runLinter` on the module(s);
  no statement changes (a needed statement change is a `/develop --continue` matter).
""")
        continue
    stmt = "\n\n".join(extract(t['file'], k) for k in t['decls']) if t['decls'] else "(no Lean declaration — an edit of `PhD/TauCeti.lean`)"
    out.append(f"""### [{t['id']}] {t['title']}
- **Status**: open · **File**: `{t['file']}` · **Depends on**: {t['deps']} · **Parallel**: {t['parallel']} · **Type**: {t['typ']}
- **Leaves**: {t['leaves']}

#### Statement
```lean
{stmt}
```
#### Proof sketch
{t['sketch']}

#### Mathlib lemmas needed
{t['lemmas']}
#### Sources
{t['sources']}
#### Generality decision
{t['generality']}
""")
OUT.write_text("\n".join(out))
print("tickets:", len(T), "proof:", len(proof), "cleanup:", len(cleans))
