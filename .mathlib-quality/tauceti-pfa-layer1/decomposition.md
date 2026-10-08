# Decomposition: p-adic functional analysis, Layer 1 (bounded linear maps)

Companion to `plan.md`. Every leaf below is a declaration in the skeleton, stated with `sorry`;
the pointer is `Operator/File.lean · declaration name` (names are stable, line numbers are not).
Sources: [RM] = the roadmap clause the leaf discharges, quoted verbatim; [JN] / [Sch] / [Bel] /
[Buz07] / [BGR] / [Lud] = literature, quoted verbatim with a locator `file:line` into
`references/`; [Mathlib] = the pinned Mathlib proof that is transported, quoted from its docstring
or named by its declaration; [L0] = Layer 0 of this chain (sorry-free, imported); [RAG] = the
in-chain field-scalar precedent `RigidAnalyticGeometry/BanachAlgebra/Noetherian.lean` (proof idea
only); [SRC] = the read-only reference development `PhD/Main/TateFredholm/…` (proof idea only,
never imported). Discharge lines name the Mathlib lemmas a worker will call — every name was checked
by elaboration (`scratch/names.lean`, `names2.lean`, `names3.lean`; the misses are recorded where
they occur). Attack categories: [1] counterexample search, [2] edge cases, [3] hypothesis strength,
[4] source drift, [5] discharge.

## Skeleton location

`PhD/TauCeti/Code/PadicFunctionalAnalysis/Operator/{Norm, Banach, OpenMapping, ClosedGraph,
BanachSteinhaus, Pi, Finite, Examples}.lean` — 8 files, 99 declaration headers, 75 `sorry`s (the
rest are instances, definitions and `rfl` lemmas complete in the skeleton).

Build status: recorded in the "Gate" section at the end of this file.

## Prior-B2 consultation (Step 4.6), once for the whole tree

`b2_log.jsonl` has 8 entries (2 Newton-polygon, 6 LWX). **No leaf matches by name.** One matches by
*shape of defect*: entry 3, `LWX.exists_binomial_basis` (2026-09-03) — *"False as stated, two
independent defects … the planner's generality claim"*: a statement generalised beyond its source's
hypotheses. This tree generalises beyond its sources in four places, each attacked explicitly:

| Generalisation | Where | How it was checked |
|---|---|---|
| open mapping / closed graph / Banach–Steinhaus with **no** `CompleteSpace R` and **no** ultrametric hypothesis | L3.1–L3.4, L4.*, L5.* | Mathlib's field proofs re-read line by line: Baire on `N`, a geometric series in `M`, nothing on `R` beyond scaling |
| the formula and its order lemmas for a **semiring** of scalars | L1.1–L1.7 | Mathlib's own proofs use only `csInf`/`Real.sInf_nonneg` |
| strictness of maps with closed range over a ring, not a field | L3.7–L3.9 | BGR 3.7.3/4 is OMT + the quotient norm; both available |
| closedness of submodules over a Noetherian Banach–**Tate** ring (BGR assume a field) | L7.3–L7.8 | [JN] l. 526–531 assert exactly this transfer; the Nakayama route of [RAG] uses only [L0] |

The other entries (`unitSlope_cases`, theta-equivariance) have no counterpart here. Two of the
roadmap's own claims were found false and are **not** stated (E9, E10 in `plan.md`); one needs a
unit (E11). These are the statement-level analogues of the B2 pattern, caught at planning time.

---

## §1.1.1–§1.1.2, §1.1.6 The operator norm (`Operator/Norm.lean`)

### Plain-English proof substrate

[JN] `jn.txt:522–523`: *"In this case, continuity of an `R`-linear map `φ` is equivalent to
boundedness; i.e. there exists `C ∈ ℝ_{>0}` such that `‖φ(m)‖ ≤ C‖m‖` for all `m ∈ M`. In this case
we set `|φ| = sup_{m ≠ 0} |φ(m)|·|m|⁻¹` as usual; `Hom_{R,cts}(M, N)` becomes a normed `R`-module with
respect to this norm."* [Sch] Prop 3.1 `schneider.txt:520–546`: *"For a `K`-linear map `f : V → W`
the following assertions are equivalent: i. `f` is continuous; ii. there is a real number `c ≥ 0`
such that `‖f(v)‖ ≤ c · ‖v‖` for any `v ∈ V`. … We now assume vice versa that `f` is continuous.
There is then a `0 < ε < 1` such that `f⁻¹(B₁(0)) ⊇ B_ε(0)`. Since the absolute value `| |` is
non-trivial we may assume `ε` to be of the form `ε = |a|` for some `a ∈ K`. This means that
`‖f(v)‖ ≤ 1` provided `‖v‖ ≤ |a|`. Let now `v` be an arbitrary nonzero vector in `V` and choose an
integer `m ∈ ℤ` such that `|a|^{m+2} < ‖v‖ ≤ |a|^{m+1}`. We compute `‖f(v)‖ = |a|^m · ‖f(a^{-m}v)‖
≤ |a|^m < |a|^{-2} · ‖v‖`."* Over a Tate normed ring the element `a` is the pseudo-uniformiser `ϖ`
([Buz07] `buzzard.txt:266–270`: *"a standard argument (see Corollary 2.1.8/3 of [1]) using the fact
that one can use `ρ` to renormalise elements of `M`, shows that `φ` is continuous iff it is
bounded"*), and the integer `m` is Layer 0's `existsUnique_zpow_norm_smul_mem_Ioc`. That one
computation is the leaf L1.8; everything else in §1.1.2 is L1.8 plus order theory. The order theory
is Mathlib's own (`ContinuousLinearMap.opNorm_le_bound`, `opNorm_nonneg`, …), whose proofs use only
`csInf_le` and `Real.sInf_nonneg` and so hold for a semiring of scalars. [Sch] Cor 3.2 and the
warning `schneider.txt:538–550`: *"`‖f‖ := sup {‖f(v)‖/‖v‖ : v ∈ V∖{0}} = sup {‖f(v)‖/‖v‖ : v ∈ V
such that 0 < ‖v‖ ≤ 1}. … We warn the reader that since the set of values `‖V‖` may be different from
the set of absolute values `|K|` we in general have `‖f‖ ≠ sup {‖f(v)‖ : v ∈ V such that ‖v‖ = 1}`."*
— this is erratum E9, and the leaves L1.13–L1.15 state what is true.

### Leaves

- **L1.1** `bounds_bddBelow` — [Mathlib] `ContinuousLinearMap.bounds_bddBelow` (`⟨0, fun _ ⟨hn, _⟩ => hn⟩`).
  Match: literal, semiring scalars. Discharge: `⟨0, fun _ hc ↦ hc.1⟩`. Attacks: [2] empty bound set
  (possible over a non-Tate ring): `BddBelow ∅` holds ✓. [3] no hypothesis to drop. [5] one-line
  term. SURVIVED.
- **L1.2** `opNorm_nonneg` — [RM] §1.1.1 *"`‖u‖ ≥ 0`"*; [Mathlib] `opNorm_nonneg := Real.sInf_nonneg
  fun _ ↦ And.left`. Discharge: `Real.sInf_nonneg`. Attacks: [2] empty bound set: `sInf ∅ = 0` in
  `ℝ`, so `0 ≤ 0` ✓ — this is why no boundedness hypothesis is needed. [5] verified. SURVIVED.
- **L1.3** `opNorm_le_bound` — [RM] §1.1.1 *"`‖u‖ ≤ C` from a uniform bound `∀ x, ‖u x‖ ≤ C ‖x‖`"*;
  [Mathlib] `opNorm_le_bound f hMp hM := csInf_le bounds_bddBelow ⟨hMp, hM⟩`. Discharge: `csInf_le`
  + L1.1. Attacks: [3] `0 ≤ C` is necessary (the set requires it; with `M` trivial every `C` bounds
  but `‖u‖ = 0`). [5] verified. SURVIVED.
- **L1.4** `opNorm_zero` — [RM] §1.1.1 *"`‖0‖ = 0`"*. Discharge: `le_antisymm (opNorm_le_bound _
  le_rfl (by simp)) (opNorm_nonneg _)`. Attacks: [2] trivial modules ✓. SURVIVED.
- **L1.5** `le_opNorm_of_bound` — [RM] §1.1.1 *"`‖u x‖ ≤ ‖u‖ ‖x‖` for any `u` admitting some uniform
  bound"*. Discharge: for `‖x‖ = 0` the hypothesis gives `‖u x‖ ≤ C * 0`, so both sides are `0`
  (seminormed `M`!); for `‖x‖ ≠ 0`, `‖u x‖ / ‖x‖` is a lower bound of the (nonempty: `max C 0` is in
  it) bound set, so `le_csInf` gives `‖u x‖ / ‖x‖ ≤ ‖u‖`, then `div_le_iff₀`. Attacks: [2] `‖x‖ = 0`
  with `x ≠ 0` (seminorm) handled explicitly ✓; `C < 0` forces `u = 0` on `M`, fine. [3] the
  existence hypothesis is necessary: over `ℤ_p` with the squared norm (L8.11) the identity has no
  bound and `‖u‖ = sInf ∅ = 0`, so `‖u x‖ ≤ 0 · ‖x‖` fails — the lemma is sharp. [5] `le_csInf`,
  `div_le_iff₀`, `max_le_iff` verified. SURVIVED.
- **L1.6** `norm_id_le` — [Mathlib] `norm_id_le : ‖ContinuousLinearMap.id 𝕜 E‖ ≤ 1 := opNorm_le_bound
  _ zero_le_one fun x => by simp`. Discharge: L1.3. Attacks: [2] trivial `M`: `‖id‖ = 0 ≤ 1` ✓ (and
  this is why `= 1` needs `Nontrivial M`, L2.8). SURVIVED.
- **L1.7** `opNorm_neg` — [RM] §1.1.1 *"`‖−u‖ = ‖u‖`"*; [Mathlib] `opNorm_neg f := by simp only
  [norm_def, neg_apply, norm_neg]`. Discharge: the same three rewrites. Attacks: [3] needs `Ring R`
  only for `-u` to exist (Mathlib's `ContinuousLinearMap.neg` instance) — stated in a `Ring`
  section. SURVIVED.
- **L1.8** `norm_map_le_div_mul_of_forall_norm_le` — the scaling trick. Lean: `(ϖ) (f : M →ₗ[R] N)
  (hε : 0 < ε) (h : ∀ x, ‖x‖ ≤ ε → ‖f x‖ ≤ C) (x) : ‖f x‖ ≤ C / (ε * ‖ϖ‖) * ‖x‖`. Source: [Sch]
  Prop 3.1 proof, quoted above (`schneider.txt:541–546`); [Buz07] `buzzard.txt:266–270`. Match: Schneider
  rescales `v` into `|a|^{m+2} < ‖v‖ ≤ |a|^{m+1}` with `ε = |a|` and gets the constant `|a|^{-2}`;
  with Layer 0's shell `ε‖ϖ‖ < ‖ϖⁿ • x‖ ≤ ε` the constant is `C / (ε‖ϖ‖)` — same argument, sharper
  bookkeeping. Discharge: `x = 0` by `map_zero`; else `obtain ⟨n, ⟨h₁, h₂⟩, -⟩ :=
  ϖ.existsUnique_zpow_norm_smul_mem_Ioc hε hx` [L0]; `h _ h₂` bounds `‖f (ϖⁿ • x)‖ = ‖ϖ‖ⁿ ‖f x‖`
  (`LinearMap.map_smul`, [L0] `norm_zpow_smul`); divide by `‖ϖ‖ⁿ > 0` (`zpow_pos`) and use
  `ε‖ϖ‖ < ‖ϖ‖ⁿ‖x‖` (`h₁`, again `norm_zpow_smul`) to get `‖ϖ‖^{-n} < ‖x‖/(ε‖ϖ‖)`; `0 ≤ C` from
  `h 0`. Attacks: [1] `lean_local_search` for a contradicting statement: none; [SRC]
  `01_OperatorNorm.le_opNorm` proves the same inequality inline (sorry-free). [2] `x = 0` ✓;
  `C = 0` gives `f = 0` on the ball hence everywhere ✓; `ε` huge ✓. [3] `hε` necessary (`ε = 0`
  says nothing); `NormOneClass R` is needed for `0 < ‖ϖ‖` ([L0] `norm_pos`); `IsTate` is not needed
  because `ϖ` is explicit. [4] no drift: [Sch]'s "`‖f(v)‖ ≤ 1` provided `‖v‖ ≤ |a|`" is our `h`
  with `C = 1`, `ε = |a|`. [5] all four [L0] names verified in `names2.lean`. SURVIVED.
- **L1.9** `exists_bound` — [JN] `jn.txt:522` (quoted above); [Sch] Prop 3.1 i ⇒ ii. Discharge:
  `obtain ⟨ϖ⟩ := IsTate.exists_pseudoUniformizer`; `Metric.continuousAt_iff` at `0` with `ε = 1`
  gives `δ > 0` with `‖x‖ < δ → ‖u x‖ < 1` (`map_zero`, `dist_zero_right`); apply L1.8 with
  `ε := δ / 2`, `C := 1` (closed half-ball inside the open ball). Attacks: [2] `δ` may be `> 1`,
  irrelevant. [3] `IsTate` necessary: L8.11 is the counterexample over `ℤ_p`. [5] `Metric.continuousAt_iff`
  verified. SURVIVED.
- **L1.10** `continuous_iff_exists_bound` — [RM] §1.1.2 *"a linear map is continuous if and only if
  it is bounded"*. Discharge: `⟨fun hf ↦ exists_bound ⟨f, hf⟩, fun ⟨C, hC⟩ ↦
  AddMonoidHomClass.continuous_of_bound f C hC⟩` (⚠ `LinearMap.continuous_of_bound` is **not** a
  Mathlib name at this pin; `AddMonoidHomClass.continuous_of_bound` is, verified). Attacks: [4] [Sch]
  Prop 3.1 is literally this iff. SURVIVED.
- **L1.11** `continuous_iff_exists_forall_norm_le` — [RM] §1.1.2 *"if and only if it is bounded on
  the unit ball (by the scaling trick)"*. Discharge: ⇒ via L1.10 (`C * 1`); ⇐ via L1.8 with `ε = 1`
  then `AddMonoidHomClass.continuous_of_bound`. Attacks: [2] `C < 0` impossible (`x = 0`). [3] closed
  unit ball, as the roadmap says. SURVIVED.
- **L1.12** `le_opNorm` — [RM] §1.1.2 *"hence `‖u x‖ ≤ ‖u‖ ‖x‖` for every `u : M →L[R] N`"*.
  Discharge: `le_opNorm_of_bound u (exists_bound u) x` (L1.5 + L1.9). Attacks: [3] `IsTate`
  necessary (L8.11). [5] two leaves. SURVIVED.
- **L1.13** `opNorm_le_div_of_forall_norm_le` — [RM] §1.1.2 (corrected, E9): the unit-ball bound
  controls `‖u‖` up to `‖ϖ‖⁻¹`. Lean: `‖u‖ ≤ C / (ε * ‖ϖ‖)`. Discharge: `opNorm_le_bound` with
  `0 ≤ C / (ε‖ϖ‖)` (`div_nonneg`, `0 ≤ C` from `h 0`) and L1.8 applied to `(u : M →ₗ[R] N)`.
  Attacks: [1] is the factor `‖ϖ‖⁻¹` sharp? E9's example: `M = ℚ_p` with `p^{1/2}|·|`, `u = id`,
  `‖u‖ = p^{-1/2}`, unit-ball sup `p^{-1}`, `‖ϖ‖⁻¹ = p`: `p^{-1/2} ≤ p · p^{-1}` ✓ with room; with
  `‖x‖' = p^{1-η}|x|`, `η → 0⁺`, the ratio `‖u‖ / sup` tends to `p` — sharp. [4] Mathlib's
  `opNorm_le_of_ball` has the same shape with `‖c‖ / ε`, `c` a scalar of norm `> 1`. SURVIVED.
- **L1.14** `norm_le_opNorm_of_norm_le_one` — the other half: `‖u x‖ ≤ ‖u‖ ‖x‖ ≤ ‖u‖`. Discharge:
  L1.12 + `mul_le_of_le_one_right (opNorm_nonneg u) hx`. SURVIVED (trivially).
- **L1.15** `opNorm_eq_iSup_div` — [Sch] Cor 3.2 `schneider.txt:538–541` (quoted above); [JN]
  `jn.txt:523` *"`|φ| = sup_{m ≠ 0} |φ(m)|·|m|⁻¹`"*. Lean: `‖u‖ = ⨆ x, ‖u x‖ / ‖x‖` (the ratio at
  `x = 0` is `0 / 0 = 0`, harmless). Discharge: `≤`: `opNorm_le_bound` with `C := ⨆ …`
  (`Real.iSup_nonneg`) and `‖u x‖ = (‖u x‖ / ‖x‖) * ‖x‖ ≤ (⨆ …) * ‖x‖` by `le_ciSup` (bounded above
  by `‖u‖` via L1.12 and `div_le_iff₀`); `≥`: `ciSup_le` (`Nonempty M` from `0`) with
  `div_le_iff₀`/`div_nonneg` cases on `‖x‖ = 0`. Attacks: [2] `M` trivial: both sides `0` ✓
  (`ciSup` over `{0}`). [3] `IsTate` needed for the `BddAbove` (otherwise `⨆` is junk `0` while
  `‖u‖` is also `0` — still equal, but the proof uses L1.12). [4] no drift: Schneider's sup over
  `v ≠ 0` equals ours since the extra term is `0`. SURVIVED.
- **L1.16** `norm_eq_opNorm` — [RM] §1.1.6 *"the scoped norm equals `ContinuousLinearMap.opNorm` on
  the nose"*. **Proved in the skeleton by `rfl`** (`names2.lean` confirmed the `rfl`). Attacks: [4]
  "on the nose" = definitional ✓. SURVIVED (done).

## §1.1.3–§1.1.6 The Banach module of operators (`Operator/Banach.lean`)

### Plain-English proof substrate

[Bel] `bellaiche.txt:1975–1981`: *"A morphism `φ : M → N` between two Banach `R`-modules is
continuous if and only if it is bounded, that is if there exists a constant `C > 0` such that
`|φ(m)| ≤ C|m|` for every `m` in `M`. In this case, the norm of `φ`, denoted `|φ|`, is defined as the
smallest constant `C` satisfying this condition. One evidently has `|φ'φ| ≤ |φ'||φ|` when
`φ : M → N` and `φ' : N → K` are continuous morphisms of Banach `R`-modules. We denote by
`Hom_R(M, N)` the `R`-module of continuous morphisms of `R`-modules from `M` to `N`. It is a Banach
`R`-module for the norm we just defined."* [Sch] Prop 3.3 `schneider.txt:551–588`: *"If `W` is a
Banach space so, too, is `L(V, W)`. Proof: Let `(fₙ)` be any Cauchy sequence in `L(V, W)`. …
`fₙ(v)`, for any `v ∈ V`, is a Cauchy sequence in `W`. By assumption the limit `f(v) := lim fₙ(v)`
exists in `W`. … `‖f(v)‖ = lim ‖fₙ(v)‖ ≤ (lim ‖fₙ‖) · ‖v‖` it follows from Prop. 3.1 that `f` is
continuous … `‖f − fₙ‖ ≤ sup_{m ≥ n} ‖f_{m+1} − f_m‖` shows that `f` indeed is the limit."* The
triangle inequality, submultiplicativity and the norm of the identity are L1.12 and L1.3; the
ultrametric inequality is the same with `max`; completeness is Schneider's argument verbatim
([SRC] `01_OperatorNorm.exists_lim_of_cauchySeq` is a sorry-free transcription). The ring and
scalar structures are Mathlib's `ContinuousLinearMap.ring` / `module` with the norm facts attached.
Sums of operators are then Mathlib's nonarchimedean summability on the ultrametric complete group
`M →L[R] N`, evaluated pointwise through the bounded additive map `u ↦ u x`. The Neumann series is
[BGR] 1.2.4/4–5 `bgr-3.7.md:135–139`: *"If `A` is complete, each element of the form `e = 1 − y`,
`y ∈ Ǎ`, is a unit in `A`. We have `e⁻¹ = Σ yⁿ = 1 + z`, where `z ∈ Ǎ`. … In a complete normed ring
`A`, the multiplicative group `E(A)` of units is open"* applied to the Banach ring `M →L[R] M`
(Mathlib's `Units.oneSub`, `Units.isOpen`), with the norms of `u` and `u⁻¹` from Layer 0's
`norm_one_sub_of_norm_lt_one` and `norm_tsum_geometric` in that ring.

### Leaves

- **L2.1** `opNorm_add_le` — [Bel] l. 1981; [Mathlib] `opNorm_add_le := (f + g).opNorm_le_bound
  (add_nonneg …) fun x => (norm_add_le_of_le (f.le_opNorm x) (g.le_opNorm x)).trans_eq (add_mul _ _ _).symm`.
  Discharge: the same with L1.3, L1.12. Attacks: [3] `IsTate` necessary (L1.12). SURVIVED.
- **L2.2** `opNorm_eq_zero_iff` — [Mathlib] `opNorm_zero_iff`. Discharge: `→`: `ext x`,
  `norm_le_zero_iff.1 ((le_opNorm u x).trans_eq (by rw [h, zero_mul]))`; `←`: L1.4. Attacks: [3]
  needs `NormedAddCommGroup N` (separation) — the section has it. SURVIVED.
- **L2.3** `instNormedAddCommGroup` — **complete in the skeleton** (`toMetricSpace` from
  `AddGroupNorm.toNormedAddCommGroup`, `dist_eq := rfl`; compiles). Attacks: [5] `names3.lean`
  synthesises `NormedAddCommGroup (M →L[R] N)`, `IsUltrametricDist`, `CompleteSpace`, `NormedRing`
  from the scoped instances ✓. SURVIVED (done).
- **L2.4** `opNorm_add_le_max` — [RM] §1.1.3 *"a complete ultrametric norm"*. Discharge:
  `opNorm_le_bound` with `max_nonneg`, and `‖(u + v) x‖ ≤ max ‖u x‖ ‖v x‖ ≤ max (‖u‖‖x‖) (‖v‖‖x‖)
  = max ‖u‖ ‖v‖ * ‖x‖` (`IsUltrametricDist.norm_add_le_max`, `max_le_max`, `max_mul_of_nonneg`).
  Attacks: [3] ultrametric `N` necessary, nothing on `M`. SURVIVED.
- **L2.5** `instIsUltrametricDist` — Discharge: `IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm`
  with L2.4 (verified name). SURVIVED.
- **L2.6** `instCompleteSpace` — [Sch] Prop 3.3 (quoted); [SRC] `exists_lim_of_cauchySeq`.
  Discharge: `Metric.complete_of_cauchySeq_tendsto`; for a Cauchy `u : ℕ → M →L[R] N`:
  `fun n ↦ u n x` is Cauchy (`Metric.cauchySeq_iff`, L1.12 on `u m - u n`), limit `v₀ x` by
  `cauchySeq_tendsto_of_complete`; `v₀` additive/`R`-linear by `tendsto_nhds_unique`; bounded by
  `‖u N₀‖ + 1` (`le_of_tendsto`); `v := LinearMap.mkContinuous …`; `‖u n - v‖ ≤ ε/2` eventually by
  `opNorm_le_bound` and `le_of_tendsto` on `‖(u n - u m) x‖`. Attacks: [2] `M` trivial ✓. [3]
  `CompleteSpace N` necessary; `CompleteSpace M` not used ✓ (not assumed). [5] all names verified;
  the [SRC] transcription is sorry-free. SURVIVED.
- **L2.7** `opNorm_comp_le` — [Bel] l. 1978 *"One evidently has `|φ'φ| ≤ |φ'||φ|`"*; [Mathlib]
  `opNorm_comp_le`. Discharge: `opNorm_le_bound` with `mul_nonneg`, `comp_apply`, L1.12 twice,
  `mul_assoc`. SURVIVED.
- **L2.8** `norm_id` — [RM] §1.1.3 *"`‖1‖ ≤ 1` with equality when `M ≠ 0`"*. Discharge:
  `le_antisymm norm_id_le`; pick `x ≠ 0` (`exists_ne 0`), `‖x‖ = ‖id x‖ ≤ ‖id‖ * ‖x‖` (L1.12),
  cancel `0 < ‖x‖`. Attacks: [2] `Nontrivial M` necessary (L1.6's note). [4] Mathlib states it with
  `NontrivialTopology E`; for a normed group that is `Nontrivial`. SURVIVED.
- **L2.9** `instNormedRing`, `instNormOneClass` — **complete in the skeleton** (Mathlib's pattern
  `{ toSeminormedAddCommGroup, ring with norm_mul_le := opNorm_comp_le }`). SURVIVED (done).
- **L2.10** `opNorm_smul_le` — [RM] §1.1.3; [Mathlib] `opNorm_smul_le`. Discharge: `opNorm_le_bound`,
  `smul_apply`, `norm_smul_le`, L1.12, `mul_assoc`. Attacks: [3] `NormedCommRing R`: forced by
  Mathlib's `ContinuousLinearMap.module` needing `SMulCommClass R R N` (`names.lean`: synthesises for
  `NormedCommRing`, not `NormedRing`). SURVIVED.
- **L2.11** `instIsBoundedSMul` — Discharge: `IsBoundedSMul.of_norm_smul_le opNorm_smul_le`. SURVIVED.
- **L2.12** `opNorm_smul_of_isMultiplicative` — [RM] §1.1.3 *"with equality for multiplicative `a`"*
  (E11: a multiplicative **unit**). Discharge: `le_antisymm (opNorm_smul_le _ _)`; `‖u‖ = ‖a⁻¹ • (a • u)‖
  ≤ ‖a⁻¹‖ ‖a • u‖ = ‖a‖⁻¹ ‖a • u‖` ([L0] `IsMultiplicative.norm_inv`, `smul_smul`, `Units.inv_mul`),
  then `le_inv_mul_iff₀` with [L0] `norm_pos`. Attacks: [1] E11's counterexample shows the
  non-unit statement is false, so the unit hypothesis is not over-specification. SURVIVED.
- **L2.13** `summable_of_tendsto_cofinite_zero` — [RM] §1.1.4 *"`∑' uᵢ` converges in operator norm"*.
  Discharge: `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero hu` with the instances
  `IsUltrametricDist.nonarchimedeanAddGroup` (L2.5) and `CompleteSpace` (L2.6). Attacks: [5] both
  names verified; the point of the leaf is that the instances compose. SURVIVED.
- **L2.14** `hasSum_apply` — [RM] §1.1.4 *"and pointwise"*. Discharge: `HasSum.map hu (AddMonoidHom.mk'
  (fun v ↦ v x) fun _ _ ↦ rfl) (AddMonoidHomClass.continuous_of_bound _ ‖x‖ fun v ↦ by rw [mul_comm];
  exact le_opNorm v x)`. Attacks: [3] needs L1.12 (Tate); `CompleteSpace N` not used here
  (section variable; `omit` at cleanup if the linter asks). SURVIVED.
- **L2.15** `tsum_apply` — Discharge: `(hasSum_apply hu.hasSum x).tsum_eq.symm`. SURVIVED.
- **L2.16** `isUnit_of_norm_one_sub_lt_one` — [RM] §1.1.5; [BGR] 1.2.4/4 (quoted). Discharge:
  `⟨Units.oneSub (1 - u) hu, by simp [Units.val_oneSub]⟩` (`sub_sub_cancel`); `HasSummableGeomSeries
  (M →L[R] M)` from `CompleteSpace` (L2.6 with `N := M`). Attacks: [2] `M` trivial: `‖1 - u‖ = 0 < 1`,
  `u = 0 = 1` is a unit ✓. SURVIVED.
- **L2.17** `norm_eq_one_of_norm_one_sub_lt_one` — [RM] §0.2.3 in the ring `M →L[R] M`. Discharge:
  `u = 1 - (1 - u)` and [L0] `NormedRing.norm_one_sub_of_norm_lt_one hu` with the instances L2.5
  (ultrametric, needs `IsUltrametricDist M`), L2.9 (`NormOneClass`, needs `Nontrivial M`). Attacks:
  [2] `Nontrivial M` necessary (trivial `M`: `‖u‖ = 0`). SURVIVED.
- **L2.18** `norm_inv_eq_one_of_norm_one_sub_lt_one` — [RM] §1.1.5 *"`‖u⁻¹‖ = 1`"*. Discharge:
  `(u⁻¹ : _) = ((Units.oneSub (1 - u) hu)⁻¹ : _)` by `Units.inv_unique` (both have value `u`,
  `Units.val_oneSub`, `sub_sub_cancel`), and `((Units.oneSub t h)⁻¹ : R) = ∑' n, t ^ n` is `rfl`
  (`Units.oneSub`'s `inv` field); then [L0] `NormedRing.norm_tsum_geometric hu`. Attacks: [5]
  `Units.inv_unique`, `Units.val_oneSub`, `norm_tsum_geometric` verified. SURVIVED.
- **L2.19** `isOpen_setOf_isUnit` — [BGR] 1.2.4/5 (quoted); Discharge: `Units.isOpen`. SURVIVED.
- **L2.20** `instNormedAddCommGroup_eq` — [RM] §1.1.6. Discharge: Mathlib's instance is
  `toNormedAddCommGroup := NormedAddCommGroup.ofSeparation …` over `toSeminormedAddCommGroup`, whose
  metric is `.replaceUniformity (seminorm.toSeminormedAddCommGroup.toPseudoMetricSpace) uniformity_eq_seminorm`
  (`Mathlib/Analysis/Normed/Operator/Basic.lean:379–383`): same `dist`, a propositionally equal
  uniformity. Proof plan: a private `NormedAddCommGroup`-extensionality lemma — for `i j :
  NormedAddCommGroup E` with `i.toAddCommGroup = j.toAddCommGroup`, `∀ x, ‖x‖ᵢ = ‖x‖ⱼ` and
  `∀ x y, distᵢ x y = distⱼ x y`, `cases i; cases j`, substitute the three equalities (`funext`,
  `MetricSpace.ext`), `rfl`; apply it with norms equal by L1.16 (`rfl`) and `dist` equal by both
  `dist_eq`s. Attacks: [1] `NormedAddCommGroup.ext` is **absent** from Mathlib at this pin
  (`names.lean`), so the helper is needed; `MetricSpace.ext`, `PseudoMetricSpace.ext` present. [3]
  the two `AddCommGroup` fields are literally `ContinuousLinearMap.addCommGroup` on both sides ✓.
  [4] "the two norms agree on the nose" is L1.16; this leaf is the instance-level consequence, which
  is what makes "every lemma of clauses 1–5 is either Mathlib's or reduces to it" usable. SURVIVED.

## §1.2.1–§1.2.2 The open mapping theorem (`Operator/OpenMapping.lean`)

### Plain-English proof substrate

[Bel] `bellaiche.txt:1983–1989`: *"The Open Mapping Theorem states that every continuous
surjective map between Banach `R`-modules is open. It is proven exactly as in the case of real
Banach spaces, using the Baire category theorem, see Wikipedia or any standard textbook of
functional analysis – or see [22, Théorème 1, Chapitre 1, §3.3] for a general proof valid in our
case. The open mapping theorem implies that if `f : M → N` is a continuous surjective map of
`R`-modules, there exists a constant `c > 0` such that for every `n` in `N` we can find `m ∈ M` with
`f(m) = n` and `|m| ≤ c|n|`."* [JN] `jn.txt:525`: *"The open mapping theorem holds in this context;
see e.g. [Hub94, Lemma 2.4(i)]."* [Lud] `ludwig.txt:226–228`: *"the open mapping theorem, which
says that for a Banach–Tate ring `A` and Banach `A`-modules `M` and `N`, any surjective continuous
`A`-linear map `φ : M → N` is open (see [22, Theorem II.4.1.1.])."* The "standard textbook proof"
is Mathlib's `exists_approx_preimage_norm_le` + `exists_preimage_norm_le`
(`Mathlib/Analysis/Normed/Operator/Banach.lean:81–225`): *"by Baire's theorem, there exists a ball in
`E` whose image closure has nonempty interior. Rescaling everything, it follows that any `y ∈ F` is
arbitrarily well approached by images of elements of norm at most `C * ‖y‖`. … starting from `y`,
we want an exact preimage of `y`. Let `g y` be the approximate preimage of `y` given by the first
step, and `h y = y − f(g y)` the part that has no preimage yet. We will iterate this process … Then
`u` is a converging series, and by design the sum of the series is a preimage of `y`. This uses
completeness of `E`."* The only field-specific step is `rescale_to_shell hc' (half_pos εpos) hy`,
which Layer 0's `existsUnique_zpow_norm_smul_mem_Ioc (half_pos εpos) hy` replaces (shell
`(ε‖ϖ‖/2, ε/2]`); [SRC] `01_OperatorNorm.exists_approx_preimage_norm_le` / `exists_preimage_norm_le`
is this transport, sorry-free. Openness and the quotient map are Mathlib's two corollaries. For
§1.2.2, [Sch] Cor 8.7 `schneider.txt:2373–2375`: *"Any continuous linear bijection between two
`K`-Fréchet spaces is a topological isomorphism"* is the OMT applied to a bijection (the preimage
of `y` is `e.symm y`), and [BGR] 3.7.3/4 `bgr-3.7.md:68`: *"A continuous `k`-linear map `φ : X → Y`
between `k`-Banach spaces is strict if and only if `φ(X)` is closed in `Y`"* — the "if" direction is
Cor 8.7 applied to the induced bijection `X / ker φ → φ(X)` between the Banach spaces `X / ker φ`
([Sch] Prop 8.3 `schneider.txt:2281`: *"Let `V` be a Fréchet (resp. Banach) space, and let `U ⊆ V`
be a closed vector subspace; then `V/U` with the quotient topology is a Fréchet (resp. Banach) space
as well"*) and `φ(X)`.

### Leaves

- **L3.1** `exists_approx_preimage_norm_le` — [Mathlib] docstring quoted above. Lean: `∃ C ≥ 0,
  ∀ y, ∃ x, dist (u x) y ≤ 1 / 2 * ‖y‖ ∧ ‖x‖ ≤ C * ‖y‖`. Discharge (transcribe
  `Banach.lean:92–152` and [SRC]): `⋃ n, closure (u '' ball 0 n) = univ` (surjectivity,
  `exists_nat_gt`); `nonempty_interior_of_iUnion_of_closed` gives `n, a, ε`; for `y ≠ 0` the shell
  `d := ϖ ^ j` with `‖d • y‖ ∈ (ε‖ϖ‖/2, ε/2]`; `a + d • y ∈ ball a ε` and `a ∈ ball a ε` give
  `x₁, x₂ ∈ ball 0 n` with `u x₁`, `u x₂` within `δ := ‖d • y‖ / 4` (`Metric.mem_closure_iff`);
  `x := ϖ ^ (-j) • (x₁ - x₂)`; `‖u x - y‖ = ‖ϖ‖^{-j} ‖u (x₁ - x₂) - d • y‖ ≤ ‖ϖ‖^{-j} · 2δ = ‖y‖ / 2`
  and `‖x‖ ≤ ‖ϖ‖^{-j} · 2n ≤ 4n / (ε‖ϖ‖) · ‖y‖` ([L0] `norm_zpow_smul`, `zpow_neg`,
  `Units.val_pow_eq_pow_val`). Constant `C := 4n / (ε‖ϖ‖)`. Attacks: [1] none; [SRC] is the
  sorry-free witness. [2] `y = 0`: `x = 0` ✓; `N` trivial: Baire needs `Nonempty N` (from `0`) ✓.
  [3] `CompleteSpace N` necessary (Baire); `CompleteSpace M` **not** used here (not assumed);
  `CompleteSpace R` never used; ultrametricity never used. [4] Mathlib's constant is
  `(ε/2)⁻¹ * ‖c‖ * 2 * n`; ours differs by the scalar bookkeeping only. [5] `nonempty_interior_of_iUnion_of_closed`,
  `Metric.mem_closure_iff`, `mem_interior_iff_mem_nhds`, `Metric.mem_nhds_iff` verified. SURVIVED.
- **L3.2** `exists_preimage_norm_le` — [Bel] l. 1986–1989 (quoted); [RM] §1.2.1. Discharge:
  transcribe `Banach.lean:162–225` verbatim (it uses only L3.1, `summable_geometric_two`,
  `norm_tsum_le_tsum_norm`, `Summable.of_norm`, `HasSum.tendsto_sum_nat`, `tendsto_nhds_unique`,
  `squeeze_zero`, `tendsto_pow_atTop_nhds_zero_of_lt_one`; all verified). Attacks: [2] `C = 2C'+1
  > 0` ✓. [3] `CompleteSpace M` necessary (the series). [4] literal. SURVIVED.
- **L3.3** `isOpenMap`, **L3.4** `isQuotientMap` — [Sch] Prop 8.6 (quoted); [Mathlib]
  `Banach.lean:229–252`. Discharge: transcribe (`Metric.isOpen_iff`, `Metric.mem_ball`, `dist_eq_norm`);
  `IsOpenMap.isQuotientMap f.continuous surj`. SURVIVED.
- **L3.5** `continuous_symm` — [Sch] Cor 8.7 (quoted); [Mathlib] `LinearEquiv.continuous_symm`.
  Discharge: `u : M →L[R] N := ⟨e, he⟩`; `obtain ⟨C, -, hC⟩ := exists_preimage_norm_le u e.surjective`;
  for `y`, the `x` with `u x = y` is `e.symm y` (`e.injective`), so `‖e.symm y‖ ≤ C * ‖y‖`;
  `AddMonoidHomClass.continuous_of_bound e.symm C`. Attacks: [3] both completenesses necessary
  (OMT). SURVIVED.
- **L3.6** `toContinuousLinearEquivOfContinuous`, `continuousLinearEquivOfBijective` + `coe` lemmas —
  **complete in the skeleton** (built on L3.5). SURVIVED (done).
- **L3.7** `norm_quotKerEquivRange_apply_le` — [Sch] Prop 8.3 / [BGR] 3.7.3/4 substrate; the
  quotient norm is `inf` over the class (Mathlib `Submodule.Quotient.norm_mk_lt`). Lean:
  `‖(quotKerEquivRange u x : N)‖ ≤ ‖u‖ * ‖x‖`. Discharge: `le_of_forall_pos_lt_add`; for `ε > 0`,
  `Submodule.Quotient.norm_mk_lt x hε` gives `m` with `mk m = x`, `‖m‖ < ‖x‖ + ε`;
  `quotKerEquivRange_apply_mk` turns the LHS into `‖u m‖ ≤ ‖u‖‖m‖` (L1.12); conclude with
  `mul_le_mul_of_nonneg_left`. Attacks: [2] `x = 0` ✓. [3] no completeness needed (not assumed);
  `NormedCommRing R` only because the section is shared with L3.8–L3.9 (a cleanup may relax it).
  SURVIVED.
- **L3.8** `exists_norm_quotKerEquivRange_symm_le` — [RM] §1.2.2 *"the quotient norm and the subspace
  norm are bounded-equivalent"*; [BGR] 3.7.3/4 (quoted). Discharge: `haveI : IsClosed (ker u) :=
  u.isClosed_ker` (so `M ⧸ ker u` is a `NormedAddCommGroup`, complete by
  `Submodule.Quotient.completeSpace`); `haveI := hu.completeSpace_coe`; `ū : (M ⧸ ker u) →L[R] range u
  := LinearMap.mkContinuous (quotKerEquivRange u) ‖u‖ (by simpa using L3.7)`; `exists_preimage_norm_le ū
  (quotKerEquivRange u).surjective` gives `C`; injectivity identifies the preimage with `.symm y`.
  Attacks: [3] `IsBoundedSMul R (M ⧸ ker u)` needs `SeminormedCommRing` scalars in Mathlib
  (`names.lean`), hence `NormedCommRing R` for this section — not over-specification but an API
  limit, recorded. [5] `Submodule.Quotient.{normedAddCommGroup, completeSpace, instIsBoundedSMul}`,
  `ContinuousLinearMap.isClosed_ker`, `IsClosed.completeSpace_coe` verified. SURVIVED.
- **L3.9** `quotKerEquivRangeL` (the `by sorry` is the continuity of `quotKerEquivRange u`) —
  Discharge: `AddMonoidHomClass.continuous_of_bound _ ‖u‖ (by simpa using L3.7)` after unfolding the
  coercion to `range u`. SURVIVED.

## §1.2.3 The closed graph theorem (`Operator/ClosedGraph.lean`)

### Plain-English proof substrate

[Sch] Prop 8.5 `schneider.txt:2322–2325`: *"Let `f : V → W` be a linear map from a barrelled locally
convex `K`-vector space (e.g., a Fréchet space) `V` into a `K`-Fréchet space `W`; if the graph
`Γ(f)` is closed then the map `f` is continuous."* Schneider proves 8.5 directly and deduces 8.6
from it; Mathlib (and this board) go the other way, `Banach.lean:532–560`: *"The closed graph theorem:
a linear map between two Banach spaces whose graph is closed is continuous"*, proof: the graph is a
closed, hence complete, submodule of `E × F`; `φ : E ≃ₗ g.graph` from `LinearEquiv.ofLeftInverse`
(`Prod.fst` is a left inverse of `x ↦ (x, g x)`) and `graph_eq_range_prod`; `ψ := φ.symm.toContinuousLinearEquivOfContinuous
continuous_subtype_val.fst`; `g = Prod.snd ∘ val ∘ ψ.symm` is continuous. The sequential form
`continuous_of_seq_closed_graph` is `IsSeqClosed.isClosed` applied to the graph.

### Leaves

- **L4.1** `continuous_of_isClosed_graph` — Discharge: transcribe `Banach.lean:532–543` with
  `toContinuousLinearEquivOfContinuous` (L3.6) in place of Mathlib's; instances:
  `IsBoundedSMul R (M × N)` (Mathlib `Prod.instIsBoundedSMul`, verified), `CompleteSpace (M × N)`,
  `IsBoundedSMul R f.graph` ([L0] `Submodule.instIsBoundedSMul`), `CompleteSpace f.graph`
  (`completeSpace_coe_iff_isComplete.mpr hf.isComplete`). Attacks: [3] no ultrametric, no
  `CompleteSpace R` (not assumed) ✓; both module completenesses necessary. [5] `LinearEquiv.ofLeftInverse`,
  `LinearMap.graph_eq_range_prod`, `completeSpace_coe_iff_isComplete` verified. SURVIVED.
- **L4.2** `continuous_of_seq_closed_graph` — Discharge: transcribe `Banach.lean:548–560`
  (`IsSeqClosed.isClosed`, `continuous_fst.tendsto`, `continuous_snd.tendsto`). SURVIVED.

## §1.2.4 Banach–Steinhaus (`Operator/BanachSteinhaus.lean`)

### Plain-English proof substrate

[Sch] Prop 6.15 `schneider.txt:1683–1690`: *"If `V` is barrelled then any bounded subset
`H ⊆ L_s(V, W)` is equicontinuous. Proof: Let `M ⊆ W` be an open lattice and consider the
`o`-submodule `L := ⋂_{f ∈ H} f⁻¹(M)` of `V`. We have to show that `L` is open. Since `L` obviously is
closed it suffices to check that `L` is a lattice."* with Example 2 `schneider.txt:1715–1718`: *"If `V`
is metrizable and is complete with respect to a defining metric (e.g., `V` is a Banach space) then `V`
is barrelled. Proof: By Baire's theorem … there must therefore exist an `n ∈ ℕ` such that `aⁿL` and
consequently `L` has a nonempty interior."* In normed terms: the closed sets `Aₙ := ⋂ᵢ {x | ‖uᵢ x‖ ≤ n}`
cover `M` (pointwise boundedness), Baire gives `Aₙ ⊇ ball x₀ ε`, so for `‖y‖ ≤ ε/2` every
`‖uᵢ y‖ = ‖uᵢ (x₀ + y) − uᵢ x₀‖ ≤ 2n`, and the scaling trick (L1.13 with `ε/2`) bounds every `‖uᵢ‖`
by `2n / ((ε/2) ‖ϖ‖)`. Mathlib's current `banach_steinhaus` routes through barrelled spaces exactly as
Schneider does; the direct Baire form above is Mathlib's pre-2023 proof. A pointwise limit of
operators is pointwise bounded (a convergent real sequence is bounded), hence uniformly bounded,
hence its limit is bounded by the same constant — Mathlib's `continuousLinearMapOfTendsto`.

### Leaves

- **L5.1** `banach_steinhaus` — Discharge: `obtain ⟨ϖ⟩ := IsTate.exists_pseudoUniformizer`;
  `A n := ⋂ i, {x | ‖u i x‖ ≤ n}` closed (`isClosed_iInter`, `isClosed_le (continuous_norm.comp
  (u i).continuous) continuous_const`), `⋃ n, A n = univ` (`exists_nat_ge`);
  `nonempty_interior_of_iUnion_of_closed` → `n, x₀, ε`; for `‖y‖ ≤ ε/2`, `x₀ + y ∈ ball x₀ ε`
  so `‖u i y‖ ≤ ‖u i (x₀ + y)‖ + ‖u i x₀‖ ≤ 2n` (`map_add`, `norm_sub_le`); L1.13 with
  `ε := ε/2`, `C := 2n` gives `‖u i‖ ≤ 2n / (ε/2 * ‖ϖ‖)` for every `i`. Attacks: [2] `ι` empty:
  any `C` ✓; `M` trivial ✓. [3] `CompleteSpace M` necessary (Baire), `N` arbitrary, no ultrametric
  (a `max` would give `n` instead of `2n`, immaterial). [4] Schneider's `L` is our `A₁` after scaling;
  the normed proof is the one Mathlib used before its barrelled refactor. [5] names verified.
  SURVIVED.
- **L5.2** `continuous_of_tendsto` — [RM] §1.2.4 *"a pointwise limit of continuous linear maps from
  a Banach module is continuous"*. Discharge: pointwise bounded by `(h x).norm.bddAbove_range`
  (`Filter.Tendsto.bddAbove_range`, verified); L5.1 gives `C`; `‖f x‖ ≤ C * ‖x‖` by `le_of_tendsto
  (h x).norm (Eventually.of_forall fun n ↦ (le_opNorm (u n) x).trans (mul_le_mul_of_nonneg_right
  (hC n) _))`; `AddMonoidHomClass.continuous_of_bound`. Attacks: [3] stated for sequences (`atTop`
  on `ℕ`): a net convergent along a general filter need not be pointwise bounded, so the sequence
  form is the honest one (Mathlib's general-filter version uses eventual bounds). SURVIVED.

## §1.2.5 Maps out of a finite free module (`Operator/Pi.lean`)

### Plain-English proof substrate

[Sch] Prop 4.13 Step 1 `schneider.txt:909–913`: *"The topology defined by the norm `‖ ‖` is finer
than any other locally convex topology on `Kⁿ`. To see this let `e₁, …, eₙ` denote the standard
basis of `Kⁿ` and let `q` be an arbitrary seminorm on `Kⁿ`. We then have `q(v) ≤ (max_{1≤i≤n} q(eᵢ))
· ‖v‖` for any `v ∈ V` which amounts to our claim."* [BGR] 3.7.3/2 proof `bgr-3.7.md:57–59`:
*"Since addition and scalar multiplication are continuous operations in normed modules, both maps `π`
and `φ' ` are continuous."* With `v = Σ vᵢ eᵢ` and an ultrametric target, `‖f v‖ = ‖Σ vᵢ • f eᵢ‖ ≤
maxᵢ ‖vᵢ‖ ‖f eᵢ‖ ≤ ‖v‖ · maxᵢ ‖f eᵢ‖`; conversely `‖f eᵢ‖ ≤ ‖f‖ ‖eᵢ‖ = ‖f‖`.

### Leaves

- **L6.1** `norm_map_le_iSup_mul` — Discharge: `x = ∑ i, x i • Pi.single i 1`
  (`Finset.univ_sum_single`, `Pi.single_smul`, `smul_eq_mul`, `mul_one`; or `pi_eq_sum_univ`),
  `map_sum`, `map_smul`, then `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg` with
  `C := (⨆ i, ‖f (Pi.single i 1)‖) * ‖x‖` (`mul_nonneg (Real.iSup_nonneg …) (norm_nonneg _)`) and
  termwise `‖x i • f eᵢ‖ ≤ ‖x i‖ ‖f eᵢ‖ ≤ ‖x‖ · ⨆` (`norm_smul_le`, `norm_le_pi_norm`, `le_ciSup
  (Set.finite_range _).bddAbove`, `mul_le_mul`). Attacks: [2] `ι` empty: `⨆ = 0`
  (`Real.iSup_of_isEmpty`), `x = 0`, `f x = 0` ✓. [3] ultrametric `M` necessary for the constant
  (E17); `NormOneClass` not needed (not assumed). [4] Schneider's `max q(eᵢ)` is our `⨆`. [5] all
  names verified in `names3.lean`. SURVIVED.
- **L6.2** `continuous_pi` — Discharge: `AddMonoidHomClass.continuous_of_bound f _ (norm_map_le_iSup_mul f)`.
  SURVIVED.
- **L6.3** `opNorm_pi_eq` — Discharge: `le_antisymm (opNorm_le_bound _ (Real.iSup_nonneg …)
  (norm_map_le_iSup_mul u))`; for `≥`: `Nonempty ι` case: `ciSup_le fun i ↦ (le_opNorm_of_bound u
  ⟨_, norm_map_le_iSup_mul u⟩ _).trans_eq (by rw [Pi.norm_single, norm_one, mul_one])`; `IsEmpty ι`
  case: `Real.iSup_of_isEmpty` + `opNorm_nonneg`. Attacks: [3] `NormOneClass R` necessary for
  `‖Pi.single i 1‖ = 1`; no `IsTate` needed (L1.5 suffices) ✓. SURVIVED.

## §1.4 Finitely generated modules (`Operator/Finite.lean`)

### Plain-English proof substrate

[Buz07] Lemma 2.2 `buzzard.txt:201–210`: *"If `M` is a Banach `A`-module, and `P` is a finite Banach
`A`-module, then any abstract `A`-module homomorphism `φ : P → M` is continuous. Proof. Let
`π : Aʳ → P` be a surjection of `A`-modules, and give `Aʳ` its usual Banach `A`-module norm. Then `π`
is open by the Open Mapping Theorem, and `φπ` is bounded and hence continuous. So `φ` is also
continuous."* ([Lud] Lemma 2.14 `ludwig.txt:231–236` restates it over a Banach–Tate ring.) In
bounds: `π` continuous by L6.2, OMT gives `‖a‖ ≤ C‖π a‖` for a preimage, and `‖φ p‖ = ‖(φ∘π) a‖ ≤
(⨆ ‖(φ∘π) eᵢ‖) · C · ‖p‖`. No Noetherian hypothesis. [BGR] 3.7.3/3 `bgr-3.7.md:60–63`: *"Each
finite `A`-module `M` can be provided with a complete `A`-module norm. All such norms are equivalent.
Proof. We only have to prove the existence of such a norm. Take any `A`-linear epimorphism
`π : Aⁿ → M`. Since `Aⁿ ∈ 𝔐_A`, the kernel `ker π` is closed. The residue norm on `Aⁿ/ker π` gives
rise to a complete `A`-module norm on `M`."* — uniqueness is Lemma 2.2 applied to the identity
between two norms, existence is closedness of `ker π`, which is [BGR] 3.7.2/1 `bgr-3.7.md:27–33`:
*"Let `A` be a `k`-Banach algebra and let `M` be a normed `A`-module such that the completion `M̂` of
`M` is a finite `A`-module. Then `M` is complete. Proof. There are elements `x₁, …, xₙ ∈ M̂` such that
the homomorphism `π : Aⁿ → M̂` defined by `π(a₁, …, aₙ) := Σ aᵢ xᵢ` is surjective. By BANACH's
Theorem, `π` is open, and therefore `Σ Ǎ xᵢ = π(Ǎⁿ)` is a neighborhood of `0` in `M̂`. Since `M` is
dense in `M̂`, we have `x_ν ∈ M + Σ_{μ=1}^{n} Ǎ x_μ` for `ν = 1, …, n`. Now NAKAYAMA's Lemma 1.2.4/6
yields `M = M̂`."* and `bgr-3.7.md:35–37`: *"As an immediate consequence of this proposition, we have
that all submodules of a Noetherian complete normed module over a Banach algebra `A` are closed."*
Nakayama is [BGR] 1.2.4/6 `bgr-3.7.md:142–150`: *"Let `A` be complete and let `M` be an `A`-module.
Let `N` be a submodule of `M` such that there are elements `x₁, …, xₙ` in `M` with the property:
`M ⊂ N + Σ Ǎ x_μ`. Then `N = M`."*, which [RAG] already derives from Mathlib's
`Submodule.le_of_le_smul_of_le_jacobson_bot` over the unit ball `A°` with `𝔫 ≤ jacobson ⊥` ([L0]
`openUnitBallIdeal_le_jacobson_bot`), avoiding BGR's determinant. [JN] `jn.txt:526–531` licenses the
transfer: *"Let `R` be a Noetherian Banach–Tate ring. The results of [BGR84, §3.7.2] hold in the
context of Banach–Tate rings with the same proofs (thanks to the open mapping theorem), so `R` being
Noetherian is equivalent to all ideals being closed. Moreover, the results of [BGR84, §3.7.3] hold
for Noetherian Banach–Tate rings with the same proofs. In particular, any finitely generated
`R`-module carries a canonical complete topology, and any abstract `R`-linear map between two
finitely generated `R`-modules is continuous and strict with respect to the canonical topology."*
[Lud] Remark 2.25 `ludwig.txt:351–358` records Bellaïche's alternative (*"Banach `K`-algebras `A`
with the property that every finitely generated submodule of an ONable Banach `A`-module is closed
([4, Hypothesis 3.1.8])"*), which is why §1.4.3's counterexample matters (L8.14).

### Leaves

- **L7.1** `exists_bound_of_finite` — [Buz07] Lemma 2.2 (quoted). Discharge:
  `obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R P`; `πL : (Fin n → R) →L[R] P := ⟨π, continuous_pi π⟩`;
  `obtain ⟨C, -, hC⟩ := exists_preimage_norm_le πL hπ` (needs `CompleteSpace (Fin n → R)` from
  `CompleteSpace R`, `CompleteSpace P`); `C' := (⨆ i, ‖(φ ∘ₗ π) (Pi.single i 1)‖) * C`; for `p`,
  take `a` with `π a = p`, `‖a‖ ≤ C‖p‖`: `‖φ p‖ = ‖(φ ∘ₗ π) a‖ ≤ (⨆ …) ‖a‖` (L6.1 into the
  ultrametric `M`) `≤ C' ‖p‖`. Attacks: [2] `P = 0` (`n = 0`) ✓. [3] `IsUltrametricDist M` **was
  missing from the first skeleton** and is necessary for L6.1's constant — added (`plan.md`
  decision 3); `IsUltrametricDist P` for `continuous_pi π`; `CompleteSpace R` for the domain of the
  OMT; `IsTate R`, `CompleteSpace P` for the OMT. [4] Buzzard's "`π` is open" is our quantitative
  preimage bound — same content. [5] `Module.Finite.exists_fin'` verified. SURVIVED.
- **L7.2** `continuous_of_finite` — Discharge: L7.1 + `AddMonoidHomClass.continuous_of_bound`.
  SURVIVED.
- **L7.3** `NormedRing.forall_mem_of_forall_exists_eq_add_sum_smul_of_norm_lt_one` — [BGR] 1.2.4/6
  (quoted); [RAG] `Ideal.forall_mem_of_forall_exists_eq_add_sum_mul_of_norm_lt_one` (the ideal case,
  sorry-free, same proof). Discharge: `N' := Submodule.span (unitClosedBall R) (Set.range x)`,
  `N₀ := N.restrictScalars (unitClosedBall R)` (instances `Subsemiring.instModuleSubtypeMem`,
  `Submonoid.instIsScalarTowerSubtypeMem`, verified); `N' ≤ N₀ ⊔ openUnitBallIdeal R • N'`
  (`Submodule.span_le`, `Submodule.add_mem_sup`, `Submodule.sum_mem`, `Submodule.smul_mem_smul` with
  `c j • x j = (⟨c j, _⟩ : unitClosedBall R) • x j` by `rfl`); `Submodule.le_of_le_smul_of_le_jacobson_bot
  (Submodule.fg_span (Set.finite_range x)) openUnitBallIdeal_le_jacobson_bot hle`; apply to
  `Submodule.subset_span ⟨i, rfl⟩`. Attacks: [3] needs `NormedCommRing R`, `IsUltrametricDist R`,
  `CompleteSpace R`, `NormOneClass R` (the [L0] Jacobson lemma's hypotheses, verified signature);
  nothing on `M` beyond being a normed module ✓ (section without `CompleteSpace M`). [4] BGR's
  `Ǎ` (topologically nilpotent) is replaced by the open unit ball `{‖c‖ < 1} ⊆ Ǎ` — a *weaker*
  hypothesis on the coefficients, hence a stronger lemma than needed; what L7.5 produces is
  `‖c‖ < 1` ✓. SURVIVED.
- **L7.4** `NormedRing.exists_forall_exists_eq_sum_smul_norm_le` — [BGR] 3.7.2/1 proof, first half
  (quoted: *"By BANACH's Theorem, `π` is open"*); [RAG] `Ideal.exists_forall_exists_eq_sum_mul_norm_le`.
  Discharge: `πl : (Fin n → R) →ₗ[R] J := { toFun := fun a ↦ ⟨∑ i, a i • x i, J.sum_mem …⟩, … }`
  (membership from `hx ▸ Submodule.subset_span`), continuous by L6.2 (`J` ultrametric as a subtype
  of `M`), surjective by `Submodule.mem_span_range_iff_exists_fun`; `haveI := hJ.completeSpace_coe`;
  OMT gives `C`; `norm_le_pi_norm a i`. Attacks: [3] `CompleteSpace M` necessary (for `J`);
  `CompleteSpace R` for `Fin n → R`. [5] verified. SURVIVED.
- **L7.5** `Submodule.isClosed_of_fg_topologicalClosure` — [BGR] 3.7.2/1 (quoted), second half;
  [RAG] `Ideal.isClosed_of_fg_closure` (same proof for ideals, sorry-free). Discharge:
  `J := N.topologicalClosure`, closed (`Submodule.isClosed_topologicalClosure`), generators from
  `Submodule.fg_iff_exists_fin_generating_family.1 hfg`; `C` from L7.4; for each `i`,
  `x i ∈ closure N` (`Submodule.topologicalClosure_coe`), so `Metric.mem_closure_iff` gives
  `y ∈ N` with `dist (x i) y < C⁻¹`; L7.4 on `x i - y ∈ J` gives coefficients `a` with
  `‖a j‖ ≤ C‖x i - y‖ < 1`; L7.3 gives `x i ∈ N`; hence `J = span ≤ N` and
  `isClosed_of_closure_subset`. Attacks: [2] `N = ⊥`, `N = ⊤` ✓. [4] BGR's `M`, `M̂` are our `N`,
  `J`; "dense" is `N ≤ J` with `J = closure N` ✓. [5] verified. SURVIVED.
- **L7.6** `Submodule.isClosed_of_isNoetherianRing` — [RM] §1.4.2; [BGR] l. 35–37 (quoted); [JN]
  l. 526–531. Discharge: `isNoetherian_of_isNoetherianRing_of_finite R M` then
  `IsNoetherian.noetherian N.topologicalClosure` and L7.5. Attacks: [3] all of `IsNoetherianRing R`,
  `Module.Finite R M`, `CompleteSpace M` necessary: L8.14 (non-Noetherian, `M = R`) and the
  roadmap's §1.4.3 warning. [4] Fresnel–van der Put 1.2.3 is cited by [RM]; its text is not to hand,
  and BGR 3.7.2/1 (whose transcription [RAG] already contains) is the same statement in BGR's
  numbering — recorded, not a drift. SURVIVED.
- **L7.7** `Ideal.isClosed_of_isTate_of_isNoetherianRing` — [Buz07] `buzzard.txt:173`; [BGR]
  3.7.2/2. Discharge: `Submodule.isClosed_of_isNoetherianRing (M := R) I` (`Module.Finite R R`
  instance). Attacks: [4] the field-scalar [RAG] `Ideal.isClosed_of_isNoetherianRing K` becomes a
  special case through [L0] `isTate_of_normedAlgebra` — noted for a later consolidation, not acted on.
  SURVIVED.
- **L7.8** `Module.Finite.exists_surjective_isClosed_ker` — [BGR] 3.7.3/3 (quoted); [RM] §1.4.1.
  Discharge: `Module.Finite.exists_fin'` and L7.6 for `M := Fin n → R` (`IsUltrametricDist (Fin n → R)`
  from `IsUltrametricDist R`, `CompleteSpace`, `Module.Finite R (Fin n → R)` instances). Attacks:
  [2] `n = 0` ✓. [3] `P` carries no topology — correct: the statement *produces* the Banach structure.
  SURVIVED.

## Examples (`Operator/Examples.lean`)

### Plain-English proof substrate

Each example is the roadmap's, quoted at its leaf; the two counterexamples are planner-constructed
with [RM]'s clause as the source (as Layer 0's `L1Pair` was). E10: for `‖1‖ = 1`,
`‖a‖ = ‖a · 1‖ ≤ ‖mulLeft a‖ · ‖1‖ = ‖mulLeft a‖ ≤ ‖a‖`. The quotient map `(x, y) ↦ x + ϖ y` has
`‖x + ϖ y‖ ≤ max(‖x‖, ‖ϖ‖‖y‖) ≤ ‖(x, y)‖` (ultrametric, `‖ϖ‖ ≤ 1`), preimage `(n, 0)` of norm
`‖n‖`, and `n = 1` forces `C ≥ 1`. On `ℚ_p`, `p • id` is a bijection whose inverse `p⁻¹ • id` has
norm `‖p⁻¹‖ = p`. On `ℤ_p` with `‖x‖² `: ultrametric (`max(a, b)² = max(a², b²)`), a normed
`ℤ_p`-module (`‖r‖² ≤ ‖r‖` as `‖r‖ ≤ 1`), the identity to `ℤ_p` is continuous (`‖x‖ < δ ⇐ ‖x‖² < δ²`)
and unbounded (`‖pⁿ‖ = p^{-n} ≤ C p^{-2n}` fails for `n` large). In `ℓ^∞(ℕ, ℚ_p)`, `a = (pⁿ)`,
`c = (p^{⌊n/2⌋})`: `c` is within `p^{-⌊N/2⌋}` of `a · b_N` with `b_N = (p^{⌊n/2⌋ - n} [n < N])`, so
`c ∈ closure (a)`; but `c = a b` forces `b_n = p^{⌊n/2⌋ - n}`, `‖b_{2k}‖ = p^k` unbounded, so
`c ∉ (a)`; M2 with `M = R` then says `ℓ^∞` is not Noetherian.

### Leaves

- **L8.1** `mulLeftL` (bound) and `opNorm_mulLeftL` — [RM] Examples (E10-corrected). Discharge:
  bound `LinearMap.mulLeft_apply`, `norm_mul_le`; `≤` by `LinearMap.mkContinuous_norm_le`-style
  `opNorm_le_bound` (`norm_nonneg`, `norm_mul_le`); `≥` by `le_opNorm_of_bound _ ⟨‖a‖, …⟩ 1` and
  `mul_one`, `norm_one`. Attacks: [3] no Tate hypothesis at all ✓ (section has none). [1] E10's
  argument is the proof. SURVIVED.
- **L8.2** `addPseudoUniformizerSMul` (bound `1`) — Discharge: `LinearMap.add_apply`,
  `LinearMap.smul_apply`, `smul_eq_mul`, `IsUltrametricDist.norm_add_le_max`, [L0] `norm_mul`
  (`ϖ.isMultiplicative`), `ϖ.norm_lt_one.le`, `norm_fst_le`, `norm_snd_le`, `Prod.norm_def`, `one_mul`.
  Attacks: [3] ultrametric `R` necessary for the constant `1`. SURVIVED.
- **L8.3** `exists_preimage_norm_le_addPseudoUniformizerSMul` — Discharge: `⟨(n, 0), by simp, by
  simp [Prod.norm_def]⟩`. SURVIVED.
- **L8.4** `one_le_of_forall_exists_preimage_norm_le_addPseudoUniformizerSMul` — Discharge:
  `obtain ⟨m, hm, hle⟩ := hC 1`; `1 = ‖(1 : R)‖ = ‖m.1 + ϖ * m.2‖ ≤ ‖m‖ ≤ C * 1` (L8.2's bound,
  `norm_one`). Attacks: [3] `NormOneClass` necessary (`‖1‖ = 1`). SURVIVED.
- **L8.5** `bijective_padic_smul_id` — Discharge: `(smul_right_injective _ (Nat.cast_ne_zero.2
  hp.out.ne_zero)).bijective`-style, or `Function.bijective_iff_has_inverse` with `p⁻¹ • ·`
  (`smul_smul`, `inv_mul_cancel₀`). SURVIVED.
- **L8.6** `norm_padic_inv_smul_id` — Discharge (Mathlib's norm, field scalars): `norm_smul`,
  `norm_inv`, `Padic.norm_p`, `inv_inv`, and `‖ContinuousLinearMap.id ℚ_[p] ℚ_[p]‖ = 1`
  (`ContinuousLinearMap.norm_id`, instance `NontrivialTopology ℚ_[p]` from a nontrivial normed field;
  fall back to `opNorm_eq_of_bounds` if the instance is missing). Attacks: [4] the roadmap says
  "whose inverse has norm `p`"; `‖p⁻¹‖ = p` ✓. SURVIVED.
- **L8.7–L8.9** `PadicIntSq` norm fields, `IsBoundedSMul`, `IsUltrametricDist` — [RM] §1.1.2
  *"(a normed `ℤ_p`-module)"*. Discharge: `map_zero'`: `norm_zero`, `zero_pow`; `add_le'`:
  `IsUltrametricDist.norm_add_le_max`, `pow_le_pow_left`, `max_le_add_of_nonneg`; `neg'`:
  `norm_neg`; `eq_zero_of_map_eq_zero'`: `pow_eq_zero_iff`, `norm_eq_zero`; `IsBoundedSMul.of_norm_smul_le`
  with `‖r • x‖² = ‖r‖² ‖x‖² ≤ ‖r‖ ‖x‖²` (`norm_smul` in `ℤ_[p]` as a normed field's subring —
  `PadicInt.norm_mul` —, `mul_pow`, `pow_le_of_le_one` via `PadicInt.norm_le_one`);
  `isUltrametricDist_of_isNonarchimedean_norm` with `max_pow`-style `(max a b)^2 = max (a^2) (b^2)`
  (`Monotone.map_max` of `pow_left_mono`). Attacks: [2] `x = 0` ✓. [3] `IsBoundedSMul` genuinely
  needs `‖r‖ ≤ 1`, i.e. the scalars `ℤ_p` not `ℚ_p` — the roadmap's choice. SURVIVED.
- **L8.10** `continuous_symm_toPadicIntSq` — Discharge: `Metric.continuous_iff`: given `ε`, take
  `δ := ε ^ 2`; `‖x - y‖² < ε²` ⇒ `‖x - y‖ < ε` (`pow_lt_pow_iff_left₀`/`abs_lt_abs`). SURVIVED.
- **L8.11** `not_exists_bound_symm_toPadicIntSq` — [RM] §1.1.2 *"continuous and unbounded"*.
  Discharge: given `C`, at `x := p ^ n`: `p^{-n} ≤ C p^{-2n}` i.e. `p^n ≤ C` (`PadicInt.norm_p_pow`,
  `zpow_neg`, `zpow_natCast`); choose `n` with `C < p^n` (`pow_unbounded_of_one_lt`,
  `Nat.one_lt_cast.2 hp.out.one_lt`). Attacks: [1] consistent with [L0] `not_isTate_padicInt`. SURVIVED.
- **L8.12** `lp.instIsUltrametricDist` — Discharge: `isUltrametricDist_of_isNonarchimedean_norm`;
  `‖f + g‖ ≤ max ‖f‖ ‖g‖` by `lp.norm_le_of_forall_le (le_max_of_le_left (norm_nonneg _))` and
  `lp.coeFn_add`, `IsUltrametricDist.norm_add_le_max`, `lp.norm_apply_le_norm`. Attacks: [2] `ι`
  empty: `‖·‖ = 0` ✓. [3] stated for all `E`, as it should be (§2.5 will reuse it). SURVIVED.
- **L8.13** `padicGeomSeq` (bounded) — Discharge: `Padic.norm_p_pow`, `zpow_neg`, `inv_le_one_of_one_le₀`;
  or `norm_pow_le'` + `Padic.norm_p_lt_one.le` + `pow_le_one₀`. SURVIVED.
- **L8.14** `not_isClosed_span_padicGeomSeq` — [RM] §1.4.3 (E18). Discharge: `c : lp _ ∞ :=
  ⟨fun n ↦ (p : ℚ_[p]) ^ (n / 2), bounded⟩`; (i) `c ∈ closure (span {a})`: `Metric.mem_closure_iff`;
  for `ε > 0` pick `N` with `(p : ℝ)^{-(N/2)} < ε` (`exists_pow_lt_of_lt_one` on `p⁻¹ < 1`, or
  `tendsto_pow_atTop_nhds_zero_of_lt_one`); `b_N := ⟨fun n ↦ if n < N then (p:ℚ_[p]) ^ (n/2) * ((p:ℚ_[p]) ^ n)⁻¹
  else 0, finite support ⇒ bounded⟩`; `b_N * a ∈ span {a}` (`Ideal.mem_span_singleton'`);
  `dist c (b_N * a) = ‖c - b_N * a‖ ≤ p^{-(N/2)}` via `lp.norm_le_of_forall_le` and
  `lp.infty_coeFn_mul`, `lp.coeFn_sub`: coordinates vanish for `n < N` and equal `c n` with
  `‖c n‖ = p^{-(n/2)} ≤ p^{-(N/2)}` for `n ≥ N`; (ii) `c ∉ span {a}`: `Ideal.mem_span_singleton'`
  gives `b` with `b * a = c`; coordinatewise `b n * p ^ n = p ^ (n / 2)`; at `n = 2k`,
  `‖b (2k)‖ = p ^ k` (`Padic.norm_p_pow`, `norm_mul`, `mul_inv_cancel₀`); `lp.norm_apply_le_norm`
  gives `p ^ k ≤ ‖b‖` for all `k`, contradicting `pow_unbounded_of_one_lt`. Conclude
  `¬ IsClosed` from `c ∈ closure S`, `c ∉ S` (`IsClosed.closure_eq`). Attacks: [1] is `c` really
  not in `(a)`? `b_n = p^{⌊n/2⌋-n}` is forced coordinatewise (`ℚ_p` is a field, `pⁿ ≠ 0`) and
  `‖b_{2k}‖ = p^{k}` → ∞ ✓. [2] `p = 2` ✓ (nothing special). [3] the ideal is principal, hence
  finitely generated — the strongest form of "finitely generated submodule not closed". [5] `lp`
  names verified (`names.lean`, `names3.lean`). SURVIVED.
- **L8.15** `not_isNoetherianRing_lp_infty` — Discharge: `intro h; exact not_isClosed_span_padicGeomSeq p
  (Submodule.isClosed_of_isNoetherianRing (R := lp _ ∞) (M := lp _ ∞) _)` with
  `haveI := isTate_of_normedAlgebra ℚ_[p] (lp _ ∞)` ([L0]), `NormOneClass` from `[Nonempty ℕ]`
  (Mathlib `lp` instance), L8.12, `lp.completeSpace`-type instance (`names2.lean`: synthesised),
  `IsBoundedSMul R R`, `Module.Finite R R`. Attacks: [3] this is exactly why L7.6 carries each of
  its hypotheses: all hold here except Noetherianity. SURVIVED.

## Internal-node attacks (composition)

- **§1.1.2 as a whole** (L1.8 → L1.9–L1.15): could the children hold and "continuity ⇔
  boundedness" fail? Only if the scaling trick needed `‖ϖ‖ < 1` *and* a lower bound on norms;
  the shell lemma [L0] gives both ends of the shell for every nonzero `x`. ✓
- **§1.1.3 instances** (L2.1–L2.9): the diamond attack — over a nontrivially normed field,
  opening the scope creates two `Norm`/`NormedAddCommGroup` instances on `M →L[K] N`; L1.16 and
  L2.20 prove them equal, and the module docstring forbids opening the scope there. Over a ring
  there is no second instance (`names.lean`: `TopologicalSpace (M →L[R] N)` fails to synthesise). ✓
- **OMT ⇒ companions** (L3.2 → L3.5 → L3.9, L4.1): each uses the OMT on a *different* pair of
  Banach modules (`M ⧸ ker u`, `range u`, `f.graph`); the completeness of each is established at the
  leaf. ✓
- **§1.4 chain** (L6.1 → L7.1, L7.4 → L7.5 → L7.6 → L7.7/L7.8): the Nakayama hypothesis `‖c‖ < 1`
  is produced by L7.4's constant `C` and the choice `dist < C⁻¹`; `C > 0` is part of L7.4's
  conclusion. ✓ Non-Noetherian failure is exhibited by L8.14, so the hypothesis of L7.6 is not an
  artifact. ✓

## API gaps

None. Every leaf is discharged from Mathlib, Layer 0, or a leaf of this tree. The three seams
(S1–S3 in `plan.md`) are documentation of *what the roadmap would have cited*, not gaps: each is
replaced by an available proof.

## Gate

- `lake build PhD.TauCeti.Code.PadicFunctionalAnalysis.Operator.Examples` — **2 254 jobs, 0
  errors**, `sorry` warnings only (2026-10-06, after adding `[IsUltrametricDist M]` to
  `Finite.lean`'s first section).
- Leaves with a verbatim source quote and a Lean ↔ source match: all (the examples cite [RM]'s
  clause as their source, as in Layer 0).
- Leaves with an attack log of ≥ 3 categories: all except the one-line transfers L1.14, L2.11,
  L2.15, L2.19, L6.2, L7.2, L8.3, whose discharge is a single named lemma (recorded as such).
- Prior-B2 log: consulted (above); no name or shape match unaddressed.
- REVIEW-PENDING leaves: none.
- Statement-shape check: no leaf has a top-level `∧`-chain except the shared-witness existentials
  inherited from Mathlib (`∃ C > 0, ∀ y, ∃ x, u x = y ∧ ‖x‖ ≤ C * ‖y‖`; `∃ C, 0 < C ∧ ∀ y ∈ J, ∃ a,
  y = … ∧ …`; `∃ n π, Surjective π ∧ IsClosed (ker π)`), each justified as a single witness used by
  both conjuncts.
