# Development Plan: Newton polygons, Layer 1 (additive valuations of a nonarchimedean field)

Board: `.mathlib-quality/tauceti-np-layer1/` (named; the default board path belongs to another
agent's Newton-polygon work, and `tauceti-np-layer0/` is the completed Layer 0 board).
Specification: `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, Layer 1 (§1.1–§1.5) and its
Examples. Code: `PhD/TauCeti/Code/NewtonPolygons/AddVal/`, module prefix
`PhD.TauCeti.Code.NewtonPolygons.AddVal`, never importing `PhD.Main.*` (CI-gated). The chain root
`PhD/TauCeti.lean` imports the leaf `AddVal/Examples.lean`. Planned 2026-10-06.

## Goal

The valuation the polygon of Layer 2 consumes, in additive form with a *usable* target
`WithTop Γ = Γ ∪ {∞}` for `Γ = ℤ, ℚ, ℝ`, built once from Mathlib's multiplicative `Valuation` and
specialised three times (roadmap convention 2), with the normalisation carried by an element and a
`Prop` class (convention 3):

```lean
-- §1.1 the dictionary (mathlib4#43578 / #43580, built here, same names and shapes)
def WithZero.negLog (x : Mᵐ⁰) : WithTop M                        -- 0 ↦ ⊤, exp m ↦ -m
def WithZero.orderAddIsoWithTop : (Additive Mᵐ⁰)ᵒᵈ ≃+o WithTop M
def WithZero.mapAddHom' (f : M →+ N) : Mᵐ⁰ →*₀ Nᵐ⁰
def Valuation.addVal (v : Valuation R Mᵐ⁰) : AddValuation R (WithTop M)
theorem Valuation.addVal_eq_coe : v.addVal x = m ↔ v x = exp (-m)      -- the lemma Layer 1 runs on
theorem Valuation.addVal_map : (v.map (mapAddHom' f) _).addVal x = WithTop.map f (v.addVal x)

-- §1.2 real, §1.3 integer, §1.4 rational members of the family
def Valuation.RankOne.addVal (v) [RankOne v] : AddValuation R (WithTop ℝ)
def Valuation.IsRankOneDiscrete.addValZ (v) [v.IsRankOneDiscrete] : AddValuation R (WithTop ℤ)
class Valuation.IsCommensurable (v : Valuation R Γ₀) (π : R) : Prop
def Valuation.addValQ (v) (π) [v.IsCommensurable π] : AddValuation R (WithTop ℚ)
theorem Valuation.addValQ_eq_of_zpow : v x ^ n = v π ^ m → v.addValQ π x = m / n   -- the workhorse
theorem Valuation.addValQ_unique : (∀ x y, w x ≤ w y ↔ v y ≤ v x) → w π = 1 → w = v.addValQ π

-- read off a norm, with norm recovery
def NormedField.normAddVal K : AddValuation K (WithTop ℝ)                 -- x ↦ -log ‖x‖
def NormedField.normAddValZ K [discrete] : AddValuation K (WithTop ℤ)
def NormedField.normAddValQ K π [commensurable at π] : AddValuation K (WithTop ℚ)
theorem NormedField.norm_eq_norm_rpow_normAddValQ : normAddValQ K π x = q → ‖x‖ = ‖π‖ ^ q

-- the instances: ℚ_p, Laurent series, extensions, ℂ_p
theorem NormedField.normAddValZ_padic : normAddValZ ℚ_[p] = Padic.addValuation
theorem LaurentSeries.addValZ_eq_order : f ≠ 0 → addValZ Valued.v f = f.order
theorem NormedField.normAddValZ_algebraMap : normAddValZ L (algebraMap K L x) = e * normAddValZ K x
instance PadicComplex.isCommensurable_p : (valuation (K := ℂ_[p])).IsCommensurable p
theorem PadicComplex.range_normAddValQ : range (normAddValQ ℂ_[p] p) = insert ⊤ (range (↑))
```

## References

| Tag | Reference | Used for |
|---|---|---|
| [RM] | `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md`, Layer 1 (§1.1–§1.5, Examples, conventions 2–3, 8, 12) | the specification; every milestone is a numbered clause there |
| [Kob84] | N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, 2nd ed., GTM 58; text layer extracted to `references/koblitz.txt` (PDF page `N` is marked `===== PDFPAGE N =====`); book pages I §2 (pp. 2–5), III §2 (pp. 57–63), III §3 (pp. 66–70), III §4 (pp. 71–74) | `ord_p` and `|x|_p = p^{-ord_p x}`; the norm of an algebraic element is `|N(α)|^{1/n} = |a_n|^{1/n}` (Theorem 11 and the paragraph before it); `ord_p a = -log_p |a|_p`, the image `(1/e)ℤ`, `x = π^m u` with `m = e·ord_p x`; the completion `Ω`: `|x|_p = |x_i|_p` eventually, `ord_p x = -log_p |x|_p`, value group `p^ℚ` (Exercise 1 of §4, with `p^r` a root of `x^b - p^a`) |
| [Gou20] | F. Q. Gouvêa, *p-adic Numbers: An Introduction*, 3rd ed. (2020); text layer in `references/gouvea.txt`; §3.1 (pp. 53–57), §6.3 (pp. 177–190), §6.4 (pp. 191–197), §6.8 (pp. 215–223) | equivalence of absolute values (Prop. 3.1.3); `|x| = |N(x)|^{1/n}` (Prop. 6.3.4, Thm 6.3.5); the `ℚ`-valued `v_p` with `|x| = p^{-v_p(x)}` (Def. 6.4.1), image `(1/e)ℤ` (Prop. 6.4.2), ramification index (Def. 6.4.3), uniformiser `v_p(π) = 1/e` (Def. 6.4.4), `x = u π^{e v_p(x)}` (Prop. 6.4.5 ii); `ℂ_p`: the value set of the completion is that of the field (Prop. 6.8.7, via Lemma 3.2.10) |
| [BGR] | Bosch–Güntzer–Remmert, *Non-Archimedean Analysis* (1984), scan at `~/Desktop/Papers/BGR - Non Archimedean Analysis.pdf` (PDF page = book page + 8), read by eye from page renders; §1.5.1 (p. 41), §1.5.2 (p. 42), §3.1.3 (pp. 130–131), §3.2.4 (pp. 139–140), §3.3.1 (p. 141) | the valuation axioms and "the completion of a valued field is a valued field" (1.5.1); the additive/multiplicative dictionary `| | = α^ν` with `ν(x) = ∞ ⇔ x = 0`, `ν(xy) = ν(x) + ν(y)` (1.5.2); the ramification index `e(B/A)` (3.1.3); the spectral norm is the unique valuation extending `K` for `K` complete (3.2.4/2) and `σ(q) = |a_m|^{1/m}` for `q` irreducible (3.2.4/3) |
| [Mathlib] | `Mathlib/RingTheory/Valuation/{Basic,RankOne}.lean`, `Discrete/{Basic,RankOne}.lean`, `Mathlib/Topology/Algebra/Valued/{NormedValued,ValuedField}.lean`, `Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean`, `Mathlib/NumberTheory/Padics/{PadicNumbers,Complex}.lean`, `Mathlib/RingTheory/LaurentSeries.lean`, `Mathlib/Data/Int/WithZero.lean` at pin `bbc4475e` | the multiplicative theory this layer reads into additive form (convention 12) |
| [PR] | mathlib4#43578 (`WithZero.negLog`, `orderAddIsoWithTop`, `mapAddHom'`), mathlib4#43580 (`Valuation.addVal`, `addValValueGroup`, `addVal_map`); diffs read 2026-10-06 | the names and shapes of §1.1; neither is in the pinned Mathlib |
| [SRC] | `PhD/Main/ForMathlib/{Algebra/Order/GroupWithZero/WithZero, Data/Real/WithZero, Algebra/Order/Group/Commensurable}.lean`, `PhD/Main/ForMathlib/RingTheory/Valuation/AddVal/{Basic,RankOne,Commensurable,Discrete}.lean`, `PhD/Main/ForMathlib/Topology/Algebra/Valued/AddVal.lean`, `PhD/Main/ForMathlib/NumberTheory/Padics/AddVal.lean` (sorry-free at the pin) | **read-only reference for proofs** of §1.1–§1.4 and the `ℚ_p` half of §1.3.5, which [RM] records as "present; shape it as those pull requests do". Never imported; cited per leaf as "[SRC] File.decl". The ported statements differ from [SRC] only in the [PR] names (`negLogOrderAddIso → orderAddIsoWithTop`, `expMap → mapAddHom'`) |

[RM] names Neukirch, *Algebraic Number Theory*, Ch. II §§3–4 and §8 as the source for the
normalisations. That book is not on this machine; the same material is quoted from [Kob84] and
[Gou20] (concrete, `ℚ_p` and its extensions) and [BGR] (abstract valuations). Every leaf's quote
below names which one.

## Mathlib inventory

| Concept | Mathlib status | Our action |
|---|---|---|
| `Valuation R Γ₀`, `AddValuation R Γ`, `Valuation.toAddValuation : Valuation R Γ₀ ≃ AddValuation R (Additive Γ₀)ᵒᵈ`, `AddValuation.map`, `Valuation.map`, `Valuation.restrict`, `MonoidWithZeroHom.valueGroup`, `ValueGroup₀.embedding` | present | USE; §1.1 composes `toAddValuation` with `orderAddIsoWithTop` |
| `WithZero.negLog`, `orderAddIsoWithTop`, `mapAddHom'`, `Valuation.addVal`, `addValValueGroup`, `addVal_map` | **absent** (mathlib4#43578/#43580 not landed at the pin; checked by grep) | DEFINE in `NegLog.lean`, `Basic.lean`, with the PR names |
| `ℝᵐ⁰ ↔ ℝ≥0`: `NNReal.toRealMultZero`, `WithZeroMulReal.toNNReal` | absent (only `WithZeroMulInt.toNNReal : ℤᵐ⁰ →*₀ ℝ≥0` exists) | DEFINE in `NegLog.lean` (second half) |
| `Valuation.RankOne` with `RankOne.hom : ValueGroup₀ →*₀ ℝ≥0`, `RankOne.strictMono`, `hom_eq_zero_iff`; `Valuation.norm`, `norm_def` | present | USE |
| `Valuation.IsRankOneDiscrete`, `generator`, `generator'`, `IsUniformizer`, `IsUniformizer.zpowers_eq_valueGroup`, `valueGroup₀_equiv_withZeroMulInt` (+ `_apply_zpow`, `_strictMono`), `IsRankOneDiscrete.mk'` (from `IsCyclic` + `Nontrivial` of the value group), `generator_eq_exp_neg_one_of_surjective` | present | USE |
| `Nontrivial (valueGroup (.ofClass v))` from `v.IsNontrivial` | present (`Mathlib/RingTheory/Valuation/Basic.lean:614`) | USE for `ℚ_p`: only `IsCyclic` is new there |
| `IsCyclic (valueGroup (.ofClass v))` for `v : Valuation R ℤᵐ⁰` | not found as an instance | the Laurent-series instance is obtained through `Subgroup.isCyclic` + `isCyclic_of_surjective` along `WithZero.unitsWithZeroEquiv` (T-LS1 sketch) |
| `NormedField.valuation : Valuation K ℝ≥0` (`= ‖·‖₊`), its `RankOne` instance for a nontrivially normed ultrametric field, `NormedField.toValued` (scoped) | present | USE; `normAddVal/Z/Q` are the layer's constructions applied to it |
| `Padic.valuation : ℚ_[p] → ℤ`, `Padic.addValuation : AddValuation ℚ_[p] (WithTop ℤ)`, `norm_eq_zpow_neg_valuation`, `valuation_p`, `norm_p`, `norm_p_lt_one` | present, defined directly for `ℚ_p` | the general `normAddValZ ℚ_[p]` is PROVED equal to `Padic.addValuation` (§1.3.5) |
| `LaurentSeries.valued : Valued K⸨X⸩ ℤᵐ⁰` (the `X`-adic valuation), `valuation_X_pow`, `valuation_single_zpow`, `valuation_surjective`, `single_order_mul_powerSeriesPart`, `intValuation_le_iff_coeff_lt_eq_zero` | present; `K⸨X⸩` is a `Valued` field, **not** a `NormedField` | §1.3.5's Laurent half is stated for `IsRankOneDiscrete.addValZ Valued.v`, for every field `K` (deviation D1 below) |
| `spectralNorm`, `spectralNorm.normedField`, `NormedAlgebra.norm_eq_spectralNorm` (the norm of an algebraic normed-field extension of a complete field is the spectral norm), `spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow` (`‖x‖ = ‖a₀‖^{1/n}`), `spectralNorm_extends`, `norm_algebraMap'`, `IsUltrametricDist.of_normedAlgebra` | present | USE; §1.5.1's "`IsUltrametricDist L`" and "extends the norm" are these Mathlib lemmas and get no new declaration; §1.5.2 is `norm_pow_natDegree_minpoly` + commensurability |
| `Valued.valuedCompletion`, `Valued.exists_coe_eq_v` (every value of the completion is a value of the field), `valuedCompletion_apply` | present | USE for §1.5.3, stated at the `Valued` level (deviation D3) |
| `PadicAlgCl p`, `ℂ_[p]`: `NormedField`, `NormedAlgebra ℚ_[p]`, `Algebra.IsAlgebraic`, `IsUltrametricDist`, `NontriviallyNormedField`, `Valued ℂ_[p] ℝ≥0 := valuedCompletion`, `norm_eq_norm`, `RankOne.hom_eq_embedding`, `norm_extends'`, `valuation_p`, `IsAlgClosed ℂ_[p]`, `IsAlgClosed.exists_pow_nat_eq` | present | USE for §1.5.4–§1.5.5 |
| Ramification index of a finite extension of a complete discretely valued field, discreteness of the extension | absent (and the "local-fields-and-ramification roadmap" [RM] cites does not exist) | §1.3.6 takes discreteness of `L` as an instance hypothesis and *defines* `e` by `normAddValZ L (algebraMap K L π) = e` (deviation D2) |

## File structure and dependency graph

```text
AddVal/NegLog.lean         §1.1.1–1.1.2 + ℝᵐ⁰ ↔ ℝ≥0        ← Mathlib only
AddVal/RatLog.lean         §1.4.2 (group level)              ← Mathlib only
AddVal/Basic.lean          §1.1.3–1.1.5                      ← NegLog
AddVal/RankOne.lean        §1.2.1                            ← Basic
AddVal/Commensurable.lean  §1.4.1–1.4.5 (valuation level)    ← RatLog, RankOne
AddVal/Discrete.lean       §1.3.1–1.3.3, discrete half of §1.4.5  ← Commensurable
AddVal/Normed.lean         §1.2.2–1.2.3, §1.3.4, §1.4.6      ← Discrete
AddVal/Padic.lean          §1.3.5 (ℚ_p)                      ← Normed
AddVal/LaurentSeries.lean  §1.3.5 (K⸨X⸩)                     ← Discrete
AddVal/Extension.lean      §1.3.6, §1.5.1–1.5.3              ← Normed
AddVal/PadicComplex.lean   §1.5.4–1.5.5                      ← Extension, Padic
AddVal/Examples.lean       Examples                          ← LaurentSeries, PadicComplex  (chain-root leaf)
```

Tau Ceti homes are recorded in each module docstring (`TauCeti/Algebra/Order/GroupWithZero/NegLog.lean`,
`TauCeti/RingTheory/Valuation/AddValuation/{Basic,RankOne,Commensurable,Discrete}.lean`,
`TauCeti/Topology/Algebra/Valued/AddVal.lean`, `TauCeti/NumberTheory/Padics/AddVal.lean`, …), per
[RM] "Scope" and [PR] file paths.

## Generality and design decisions

1. **Architecture pinned by [RM] §1.1.5.** The `ℤ`-, `ℚ`- and `ℝ`-valued valuations are
   `(v.restrict.map φ _).addVal` for multiplicative homs `φ` into `ℤᵐ⁰`, `ℚᵐ⁰`, `ℝᵐ⁰`, converted
   once with `addVal`; `WithZero.unzero` bookkeeping is confined to `addVal_eq_coe`. The `ℚ`-valued
   one is the exception that [RM] §1.4.2 itself prescribes: `addValValueGroup` pushed along the
   additive hom `ratLog v π`, whose existence is the content of commensurability.
2. **Names and shapes of [PR].** `WithZero.negLog`, `orderAddIsoWithTop`, `mapAddHom'` (with
   `mapAddHom'_exp`, `mapAddHom'_strictMono`, `negLog_mapAddHom'`), `Valuation.addVal`,
   `addVal_apply`, `addVal_eq_coe`, `addVal_map`, `addValValueGroup`, `addValValueGroup_apply` are
   exactly the PR declarations, so that when the PRs land the files are deleted in favour of an
   import. `addVal_eq_top`, `addVal_le_addVal`, `negLog_lt_negLog`, `addValValueGroup_eq_top` are
   the extra API this layer uses.
3. **`IsCommensurable` is a `Prop` class on `(v, π)`** ([RM] convention 3), with `0 < v π < 1` and
   `∀ x, v x ≠ 0 → ∃ m n : ℤ, 0 < n ∧ v x ^ n = v π ^ m`. Uniqueness (§1.4.4) is stated for an
   arbitrary `w : AddValuation R (WithTop ℚ)` inducing the same order as `v` and with `w π = 1`.
4. **Rings, not fields,** wherever [SRC] allowed it: `addVal`, `addValValueGroup`, `RankOne.addVal`,
   `addValQ`, `addValZ` and all their API are over `[Ring R]`; only the normed statements take a
   field. Universe-polymorphic throughout (`Type*`).
5. **Norm recovery without a base** ([RM] §1.4.6): `‖x‖ = ‖π‖ ^ (q : ℝ)`; the discrete statement
   `‖x‖ = e ^ (-d)` takes the scalar as a hypothesis on the generator (`hgen`) or on a uniformiser
   (`‖π‖ = e⁻¹`), both forms stated.
6. **Instances.** `Padic.isCyclic_valueGroup` (so `IsRankOneDiscrete (valuation ℚ_[p])` is found
   through `IsRankOneDiscrete.mk'`), `Padic.isCommensurable_p`, `LaurentSeries.isRankOneDiscrete_valued`,
   `NormedField.isCommensurable_algebraMap` (algebraic extension of a complete field),
   `NormedField.isCommensurable_natCast_prime` (any algebraic ultrametric normed `ℚ_p`-algebra field
   at `p`) and `PadicComplex.isCommensurable_p` are instances; everything else is a theorem.
7. **Statement shapes.** `WithTop.map f (v x)` for a rescaled valuation (no multiplication on
   `WithTop ℤ`), explicit `(k : WithTop ℤ)` casts, `(((m : ℚ) / (n : ℚ) : ℚ) : WithTop ℚ)` for the
   workhorse's value, `∃ r : ℝ, w x = r ∧ ‖x‖ = Real.exp (-r)` for the defining equivalence of
   `normAddVal` (no exponential of a `WithTop ℝ`).

## Deviations from the roadmap text (recorded, not silent)

- **D1 (§1.3.5, Laurent series).** [RM] asks for `normAddValZ` of `𝔽_q⸨t⸩`; Mathlib's `K⸨X⸩` is a
  `Valued` field with no `NormedField` structure, so the file states `IsRankOneDiscrete.addValZ
  Valued.v` for an arbitrary field `K` (more general than `𝔽_q`), with `X` a uniformiser and
  `addValZ = order`.
- **D2 (§1.3.6).** [RM] cites discreteness of `L` and `e(L/K)` from a roadmap that does not exist.
  The file takes `[(valuation (K := L)).IsRankOneDiscrete]` as a hypothesis and *defines* the
  ramification index by `normAddValZ L (algebraMap K L π) = e` for a uniformiser `π` of `K`
  (`exists_normAddValZ_algebraMap_eq` shows it is a positive integer), then proves the formula
  `normAddValZ L (algebraMap K L x) = e * normAddValZ K x` and the identification with
  `e * normAddValQ L (algebraMap K L π)`. No finiteness hypothesis is needed for either.
- **D3 (§1.5.3).** Stated at the `Valued` level: `Valued.isCommensurable_completion`, for a
  `Valued K Γ₀` field and its `UniformSpace.Completion`, from Mathlib's `Valued.exists_coe_eq_v`.
  The normed reading is used only for `ℂ_[p]` (§1.5.4), through `PadicComplex.valuation_eq_nnnorm`.
- **D4 (§1.5.1).** "`IsUltrametricDist L`" and "the spectral norm extends the norm of `K`" are
  Mathlib's `IsUltrametricDist.of_normedAlgebra` and `norm_algebraMap'`; only the restriction
  `normAddVal L (algebraMap K L x) = normAddVal K x` is a new declaration. The extension `L` is
  taken as any ultrametric nontrivially normed `K`-algebra field (`NormedAlgebra.norm_eq_spectralNorm`
  identifies its norm with the spectral norm when `K` is complete and `L/K` algebraic), so
  `PadicAlgCl p` is an instance rather than a special case.
- **D5 (§1.2.1).** "unchanged when `v` is replaced by an equivalent valuation with the matching
  `hom`" is stated as `RankOne.addVal_eq_of_hom_eq`: equal `hom ∘ restrict` gives equal `addVal`
  (equivalence plus matching `hom` is exactly that hypothesis).
- **D6 (Examples).** `ℚ_p(√p)` is not constructed; its two claims are stated for any algebraic
  ultrametric normed `ℚ_p`-algebra field `L` and `s : L` with `s ^ 2 = p`: `normAddValQ L p s = 1/2`
  unconditionally, and `normAddValZ L p = 2` given `normAddValZ L s = 1` (discrete `L`).

## Skeleton status

`PhD/TauCeti/Code/NewtonPolygons/AddVal/*.lean`: 12 files, 144 open declarations (152 `sorry`s),
every proof `sorry`; `lake build PhD.TauCeti.Code.NewtonPolygons.AddVal.Examples` →
`Build completed successfully (2884 jobs)`, `sorry` warnings only (2026-10-06). Elaborated
signatures of every declaration are in `scratch/signatures.txt` (`scratch/fullnames.py`); the
current line of every open declaration is printed by `scratch/sorries.py`.

## Name check

Every Mathlib name cited in the tickets' "Mathlib lemmas needed" blocks is elaborated against the
pin by `scratch/names_tickets_mathlib.lean` (generated from `tickets.md` by
`scratch/extract_names.py`): **280 names, 0 errors** (2026-10-06). Every skeleton declaration is
elaborated by `scratch/signatures.lean` → `scratch/signatures.txt`: **143 signatures, 0 errors**.
Planning-time spot checks of further names are in `scratch/names_pre.lean`, `scratch/names_pre2.lean`
(the four misspellings found there were corrected in the tickets).

## Milestones

- **M1** = T009 `Valuation.addVal_map` (with `addVal_eq_coe`): the §1.1 dictionary complete.
- **M2** = T017 `Valuation.addValQ_unique`: the element pins the valuation (§1.4.4, convention 3).
- **M3** = T035 `NormedField.normAddValZ_padic`: the general construction reproduces
  `Padic.addValuation` (§1.3.5).
- **M4** = T042 `NormedField.normAddValZ_algebraMap`: the ramification formula (§1.3.6).
- **M5** = T048 `PadicComplex.range_normAddValQ` (with `isCommensurable_p`): the value group of
  `ℂ_p` is `p^ℚ` (§1.5.4–§1.5.5, convention 8).

Each milestone ticket is preceded by a `CLEANUP-ALL` sweep (cadence rule), and the board ends with
`CLEANUP-FINAL`.

## Worker protocol

`/beastmode` inline as the main agent (user preference, 2026-09-05); one Lean process at a time on
this machine; after each ticket `lake build PhD.TauCeti.Code.NewtonPolygons.AddVal.<File>` (the leaf
`…AddVal.Examples` before marking a milestone done) and `#print axioms` on each declaration (only
`propext`, `Classical.choice`, `Quot.sound`); `lake exe runLinter` on the module at every cleanup
ticket; mark `done` only with zero `sorry` in the ticket's declarations. [SRC] is read for proof
ideas and ported with the [PR] names; it is never imported.

## Execution notes (2026-10-06, `/beastmode`)

All 144 declarations proved in one session; no statement was changed except as listed here, and no
B2 was raised (`b2_log.jsonl` is empty).

- **`@[simp]` attributes removed** (Mathlib's `simpNF` linter): the definition-unfolding lemmas
  `Valuation.addVal_apply`, `Valuation.addValValueGroup_apply`, `Valuation.RankOne.addVal_apply`,
  `Valuation.addValQ_apply`, `Valuation.IsRankOneDiscrete.addValZ_apply` (as simp lemmas they expose
  the implementation and make the `_eq_top` lemmas simp-provable), and the instances of Mathlib simp
  lemmas `RankOne.addVal_zero`, `addValQ_zero`, `addValZ_zero`, `normAddVal_zero`,
  `normAddValZ_zero`, `normAddValQ_zero` (`AddValuation.map_zero`) and `normAddVal_eq_top`,
  `normAddValZ_eq_top`, `normAddValQ_eq_top` (`AddValuation.top_iff` on a field). The lemmas remain.
- **Unused instances omitted** (linter): `omit [IsUltrametricDist L] in` on
  `NormedField.norm_pow_natDegree_minpoly`; `omit [Fact p.Prime] [NormedAlgebra ℚ_[p] L]
  [Algebra.IsAlgebraic ℚ_[p] L] in` on `NormedField.normAddValZ_prime_of_sq_eq_prime`. Both are
  strict generalisations.
- **Helpers added**: `Padic.valueGroupGen_lt_one`, `Padic.generator'_eq_valueGroupGen` (from [SRC]),
  the private `Valuation.toNNReal_exp` (`WithZeroMulInt.toNNReal he (exp n) = e ^ n`).
- **Seam traps met**: `rw` with `negLog_*` lemmas at `v.restrict x : ValueGroup₀ (.ofClass v)` fails
  (`ValueGroup₀ f` is `WithZero (valueGroup f)`, not syntactically `(Additive (valueGroup f))ᵐ⁰`);
  cross it with term proofs `(negLog_eq_top (x := v.restrict x)).trans …`. Inside `namespace Padic`,
  `valuation` means `Padic.valuation`: write `NormedField.valuation (K := ℚ_[p])`. The anonymous
  instance binders of `isCommensurable_completion` and `isCommensurable_algebraMap` are recovered
  with `inferInstance`. `HahnSeries.coeff_order_ne_zero` does not exist at the pin; use
  `HahnSeries.coeff_order_eq_zero.not.mpr`. `zero_le'` is deprecated (use `zero_le`).
