# -*- coding: utf-8 -*-
"""Ticket data for the board `tauceti-rag-layer2`. Statements are NOT stored here: the generator
copies them verbatim from the skeleton (through sorries.json). A ticket lists its declarations as
(file, name) or (file, name, occurrence)."""

SEM = 'SupSeminorm/Seminorm.lean'
SPV = 'SupSeminorm/SpectralValue.lean'
INT = 'SupSeminorm/Integral.lean'
BAN = 'SupSeminorm/Banach.lean'
MOD = 'BanachAlgebra/Module.lean'
BFA = 'SupSeminorm/FunctionAlgebra.lean'
ASUP = 'Affinoid/SupSeminorm.lean'
APB = 'Affinoid/PowerBounded.lean'
RED = 'Affinoid/Reduction.lean'
AFA = 'Affinoid/FunctionAlgebra.lean'
RF = 'Affinoid/ReductionFunctor.lean'
EX = 'Affinoid/SupExamples.lean'

T = []  # proof tickets, in board order

def t(**kw):
    T.append(kw)

# ---------------------------------------------------------------- SupSeminorm/Seminorm.lean
t(id='T001', title='Point evaluations are the spectral norms of the residue fields (BGR 3.8.1/3, pointwise)',
  file=SEM, deps='none', par='yes (with T002, T008, T028)', typ='lemmas', leaves='L1.1–L1.8',
  decls=[(SEM,'evalNorm_mul_le'),(SEM,'evalNorm_add_le_max'),(SEM,'evalNorm_pow'),(SEM,'evalNorm_smul'),
         (SEM,'evalNorm_one'),(SEM,'evalNorm_neg'),(SEM,'evalNorm_algebraMap'),(SEM,'evalNorm_eq_zero_iff')],
  sketch="""All eight are the same two steps. (1) `letI := Ideal.Quotient.field x.asIdeal` (the quotient by
`x.asIdeal` is a field; `MaximalSpectrum.isMaximal` is an instance, `Ideal.Quotient.field` is a def);
`evalNorm K x f` unfolds to `spectralValue (minpoly K (Ideal.Quotient.mk x.asIdeal f))`, which is
`spectralNorm K (A ⧸ x.asIdeal) (mk f)` by `rfl` (`spectralNorm` is defined as exactly that). (2) Apply the
Mathlib spectral-norm lemma for the algebraic field extension `A ⧸ x` of `K` with `map_mul`/`map_add` of
`Ideal.Quotient.mk` pushed through: `spectralNorm_mul` (submultiplicative, needs `IsAlgebraic` of both
elements: `Algebra.IsAlgebraic.isAlgebraic`), `isNonarchimedean_spectralNorm` (`IsNonarchimedean` gives
`add_le_max`), `isPowMul_spectralNorm` (`evalNorm_pow` for `n ≥ 1`; `n = 0` is `evalNorm_one`),
`spectralNorm_smul` (`c • f ↦ ‖c‖ * _`; `mk (c • f) = c • mk f` by `Ideal.Quotient.mk_smul`?? — spell
`c • f = algebraMap K A c * f` with `Algebra.smul_def` and use `spectralNorm_mul`+`spectralNorm_extends`
if `spectralNorm_smul` has an awkward form), `spectralNorm_one`, `spectralNorm_neg`,
`spectralNorm_extends` (`evalNorm_algebraMap`: `mk (algebraMap K A c) = algebraMap K (A ⧸ x) c`,
`Ideal.Quotient.algebraMap_eq`/`rfl`), and for `evalNorm_eq_zero_iff`: `→` is
`eq_zero_of_map_spectralNorm_eq_zero` + `Ideal.Quotient.eq_zero_iff_mem`; `←` is `evalNorm_eq_zero_of_mem`
(Layer 0).""",
  mathlib="""`Ideal.Quotient.field`, `spectralNorm`, `spectralNorm_mul`, `isNonarchimedean_spectralNorm`,
`isPowMul_spectralNorm`, `spectralNorm_smul`, `spectralNorm_one`, `spectralNorm_neg`, `spectralNorm_extends`,
`spectralNorm_zero_lt`, `eq_zero_of_map_spectralNorm_eq_zero`, `Algebra.IsAlgebraic.isAlgebraic`,
`Ideal.Quotient.eq_zero_iff_mem`, `Algebra.smul_def`; Layer 0 `Affinoid.evalNorm_eq_zero_of_mem`.""",
  sources="""BGR 3.8.1/1–2 (`|f(x)|` is the spectral norm of `f(x) ∈ A/x`, `bgr-3.8.md:18–44`); BGR 3.2
(spectral norm of an algebraic extension is a power-multiplicative nonarchimedean algebra norm, used in
3.8.1/3's proof: "`| |_sup` … power-multiplicative `k`-algebra semi-norm", `bgr-3.8.md:45`).""",
  gen="""Stated for one point `x` with `[Algebra.IsAlgebraic K (A ⧸ x.asIdeal)]` as an instance hypothesis, not
for `[HasSupSeminorm K A]`: these are the pointwise facts and are reused for fields (`HasSupSeminorm.of_field`)
and for the fibre computation. `[NormedField K] [IsUltrametricDist K]` only — the spectral norm needs
no completeness for these.""")

t(id='T002', title='Basic bounds for `|·|_sup`: nonnegativity, `|f(x)| ≤ |f|_sup`, `|1|_sup`', file=SEM,
  deps='none', par='yes (with T001, T008, T028)', typ='lemmas', leaves='L1.9–L1.14',
  decls=[(SEM,'supSeminorm_nonneg'),(SEM,'evalNorm_le_supSeminorm'),(SEM,'supSeminorm_le_of_forall'),
         (SEM,'supSeminorm_zero'),(SEM,'supSeminorm_one_le'),(SEM,'supSeminorm_one')],
  sketch="""`supSeminorm K f = ⨆ x, evalNorm K x f` (Layer 0). `supSeminorm_nonneg`: `Real.iSup_nonneg` with
`evalNorm_nonneg` (holds with no class: for an empty or unbounded family the junk value is `0`).
`evalNorm_le_supSeminorm`: `le_ciSup (HasSupSeminorm.bddAbove f) x`. `supSeminorm_le_of_forall`: cases
on `isEmpty_or_nonempty (MaximalSpectrum A)`; empty: `Real.iSup_of_isEmpty` and `hC`; nonempty: `ciSup_le h`
(the Layer 0 proof of `supSeminorm_le_norm` is the template). `supSeminorm_zero`: `le_antisymm` with
`supSeminorm_le_of_forall le_rfl (fun x ↦ (evalNorm_eq_zero_of_mem (zero_mem _)).le)` and nonneg.
`supSeminorm_one_le`: `supSeminorm_le_of_forall zero_le_one` with `evalNorm_one` (T001, each `x` is
algebraic by `HasSupSeminorm.instIsAlgebraic`). `supSeminorm_one`: `[Nontrivial A]` gives a maximal ideal
`Ideal.exists_maximal`, so a point `x₀`; `evalNorm K x₀ 1 = 1` and `le_antisymm supSeminorm_one_le
(evalNorm_one ▸ evalNorm_le_supSeminorm x₀ 1)`.""",
  mathlib="""`Real.iSup_nonneg`, `le_ciSup`, `ciSup_le`, `Real.iSup_of_isEmpty`, `Ideal.exists_maximal`,
`isEmpty_or_nonempty`.""",
  sources="""BGR 3.8.1/2–3 (`bgr-3.8.md:30–52`): "(a) `|f|_sup ∈ ℝ`, `|f|_sup ≥ 0`, `|0|_sup = 0` … (e) `|1|_sup ≤ 1`".""",
  gen="""`supSeminorm_nonneg` has no hypothesis at all (it is about the real `iSup`); the others take
`[HasSupSeminorm K A]` for the bound. `supSeminorm_one` needs `[Nontrivial A]` (for the trivial ring
`|1|_sup = |0|_sup = 0`).""")

t(id='T003', title='`|·|_sup` is a power-multiplicative nonarchimedean `K`-algebra seminorm (BGR 3.8.1/3, 6.2.1/1)',
  file=SEM, deps='T001, T002', par='yes (with T008, T028)', typ='lemmas+def', leaves='L1.15–L1.23',
  decls=[(SEM,'supSeminorm_add_le_max'),(SEM,'supSeminorm_mul_le'),(SEM,'supSeminorm_pow'),(SEM,'supSeminorm_smul'),
         (SEM,'supSeminorm_neg'),(SEM,'supSeminorm_algebraMap'),(SEM,'isNonarchimedean_supSeminorm'),
         (SEM,'isPowMul_supSeminorm'),(SEM,'supRingSeminorm')],
  sketch="""Each is `supSeminorm_le_of_forall` + the pointwise lemma of T001 + `evalNorm_le_supSeminorm`:
`add_le_max`: at `x`, `evalNorm (f+g) ≤ max (evalNorm f) (evalNorm g) ≤ max (sup f) (sup g)` (`max_le_max`),
the constant `max _ _ ≥ 0`. `mul_le`: `evalNorm (f*g) ≤ evalNorm f * evalNorm g ≤ sup f * sup g`
(`mul_le_mul` with nonnegativity). `pow`: `≤` as for `mul`; `≥`: for each `x`, `evalNorm f ^ n =
evalNorm (f^n) ≤ sup (f^n)`, so `sup f ≤ sup (f^n) ^ (1/n)` — cleaner: `(sup f)^n = ⨆ x, (evalNorm x f)^n`
by `Real.iSup_pow`? Do: `le_antisymm` with `supSeminorm_le_of_forall` for `≤`, and for `≥` use
`pow_le_pow_left`-free route: `evalNorm x f ≤ (sup (f^n))^(1/n)` for all `x` by `Real.le_rpow_inv_iff_of_pos`
and `evalNorm_pow`, hence `sup f ≤ (sup (f^n))^(1/n)`, then `Real.rpow_natCast`/`Real.rpow_inv_le_iff`.
Handle `n = 0` separately (`pow_zero`, `supSeminorm_one_le`, needs care: `|1|_sup = (|f|_sup)^0 = 1` only
for nontrivial `A`!) — ⚠ for the trivial ring `supSeminorm (f^0) = 0 ≠ 1`; the statement is for all `n`,
so the trivial case is a **statement defect**: fix at ticket time by adding `[Nontrivial A]` to
`supSeminorm_pow` or restricting to `n ≠ 0`… NO: prove it as stated using `Subsingleton`/`Nontrivial`
split: in a subsingleton ring `MaximalSpectrum A` is empty so both sides are `0 ^ 0 = 1`?? `0^0 = 1` in ℝ,
left side `supSeminorm 1 = 0`: FALSE. Statement defect for `n = 0`, `A` trivial: **B2-repair in place
by adding `(hn : n ≠ 0)`** or `[Nontrivial A]`; choose `[Nontrivial A]` — no: `isPowMul_supSeminorm`
requires `IsPowMul` = `∀ a, ∀ n ≥ 1, f (a^n) = f a ^ n`, so `n ≥ 1` only. Resolution (planned now, see
`decomposition.md` statement-defects table): the skeleton's `supSeminorm_pow` is restated at ticket
start as `(hn : n ≠ 0)`. `smul`: `evalNorm_smul` pointwise and `Real.mul_iSup_of_nonneg`-style equality:
`le_antisymm` both via `supSeminorm_le_of_forall` and `evalNorm_le_supSeminorm` scaled (for `‖c‖ = 0`
both sides are `0`). `neg`: pointwise equality. `algebraMap`: `smul_one` + `supSeminorm_one`.
`isNonarchimedean`: `add_le_max`. `isPowMul`: `pow` with `n ≥ 1`. `supRingSeminorm`: fields from the
above (`add_le'` from `add_le_max` and `max_le_add_of_nonneg`).""",
  mathlib="""`max_le_max`, `mul_le_mul`, `Real.rpow_natCast`, `Real.rpow_le_rpow_left_iff`, `Real.le_rpow_inv_iff_of_pos`,
`IsNonarchimedean`, `IsPowMul`, `RingSeminorm`, `max_le_add_of_nonneg`, `Algebra.smul_def`, `smul_one`.""",
  sources="""BGR 3.8.1/3 (`bgr-3.8.md:45–52`): "(b) `|f + g|_sup ≤ max{|f|_sup, |g|_sup}`, (c) `|cf|_sup = |c| |f|_sup`,
(d) `|fg|_sup ≤ |f|_sup |g|_sup`, (e) `|1|_sup ≤ 1`, (f) `|fⁿ|_sup = |f|ⁿ_sup`"; BGR 6.2.1/1
(`bgr-6.2-6.3.1.md`, "is a power-multiplicative `k`-algebra semi-norm").""",
  gen="""`[HasSupSeminorm K A]`, `[NormedField K] [IsUltrametricDist K]`. `supSeminorm_pow` gets `(hn : n ≠ 0)`
(BGR's (f) is for `n ∈ ℕ = {1, 2, …}`); `supSeminorm_algebraMap` needs `[Nontrivial A]`.""")

t(id='T004', title='`|f|_sup = 0` iff `f` lies in every maximal ideal (BGR 3.8.1/9)', file=SEM, deps='T002',
  par='yes (with T005, T008, T028)', typ='lemmas', leaves='L1.24–L1.25',
  decls=[(SEM,'supSeminorm_eq_zero_iff_forall_mem'),(SEM,'supSeminorm_eq_zero_iff_mem_jacobson_bot')],
  sketch="""`→`: for each `x`, `evalNorm x f ≤ supSeminorm f = 0` and `evalNorm_nonneg` give `evalNorm x f = 0`,
then `evalNorm_eq_zero_iff` (T001, `x` algebraic by the class). `←`: `supSeminorm_le_of_forall le_rfl`
with `evalNorm_eq_zero_of_mem`. Second lemma: `Ideal.mem_jacobson_bot`?? — the Jacobson radical of `⊥`
is `sInf {J | J.IsMaximal}` (`Ideal.jacobson`, `Ideal.mem_sInf`), so `f ∈ jacobson ⊥ ↔ ∀ 𝔪 maximal, f ∈ 𝔪
↔ ∀ x : MaximalSpectrum A, f ∈ x.asIdeal` (`⟨𝔪, h⟩`).""",
  mathlib="""`Ideal.jacobson`, `Ideal.mem_sInf`, `Ideal.mem_jacobson_iff` (check the exact name), `MaximalSpectrum`.""",
  sources="""BGR 3.8.1/9 (`bgr-3.8-proofs.md`, "If `| |_sup` is a norm on a `k`-algebra `A`, then `⋂_{𝔪 ∈ Max_k A} 𝔪 = (0)`.
In particular, `A` is reduced, and the Jacobson radical `⋂_{𝔪 ∈ Max A} 𝔪` vanishes").""",
  gen="""The iff form: BGR state "norm ⇒ `⋂ 𝔪 = 0`"; the pointwise iff is what 6.2.1/4 (iii) and 6.3.1/3 use.""")

t(id='T005', title='Every `K`-algebra homomorphism is a contraction for `|·|_sup` (BGR 3.8.1/4)', file=SEM,
  deps='T002', par='yes (with T004, T008, T028)', typ='lemmas+def', leaves='L1.26–L1.28',
  decls=[(SEM,'isMaximal_comap_of_isAlgebraic'),(SEM,'evalNorm_comapPoint'),(SEM,'supSeminorm_map_le')],
  sketch="""`isMaximal_comap_of_isAlgebraic`: `φ` induces an injective `K`-algebra map
`ψ : B ⧸ x.asIdeal.comap φ →ₐ[K] A ⧸ x.asIdeal` (`Ideal.quotientMap`/`Ideal.Quotient.liftₐ` with
`Ideal.mem_comap`); `A ⧸ x` is a field algebraic over `K`, so `ψ.range` is a subalgebra of an algebraic
field extension, hence a field (`Subalgebra.isField_of_algebraic`), and `B ⧸ comap` ≅ `ψ.range`
(`AlgEquiv.ofInjective`) is a field, so `comap` is maximal (`Ideal.Quotient.maximal_of_isField`). This is
exactly the Layer 0 proof of `isMaximal_ker_of_isAlgebraic` with `RingHom.ker` replaced by `comap`
(`x.asIdeal.comap φ = RingHom.ker ((Ideal.Quotient.mk x.asIdeal).comp φ)`: reuse it directly through
`Ideal.comap_eq_ker`-style rewriting: `comap φ (ker (mk x)) = ker (mk x ∘ φ)` = `RingHom.comap_ker`).
`evalNorm_comapPoint`: both sides are spectral values of minimal polynomials of corresponding elements:
`mk x (φ g)` and `mk (comap) g` are related by the injective `K`-algebra map `ψ`, so
`minpoly.algHom_eq ψ hψ` gives equality of `minpoly K` — exactly Layer 0 `evalNorm_eq_norm_algHom`'s
proof. `supSeminorm_map_le`: `supSeminorm_le_of_forall (supSeminorm_nonneg _)` with
`evalNorm_comapPoint ▸ evalNorm_le_supSeminorm (comapPoint φ x) g`.""",
  mathlib="""`Ideal.Quotient.liftₐ`, `Ideal.mem_comap`, `RingHom.comap_ker`, `Subalgebra.isField_of_algebraic`,
`AlgEquiv.ofInjective`, `Ideal.Quotient.maximal_of_isField`, `minpoly.algHom_eq`; Layer 0
`Affinoid.isMaximal_ker_of_isAlgebraic`, `Affinoid.evalNorm_eq_norm_algHom` (as templates).""",
  sources="""BGR 3.8.1/4 and its proof (`bgr-3.8.md:54–62`): "`φ` induces a `k`-algebra monomorphism `B/φ⁻¹(x) → A/x`.
Because `A/x` is an algebraic extension of `k`, its subring `B/φ⁻¹(x)` must also be an algebraic extension
of `k`. Hence `φ⁻¹(x) ∈ Max_k B`. Then one has (*) `|φ(g)|_sup = sup |φ(g)(x)| = sup |g(φ⁻¹(x))| ≤ |g|_sup`".""",
  gen="""`isMaximal_comap_of_isAlgebraic` needs only `[Algebra.IsAlgebraic K (A ⧸ x.asIdeal)]` at the one point and
`[NormedField K]`; `comapPoint` is a `def` for `[HasSupSeminorm K A]`; the contraction needs both classes
and `[IsUltrametricDist K]` (through T002's bounds).""")

t(id='T006', title='`|·|_sup` on quotients: the instance, contraction, and invariance modulo the Jacobson radical (BGR 6.2.1/3)',
  file=SEM, deps='T004, T005', par='yes (with T008, T028)', typ='lemmas+instance', leaves='L1.29–L1.33',
  decls=[(SEM,'HasSupSeminorm.quotient'),(SEM,'supSeminorm_mk_le'),(SEM,'evalNorm_le_supSeminorm_mk'),
         (SEM,'supSeminorm_mk_eq_of_le_jacobson'),(SEM,'supSeminorm_mk_nilradical')],
  sketch="""Points of `A ⧸ I` are points of `A` containing `I`: for `x̄ : MaximalSpectrum (A ⧸ I)`, `x := comapPoint
(Ideal.Quotient.mkₐ K I) x̄` (T005) is maximal with `I ≤ x.asIdeal`, and the residue fields agree:
`(A ⧸ I) ⧸ x̄ ≃ₐ[K] A ⧸ x` (`DoubleQuot.quotQuotEquivQuotOfLE`-type, or directly `Ideal.quotientKerAlgEquivOfSurjective`
for `mk x ∘ mk I`), so `evalNorm K x̄ (mk I f) = evalNorm K x f` (`minpoly.algHom_eq` along the equiv).
Instance: `isAlgebraic` transports along the equivalence (`Algebra.IsAlgebraic.of_equiv`?/`AlgEquiv.isAlgebraic`),
`bddAbove`: bounded by `supSeminorm K f` through the evaluation equality. `supSeminorm_mk_le`:
`supSeminorm_map_le (Ideal.Quotient.mkₐ K I)`. `evalNorm_le_supSeminorm_mk`: `x` with `I ≤ x` yields the
point `x̄ := ⟨x.asIdeal.map (mk I), map_isMaximal…⟩` (`Ideal.map_eq_top_or_isMaximal_of_surjective`;
`≠ ⊤` since `comap (map) = x` for `I ≤ x`: `Ideal.comap_map_of_surjective` + `sup_eq_left`), with
`evalNorm x̄ (mk f) = evalNorm x f`, then `evalNorm_le_supSeminorm`. `supSeminorm_mk_eq_of_le_jacobson`:
`le_antisymm supSeminorm_mk_le (supSeminorm_le_of_forall _ (fun x ↦ evalNorm_le_supSeminorm_mk (hI.trans
(sInf_le ⟨x.isMaximal, rfl⟩)) f))`: every maximal ideal contains `I` because `I ≤ jacobson ⊥ = sInf {maximal}`.
`supSeminorm_mk_nilradical`: `nilradical A ≤ jacobson ⊥` (`nilradical_le_jacobson`?? — `Ideal.radical_le_jacobson`:
`nilradical A = radical ⊥ ≤ jacobson ⊥`).""",
  mathlib="""`Ideal.Quotient.mkₐ`, `Ideal.comap_map_of_surjective`, `Ideal.map_eq_top_or_isMaximal_of_surjective`,
`Ideal.comap_isMaximal_of_surjective`, `DoubleQuot.quotQuotEquivQuotOfLE`, `Ideal.quotientKerAlgEquivOfSurjective`,
`Ideal.radical_le_jacobson`, `nilradical_eq_sInf`/`Ideal.radical_bot`?, `Algebra.IsAlgebraic.of_equiv`?
(verify: `AlgEquiv.isAlgebraic` / `Algebra.IsAlgebraic.of_injective`).""",
  sources="""BGR 6.2.1/3 (`bgr-6.2-6.3.1.md`): "The second one follows from the fact that the nilradical `rad A` is
contained in each maximal ideal of `A`"; BGR 3.8.1/4 for the contraction along `A → A/I`.""",
  gen="""Stated for an arbitrary ideal `I` (instance) and for `I ≤ jacobson ⊥` (equality), of which the nilradical
is the case BGR need; no noetherianity.""")

t(id='T007', title='`|f|_sup` is attained modulo a minimal prime (BGR 3.8.1/5, 6.2.1/3)', file=SEM, deps='T006',
  par='yes (with T008, T028)', typ='lemma', leaves='L1.34',
  decls=[(SEM,'exists_minimalPrimes_supSeminorm_mk_eq')],
  sketch="""`minimalPrimes A` is finite (`minimalPrimes.finite_of_isNoetherianRing`) and nonempty
(`Ideal.nonempty_minimalPrimes` for a nontrivial ring, `⊥ ≠ ⊤`). Let `s := hfin.toFinset`. For each
`𝔭 ∈ s`, `supSeminorm (mk 𝔭 f) ≤ supSeminorm f` (T006). Conversely every `x : MaximalSpectrum A` contains
some minimal prime `𝔭` (`Ideal.exists_minimalPrimes_le` with `x.isMaximal.isPrime`, `bot_le`), so
`evalNorm x f ≤ supSeminorm (mk 𝔭 f)` (T006 `evalNorm_le_supSeminorm_mk`) `≤ s.sup' hs (fun 𝔭 ↦
supSeminorm (mk 𝔭 f))`; hence `supSeminorm f ≤ s.sup' …` (`supSeminorm_le_of_forall`, nonneg by
`supSeminorm_nonneg`). `Finset.exists_mem_eq_sup'` gives `𝔭₀` attaining the `sup'`, and the two
inequalities give equality.""",
  mathlib="""`minimalPrimes.finite_of_isNoetherianRing`, `Ideal.nonempty_minimalPrimes`, `Ideal.exists_minimalPrimes_le`,
`Finset.sup'`, `Finset.exists_mem_eq_sup'`, `Finset.le_sup'`, `Set.Finite.toFinset`.""",
  sources="""BGR 3.8.1/5 (`bgr-3.8.md:64–66`): "`|f|_sup = sup_{𝔭 ∈ 𝔐} |π_𝔭(f)|_sup`"; BGR 6.2.1/3 (`bgr-6.2-6.3.1.md`):
"Since `A` is Noetherian, there are only finitely many minimal prime ideals … `|f|_sup = max_{1≤i≤r} |π_i(f)|_sup`".""",
  gen="""Stated for `[IsNoetherianRing A] [Nontrivial A]` in the attained form (the noetherian case is all 6.2.1/4
and 6.2.2/4 use); BGR's general `sup` over all minimal primes is not stated.""")

# ---------------------------------------------------------------- SupSeminorm/SpectralValue.lean
t(id='T008', title='The spectral value `σ(q) = max |bᵢ|_sup^{1/i}` for the supremum seminorm: definition lemmas',
  file=SPV, deps='none', par='yes (with T001–T007, T028)', typ='lemmas', leaves='L2.1–L2.9',
  decls=[(SPV,'supSpectralValueTerms_of_lt_natDegree'),(SPV,'supSpectralValueTerms_of_natDegree_le'),
         (SPV,'supSpectralValueTerms_nonneg'),(SPV,'supSpectralValueTerms_finite_range'),
         (SPV,'supSpectralValueTerms_bddAbove'),(SPV,'supSpectralValue_nonneg'),
         (SPV,'supSpectralValueTerms_le_supSpectralValue'),(SPV,'supSpectralValue_le_of_forall'),
         (SPV,'supSpectralValue_X_pow')],
  sketch="""Mirror Mathlib's `spectralValueTerms` lemmas line by line (`Mathlib/Analysis/Normed/Unbundled/SpectralNorm.lean`,
lines 95–200): `of_lt_natDegree`/`of_natDegree_le` by `simp [supSpectralValueTerms, hn]`; `nonneg` by
`split_ifs` with `Real.rpow_nonneg (supSeminorm_nonneg _ _)`; `finite_range`: the range is contained in
`insert 0 (Finset.range natDegree).image …` (copy `spectralValueTerms_finite_range`); `bddAbove` from
`Set.Finite.bddAbove`; `supSpectralValue_nonneg`: `Real.iSup_nonneg`; `terms_le`: `le_ciSup bddAbove n`;
`le_of_forall`: `ciSup_le` (ℕ is nonempty) with the term bound (`if` cases: `h n hn` or `hC`);
`X_pow`: all coefficients below the degree are `0` (`coeff_X_pow`), `supSeminorm_zero`, `Real.zero_rpow`
(exponent `≠ 0`), so every term is `0` and the `iSup` of the zero family is `0` (`ciSup_const`).""",
  mathlib="""`spectralValueTerms_of_lt_natDegree`, `spectralValueTerms_finite_range`, `Set.Finite.bddAbove`,
`Real.iSup_nonneg`, `le_ciSup`, `ciSup_le`, `ciSup_const`, `Real.zero_rpow`, `Polynomial.coeff_X_pow`.""",
  sources="""BGR 1.5.4 (`bgr-1.3-1.5.md`, "`σ(p) := max_{1≤μ≤m} |a_μ|^{1/μ}` … `σ(X^m) = 0`").""",
  gen="""No class needed except for `supSpectralValue_X_pow` (`supSeminorm_zero` needs `[HasSupSeminorm K B]`? — no:
`supSeminorm K 0 = 0` is `Real.iSup` of zeros, `supSeminorm_zero` is stated with the class; prove
`supSeminorm K (0 : B) = 0` inline via `evalNorm_eq_zero_of_mem` + `ciSup_const` or restate `supSeminorm_zero`
without the class at ticket time (it is true for the bare `iSup`)). `[NormedField K]` only.""")

t(id='T009', title='Coefficient bounds and attainment of `σ(q)`; `σ(q) = spectralValue q` when `|·|_sup = ‖·‖`',
  file=SPV, deps='T008', par='yes (with T001–T007, T028)', typ='lemmas', leaves='L2.10–L2.12',
  decls=[(SPV,'supSeminorm_coeff_le_supSpectralValue_pow'),(SPV,'exists_supSpectralValue_eq'),
         (SPV,'supSpectralValue_eq_spectralValue')],
  sketch="""`coeff_le_pow`: from `terms_le`: `|b_n|_sup ^ (1/(d-n)) ≤ σ` with `d - n ≥ 1`, raise to the power
`d - n` (`Real.rpow_natCast`, `Real.rpow_le_rpow` with nonnegativity, `Real.rpow_inv_natCast_pow`).
`exists_supSpectralValue_eq`: the terms with `n < natDegree` form a nonempty finite family
(`Finset.exists_max_image` on `Finset.range natDegree`), the others are `0 ≤` every term, so the `iSup`
equals the max term (`ciSup_eq_of_forall_le_of_forall_lt_exists_gt` or `le_antisymm` with `terms_le` and
`le_of_forall`). `eq_spectralValue`: unfold both `iSup`s; `spectralValueTerms q n` and
`supSpectralValueTerms K q n` agree termwise by `h (q.coeff n)` (`congrArg iSup (funext _)`).""",
  mathlib="""`Real.rpow_natCast`, `Real.rpow_le_rpow`, `Real.rpow_inv_natCast_pow`, `Finset.exists_max_image`,
`Polynomial.spectralValueTerms`, `spectralValue`.""",
  sources="""BGR 1.5.4 (`bgr-1.3-1.5.md`): "From `|a_μ| ≤ σ(p)^μ`"; BGR 1.5.4/1's proof (2): "We choose `j` … such
that `|b_j|^{1/j} = σ(q)`".""",
  gen="""`supSpectralValue_eq_spectralValue` takes `[NormedCommRing B] [NormedAlgebra K B]` and the pointwise equality
`∀ b, supSeminorm K b = ‖b‖` as a hypothesis (true for `T_d` by Layer 0, and for fields with the spectral
norm); no class needed.""")

t(id='T010', title='`q(f) = 0` for monic `q` over `B` implies `|f|_sup ≤ σ(q)` (BGR 6.2.2/3 = 3.8.1/6 (b))',
  file=SPV, deps='T003, T005, T009', par='yes (with T006, T007, T028)', typ='lemma', leaves='L2.13',
  decls=[(SPV,'supSeminorm_le_supSpectralValue_of_eval₂_eq_zero')],
  sketch="""BGR p. 239, purely seminorm-theoretic. Let `n := q.natDegree` (`n ≥ 1` unless `q = 1`, in which case
`eval₂ = 1 = 0` forces `A` trivial and `|f|_sup = 0`: handle by `subsingleton_or_nontrivial A`). From
`eval₂ φ f q = 0` and `Monic`: `f ^ n = - ∑ i < n, φ (q.coeff i) * f ^ i` (`Polynomial.eval₂_eq_sum_range`,
`Monic.coeff_natDegree`, `Finset.sum_range_succ`). Apply `supSeminorm_pow` (`n ≠ 0`), `supSeminorm_neg`,
and the nonarchimedean finite-sum bound: for the seminorm `supRingSeminorm K A`, which is nonarchimedean
(T003), `|∑_{i<n} t_i|_sup ≤ max_i |t_i|_sup` — use `IsNonarchimedean.apply_sum_le_sup_of_isEmpty`-style
lemma or prove by induction on the `Finset` with `supSeminorm_add_le_max`; pick `j < n` attaining the max
(`Finset.exists_max_image`). Then `|f|^n ≤ |φ(b_j)|_sup |f|^j ≤ |b_j|_sup |f|^j` (`supSeminorm_mul_le`,
`supSeminorm_map_le`). If `|f|_sup = 0` done; else divide: `|f|^(n-j) ≤ |b_j|_sup`, so
`|f| ≤ |b_j|_sup ^ (1/(n-j)) = supSpectralValueTerms K q j ≤ σ(q)` (`Real.le_rpow_inv_iff_of_pos`,
`supSpectralValueTerms_le_supSpectralValue`).""",
  mathlib="""`Polynomial.eval₂_eq_sum_range`, `Polynomial.Monic.coeff_natDegree`, `Finset.sum_range_succ`,
`Finset.exists_max_image`, `Real.le_rpow_inv_iff_of_pos`, `Real.rpow_natCast`, `pow_le_pow_left`,
`subsingleton_or_nontrivial`; a nonarchimedean finite-sum lemma (`IsNonarchimedean` API in
`Mathlib/Algebra/Order/Ring/IsNonarchimedean.lean` — verify the name, else induct).""",
  sources="""BGR 6.2.2/3 and proof (`bgr-6.2-6.3.1.md`): "There exists an index `j`, `1 ≤ j ≤ n`, such that
`|f|_sup^n = |fⁿ|_sup ≤ |φ(b_j) fⁿ⁻ʲ|_sup ≤ |b_j|_sup |f|_sup^{n−j}`. Then `|f|_sup ≤ |b_j|_sup^{1/j}`."
(BGR index `j` counts from the top; ours is the coefficient index.)""",
  gen="""Stated for any `K`-algebra homomorphism `φ : B →ₐ[K] A` between algebras with `HasSupSeminorm` (BGR: affinoid
algebras; the proof uses only 3.8.1/3–4), with `q.eval₂ (φ : B →+* A) f = 0`.""")

t(id='T011', title='`σ` under coefficient contraction, products, powers (BGR 1.5.4/1, the inequality)',
  file=SPV, deps='T009', par='yes (with T010, T028)', typ='lemmas', leaves='L2.14–L2.17',
  decls=[(SPV,'supSpectralValue_map_le'),(SPV,'supSpectralValue_mul_le'),
         (SPV,'supSpectralValue_prod_le_of_forall_le'),(SPV,'supSpectralValue_pow_le')],
  sketch="""`map_le`: `(q.map φ).natDegree = q.natDegree` (`Monic.natDegree_map`), `coeff_map`, and
`supSeminorm_map_le φ` on each coefficient (`Real.rpow_le_rpow`), then `supSpectralValue_le_of_forall` +
`terms_le`. `mul_le` (BGR 1.5.4/1, part (1)): WLOG `σ(p) ≤ σ(q) =: s` (`le_total`); `c_λ = ∑_{μ+ν=λ} a_μ b_ν`
(`Polynomial.coeff_mul`, `Finset.antidiagonal`), each `|a_μ b_ν|_sup ≤ |a_μ|_sup |b_ν|_sup ≤ s^μ' s^ν'`
where `μ' = natDegree p - μ` etc. (T009 `coeff_le_pow` — careful with the index conventions: for the
coefficient of `X^k` in `pq` with `k < m + n` the bound is `s^{(m+n)-k}`; the leading coefficients
`a_m = b_n = 1` contribute `1 ≤ s^0`), so by the nonarchimedean sum bound `|c_k|_sup ≤ s^{(m+n)-k}`, hence
`supSpectralValue_le_of_forall` with `Real.rpow_le_rpow_left_iff`-free manipulation
(`|c_k| ^ (1/((m+n)-k)) ≤ s`: `Real.rpow_le_rpow` + `Real.pow_rpow_inv_natCast`). `prod_le`: induction on `s`
(`Finset.prod_insert`, `Monic.prod`?? use `Polynomial.monic_prod_of_monic`) with `mul_le` and `max_le`.
`pow_le`: `prod_le` over `Finset.range e` (`Finset.prod_const`) or induction with `mul_le`.""",
  mathlib="""`Polynomial.Monic.natDegree_map`, `Polynomial.coeff_map`, `Polynomial.coeff_mul`, `Finset.sum_antidiagonal`,
`Polynomial.Monic.mul`, `Polynomial.monic_prod_of_monic`, `Polynomial.natDegree_mul'`/`Monic.natDegree_mul`,
`Real.rpow_le_rpow`, `Real.pow_rpow_inv_natCast`, `Finset.prod_const`, `max_le`.""",
  sources="""BGR 1.5.4/1 and proof part (1) (`bgr-1.3-1.5.md`): "`|c_λ| ≤ max_{μ+ν=λ} {|a_μ| |b_ν|} ≤ max {σ(p)^μ σ(q)^ν}
… Suppose `σ(p) ≤ σ(q)`. Then `|c_λ| ≤ σ(q)^λ`. Thus `σ(pq) ≤ σ(q) = max{σ(p), σ(q)}`"; BGR 6.2.2/4's proof
("`|f|_sup = σ(p) ≥ σ(q)`" for the coefficient contraction).""",
  gen="""Only the inequality half of 1.5.4/1 (the equality under `σ(p) ≠ σ(q)` or for valuations is not needed:
6.2.2/4 uses `σ(q) ≤ max σ(q_i)`). `map_le` needs `HasSupSeminorm` on both `B` and `C`.""")

# ---------------------------------------------------------------- SupSeminorm/Integral.lean
t(id='T012', title='Going up for maximal ideals along an integral map; residue fields stay algebraic',
  file=INT, deps='none', par='yes (with T001–T011, T028)', typ='lemmas', leaves='L3.1–L3.3',
  decls=[(INT,'exists_comap_algebraMap_eq'),(INT,'isMaximal_comap_algebraMap_of_isIntegral'),
         (INT,'isAlgebraic_quotient_of_isAlgebraic_quotient_comap')],
  sketch="""`exists_comap_algebraMap_eq`: `Ideal.exists_ideal_over_maximal_of_isIntegral y.asIdeal` with
`RingHom.ker (algebraMap B A) ≤ y.asIdeal` from `RingHom.ker_eq_bot_iff_eq_zero`/`FaithfulSMul`
(`(FaithfulSMul.algebraMap_injective B A)`, `RingHom.injective_iff_ker_eq_bot`), giving `Q` maximal with
`comap Q = y`; package `⟨Q, hQ⟩`. `isMaximal_comap_algebraMap_of_isIntegral`:
`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal x.asIdeal`. `isAlgebraic_quotient…`: with
`letI := Ideal.Quotient.algebraQuotientOfLEComap le_rfl : Algebra (B ⧸ comap) (A ⧸ x)` and
`Algebra.IsIntegral.quotient : Algebra.IsIntegral (B ⧸ comap) (A ⧸ x)`, the tower `K → B ⧸ comap → A ⧸ x`
is a scalar tower (`IsScalarTower.of_algebraMap_eq`, both maps are induced by `algebraMap`), so
`Algebra.IsAlgebraic.trans` (integral ⇒ algebraic: `Algebra.IsIntegral.isAlgebraic`) gives
`Algebra.IsAlgebraic K (A ⧸ x)`.""",
  mathlib="""`Ideal.exists_ideal_over_maximal_of_isIntegral`, `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`,
`FaithfulSMul.algebraMap_injective`, `Ideal.Quotient.algebraQuotientOfLEComap`, `Algebra.IsIntegral.quotient`,
`Algebra.IsIntegral.isAlgebraic`, `Algebra.IsAlgebraic.trans`, `IsScalarTower.of_algebraMap_eq`.""",
  sources="""BGR 3.8.1/6 (a), proof (`bgr-3.8.md:76–84`): "Since `φ` is integral and injective, there is a maximal
ideal `x` of `A` lying over `y`, i.e., `φ⁻¹(x) = y`. Now `φ` induces an integral monomorphism from `B/y`
into `A/x`. The field `B/y` is an algebraic extension of `k` by our assumption, and `A/x` is integral
over `B/y`. Therefore `A/x` is an algebraic extension of `k`."
""",
  gen="""Pure commutative algebra over `[Algebra B A] [IsScalarTower K B A]`; `K` is only needed for the third
lemma. `FaithfulSMul B A` is Mathlib's spelling of "monomorphism".""")

t(id='T013', title='Finiteness of `|·|_sup` transfers along integral maps (BGR 3.8.1/6 (c))', file=INT,
  deps='T003, T005, T006, T010, T012', par='yes (with T011, T028)', typ='lemmas', leaves='L3.4–L3.5',
  decls=[(INT,'HasSupSeminorm.of_isIntegral'),(INT,'HasSupSeminorm.of_isIntegral_of_faithfulSMul')],
  sketch="""`of_isIntegral`: `isAlgebraic`: T012 (`comap x` is maximal with algebraic residue field by the class on `B`,
packaged as the point `⟨comap x, _⟩`). `bddAbove`: for `f`, take an integral equation `q := minpoly`-free:
`Algebra.IsIntegral.isIntegral f` gives monic `q ∈ B[X]` with `aeval f q = 0`; the POINTWISE bound
`evalNorm K x f ≤ max_i |q.coeff i (comap x)|^{1/(n-i)} ≤ max_i |q.coeff i|_sup^{1/(n-i)}` — proved as
in T010 but at the single point `x` with the pointwise seminorm properties of T001 (`evalNorm_pow`,
`evalNorm_add_le_max`, `evalNorm_mul_le`, `evalNorm_comapPoint`-style equality
`evalNorm K x (algebraMap B A b) = evalNorm K ⟨comap x, _⟩ b` from T005's `evalNorm_comapPoint` applied to
`IsScalarTower.toAlgHom K B A`), then `evalNorm_le_supSeminorm` on `B`. Package the bound as
`BddAbove`. (Do NOT use `supSeminorm_le_supSpectralValue_of_eval₂_eq_zero`: it needs the class on `A`,
which is what is being constructed; factor the pointwise argument out of T010 as a private lemma if
convenient.) `of_isIntegral_of_faithfulSMul`: `isAlgebraic` for `y`: pick `x` over `y` (T012),
`B ⧸ y ≃ₐ[K] (image in A ⧸ x)` via the injective map `B ⧸ comap x → A ⧸ x`, and a subalgebra of an
algebraic extension is algebraic (`Algebra.IsAlgebraic.of_injective`/`AlgHom.isAlgebraic_of_injective`?
verify: `Algebra.IsAlgebraic.of_injective (f : B' →ₐ[K] A') (hf : Injective f)`). `bddAbove`: `|b(y)| =
|algebraMap b (x)| ≤ supSeminorm K (algebraMap B A b)`.""",
  mathlib="""`Algebra.IsIntegral.isIntegral`, `IsIntegral` (monic `p` with `eval₂ = 0`), `IsScalarTower.toAlgHom`,
`Algebra.IsAlgebraic.of_injective` (verify name), `Ideal.quotientMap`, `Ideal.quotientMap_injective`.""",
  sources="""BGR 3.8.1/6 (c) and proof (`bgr-3.8.md:68–90`): "`| |_sup` is finite on `A` if and only if it is finite
on `B`" / "If `g(Max_k B)` is bounded for all `g ∈ B`, then `f(Max_k A)` is also bounded for all `f ∈ A`
due to (b). The converse is true due to (a)."; 3.8.1/6 (b)'s proof: "Due to Proposition 3.1.2/1, this
equation implies `|f(x)| ≤ max |b_i(φ⁻¹(x))|^{1/i} ≤ max |b_i|_sup^{1/i}`".""",
  gen="""The two directions are separate theorems (not instances: `B` cannot be inferred). The first needs no
injectivity; the second needs `FaithfulSMul B A`.""")

t(id='T014', title='An integral monomorphism is an isometry; `|f|_sup = sup_y |f mod yA|_sup` (BGR 3.8.1/6 (a))',
  file=INT, deps='T005, T006, T012, T013', par='yes (with T011, T028)', typ='lemmas', leaves='L3.6–L3.7',
  decls=[(INT,'supSeminorm_algebraMap_eq'),(INT,'supSeminorm_le_of_forall_supSeminorm_mk_map_le')],
  sketch="""`supSeminorm_algebraMap_eq`: `≤` is `supSeminorm_map_le (IsScalarTower.toAlgHom K B A)` (T005). `≥`:
`supSeminorm_le_of_forall (supSeminorm_nonneg _ _)`: for `y`, pick `x` over `y` (T012); then
`evalNorm K y b = evalNorm K x (algebraMap b)` (`evalNorm_comapPoint` with `comapPoint _ x = y` by
`MaximalSpectrum.ext`/`Subtype.ext` on `asIdeal`) `≤ supSeminorm K (algebraMap b)`.
`supSeminorm_le_of_forall_supSeminorm_mk_map_le`: `supSeminorm_le_of_forall hC`: for `x`, let
`y := comapPoint (IsScalarTower.toAlgHom K B A) x`; `y.asIdeal.map (algebraMap B A) ≤ x.asIdeal`
(`Ideal.map_comap_le`), so `evalNorm K x f ≤ supSeminorm K (mk _ f)` (T006 `evalNorm_le_supSeminorm_mk`)
`≤ C`.""",
  mathlib="""`Ideal.map_comap_le`, `MaximalSpectrum.ext`, `IsScalarTower.toAlgHom`, `IsScalarTower.coe_toAlgHom'`.""",
  sources="""BGR 3.8.1/6 (a), proof (`bgr-3.8.md:76–84`): "the map `x ↦ φ⁻¹(x)` from `Max_k A` to `Max_k B` is surjective.
Therefore, one has equality in the formula (*) occurring in the proof of Lemma 4, and so `φ` is an
isometry"; BGR p. 172 (`bgr-3.8-proofs.md`): "Since each `y ∈ Max_k B` is contained in some ideal
`x ∈ Max_k A`, we see that `|f|_sup = sup_{y ∈ Max_k B} |f_y|_sup`".""",
  gen="""`supSeminorm_le_of_forall_supSeminorm_mk_map_le` needs no integrality (every `x` lies over `comap x`); it is
stated in the Isometry section for convenience — drop the unused `[Algebra.IsIntegral B A]` with `omit` if the
linter asks.""")

t(id='T015', title='Fields: `|·|_sup` is the spectral norm, and `HasSupSeminorm.of_field`', file=INT,
  deps='T002, T005', par='yes (with T011, T013, T028)', typ='lemmas', leaves='L3.8–L3.9',
  decls=[(INT,'supSeminorm_eq_spectralNorm'),(INT,'HasSupSeminorm.of_field')],
  sketch="""A field `L` has exactly one maximal ideal, `⊥` (`Ideal.bot_isMaximal`, `Ideal.eq_bot_or_top`). Let
`x₀ : MaximalSpectrum L := ⟨⊥, Ideal.bot_isMaximal⟩`; every `x` equals `x₀` (`Subsingleton`-style:
`MaximalSpectrum.ext` + `x.isMaximal.ne_top` + `eq_bot_or_top`). `evalNorm K x₀ b = spectralNorm K L b`:
`L ⧸ ⊥ ≃ₐ[K] L` (`(RingEquiv.quotientBot L)` upgraded to an `AlgEquiv`, or `Ideal.quotientKerAlgEquivOfSurjective`
for `AlgHom.id`), and `minpoly.algHom_eq` along the injective map gives `minpoly K (mk ⊥ b) = minpoly K b`.
Then `supSeminorm K b = ⨆ x, evalNorm K x b = evalNorm K x₀ b` (`ciSup_const` after rewriting the family
as constant, via `Unique (MaximalSpectrum L)`). `of_field`: `isAlgebraic` by transport along the same
equivalence; `bddAbove` by the constant family.""",
  mathlib="""`Ideal.bot_isMaximal`, `Ideal.eq_bot_or_top`, `RingEquiv.quotientBot`, `Ideal.quotientKerAlgEquivOfSurjective`,
`minpoly.algHom_eq`, `ciSup_const`, `Unique`.""",
  sources="""BGR 3.8.1/2 (`bgr-3.8.md:38–40`): "if `A` is an algebraic extension of `k`, this definition obviously yields the
spectral norm on `A`".""",
  gen="""`[NontriviallyNormedField K] [CompleteSpace K]` come from the section (the Fibre section needs them for the
splitting-field norms); these two lemmas need only `[NormedField K]` — `omit` the extra instances at
cleanup if the linter reports them unused.""")

t(id='T016', title='Fibre upper bound: `|X(x)| ≤ σ(q)` at every point of `L[X] ⧸ (q)`', file=INT,
  deps='T001, T009, T015', par='yes (with T013, T014, T028)', typ='lemma', leaves='L3.10',
  decls=[(INT,'evalNorm_root_le_supSpectralValue')],
  sketch="""Let `x : MaximalSpectrum (AdjoinRoot q)` and `E := AdjoinRoot q ⧸ x.asIdeal`, a field, algebraic over `K`
(class) and over `L` (`Algebra L E` through `AdjoinRoot.of`; `IsScalarTower K L E`). Give `L` and `E` their
spectral norms over `K`: `letI := spectralNorm.normedField K L`, `letI := spectralNorm.normedAlgebra' K L E`
(Mathlib: `[NormedField E] [NormedAlgebra K E] [Algebra E L]`… check the direction of
`spectralNorm.normedAlgebra'`: it makes `L` a normed `E`-algebra when `K → E → L`; here use it with
`(E := L) (L := E)` names swapped). The class of `X` in `E` is a root of `q.map (algebraMap L E)`
(`AdjoinRoot.eval₂_root`/`AdjoinRoot.aeval_eq`, `Ideal.Quotient.mk` is a ring hom). Mathlib's
`norm_root_le_spectralValue (f := spectralAlgNorm L E)` — with base field `L` (normed by the `K`-spectral
norm; its `L`-spectral norm on `E` coincides with the `K`-spectral norm by `spectralNorm.eq_of_tower`, so
`IsPowMul`/`IsNonarchimedean` hold) — gives `‖root‖_E ≤ spectralValue (q)` where `spectralValue` is for the
norm on `L`, which is `supSpectralValue K q` by T009 `supSpectralValue_eq_spectralValue` and T015
`supSeminorm_eq_spectralNorm`. Finally `evalNorm K x (root q) = spectralNorm K E (mk (root q))`
(definition, `Ideal.Quotient.field`) `= ‖mk (root q)‖_E` (`NormedAlgebra.norm_eq_spectralNorm`/`rfl` for
the spectral-norm instance).""",
  mathlib="""`spectralNorm.normedField`, `spectralNorm.normedAlgebra'`, `spectralNorm.eq_of_tower`, `norm_root_le_spectralValue`,
`spectralAlgNorm`, `spectralAlgNorm_isPowMul`, `isNonarchimedean_spectralNorm`, `AdjoinRoot.of`,
`AdjoinRoot.aeval_eq`, `AdjoinRoot.eval₂_root`, `NormedAlgebra.norm_eq_spectralNorm`, `Ideal.Quotient.field`.""",
  sources="""BGR 3.8.1/6 (b), proof (`bgr-3.8.md:85–90`): "Due to Proposition 3.1.2/1, this equation implies
`|f(x)| ≤ max |b_i(φ⁻¹(x))|^{1/i}`"; BGR p. 172 (`bgr-3.8-proofs.md`): "denote by `| |_ν` the spectral norm
on `(B/y)[X]/(q_ν)` over `B/y` (which equals the spectral norm over `k` by Proposition 3.2.2/4)".""",
  gen="""Stated over an arbitrary field `L` algebraic over `K` (BGR: `L = B/y` with `y ∈ Max_k B`), with the
`HasSupSeminorm K (AdjoinRoot q)` instance as an explicit hypothesis (provided by T013 at the use site).""")

t(id='T017', title='THE FIBRE COMPUTATION: `σ(q)` is attained at a point of `L[X] ⧸ (q)` (BGR p. 172)', file=INT,
  deps='T015, T016', par='no', typ='lemma', leaves='L3.11',
  decls=[(INT,'exists_evalNorm_root_eq_supSpectralValue')],
  sketch="""Let `E := q.SplittingField` over `L` (`Polynomial.SplittingField`, with `Algebra L E`, `IsScalarTower K L E`
through `Polynomial.SplittingField.algebra'`; `E` is finite over `L` hence algebraic over `K`:
`Algebra.IsAlgebraic.trans`). Spectral norms over `K` on `L` and `E` as in T016. `q.map (algebraMap L E)`
splits: `q.map _ = ∏_{a ∈ roots} (X − C a)` (`Splits.eq_prod_roots_of_monic`, `SplittingField.splits`).
Mathlib `max_norm_root_eq_spectralValue (K := L) (L := E) (f := spectralAlgNorm L E)` (power-multiplicative,
nonarchimedean, `f 1 = 1`; `mapAlg L E q = ∏ (X - C a)`) gives `(⨆ a, if a ∈ roots then ‖a‖ else 0) =
spectralValue q = supSpectralValue K q` (T009, T015). The roots form a nonempty finite multiset (`natDegree > 0`,
`Multiset.card_roots'`/`Polynomial.natDegree_eq_card_roots` for split polynomials), so some root `a₀` attains
`‖a₀‖ = σ(q)` (`Finset.exists_max_image` on `roots.toFinset`). Now `AdjoinRoot.liftAlgHom`-style evaluation
`ev : AdjoinRoot q →ₐ[L] E`, `root q ↦ a₀` (`AdjoinRoot.liftAlgHom (Algebra.ofId L E) a₀ (by simpa using
root)`; restrict scalars to `K`); its kernel is a maximal ideal `x` (Layer 0 `isMaximal_ker_of_isAlgebraic`
for `ev.restrictScalars K` into the algebraic field `E`), and Layer 0 `evalNorm_eq_norm_algHom` (with `L := E`
normed by the spectral norm — `NormedAlgebra K E`, `Algebra.IsAlgebraic K E`) gives
`evalNorm K x (root q) = ‖ev (root q)‖ = ‖a₀‖ = σ(q)`.""",
  mathlib="""`Polynomial.SplittingField`, `Polynomial.SplittingField.splits`, `Polynomial.SplittingField.algebra'`,
`Splits.eq_prod_roots_of_monic`, `max_norm_root_eq_spectralValue`, `mapAlg`, `Polynomial.natDegree_eq_card_roots`,
`Finset.exists_max_image`, `AdjoinRoot.liftAlgHom`, `AlgHom.restrictScalars`; Layer 0
`Affinoid.isMaximal_ker_of_isAlgebraic`, `Affinoid.evalNorm_eq_norm_algHom`, and the Layer 0 pattern in
`TateAlgebra/MaxModulus.lean` (`letI := spectralNorm.normedField K E; letI := spectralNorm.normedAlgebra K E;
haveI : IsUltrametricDist E := …; haveI := spectralNorm.completeSpace K E`).""",
  sources="""BGR p. 172 (`bgr-3.8-proofs.md`, proof of 3.8.1/7 (a)): "`red (A/yA) = (B/y)[X]/(q₁ ⋯ q_r) = ⊕ (B/y)[X]/(q_ν)`.
Provide `B/y` with the spectral norm over `k` … Then if `f̄_ν` is the residue class of `f̄_y` in
`(B/y)[X]/(q_ν)`, we have by Corollary 3.2.1/6 `|f̄_y|_sup = max_ν |f̄_ν|_ν = max_ν σ(q_ν) = σ(q_y)`"; BGR 1.5.4
"if a monic polynomial splits into linear factors, then its spectral value is the norm of its largest root"
(Mathlib's docstring of `spectralValue`).""",
  gen="""Formulated on `AdjoinRoot q` for a monic `q ∈ L[X]` of positive degree over a field `L` algebraic over `K`:
BGR's `A/yA = (B/y)[X]/(q_y)` is this with `L = B/y`. Our route goes through ONE splitting field and the
evaluation at a maximal root instead of BGR's prime factorisation `q_y = ∏ q_ν^{n_ν}` and the reduced ring
`⊕ (B/y)[X]/(q_ν)` (the point over the factor `q_ν` of the root `a₀` is the kernel of `ev`); both facts
BGR invoke (3.2.1/6, 3.2.2/4) are replaced by Mathlib's `max_norm_root_eq_spectralValue`.""")

t(id='T018', title='`σ(minpoly_B f) ≤ |f|_sup`: the lower bound of BGR 3.8.1/7 (a)', file=INT,
  deps='T006, T009, T011, T014, T017', par='no', typ='lemma', leaves='L3.12',
  decls=[(INT,'supSpectralValue_minpoly_le_supSeminorm')],
  sketch="""Let `q := minpoly B f` (monic: `minpoly.monic (Algebra.IsIntegral.isIntegral f)`, positive degree:
`minpoly.natDegree_pos`). Step 1 (BGR: "we may assume `A = B[f]`"): let `A' := Algebra.adjoin B {f}`; `A'` is
integral over `B`, `A` is integral over `A'` (`Algebra.IsIntegral.tower_top`), and `A' → A` is injective, so
`supSeminorm K (f : A') = supSeminorm K f` by T014 `supSeminorm_algebraMap_eq` (with `HasSupSeminorm K A'` from
T013 `of_isIntegral_of_faithfulSMul` applied to `A' ↪ A`, or from `of_isIntegral` over `B`). So it suffices
to prove the bound on `A'`. Step 2: `AdjoinRoot q ≃ₐ[B] A'`: `AdjoinRoot.equiv'`/`Algebra.adjoin.powerBasis'`
… the cleanest is `minpoly.equivAdjoin`-type for integrally closed `B` — Mathlib: `AdjoinRoot.equiv' q
(Algebra.adjoin.powerBasis' hf)` with the `minpoly` identification `minpoly_powerBasis_gen_of_monic`; or
avoid the equivalence: the surjection `AdjoinRoot.liftAlgHom q f : AdjoinRoot q →ₐ[B] A'` is injective
because its kernel is `span {q}` (`minpoly.ker_eval`, `AdjoinRoot.mk_eq_zero`), hence an isomorphism
(`AlgEquiv.ofBijective`). Transport the seminorm along it (`supSeminorm_map_le` both ways, or
`evalNorm`-level equality through `comapPoint`): `supSeminorm K (root q) = supSeminorm K (f : A')`.
Step 3 (the fibre over `y`): for `y : MaximalSpectrum B`, `AdjoinRoot q ⧸ (y.asIdeal.map (of q)) ≃ₐ[B]
AdjoinRoot (q.map (mk y))` (`AdjoinRoot.quotEquivQuotMap q y.asIdeal`, then `AdjoinRoot` of the mapped
polynomial over the field `L := B ⧸ y`); by T006/T014, `supSeminorm K (root q) ≥ supSeminorm K (mk _ (root q))
= supSeminorm K (root q̄)` (transport along the equivalence; the class on `AdjoinRoot q̄` from T013 over `L`
with T015) `= σ(q̄)` where `≥` is T017's attained point (and `≤` T016; equality is not needed, only `≥`).
Step 4: `σ(q̄) ≥ |b_i(y)|^{1/i}` for each coefficient (T009 `terms_le`, `q̄.coeff i = mk y (q.coeff i)`,
`Monic.natDegree_map`, and `supSeminorm K (mk y b) = evalNorm K y b` by T015 on the field `L` + T006), so
`|f|_sup ≥ sup_y max_i |b_i(y)|^{1/i} = max_i |b_i|_sup^{1/i} = σ(q)`: for each `i`,
`|b_i|_sup = ⨆ y, |b_i(y)|` (definition), take `rpow` (monotone, `Real.iSup_rpow`-free: show
`|b_i(y)|^{1/i} ≤ |f|_sup` for all `y`, hence `|b_i|_sup^{1/i} ≤ |f|_sup` by `Real.rpow_le_rpow` after
`ciSup_le` on `|b_i(y)| ≤ |f|_sup^i`), then `supSpectralValue_le_of_forall`.""",
  mathlib="""`minpoly.monic`, `minpoly.natDegree_pos`, `minpoly.ker_eval`, `AdjoinRoot.liftAlgHom`, `AdjoinRoot.mk_eq_zero`,
`AlgEquiv.ofBijective`, `Algebra.adjoin`, `Algebra.IsIntegral.tower_top`, `AdjoinRoot.quotEquivQuotMap`,
`Polynomial.coeff_map`, `Polynomial.Monic.natDegree_map`, `Real.rpow_le_rpow`, `ciSup_le`,
`Real.rpow_natCast`.""",
  sources="""BGR 3.8.1/7, proof Ad (a) (`bgr-3.8-proofs.md`): "We may assume that `B` is a subalgebra of `A` and that
`A = B[f]` … `A = B[f] ≅ B[X]/(q)` … `|f|_sup = sup_{y ∈ Max_k B} |f_y|_sup = sup_y |f̄_y|_sup` … `A/yA =
(B/y)[X]/(q_y)` … `|f̄_y|_sup = σ(q_y)`. Therefore `|f|_sup = sup_y σ(q_y) = sup_y max_i |b_i(y)|^{1/i}
= max_i |b_i|_sup^{1/i}`"; the preliminaries pp. 171–172 for `B[X]/(q) ≅ B[f]` ("`ker τ` is generated by `q`",
= `minpoly.ker_eval`).""",
  gen="""`A` a domain (plan D8), `B` an integrally closed domain, `[Algebra.IsIntegral B A] [Module.IsTorsionFree B A]`,
both with `HasSupSeminorm`; `[CompleteSpace K]` through the fibre computation. Only the `≥` half of the
fibre identity is used here; T010 gives `≤` globally.""")

t(id='T019', title='M1 — BGR 3.8.1/7 (a): `|f|_sup = σ(minpoly_B f)`', file=INT, deps='T010, T018', par='no',
  typ='theorem', leaves='L3.13', milestone='M1 ([RM] §2.1.4, BGR 3.8.1/7 (a))',
  decls=[(INT,'supSeminorm_eq_supSpectralValue_minpoly')],
  sketch="""`le_antisymm (supSeminorm_le_supSpectralValue_of_eval₂_eq_zero K (IsScalarTower.toAlgHom K B A)
(minpoly.monic _) (by simpa [Polynomial.aeval_def] using minpoly.aeval B f)) (supSpectralValue_minpoly_le_supSeminorm K f)`.
Then `#print axioms` (standard) and record in `tickets.md`.""",
  mathlib="""`minpoly.aeval`, `Polynomial.aeval_def`, `IsScalarTower.toAlgHom`.""",
  sources="""BGR 3.8.1/7 (a) (`bgr-3.8-proofs.md`): "`|f|_sup = max_{1≤i≤n} |b_i|_sup^{1/i}` for `f ∈ A`, where
`fⁿ + φ(b₁) fⁿ⁻¹ + ⋯ + φ(bₙ) = 0` is the (unique) integral equation of minimal degree for `f` over `φ(B)`".""",
  gen="""As T018.""")

t(id='T020', title='`minpoly (b • f)` is the scaled polynomial; `|φ(b) f|_sup = |b|_sup |f|_sup` (BGR 3.8.1/7 (d))',
  file=INT, deps='T019', par='yes (with T021, T022, T023, T028)', typ='lemmas', leaves='L3.14–L3.15',
  decls=[(INT,'minpoly_algebraMap_mul_eq_scaleRoots'),(INT,'supSeminorm_algebraMap_mul')],
  sketch="""`minpoly_algebraMap_mul_eq_scaleRoots`: `p := (minpoly B f).scaleRoots b` is monic (`monic_scaleRoots_iff`),
has `b•f` as a root (`scaleRoots_aeval_eq_zero (minpoly.aeval B f)`, `Algebra.smul_def`), and
`natDegree p = natDegree (minpoly B f)` (`natDegree_scaleRoots`). `minpoly B (b•f) ∣ p`
(`minpoly.isIntegrallyClosed_dvd`, needs `IsIntegral B (b • f)`: product of integrals) and
`natDegree (minpoly B (b•f)) ≥ natDegree (minpoly B f)`: both equal the degrees over `Q(B)`
(`minpoly.isIntegrallyClosed_eq_field_fractions'` + `natDegree_map`), and over the field `Q(B)` the
elements `f` and `b•f` (with `b ≠ 0` a unit of `Q(B)`) generate the same intermediate field, so
`minpoly.natDegree_eq_finrank`-style equality (`IntermediateField.adjoin_simple_eq`? easier: apply the
same divisibility argument symmetrically: `f = b⁻¹ • (b•f)` in `Q(A)`, so `minpoly_{Q(B)} f ∣
(minpoly_{Q(B)} (b•f)).scaleRoots b⁻¹`, giving `deg f ≤ deg (b•f)`). Monic divisor of a monic polynomial
of the same degree: `Polynomial.eq_of_monic_of_dvd_of_natDegree_le`. `supSeminorm_algebraMap_mul`: `b = 0`
trivial (`supSeminorm_zero`, `zero_mul`); else by M1 twice and the scaled polynomial:
`σ(q.scaleRoots b)`'s terms are `|b^{n-i} b_i|_sup^{1/(n-i)} = |b|_sup |b_i|_sup^{1/(n-i)}` using `hB` for
`|b^{n-i} b_i| = |b|^{n-i} |b_i|` and `Real.mul_rpow`; so `σ(q.scaleRoots b) = |b|_sup σ(q)`
(`Real.mul_iSup_of_nonneg`).""",
  mathlib="""`Polynomial.scaleRoots`, `monic_scaleRoots_iff`, `scaleRoots_aeval_eq_zero`, `natDegree_scaleRoots`,
`coeff_scaleRoots`, `minpoly.isIntegrallyClosed_dvd`, `minpoly.isIntegrallyClosed_eq_field_fractions'`,
`Polynomial.eq_of_monic_of_dvd_of_natDegree_le`, `IsIntegral.mul`, `Real.mul_rpow`, `Real.mul_iSup_of_nonneg`.""",
  sources="""BGR 3.8.1/7, proof Ad (d) (`bgr-3.8-proofs.md`): "`f` is of degree `n` over the fraction field `Q(B)`, and so
is any product `bf` where `b ∈ B − {0}`. Therefore `(bf)ⁿ + bb₁(bf)ⁿ⁻¹ + ⋯ + bⁿbₙ = 0` is the integral
equation of minimal degree for any such product `bf` … `|bf|_sup = max |b^i b_i|_sup^{1/i} = |b|_sup
max |b_i|_sup^{1/i} = |b|_sup |f|_sup`".""",
  gen="""Only the "if" direction of (d) (the "only if" is 3.8.1/6 (a), T014). `hB` is BGR's "`| |_sup` is
multiplicative on `B`" (for `T_d`: the Gauss norm is multiplicative, Layer 0 `NormMulClass`).""")

t(id='T021', title='The maximum modulus principle and the norm property transfer along integral maps (BGR 3.8.1/7 (b), (c))',
  file=INT, deps='T009, T017, T019', par='yes (with T020, T022, T023, T028)', typ='lemmas', leaves='L3.16–L3.17',
  decls=[(INT,'exists_evalNorm_eq_supSeminorm_of_forall_exists'),(INT,'eq_zero_of_supSeminorm_eq_zero')],
  sketch="""(b): `q := minpoly B f`; if `|f|_sup = 0` any point works (`A` is a domain so nontrivial; take any `x`,
`evalNorm_nonneg` + `evalNorm_le_supSeminorm`). Else `σ(q) = |f|_sup ≠ 0` is attained at a coefficient index
`i` (T009 `exists_supSpectralValue_eq`); by `hB` pick `y` with `|b_i(y)| = |b_i|_sup`. Then `σ(q̄_y) ≥
|b_i(y)|^{1/(n-i)} = σ(q)` (T009 on `L = B ⧸ y` as in T018 step 4), and `≤` by T011 `map_le`-style
(coefficientwise `|b(y)| ≤ |b|_sup`); so `σ(q̄_y) = |f|_sup`. T017 gives a point `x̄` of `AdjoinRoot q̄_y` with
`evalNorm x̄ (root q̄_y) = σ(q̄_y)`; transport to a point of `A ⧸ yA`-side: through the equivalences of T018
(steps 2–3) the point `x̄` corresponds to a maximal ideal `x` of `A'` = `B[f]` over `y`, and then to a maximal
ideal of `A` lying over it (T012 going up, `A` integral over `A'`), with `evalNorm K x f = evalNorm x̄ (root)`
(`evalNorm_comapPoint`/`evalNorm_eq_norm_algHom` along the composite). (c): `f ≠ 0`, `q := minpoly B f` has some
coefficient `b_i ≠ 0` with `i < n` (else `q = Xⁿ`, so `fⁿ = 0`, `f = 0` in the domain `A`), `|b_i|_sup ≠ 0` by `hB`,
so `|f|_sup = σ(q) ≥ |b_i|_sup^{1/(n-i)} > 0` (M1 + `terms_le` + `Real.rpow_pos_of_pos`).""",
  mathlib="""`Real.rpow_pos_of_pos`, `Polynomial.ext_iff`, `pow_eq_zero_iff`, `minpoly.natDegree_pos`, `Finset.exists_max_image`.""",
  sources="""BGR 3.8.1/7, proof Ad (b) and Ad (c) (`bgr-3.8-proofs.md`): "there is a `y ∈ Max_k B` such that
`|f̄_y|_sup = σ(q_y) = |f|_sup`. Since `A/yA` contains only finitely many maximal ideals, there must exist an
`x ∈ Max_k A` such that `|f̄_y|_sup = |f(x)|`" / "Because `A` is reduced, there exists an index `m` … `b_m ≠ 0`
… `|f|_sup ≥ |b_m|_sup^{1/m} > 0`".""",
  gen="""(b) is stated in the `∀ b, ∃ y, …` form (the hypothesis "the maximum modulus principle holds for `B`"), (c) in
the `∀ b, |b|_sup = 0 → b = 0` form, both for `A` a domain (D8); the converses are T014/T013.""")

t(id='T022', title='A uniform power of `|f|_sup` lies in `‖K‖` (BGR 3.8.1/8, the form 6.2.1/4 (ii) needs)', file=INT,
  deps='T009, T019', par='yes (with T020, T021, T023, T028)', typ='lemma', leaves='L3.18',
  decls=[(INT,'supSeminorm_pow_factorial_mem_range_norm')],
  sketch="""`q := minpoly B f`, `d := natDegree q ≥ 1`, `d ≤ n`. By M1 and T009 `exists_supSpectralValue_eq`,
`|f|_sup = |b_i|_sup ^ (1/(d-i))` for some `i < d`; set `j := d - i ∈ [1, n]`, so `|f|_sup ^ j = |b_i|_sup`
(`Real.rpow_inv_natCast_pow`, nonneg) `= ‖c‖` for some `c : K` (`hB`). Since `j ∣ n!` (`Nat.dvd_factorial`),
`|f|_sup ^ n! = (|f|_sup ^ j) ^ (n!/j) = ‖c‖ ^ (n!/j) = ‖c ^ (n!/j)‖` (`norm_pow`), i.e. `∈ Set.range ‖·‖`.""",
  mathlib="""`Nat.dvd_factorial`, `Nat.div_mul_cancel`, `pow_mul`, `norm_pow`, `Real.rpow_inv_natCast_pow`, `Set.mem_range`.""",
  sources="""BGR 3.8.1/8, proof (`bgr-3.8-proofs.md`): "According to assertion (a) of the preceding proposition,
`|f|_sup ∈ |k_a|` for all `f ∈ A`. Hence there are an element `d ∈ k` and an integer `m` such that
`|d|^{1/m} = |f|_sup`"; the uniform exponent is [RM] §2.2.2 ("State the uniform version: `m` may be chosen to
depend only on `A`"), with `|T_d|_sup = |K|` replacing BGR's `|k_a|`.""",
  gen="""Hypotheses: `|B|_sup ⊆ ‖K‖` (true for `T_d`: Gauss norms are coefficient norms) and a degree bound
`∀ f, natDegree (minpoly B f) ≤ n` (supplied in `Affinoid/SupSeminorm.lean` from
`FractionRing.finiteDimensional_of_finite` + `minpoly.natDegree_le`). Exponent `n!` (any common multiple
of `1..n` would do).""")

# ---------------------------------------------------------------- SupSeminorm/Banach.lean
t(id='T023', title='Continuity into a Banach algebra on which `|·|_sup` is a norm; all complete norms equivalent (BGR 3.8.2/3–4)',
  file=BAN, deps='T004, T005', par='yes (with T020–T022, T028)', typ='lemmas', leaves='L4.1–L4.3',
  decls=[(BAN,'MaximalSpectrum.isClosed_asIdeal'),(BAN,'AlgHom.continuous_of_supSeminorm_eq_zero_imp'),
         (BAN,'AlgEquiv.exists_forall_norm_le_mul_of_supSeminorm_eq_zero_imp')],
  sketch="""`isClosed_asIdeal`: `Ideal.IsMaximal.isClosed` (needs `HasSummableGeomSeries A`: instance from
`[NormedRing A] [CompleteSpace A]`). `continuous_of…`: Layer 1
`AlgHom.continuous_of_forall_isClosed_of_finiteDimensional φ {𝔪 | 𝔪.IsMaximal}` with: `hB` closed by the first
lemma; `hA`: `𝔪.comap φ` is maximal (T005 `isMaximal_comap_of_isAlgebraic` with `x := ⟨𝔪, h⟩`, the class gives
algebraicity) hence closed in the Banach algebra `B` (`Ideal.IsMaximal.isClosed` again); `hfin` from the
hypothesis; `hinf`: `sInf {𝔪 | IsMaximal} = jacobson ⊥` (`Ideal.jacobson` is `sInf` of maximals ⊇ `⊥`,
`Ideal.jacobson_bot`-style unfolding) `= ⊥` because `f ∈ jacobson ⊥ ↔ |f|_sup = 0` (T004) `→ f = 0` (`hA`).
`exists_forall_norm_le_mul…`: `e.symm : B →ₐ[K] A` is continuous by the previous lemma (hypotheses on `A`);
then `e = (e.symm)⁻¹` is continuous by the open mapping theorem for the continuous linear bijection
`e.symm.toLinearMap` (`LinearEquiv.continuous_symm`/`ContinuousLinearEquiv.ofBijective`), and a continuous
linear map is bounded (`ContinuousLinearMap.exists_bound`/`LinearMap.continuous_iff_isBoundedLinearMap`).
Layer 1's `AlgEquiv.exists_forall_norm_le_mul_of_isNoetherianRing` is the template.""",
  mathlib="""`Ideal.IsMaximal.isClosed`, `HasSummableGeomSeries`, `Ideal.jacobson`, `Ideal.sInf_eq_bot`?, `LinearEquiv.continuous_symm`,
`ContinuousLinearMap.exists_bound`, `AlgEquiv.toLinearEquiv`; Layer 1 `AlgHom.continuous_of_forall_isClosed_of_finiteDimensional`,
`AlgEquiv.exists_forall_norm_le_mul_of_isNoetherianRing` (template).""",
  sources="""BGR 3.8.2/3 and proof (`bgr-3.8-proofs.md`): "`φ⁻¹(x) ∈ Max_k B` … Then by Lemma 3.8.1/9, we may finish the proof
by using the Closed Graph Theorem (in almost literally the same way as in the proof of Proposition 3.7.5/1)";
BGR 3.8.2/4: "all complete `k`-algebra norms on `A` are equivalent".""",
  gen="""BGR take `|·|_sup` a norm on `A` with `A` Banach and `Max_k A` the algebraic points; we add the finiteness of the
residue fields (`hfin`) because Layer 1's closed-graph lemma asks for `FiniteDimensional K (B ⧸ 𝔟)` (BGR 3.7.5/1 uses
"`A/𝔟` finite-dimensional" too). Affinoid algebras satisfy it.""")

t(id='T024', title='`|f|_sup ≤ inf ‖fⁱ‖^{1/i}`; power-bounded elements have `|f|_sup ≤ 1`', file=BAN, deps='T003',
  par='yes (with T020–T023, T028)', typ='lemmas', leaves='L4.4–L4.6',
  decls=[(BAN,'supSeminorm_le_norm_pow_rpow'),(BAN,'supSeminorm_le_smoothingFun'),(BAN,'IsPowerBounded.supSeminorm_le_one')],
  sketch="""`supSeminorm_le_norm_pow_rpow`: `|f|_sup = |f^i|_sup^(1/i) ≤ ‖f^i‖^(1/i)` by `supSeminorm_pow` (`i ≠ 0`),
Layer 0 `supSeminorm_le_norm`, `Real.rpow_le_rpow`, `Real.pow_rpow_inv_natCast`. `supSeminorm_le_smoothingFun`:
`smoothingFun μ f = ⨅ n : ℕ+, μ (f^n) ^ (1/n)` (unfold the `abbrev`), `μ = SeminormedRing.toRingSeminorm A` is the
norm; `le_ciInf` (`ℕ+` nonempty) with the first lemma. `IsPowerBounded.supSeminorm_le_one`: by
`IsPowerBounded.exists_norm_pow_le K` (PFA) get `C` with `‖f^n‖ ≤ C`; then `|f|_sup^n ≤ C` for all `n ≥ 1`, so
`|f|_sup ≤ 1` (`pow_le_one`-contrapositive: if `|f|_sup > 1` then `|f|_sup^n → ∞`, `tendsto_pow_atTop_atTop_of_one_lt`;
or `Real.le_one_of_pow_le`-style: `|f|_sup ≤ C^(1/n) → 1`).""",
  mathlib="""`smoothingFun`, `le_ciInf`, `Real.rpow_le_rpow`, `Real.pow_rpow_inv_natCast`, `tendsto_pow_atTop_atTop_of_one_lt`,
`PowerBounded.IsPowerBounded.exists_norm_pow_le`, `SeminormedRing.toRingSeminorm`.""",
  sources="""BGR 3.8.2/5, proof (`bgr-3.8-proofs.md`): "From Corollary 2 one deduces immediately that `|f|_sup ≤ |f|_r`";
BGR 6.2.3 intro (`bgr-6.2-6.3.1.md`): "all power-bounded elements `f ∈ A` must satisfy `|f|_sup ≤ 1`, since
`| |_sup` is power-multiplicative".""",
  gen="""Any Banach `K`-algebra with `HasSupSeminorm`; `IsPowerBounded` is PFA's topological notion (needs
`NontriviallyNormedField K` for the norm bound).""")

t(id='T025', title='The smoothing seminorm of a root is bounded by the spectral value of its equation (BGR 3.1.2/1 for `|·|_r`)',
  file=BAN, deps='none', par='yes (with T020–T024, T028)', typ='lemma', leaves='L4.7',
  decls=[(BAN,'smoothingFun_le_of_eval₂_eq_zero')],
  sketch="""`μ' := smoothingSeminorm μ hμ1 hna` with `μ := SeminormedRing.toRingSeminorm A`, `hμ1 : μ 1 ≤ 1`
(`NormOneClass`), `hna : IsNonarchimedean μ` (`IsUltrametricDist.isNonarchimedean_norm`); `μ'` is a `RingSeminorm`
(submultiplicative), power-multiplicative (`isPowMul_smoothingFun hμ1`), nonarchimedean
(`isNonarchimedean_smoothingFun`), with `μ' ≤ μ` (`smoothingFun_le_self`) and `μ' f = smoothingFun μ f`
(`smoothingSeminorm_apply`-level `rfl`). Then repeat T010's argument for `μ'` in place of `|·|_sup`:
`f^n = -∑_{i<n} φ(b_i) f^i`, `μ'(f)^n = μ'(f^n) ≤ max_i μ'(φ b_i) μ'(f)^i ≤ max_i ‖φ b_i‖ μ'(f)^i`, pick the
maximising `i`, divide: `μ'(f) ≤ ‖φ b_i‖^(1/(n-i)) ≤ ⨆ j : Fin n, ‖φ (coeff j)‖^(1/(n-j))` (`le_ciSup`, finite
family). Trivial `A`/`n = 0`: `μ' f = 0` (norm `0`) and the `iSup` over `Fin 0` is `0`.""",
  mathlib="""`smoothingSeminorm`, `isPowMul_smoothingFun`, `isNonarchimedean_smoothingFun`, `smoothingFun_le_self`,
`IsUltrametricDist.isNonarchimedean_norm`, `RingSeminorm.mul_le'`?, `Finset.exists_max_image`, `le_ciSup`,
`Real.iSup_of_isEmpty`.""",
  sources="""BGR 3.8.2/5, proof (`bgr-3.8-proofs.md`): "Since `| |_r` is a power-multiplicative semi-norm on `A`, one can
apply Proposition 3.1.2/1 to `A/ker | |_r` (viewed as a normed algebra over itself), and one gets
`|f|_r ≤ max |φ(b_i)|_r^{1/i} ≤ max |φ(b_i)|^{1/i}`".""",
  gen="""Stated for any ring hom `φ : B →+* A` (no `K`) and the norm's smoothing seminorm; the bound is phrased with the
coefficient norms `‖φ (coeff n)‖` in the `supSpectralValueTerms` shape.""")

t(id='T026', title='BGR 3.8.2/5: `|f|_sup = inf ‖fⁱ‖^{1/i}` along a continuous integral monomorphism', file=BAN,
  deps='T019, T024, T025', par='no', typ='theorem', leaves='L4.8',
  decls=[(BAN,'supSeminorm_eq_smoothingFun_of_isIntegral')],
  sketch="""`≤`: T024. `≥`: with `q := minpoly B f`, T025 gives `μ'(f) ≤ max_i ‖algebraMap (coeff i)‖^(1/(n-i)) ≤
max_i (C |coeff i|_sup)^(1/(n-i))` (`hC`, `Real.rpow_le_rpow`) `≤ C' max_i |coeff i|_sup^(1/(n-i)) = C' σ(q)
= C' |f|_sup` (M1), where `C' := max 1 C` handles `C^(1/j) ≤ C'` for `j ≥ 1` (`Real.rpow_le_self_of_one_le`-type:
`C^(1/j) ≤ max 1 C` since `1/j ≤ 1`). So `μ'(f) ≤ C' |f|_sup` for ALL `f`; apply to `f^m`: `μ'(f)^m ≤ C' |f|_sup^m`
(both power-multiplicative), take `m`-th roots and let `m → ∞` (`C'^(1/m) → 1`: `tendsto_rpow_div`-style,
`Real.tendsto_rpow_div_one`? use `le_of_tendsto` with `Filter.Tendsto (fun m ↦ C'^(1/m)) atTop (𝓝 1)` from
`tendsto_const_rpow_inv`?? — concretely `Real.rpow_natCast`-free: if `μ'(f) > |f|_sup` then `(μ'(f)/|f|_sup)^m ≤ C'`
for all `m` with ratio `> 1`, contradiction with `tendsto_pow_atTop_atTop_of_one_lt`; the case `|f|_sup = 0`
forces `μ'(f)^m ≤ 0`, so `μ'(f) = 0`). This is BGR's "This implies `|f|_r ≤ |f|_sup`, since both `| |_r` and
`| |_sup` are power-multiplicative" (= BGR 1.3.1/2, the contraction argument of T001-type).""",
  mathlib="""`isPowMul_smoothingFun`, `tendsto_pow_atTop_atTop_of_one_lt`, `Real.rpow_le_rpow`, `Real.mul_rpow`,
`Real.rpow_le_rpow_left_iff`, `div_pow`, `le_max_right`.""",
  sources="""BGR 3.8.2/5 and proof (`bgr-3.8-proofs.md`): "Because `φ` is continuous, there is a real constant `C > 1` such
that `|φ(b)| ≤ C|b|_sup` for all `b ∈ B`, and a fortiori `|φ(b)|^{1/i} ≤ C|b|_sup^{1/i}` … we have shown that
`|f|_r ≤ C max |b_i|_sup^{1/i} = C|f|_sup`. This implies `|f|_r ≤ |f|_sup`, since both `| |_r` and `| |_sup`
are power-multiplicative."; BGR 1.3.1/2 (`bgr-1.3-1.5.md`).""",
  gen="""Hypotheses of 3.8.1/7 (D8: `A` a domain) plus `A` Banach and the continuity bound `hC`; BGR's "`φ` continuous
if `B` is provided with the topology induced by `| |_sup`" is exactly `‖algebraMap b‖ ≤ C |b|_sup`.""")

t(id='T027', title='BGR 3.8.2/6: power-bounded ⇔ `|f|_sup ≤ 1`, topologically nilpotent ⇔ `|f|_sup < 1`', file=BAN,
  deps='T024, T026', par='no', typ='lemmas', leaves='L4.9–L4.10',
  decls=[(BAN,'isPowerBounded_of_supSeminorm_le_one_of_isIntegral'),(BAN,'isTopologicallyNilpotent_iff_supSeminorm_lt_one_of_isIntegral')],
  sketch="""`isPowerBounded_of…`: `q := minpoly B f`, `n := natDegree q ≥ 1`; by M1, `|f|_sup ≤ 1` gives `|coeff i|_sup ≤ 1`
for every `i < n` (T009 `coeff_le_pow` with `σ(q) ≤ 1`). Let `R := Subring.closure (range (algebraMap ∘ coeff))`
… simpler: show by induction on `j` that `f^j ∈ N := Submodule.span (Subring.closure {coeff i}) {f^i | i < n}`-free
version: prove `∀ j, ∃ c : Fin n → B, (∀ i, |c i|_sup ≤ 1) ∧ f^j = ∑ i, algebraMap (c i) * f^i` by induction
(`f^{j+1} = ∑ c_i f^{i+1}`; `f^n = -∑ b_i f^i` replaces the top term; the new coefficients are
`c_{i-1} - c_{n-1} b_i`, still of `|·|_sup ≤ 1` by `supSeminorm_add_le_max`, `supSeminorm_mul_le`, `supSeminorm_neg`).
Then `‖f^j‖ ≤ max_i ‖algebraMap (c i)‖ ‖f^i‖ ≤ C · max_i ‖f^i‖` (`hC`, `IsUltrametricDist` sum bound
`IsUltrametricDist.norm_sum_le_of_forall_le`?, `norm_mul_le`), a bound independent of `j`:
`isPowerBounded_of_norm_pow_le` (PFA). `isTopologicallyNilpotent_iff…`: (a) ⇔ (b) `inf ‖fⁱ‖^{1/i} < 1`:
`→`: `‖f^n‖ → 0` so some `‖f^m‖ < 1`, hence `smoothingFun ≤ ‖f^m‖^{1/m} < 1` (`smoothingFun_le`, `Real.rpow_lt_one`);
`←`: some `‖f^m‖^{1/m} < 1` (`ciInf_lt_iff`/`exists_lt_of_ciInf_lt`), so `r := ‖f^m‖ < 1` and `f^m` is
topologically nilpotent (`IsTopologicallyNilpotent.of_norm_lt_one`, PFA), hence `f` is (BGR 1.2.5/7 argument:
`‖f^{mq+s}‖ ≤ ‖f^m‖^q max_{s<m} ‖f^s‖ → 0`; write `n = m*q + s` by `Nat.div_add_mod`, `norm_mul_le`,
`squeeze_zero`). (b) ⇔ (c) by T026.""",
  mathlib="""`PowerBounded.isPowerBounded_of_norm_pow_le`, `IsTopologicallyNilpotent.of_norm_lt_one`, `smoothingFun_le`,
`exists_lt_of_ciInf_lt`, `Real.rpow_lt_one`, `Nat.div_add_mod`, `squeeze_zero`, `tendsto_pow_atTop_nhds_zero_of_lt_one`,
`IsUltrametricDist.norm_sum_le_of_forall_le`?/`exists_norm_finsetSum_le_of_nonempty`.""",
  sources="""BGR 3.8.2/6 and proof (`bgr-3.8-proofs.md`): "(c') implies (a'): … from (c') we get `|b_i|_sup ≤ 1` … Since `φ` is
continuous, `R := φ(P)[φ(b₁), …, φ(bₙ)]` is bounded under `| |`. From the integral equation for `f`, one easily
derives `f^j ∈ Σ_{i=0}^{n−1} R f^i` for all `j ∈ ℕ` (use induction on `j`). Hence `f` is power-bounded"; "it is
easily seen that an element `f` is topologically nilpotent in `A` if and only if `inf |f^i|^{1/i} < 1`".""",
  gen="""Under the hypotheses of 3.8.2/5 (`A` a domain, D8). The affinoid versions (6.2.3/1–2) are proved
separately in `Affinoid/PowerBounded.lean` without domain hypotheses (BGR's direct proofs).""")

# ---------------------------------------------------------------- BanachAlgebra/Module.lean
t(id='T028', title='Nakayama for the unit ball and open mapping for finitely generated submodules of `Aⁿ`', file=MOD,
  deps='none', par='yes (with T001–T027)', typ='lemmas', leaves='L5.1–L5.2',
  decls=[(MOD,'Submodule.forall_mem_of_forall_exists_eq_add_sum_smul_of_norm_lt_one'),(MOD,'Submodule.exists_forall_exists_eq_sum_smul_norm_le')],
  sketch="""Both are the module versions of Layer 1 `BanachAlgebra/Noetherian.lean`, whose proofs port with `*` replaced
by `•`. Nakayama: work in the `unitClosedBall A`-module `Fin n → unitClosedBall A`?? — Layer 1's trick: view the
`Fin m` vectors `x i` as generating the `Å := unitClosedBall A`-submodule `M := span Å (range x)` of the
`Å`-module `Fin n → A` (restrict scalars: `(Fin n → A)` is an `Å`-module via `Subring` coercion,
`Module.compHom`/`Subring.module`); the hypothesis says `M ≤ N' + 𝔞 • M` with `𝔞 := openUnitBallIdeal A`
(`Ideal.smul`), `N' := N.restrictScalars Å`; `𝔞 ≤ jacobson ⊥` (PFA `openUnitBallIdeal_le_jacobson_bot`), so
`Submodule.le_of_le_smul_of_le_jacobson_bot` (Nakayama, `M` finitely generated) gives `M ≤ N'`. Copy the proof of
`Ideal.forall_mem_of_forall_exists_eq_add_sum_mul_of_norm_lt_one` (Layer 1, lines 44–73) line by line. Open mapping:
the `K`-linear map `π : (Fin m → A) →L[K] N`, `a ↦ ⟨∑ a i • x i, _⟩` is continuous (`ContinuousLinearMap`, finite
sum of continuous smul) and surjective (`hx`), `N` is complete (closed in the Banach space `Fin n → A`:
`IsClosed.completeSpace_coe`), so `ContinuousLinearMap.exists_preimage_norm_le` gives `C` with preimages of norm
`≤ C ‖z‖`; coordinates `‖a i‖ ≤ ‖a‖` (`norm_le_pi_norm`). Copy `Ideal.exists_forall_exists_eq_sum_mul_norm_le`
(Layer 1, lines 77–110).""",
  mathlib="""`Submodule.le_of_le_smul_of_le_jacobson_bot`, `Submodule.restrictScalars`, `Ideal.smul`?,
`ContinuousLinearMap.exists_preimage_norm_le`, `IsClosed.completeSpace_coe`, `norm_le_pi_norm`, `Submodule.span`,
`Submodule.mem_span_range_iff_exists_fun`; PFA `openUnitBallIdeal_le_jacobson_bot`, `unitClosedBall`.""",
  sources="""BGR 3.7.2/2 and its proof (`bgr-3.7.md:39–46`, via 3.7.2/1 and 1.2.4/6 "Let `A` be complete and let `M` be an
`A`-module. Let `N` be a submodule of `M` such that …" — the Nakayama lemma for `Ǎ`); Layer 1's
`BanachAlgebra/Noetherian.lean` (ideal case, the direct template).""",
  gen="""`K` explicit (`include K`): the open mapping theorem needs a nontrivially normed field of scalars (Layer 1 B2
log, T022/T023: "without a nontrivially normed field of scalars Banach open mapping fails"). `A` noetherian
is a section variable, unused in these two lemmas (`omit` at cleanup if the linter asks).""")

t(id='T029', title='BGR 3.7.2/2 (module form): every submodule of `Aⁿ` over a noetherian Banach algebra is closed', file=MOD,
  deps='T028', par='no', typ='theorem', leaves='L5.3',
  decls=[(MOD,'Submodule.isClosed_of_isNoetherianRing_pi')],
  sketch="""Port `Ideal.isClosed_of_fg_closure` and `Ideal.isClosed_of_isNoetherianRing` (Layer 1, lines 114–168):
`N̄ := N.topologicalClosure` is a submodule (`Submodule.topologicalClosure`), finitely generated (noetherian:
`IsNoetherian.noetherian`), say by `x : Fin m → Fin n → A` (`Submodule.fg_iff_exists_fin_generating_family`);
each `x i ∈ N̄` is a limit of elements of `N`, so `x i = y_i + (x i − y_i)` with `y_i ∈ N` and `x i − y_i ∈ N̄`
of norm `< ε`; by the open-mapping lemma (T028, applied to the closed `N̄` with generators `x`) write
`x i − y_i = ∑ c μ • x μ` with `‖c μ‖ ≤ C ‖x i − y_i‖ < 1` for `ε` small; Nakayama (T028) then gives `x i ∈ N`
for all `i`, so `N̄ = span (range x) ≤ N`, i.e. `N` is closed (`Submodule.topologicalClosure_minimal`-free:
`isClosed_of_closure_subset`).""",
  mathlib="""`Submodule.topologicalClosure`, `Submodule.le_topologicalClosure`, `Submodule.isClosed_topologicalClosure`,
`IsNoetherian.noetherian`, `Submodule.fg_iff_exists_fin_generating_family`, `Metric.mem_closure_iff`,
`isClosed_of_closure_subset`; Layer 1 `Ideal.isClosed_of_fg_closure` (template).""",
  sources="""BGR 3.7.2/2 (`bgr-3.7.md:39`): "Let `A` be a `k`-Banach algebra and `M` a complete normed `A`-module. Then `M` is
Noetherian ⇔ … every submodule of `M` is closed" (the direction used: finitely generated submodules of a
complete module over a complete ring are closed, 3.7.2/1).""",
  gen="""`Fin n → A` with the sup norm; `K` explicit. The ideal case is Layer 1's; this is the module case needed by
3.8.3/7 and 6.2.4/1.""")

t(id='T030', title='BGR 3.7.3/1: submodules of complete finite normed modules are closed', file=MOD, deps='T029', par='no',
  typ='lemmas', leaves='L5.4–L5.5',
  decls=[(MOD,'Submodule.isClosed_of_isClosed_comap'),(MOD,'Submodule.isClosed_of_isNoetherianRing_of_finite')],
  sketch="""`isClosed_of_isClosed_comap`: `π.restrictScalars K` is a continuous surjective `K`-linear map between Banach spaces,
hence open (`ContinuousLinearMap.isOpenMap`, from `exists_preimage_norm_le`) and a quotient map
(`IsOpenMap.isQuotientMap`/`IsOpenMap.to_isQuotientMap` with continuity and surjectivity); a set is closed iff its
preimage under a quotient map is closed (`IsQuotientMap.isClosed_preimage`), and `π ⁻¹' N = N.comap π`.
`isClosed_of_isNoetherianRing_of_finite`: `Module.Finite A M` gives `x : Fin n → M` spanning `M`
(`Module.Finite.exists_fin`); `π := Fintype.linearCombination A x : (Fin n → A) →ₗ[A] M` is surjective
(`Fintype.range_linearCombination`, `span = ⊤`) and continuous (finite sum of `fun a ↦ a i • x i`, continuous by
`ContinuousSMul A M` and `continuous_apply`); `N.comap π` is a submodule of `Fin n → A`, closed by T029; conclude
with the first lemma.""",
  mathlib="""`ContinuousLinearMap.isOpenMap`, `IsOpenMap.isQuotientMap`, `IsQuotientMap.isClosed_preimage`, `Submodule.comap`,
`Module.Finite.exists_fin`, `Fintype.linearCombination`, `Fintype.range_linearCombination`, `continuous_finset_sum`,
`Continuous.smul`, `continuous_apply`, `LinearMap.restrictScalars`.""",
  sources="""BGR 3.7.3/1 (`bgr-3.7.md:53`): "Every submodule `M′` of a module `M ∈ 𝔐_A` is closed"; BGR p. 242 (6.2.4/1's proof):
"Viewing `A` as a submodule of the finite `A`-module `A'`, we see by Proposition 3.7.3/1 that `A` is closed in `A'`".""",
  gen="""`M` a Banach `K`-space with a compatible `A`-module structure (`IsScalarTower K A M`, `ContinuousSMul A M`) — BGR's
`𝔐_A` (finite complete normed `A`-modules). `K` explicit.""")

# ---------------------------------------------------------------- SupSeminorm/FunctionAlgebra.lean
t(id='T031', title='Banach function algebras: `|·|_sup` is a norm and is the only power-multiplicative complete norm (BGR 3.8.3/1–3)',
  file=BFA, deps='T003', par='yes (with T020–T030)', typ='lemmas', leaves='L6.1–L6.2',
  decls=[(BFA,'IsBanachFunctionAlgebra.eq_zero_of_supSeminorm_eq_zero'),(BFA,'IsBanachFunctionAlgebra.norm_eq_supSeminorm_of_isPowMul')],
  sketch="""`eq_zero_of…`: `‖f‖ ≤ C * 0 = 0` so `f = 0` (`norm_eq_zero`). `norm_eq_supSeminorm_of_isPowMul` (BGR 1.3.1/3):
`|f|_sup ≤ ‖f‖` (Layer 0) and `‖f‖^n = ‖f^n‖ ≤ C |f^n|_sup = C |f|_sup^n` for `n ≥ 1` (`hpm`, `supSeminorm_pow`),
so `‖f‖ ≤ C^(1/n) |f|_sup → |f|_sup` as `n → ∞` (as in T026: contradiction with `tendsto_pow_atTop_atTop_of_one_lt`
if `‖f‖ > |f|_sup`, after dividing; `|f|_sup = 0` forces `‖f‖ = 0`).""",
  mathlib="""`norm_eq_zero`, `IsPowMul`, `tendsto_pow_atTop_atTop_of_one_lt`, `div_pow`, `norm_nonneg`.""",
  sources="""BGR 3.8.3/1–3 (`bgr-3.8-proofs.md`): "A `k`-algebra `A` is called a Banach function algebra if `| |_sup` is a
complete norm on `A`"; "A `k`-Banach algebra `A` is a Banach function algebra if and only if `| |_sup` is equivalent
to the given norm on `A`"; "`| |_sup` is the only power-multiplicative complete `k`-algebra norm on `A`" (proof via
1.3.1/3, `bgr-1.3-1.5.md`).""",
  gen="""`IsBanachFunctionAlgebra K A := ∃ C, ∀ f, ‖f‖ ≤ C * supSeminorm K f` for a Banach `K`-algebra `A` is BGR 3.8.3/2's
characterisation (plan D3: no type synonym carrying `|·|_sup` as a `NormedRing` structure).""")

t(id='T032', title='Closed subalgebras and finite subalgebras of Banach function algebras (BGR 3.8.3/4–5)', file=BFA,
  deps='T005, T023, T030, T031', par='yes (with T033)', typ='lemmas', leaves='L6.3–L6.4',
  decls=[(BFA,'IsBanachFunctionAlgebra.of_isClosed_range'),(BFA,'IsBanachFunctionAlgebra.of_finite_injective')],
  sketch="""`of_isClosed_range`: `φ.toLinearMap.restrictScalars K`-free: `φ` is a continuous injective `K`-linear map
`B → A` with closed (hence complete) range; the open mapping theorem onto the range
(`ContinuousLinearEquiv.ofBijective` for `B ≃ range φ`, or `ContinuousLinearMap.exists_preimage_norm_le` for the
surjection `B → range φ`) gives `‖b‖ ≤ C₁ ‖φ b‖`; then `‖φ b‖ ≤ C₂ |φ b|_sup` (`hA`) and `|φ b|_sup ≤ |b|_sup`
(T005): `‖b‖ ≤ C₁ C₂ |b|_sup`. `of_finite_injective`: let `letI := φ.toAlgebra`; `Module.Finite B A` from
`hfin`; `IsScalarTower K B A` (`IsScalarTower.of_algebraMap_eq`, `φ.commutes`); `ContinuousSMul B A`
(`b • a = φ b * a`, `hφ.mul continuous_snd`… via `ContinuousSMul.mk` + `continuous_smul` unfolding
`Algebra.smul_def`); then T030 `Submodule.isClosed_of_isNoetherianRing_of_finite K (LinearMap.range
(Algebra.linearMap B A))` shows `range φ` closed; conclude with `of_isClosed_range`.""",
  mathlib="""`ContinuousLinearMap.exists_preimage_norm_le`, `IsClosed.completeSpace_coe`, `LinearMap.range`, `Algebra.linearMap`,
`RingHom.Finite`, `Module.Finite`, `IsScalarTower.of_algebraMap_eq`, `ContinuousSMul`, `Algebra.smul_def`,
`RingHom.toAlgebra`.""",
  sources="""BGR 3.8.3/4 and proof (`bgr-3.8-proofs.md`): "Applying Corollary 3.8.2/2, we see that the new norm dominates the
supremum semi-norm on `B` … by Lemma 3.8.1/4, the monomorphism `φ` is a contraction … Putting these inequalities
together"; BGR 3.8.3/5 and proof: "Since `B` is a Noetherian `k`-Banach algebra, all `B`-submodules of `A` are closed
(see Proposition 3.7.2/2); in particular, `φ(B)` is closed in `A`."
""",
  gen="""Both for Banach `B` with its own norm and continuous `φ` (BGR transport the norm along `φ`; with a given
complete norm on `B` the open mapping theorem supplies the comparison). Not used by the milestones; cheap
corollaries BGR state.""")

t(id='T033', title='Torsion-freeness of a finite domain extension; a basis of `Q(A)` over `Q(B)` with a universal denominator',
  file=BFA, deps='none', par='yes (with T020–T032)', typ='lemmas', leaves='L6.5–L6.6',
  decls=[(BFA,'Module.isTorsionFree_of_faithfulSMul_of_isDomain'),(BFA,'exists_basis_universalDenominator')],
  sketch="""`isTorsionFree`: `Module.IsTorsionFree B A` unfolds to `∀ b ≠ 0, Injective (b • ·)`/no zero smul divisors
(check the current definition: `Module.IsTorsionFree R M : ∀ {r : R} {m : M}, r • m = 0 → r = 0 ∨ m = 0`?);
`b • a = algebraMap b * a = 0` in the domain `A` gives `algebraMap b = 0` (so `b = 0` by `FaithfulSMul.algebraMap_injective`)
or `a = 0`. `exists_basis_universalDenominator`: `L := FractionRing A` is finite-dimensional over
`F := FractionRing B` (Layer 1 `FractionRing.finiteDimensional_of_finite B A` with the `Algebra F L` instance
`FractionRing.liftAlgebra`? — Layer 1 states it with `[Algebra (FractionRing R) (FractionRing S)]
[IsScalarTower R (FractionRing R) (FractionRing S)]` as hypotheses: supply `FractionRing.liftAlgebra` and
`FractionRing.isScalarTower_liftAlgebra`). Take a basis `v` of `L` over `F` (`Module.Basis.ofVectorSpace`),
`n := finrank`; clear denominators: each `v i = algebraMap (a i) / algebraMap (s i)` with `s i ∈ nonZeroDivisors A`
(`IsFractionRing.div_surjective`/`IsLocalization.mk'_surjective`); replacing `v i` by `s i • v i` keeps linear
independence over `F` (scaling by units), so WLOG `v i = algebraMap A L (a i)` with `a i ∈ A`; `LinearIndependent B a`
follows from linear independence over `F` by restricting scalars (`LinearIndependent.restrict_scalars`-type with
`algebraMap B F` injective). Universal denominator: `A` is a finite `B`-module with generators `g j`
(`Module.Finite.exists_fin`); each `algebraMap A L (g j) = ∑ (β_ij / d_ij) v i` with `β_ij ∈ B`, `d_ij ∈ B∖0`
(`IsLocalization.exist_integer_multiples_of_finset`-style: `IsLocalization.exist_integer_multiples` on the finite
set of coordinates gives ONE `b ∈ nonZeroDivisors B` with `b • coord ∈ B` for all); take `b := ∏ d_ij` (or the
witness of `exist_integer_multiples` over the finite family of all coordinates of all `g j`); for general
`f = ∑ c_j g_j` (`c_j ∈ B`), `b • f = ∑ c_j (b • g_j) ∈ ∑ B a_i` with `B`-coefficients, and the identity
`b • f = ∑ β_i • a_i` in `L` descends to `A` (`IsFractionRing.injective A L`).""",
  mathlib="""`Module.IsTorsionFree`, `FaithfulSMul.algebraMap_injective`, `Module.Basis.ofVectorSpace`, `FractionRing.liftAlgebra`,
`FractionRing.isScalarTower_liftAlgebra`, `IsFractionRing.div_surjective`, `IsLocalization.mk'_surjective`,
`IsLocalization.exist_integer_multiples`, `IsLocalization.IsInteger`, `LinearIndependent.map'`/`restrict_scalars`,
`Module.Finite.exists_fin`, `IsFractionRing.injective`; Layer 1 `FractionRing.finiteDimensional_of_finite`.""",
  sources="""BGR 3.8.3/7, proof (`bgr-3.8-proofs.md`): "Let `a₁, …, aₙ` be a `Q(B)`-basis of `Q(A)`. Because `φ` is finite, there is a
universal denominator `b ∈ B − {0}` such that `A ⊂ A' := Σ B a_i/b ⊂ Q(A)`"; BGR 3.8.1/7 preliminaries: "Since `A`
is torsion-free over `B`, we have a commutative diagram of inclusions `B ⊂ A`, `Q(B) ⊂ Q(A)`".""",
  gen="""Pure algebra (`K` unused, dropped): `B`, `A` domains, `A` finite over `B`, `FaithfulSMul B A`. `n` is left
existential (it equals `finrank (FractionRing B) (FractionRing A)`).""")

t(id='T034', title='The coordinate map `A → Bⁿ`: injective, closed range, and `‖f‖ ≤ C ‖θ f‖` (closed graph + open mapping)',
  file=BFA, deps='T029, T033', par='no', typ='lemmas', leaves='L6.7–L6.8',
  decls=[(BFA,'exists_coordinateMap'),(BFA,'exists_norm_le_mul_norm_coordinateMap')],
  sketch="""`exists_coordinateMap`: define `θ f := Classical.choose (hA f)`; uniqueness of the coefficients from
`LinearIndependent B a` (`LinearIndependent.eq_coords_of_eq`/`linearIndependent_iff'`: `∑ (β - β') i • a i = 0 →
β = β'`) makes `θ` additive and `B`-linear (`b' • f` has coefficients `b' • θ f` by uniqueness); injective: `θ f = 0 →
b • f = 0 → f = 0` (torsion-free, T033); `range θ` is a `B`-submodule (`LinearMap.range θ`) of `Fin n → B`, closed
by T029 (`Submodule.isClosed_of_isNoetherianRing_pi K`, `B` noetherian Banach). `exists_norm_le_mul_norm…`:
`θ' := θ.restrictScalars K` (K-linear: `k • f = algebraMap K B k • f` by `IsScalarTower`); closed graph
(`LinearMap.continuous_of_isClosed_graph`): if `(f_k, θ f_k) → (f, v)` then `b • f_k → b • f` (`continuous_const_smul`)
and `∑ θ f_k i • a i = ∑ algebraMap (θ f_k i) * a i → ∑ algebraMap (v i) * a i` (`hcont`, `continuous_finset_sum`),
so `b • f = ∑ v i • a i` and `θ f = v` by uniqueness: the graph is sequentially closed hence closed (metric). Then
`θ'` is a continuous injective `K`-linear map with closed range; open mapping (`ContinuousLinearMap.exists_preimage_norm_le`
on `A → range θ'`, a Banach space) gives `‖f‖ ≤ C ‖θ f‖`.""",
  mathlib="""`linearIndependent_iff'`, `LinearMap.range`, `LinearMap.continuous_of_isClosed_graph`, `isClosed_of_closure_subset`,
`IsSeqClosed.isClosed`, `continuous_const_smul`, `continuous_finset_sum`, `Algebra.smul_def`,
`ContinuousLinearMap.exists_preimage_norm_le`, `IsClosed.completeSpace_coe`, `LinearMap.restrictScalars`;
`Submodule.isClosed_of_isNoetherianRing_pi` (T029).""",
  sources="""BGR 3.8.3/7, proof (`bgr-3.8-proofs.md`): "we get a complete finite (and hence Noetherian) `B`-module if we restrict
`| |_sp` to `A'`. By Proposition 3.7.2/2, the `B`-submodule `A` of `A'` is closed with respect to the restriction of
`| |_sp`. Because `A'` is complete, `A` is complete and hence a `k`-Banach algebra"; the comparison with the given
norm is BGR 3.8.2/4 ("all complete `k`-algebra norms on `A` are equivalent", here through the closed graph
theorem as in 3.8.2/3's proof).""",
  gen="""`K` explicit (`variable (K) in include K in`): the closed-graph and open-mapping steps need the field of scalars
(Layer 1 B2 precedent). `hcont : Continuous (algebraMap B A)` replaces BGR's construction of the topology of `A`
from `A'` (with a given norm on `A` the continuity is needed to compare, see plan §5.5).""")

t(id='T035', title='The spectral norm of `Q(A)` over `Q(B)` restricts to `|·|_sup` on `A` (BGR 3.8.3/7, "`|f|_sup = |f|_sp`")',
  file=BFA, deps='T019, T009', par='yes (with T034, T036)', typ='lemma', leaves='L6.9',
  decls=[(BFA,'spectralNorm_fractionRing_eq_supSeminorm')],
  sketch="""`letI := IsFractionRing.normedField B (FractionRing B)` (needs `NormMulClass B`, Layer 0). For `f : A`, `y := algebraMap A
(FractionRing A) f` is integral over `B` (`IsIntegral.algebraMap`-type: `f` integral since `Module.Finite B A`,
`Algebra.IsIntegral.isIntegral f`, then map along `A → FractionRing A`: `IsIntegral.map`). `minpoly (FractionRing B) y =
(minpoly B y).map (algebraMap B (FractionRing B))` (`minpoly.isIntegrallyClosed_eq_field_fractions'` with `R := B`,
`K := FractionRing B`, `S := FractionRing A`, the scalar tower instance given) and `minpoly B y = minpoly B f`
(`minpoly.algHom_eq` for the injective `IsScalarTower.toAlgHom B A (FractionRing A)`). `spectralNorm (FractionRing B) _ y
= spectralValue (minpoly _ y)`; its terms are `‖algebraMap (coeff i)‖^(1/(d-i))` with `‖algebraMap B (FractionRing B) b‖
= ‖b‖` (Layer 0 `IsFractionRing.normAbsoluteValue_algebraMap`, `natDegree_map`, `coeff_map`), `= |coeff i|_sup^(1/(d-i))`
(`hBsup`), i.e. `spectralValue = supSpectralValue K (minpoly B f)` termwise (T009 `supSpectralValue_eq_spectralValue`-style
`congrArg iSup`), `= supSeminorm K f` by M1 (T019: `A` domain, integral over `B` (finite), torsion-free (T033),
`HasSupSeminorm` on both).""",
  mathlib="""`IsFractionRing.normedField` (Layer 0), `IsFractionRing.normAbsoluteValue_algebraMap` (Layer 0),
`minpoly.isIntegrallyClosed_eq_field_fractions'`, `minpoly.algHom_eq`, `IsIntegral.map`, `Algebra.IsIntegral.isIntegral`,
`Module.Finite` → `Algebra.IsIntegral` (`Algebra.IsIntegral.of_finite`), `spectralNorm`, `spectralValueTerms`,
`Polynomial.coeff_map`, `Polynomial.natDegree_map_eq_of_injective`.""",
  sources="""BGR 3.8.3/7, proof end (`bgr-3.8-proofs.md`): "From Proposition 3.8.1/7 (a), we derive `|f|_sup = |f|_sp` for all
`f ∈ A`"; BGR Remark after 3.8.1/9: "The spectral norm on `Q(A)` considered as a `Q(B)`-algebra yields — if
restricted to `A` — the supremum norm on `A` considered as a `k`-algebra".""",
  gen="""`B` a valued (`NormMulClass`) domain with `|·|_sup = ‖·‖` (BGR: "`B` is a valued integrally closed Noetherian
`k`-Banach algebra"); the `Algebra (FractionRing B) (FractionRing A)` instance and the tower are hypotheses
(instantiate with `FractionRing.liftAlgebra`).""")

t(id='T036', title='Weak stability bounds the coordinates by `|·|_sup`', file=BFA, deps='T033, T035', par='no', typ='lemma',
  leaves='L6.10', decls=[(BFA,'exists_norm_coordinateMap_le_mul_supSeminorm')],
  sketch="""`F := FractionRing B` (normed by `IsFractionRing.normedField`, ultrametric by Layer 0 `IsFractionRing.isUltrametricDist`),
`L := FractionRing A` with `Algebra F L` (`FractionRing.liftAlgebra`), finite-dimensional (Layer 1). The family
`algebraMap A L ∘ a` is linearly independent over `F` (from `LinearIndependent B a` by clearing denominators:
`LinearIndependent.localization`-type / `linearIndependent_iff'` with `IsLocalization.exist_integer_multiples`) and
spans `L`: every `y ∈ L` is `(algebraMap f)/(algebraMap g)` with `f ∈ A`, `g ∈ A∖0`… — spanning is NOT needed: extend
to a basis `v` of `L` (`LinearIndependent.extend`/`Basis.extend`) whose first `n` vectors are the `a i`; the
coordinate functionals `ψ i := v.coord i : L →ₗ[F] F`. Weak stability `hws` gives `C_i` with `‖ψ i z‖ ≤ C_i *
spectralNorm F L z`. For `f : A`: `algebraMap (b • f) = ∑ algebraMap (θ f i) • a i`, so `ψ i (algebraMap (b • f))
= algebraMap B F (θ f i)` for `i < n` (and `0` beyond), hence `‖θ f i‖ = ‖ψ i (algebraMap (b•f))‖ ≤ C_i
spectralNorm F L (algebraMap (b • f)) = C_i ‖b‖ spectralNorm F L (algebraMap f)` (the spectral norm is
`F`-multiplicative: `spectralNorm_smul`/`spectralAlgNorm` with `‖algebraMap b‖ = ‖b‖`) `= C_i ‖b‖ |f|_sup` (T035).
`C := ‖b‖ * max_i C_i` (`Finset.sup'`), and `‖θ f‖ = max_i ‖θ f i‖` (`pi_norm_le_iff_of_nonneg`).""",
  mathlib="""`IsWeaklyStable` (Layer 0: `∀ L [Field L] [Algebra K L] [FiniteDimensional K L] (φ : L →ₗ[K] K), ∃ C, ∀ y, ‖φ y‖ ≤ C *
spectralNorm K L y`), `Module.Basis.extend`, `Module.Basis.coord`, `LinearIndependent.localization`?,
`spectralNorm_smul`, `pi_norm_le_iff_of_nonneg`, `Finset.sup'`, `Finset.le_sup'`; Layer 0 `IsFractionRing.isUltrametricDist`.""",
  sources="""BGR 3.8.3/7, proof (`bgr-3.8-proofs.md`): "Since `Q(B)` is weakly stable, all these extensions are weakly
`Q(B)`-cartesian under their spectral norm. Then `Q(A)`, provided with its spectral norm, is weakly `Q(B)`-cartesian
(use Theorem 3.2.2/2). Let `a₁, …, aₙ` be a `Q(B)`-basis of `Q(A)` … Since `| |_sp` induces the `Q(B)`-product
topology on `Q(A)`"; the definition of weak stability (`bgr-4-and-3.8.3.7.md` / Layer 0 `WeaklyStable.lean`):
"weakly cartesian = the coordinate functionals are bounded by the spectral norm".""",
  gen="""Universe: `A` and `B` in one universe `u` (plan D12). `A` is a domain so `Q(A)` is a field and `IsWeaklyStable`
applies directly (BGR's Dedekind decomposition for reduced `A` is D1).""")

t(id='T037', title='BGR 3.8.3/7 (domain case): a finite domain over a weakly-stable valued Banach function algebra is one', file=BFA,
  deps='T034, T036', par='no', typ='theorem', leaves='L6.11', decls=[(BFA,'IsBanachFunctionAlgebra.of_finite_domain')],
  sketch="""Assemble: T033 gives `n, a, b`; T034 gives `θ` and `‖f‖ ≤ C₁ ‖θ f‖`; T036 gives `‖θ f‖ ≤ C₂ |f|_sup`
(instances: `HasSupSeminorm K A` from T013 `of_isIntegral` over `B`; `Algebra (FractionRing B) (FractionRing A)` and
the tower via `FractionRing.liftAlgebra`/`FractionRing.isScalarTower_liftAlgebra`, `Module.IsTorsionFree` from T033).
`⟨C₁ * C₂, fun f ↦ by nlinarith/calc⟩`.""",
  mathlib="""`FractionRing.liftAlgebra`, `FractionRing.isScalarTower_liftAlgebra`, `mul_assoc`, `mul_le_mul_of_nonneg_left`.""",
  sources="""BGR 3.8.3/7 (`bgr-3.8-proofs.md`), statement and proof; the domain restriction is plan D1.""",
  gen="""`B` valued (`NormMulClass`), integrally closed, noetherian, Banach with `|·|_sup = ‖·‖` and `HasSupSeminorm`,
weakly stable fraction field; `A` a domain, finite over `B` with injective continuous structure map, any complete
`K`-algebra norm. Conclusion: `‖f‖ ≤ C |f|_sup` (= Banach function algebra, D3).""")

# ---------------------------------------------------------------- Affinoid/SupSeminorm.lean
t(id='T038', title='Affinoid algebras have a supremum seminorm (BGR 6.2.1/1); `|f|_sup ≤ ‖g‖` through a presentation', file=ASUP,
  deps='T005', par='yes (with T020–T037)', typ='lemmas+instance', leaves='L7.1–L7.3',
  decls=[(ASUP,'hasSupSeminorm'),(ASUP,'supSeminorm_le_norm_of_eq')],
  sketch="""`hasSupSeminorm`: `isAlgebraic`: Layer 1 `finiteDimensional_quotient_of_isMaximal hA x.asIdeal` gives
`FiniteDimensional K (A ⧸ x)`, hence `Algebra.IsAlgebraic` (`Algebra.IsAlgebraic.of_finite`). `bddAbove`: take a
presentation `⟨n, α, hα⟩ := hA`; for `f` choose `g` with `α g = f`; for every `x`, `evalNorm K x f = evalNorm K x (α g)
= evalNorm K (comapPoint α x) g` (T005, the point `x` is algebraic by the first part — note `comapPoint` needs
`HasSupSeminorm K A`, so use the underlying `isMaximal_comap_of_isAlgebraic` + `evalNorm_comapPoint`'s proof shape, or
first build the instance with the bound through `evalNorm_eq_norm_algHom`-free reasoning: `evalNorm K x (α g) =
evalNorm K ⟨comap α x, _⟩ g ≤ ‖g‖` (Layer 0 `evalNorm_le_norm` on the Banach algebra `Tₙ`)). `supSeminorm_le_norm_of_eq`:
`supSeminorm K f = supSeminorm K (α g) ≤ supSeminorm K g ≤ ‖g‖` (T005 + Layer 0 `supSeminorm_le_norm`), with the
instances from `hA.hasSupSeminorm` and `Affinoid.TateAlgebra.instHasSupSeminorm`.""",
  mathlib="""`Algebra.IsAlgebraic.of_finite`; Layer 1 `IsAffinoidAlgebra.finiteDimensional_quotient_of_isMaximal`; Layer 0
`Affinoid.evalNorm_le_norm`, `Affinoid.supSeminorm_le_norm`, `Affinoid.bddAbove_range_evalNorm`.""",
  sources="""BGR 6.2.1 p. 236 (`bgr-6.2-6.3.1.md`): "According to Corollary 6.1.2/3, all maximal ideals in a `k`-affinoid
algebra `A` are `k`-algebraic … because `A` is a `k`-Banach algebra, Corollary 3.8.2/2 yields that `| |_sup` is
finite; more precisely, `|f|_sup ≤ |f|_α` for all `f ∈ A` and all epimorphisms `α: Tₙ → A`".""",
  gen="""`hasSupSeminorm` is a theorem (its hypothesis `hA` is a Prop, not a class); the Tate-algebra instance is
derived from it. No norm on `A` is needed.""")

t(id='T039', title='Integral monomorphisms of affinoid algebras are isometries (BGR 6.2.2/1)', file=ASUP, deps='T014, T038',
  par='yes (with T040)', typ='lemma', leaves='L7.4', decls=[(ASUP,'supSeminorm_map_eq_of_isIntegral')],
  sketch="""`letI := φ.toAlgebra`; `IsScalarTower K B A` (`IsScalarTower.of_algebraMap_eq fun k ↦ (φ.commutes k).symm`);
`Algebra.IsIntegral B A := ⟨hint⟩` (`RingHom.IsIntegral` ↔ `Algebra.IsIntegral` under `toAlgebra`:
`Algebra.IsIntegral.mk`/`RingHom.IsIntegral`); `FaithfulSMul B A` from `hinj` (`faithfulSMul_iff_algebraMap_injective`);
`haveI := hA.hasSupSeminorm; haveI := hB.hasSupSeminorm`; `exact supSeminorm_algebraMap_eq K b` (T014). The contraction
half of 6.2.2/1 is `Affinoid.supSeminorm_map_le` (T005).""",
  mathlib="""`RingHom.toAlgebra`, `IsScalarTower.of_algebraMap_eq`, `faithfulSMul_iff_algebraMap_injective`, `RingHom.IsIntegral`,
`Algebra.IsIntegral`.""",
  sources="""BGR 6.2.2/1 (`bgr-6.2-6.3.1.md`): "Every homomorphism of `k`-affinoid algebras `φ: B → A` is a contraction with
respect to the supremum semi-norm. If `φ` is an integral monomorphism, it is an isometry." (from 3.8.1/4 and 3.8.1/6).""",
  gen="""Affinoid wrapper of T014 with `φ.toRingHom.IsIntegral` (BGR: integral, not finite).""")

t(id='T040', title='`|f|_sup = σ(minpoly_{T_d} f)` and `|φ(t) f|_sup = ‖t‖ |f|_sup` for affinoid domains over `T_d` (BGR 6.2.2/2)',
  file=ASUP, deps='T019, T020, T038', par='yes (with T039)', typ='lemmas', leaves='L7.5–L7.6',
  decls=[(ASUP,'supSeminorm_eq_supSpectralValue_minpoly_tateAlgebra'),(ASUP,'supSeminorm_algebraMap_tateAlgebra_mul')],
  sketch="""Instances for M1 with `B := TateAlgebra K d`: `IsDomain` (Layer 0 `Restricted.instIsDomain`), `IsIntegrallyClosed`
(Layer 0 `TateAlgebra/Rueckert.lean`, line 68), `HasSupSeminorm` (T038 instance), `Module.IsTorsionFree (TateAlgebra K d) A`
from `[IsDomain A] [FaithfulSMul _ A]` (T033's lemma, `Module.isTorsionFree_of_faithfulSMul_of_isDomain`, but it is
stated for finite `A` — for integral `A` reprove inline: `b • a = algebraMap b * a = 0`, domain). Then
`supSeminorm_eq_supSpectralValue_minpoly K f` (T019) and `supSeminorm_algebraMap_mul K (hB := …) t f` (T020) with
`hB : ∀ t t', |t t'|_sup = |t|_sup |t'|_sup` from Layer 0 `supSeminorm_eq_norm` + `NormMulClass` (`norm_mul`), and
`‖t‖ = supSeminorm K t` to rewrite the conclusion.""",
  mathlib="""`norm_mul` (`NormMulClass`); Layer 0 `MvPowerSeries.Restricted.supSeminorm_eq_norm`, `Restricted.instIsDomain`,
the `IsIntegrallyClosed (TateAlgebra K n)` instance of `TateAlgebra/Rueckert.lean`.""",
  sources="""BGR 6.2.2/2 (`bgr-6.2-6.3.1.md`): "Let `φ: T_d → A` be an integral torsion-free monomorphism into some `k`-affinoid
algebra `A`. Then `| |_sup` is a faithful `T_d`-algebra norm on `A` (i.e., `|φ(t) f|_sup = |t| |f|_sup` …). If
`fⁿ + φ(t₁) fⁿ⁻¹ + ⋯ + φ(tₙ) = 0` is the integral equation of minimal degree for `f` over `T_d`, then one has
`|f|_sup = max |t_i|^{1/i}`" ("Since `T_d` is a valued integrally closed domain, we can derive from Proposition
3.8.1/7 (a) and (d)").""",
  gen="""For `A` a domain (D8: BGR say "torsion-free"); stated with `[Algebra (TateAlgebra K d) A] [IsScalarTower …]
[Algebra.IsIntegral …] [FaithfulSMul …]` (the consumer applies Noether normalisation and `letI := φ.toAlgebra`).""")

t(id='T041', title='The maximum modulus principle for affinoid domains (BGR 6.2.1/4 (i), special case)', file=ASUP,
  deps='T021, T040', par='no', typ='theorem', leaves='L7.7', decls=[(ASUP,'exists_evalNorm_eq_supSeminorm_of_isDomain')],
  sketch="""Noether normalisation (Layer 1 `hA.exists_finite_injective`): `φ : TateAlgebra K d →ₐ[K] A` finite injective.
`letI := φ.toAlgebra`, tower, `Algebra.IsIntegral` (finite ⇒ integral: `RingHom.Finite.to_isIntegral`),
`FaithfulSMul`, torsion-free (T033 lemma), `HasSupSeminorm` both (T038). Apply T021 `exists_evalNorm_eq_supSeminorm_of_forall_exists K`
with `hB : ∀ t, ∃ y, evalNorm K y t = supSeminorm K t`: Layer 0 `exists_evalNorm_eq_norm t` gives `y` with
`evalNorm K y t = ‖t‖ = supSeminorm K t` (`supSeminorm_eq_norm`).""",
  mathlib="""`RingHom.Finite.to_isIntegral`; Layer 1 `IsAffinoidAlgebra.exists_finite_injective`; Layer 0
`MvPowerSeries.Restricted.exists_evalNorm_eq_norm`, `supSeminorm_eq_norm`.""",
  sources="""BGR 6.2.1/4, proof (`bgr-6.2-6.3.1.md`): "Let us first consider the special case, where `A` is an integral domain.
Applying the Noether Normalization Lemma (Corollary 6.1.2/2), we find a finite monomorphism `φ: T_d → A` … Since `T_d`
is integrally closed (Theorem 5.2.6/2) and since the Maximum Modulus Principle holds for `T_d` (Corollary 5.1.4/6),
assertions (i) and (ii) follow from Proposition 3.8.1/7."; Bosch 1.4/14 (`bosch-lectures.txt`).""",
  gen="""`[IsDomain A]`; no norm on `A`.""")

t(id='T042', title='M2 — THE MAXIMUM MODULUS PRINCIPLE (BGR 6.2.1/4 (i); Bosch 1.4/14)', file=ASUP, deps='T007, T041', par='no',
  typ='theorem', leaves='L7.8', milestone='M2 ([RM] §2.2.1)', decls=[(ASUP,'exists_evalNorm_eq_supSeminorm')],
  sketch="""`haveI := hA.hasSupSeminorm`, `IsNoetherianRing A` (Layer 1). T007: `𝔭 ∈ minimalPrimes A` with
`supSeminorm K (mk 𝔭 f) = supSeminorm K f`. `A ⧸ 𝔭` is an affinoid domain (`hA.quotient 𝔭`, `Ideal.Quotient.isDomain`
with `𝔭.IsPrime` from `Ideal.minimalPrimes_isPrime`/`minimalPrimes` ⊆ primes); T041 gives `x̄ : MaximalSpectrum (A ⧸ 𝔭)`
with `evalNorm K x̄ (mk f) = supSeminorm K (mk f)`. Lift: `x := comapPoint (Ideal.Quotient.mkₐ K 𝔭) x̄` (T005; the
instance on `A ⧸ 𝔭` is `HasSupSeminorm.quotient`), `evalNorm K x f = evalNorm K x̄ (mk f)` (`evalNorm_comapPoint`).
Chain the equalities.""",
  mathlib="""`Ideal.Quotient.isDomain`, `Ideal.minimalPrimes_isPrime`?/`minimalPrimes` membership → `IsPrime`
(`Ideal.minimalPrimes.isPrime`), `Ideal.Quotient.mkₐ`.""",
  sources="""BGR 6.2.1/4, proof (`bgr-6.2-6.3.1.md`): "Now let `A` be arbitrary. Denote by `𝔭₁, …, 𝔭_r` the minimal prime
ideals in `A`. By what we have just seen, assertions (i) and (ii) are true for the algebras `A/𝔭_i` … Thus by
Lemma 3, they must also be true for `A`."; Bosch 1.4, Prop. 14 (`bosch-lectures.txt`, "maximum modulus").""",
  gen="""`[Nontrivial A]` (the zero ring has no points); no norm on `A`.""")

t(id='T043', title='The value group: `|f|_sup^m ∈ ‖K‖` uniformly, and `|c f^m|_sup = 1` (BGR 6.2.1/4 (ii), 3.8.1/8)', file=ASUP,
  deps='T007, T022, T040', par='yes (with T044, T045)', typ='lemmas', leaves='L7.9–L7.11',
  decls=[(ASUP,'exists_forall_pow_supSeminorm_mem_range_norm_of_isDomain'),(ASUP,'exists_forall_exists_smul_pow_supSeminorm_eq_one'),
         (ASUP,'exists_smul_pow_supSeminorm_eq_one')],
  sketch="""Domain case: Noether normalisation as in T041; `n := Module.finrank (FractionRing (TateAlgebra K d)) (FractionRing A)`
(finite by Layer 1 `FractionRing.finiteDimensional_of_finite`), and `natDegree (minpoly (TateAlgebra K d) f) ≤ n` by
`minpoly.natDegree_le` over the fraction field plus `minpoly.isIntegrallyClosed_eq_field_fractions'` (degree preserved
by `map`); `hB : ∀ t, supSeminorm K t ∈ range ‖·‖`: `supSeminorm_eq_norm` + Layer 0 `norm_mem_range_norm`
(`exists_norm_coeff_eq`: the Gauss norm is a coefficient norm). T022 gives `m := n!`. General case: `𝔭 ↦ m_𝔭` for the
finitely many minimal primes (`minimalPrimes.finite_of_isNoetherianRing`), `m := ∏ m_𝔭` (`Finset.prod` over
`hfin.toFinset`, `≠ 0` as a product of nonzeros); for `f` with `|f|_sup ≠ 0`: T007 gives `𝔭` with
`|mk 𝔭 f|_sup = |f|_sup`, and `|f|_sup^m = (|mk f|_sup^{m_𝔭})^{m/m_𝔭} = ‖d‖^{m/m_𝔭} = ‖d^{m/m_𝔭}‖ =: ‖d'‖`
(`Finset.dvd_prod_of_mem`, `pow_mul`); `d' ≠ 0` since `|f|_sup ≠ 0`; `c := d'⁻¹`: `|c • f^m|_sup = ‖c‖ |f|_sup^m = 1`
(`supSeminorm_smul`, `supSeminorm_pow`, `norm_inv`). Trivial `A`: `m := 1`, vacuous. `exists_smul_pow…`: specialise.""",
  mathlib="""`minpoly.natDegree_le`, `Module.finrank`, `Finset.prod_ne_zero_iff`, `Finset.dvd_prod_of_mem`, `pow_mul`, `norm_inv`,
`norm_pow`, `inv_mul_cancel₀`; Layer 0 `MvPowerSeries.Restricted.norm_mem_range_norm`/`exists_norm_coeff_eq`; Layer 1
`FractionRing.finiteDimensional_of_finite`.""",
  sources="""BGR 6.2.1/4 (ii) and proof (`bgr-6.2-6.3.1.md`): "For all `f ∈ A` such that `|f|_sup ≠ 0`, there are `c ∈ k` and
`m ∈ ℕ` such that `|cf^m|_sup = 1`" ("assertions (i) and (ii) follow from Proposition 3.8.1/7" and "Thus by Lemma 3,
they must also be true for `A`"); BGR 3.8.1/8 (`bgr-3.8-proofs.md`); [RM] §2.2.2 for the uniform `m`; Bosch 1.4/15.""",
  gen="""Three statements: the domain-case uniform exponent, the uniform exponent for every affinoid algebra (plan D6:
`m = ∏ (n_𝔭)!`), and the pointwise BGR form. BGR's "`|A|_sup ⊂ |k_a|`" is implied and not stated separately.""")

t(id='T044', title='`|f|_sup = 0` iff `f` is nilpotent; `|·|_sup` is a norm iff `A` is reduced (BGR 6.2.1/4 (iii))', file=ASUP,
  deps='T004, T038', par='yes (with T043, T045)', typ='lemmas', leaves='L7.12–L7.14',
  decls=[(ASUP,'supSeminorm_eq_zero_iff_isNilpotent'),(ASUP,'eq_zero_of_supSeminorm_eq_zero'),(ASUP,'isReduced_of_forall_supSeminorm_eq_zero_imp')],
  sketch="""`haveI := hA.hasSupSeminorm`. T004: `supSeminorm K f = 0 ↔ f ∈ jacobson ⊥`. Affinoid algebras are Jacobson (Layer 1
`hA.isJacobsonRing`): `jacobson ⊥ = radical ⊥ = nilradical A`: `Ideal.radical_bot`?-free: `(IsJacobsonRing.out
(radical ⊥).radical_isRadical : jacobson (radical ⊥) = radical ⊥)` and `jacobson ⊥ ≤ jacobson (radical ⊥)`
(`Ideal.jacobson_mono bot_le`) with `radical ⊥ ≤ jacobson ⊥` (`Ideal.radical_le_jacobson`), so `jacobson ⊥ = radical ⊥
= nilradical A` (`nilradical_eq_radical_bot`?—`nilradical` is defined as `(⊥ : Ideal R).radical`, `rfl`), and
`mem_nilradical : f ∈ nilradical A ↔ IsNilpotent f`. `eq_zero_of…`: `IsNilpotent f → f = 0` in a reduced ring
(`IsReduced.eq_zero`/`IsNilpotent.eq_zero`). `isReduced_of…`: `⟨fun f hf ↦ h f ((iff).2 hf)⟩` (`isReduced_iff`).""",
  mathlib="""`IsJacobsonRing.out`, `Ideal.radical_isRadical`?/`Ideal.IsRadical`, `Ideal.jacobson_mono`, `Ideal.radical_le_jacobson`,
`nilradical`, `mem_nilradical`, `IsNilpotent.eq_zero`, `isReduced_iff`; Layer 1 `IsAffinoidAlgebra.isJacobsonRing`.""",
  sources="""BGR 6.2.1/4 (iii) and proof (`bgr-6.2-6.3.1.md`): "An element `f ∈ A` is nilpotent if and only if `| |_sup = 0`. In
particular, `| |_sup` is a norm on `A` if and only if `A` is reduced." / "it follows that `| |_sup` is a norm on
`red A = A/rad A`, since `rad A = ⋂ 𝔭_i`"; the Remark after 6.2.1/5: "assertion (iii) … is equivalent to the fact that
each `Tₙ` is a Jacobson ring" (our route).""",
  gen="""Three single-conclusion statements (statement-splitting rule); the Jacobson route replaces BGR's minimal-primes
route (BGR's own Remark records the equivalence).""")

t(id='T045', title='Homomorphisms of Banach algebras into reduced affinoid algebras are continuous (BGR 6.2.1/5)', file=ASUP,
  deps='T023, T038, T044', par='yes (with T043, T044)', typ='theorem', leaves='L7.15',
  decls=[(ASUP,'_root_.AlgHom.continuous_of_isReduced_of_isAffinoidAlgebra')],
  sketch="""`haveI := hA.hasSupSeminorm`; `AlgHom.continuous_of_supSeminorm_eq_zero_imp (hfin := fun x ↦
hA.finiteDimensional_quotient_of_isMaximal x.asIdeal) (hA := fun f hf ↦ hA.eq_zero_of_supSeminorm_eq_zero hf) φ` (T023, T044).""",
  mathlib="""Layer 1 `IsAffinoidAlgebra.finiteDimensional_quotient_of_isMaximal`.""",
  sources="""BGR 6.2.1/5 (`bgr-6.2-6.3.1.md`): "If `A` is a reduced `k`-affinoid algebra, then each homomorphism of a (not
necessarily Noetherian) `k`-Banach algebra into `A` is continuous." ("Combining assertion (iii) of the above
proposition with the assertion of Proposition 3.8.2/3").""",
  gen="""`B` any Banach `K`-algebra (no ultrametric/noetherian hypothesis on `B`); `A` affinoid with any complete norm,
reduced.""")

t(id='T046', title='Integral equations compute `|f|_sup` (BGR 6.2.2/4; Bosch 1.4/13), domain case then general', file=ASUP,
  deps='T007, T010, T011, T040, T044', par='no', typ='lemmas', leaves='L7.16–L7.17',
  decls=[(ASUP,'exists_monic_eval₂_eq_zero_supSeminorm_eq_supSpectralValue_of_isDomain'),(ASUP,'exists_monic_eval₂_eq_zero_supSeminorm_eq_supSpectralValue')],
  sketch="""Domain case: `A` nontrivial; Layer 1 `hB.exists_finite_injective_comp φ hfin` gives `ψ : TateAlgebra K d →ₐ[K] B` with
`φ ∘ ψ` finite and injective. With `letI := (φ.comp ψ).toAlgebra` and T040, `p := minpoly (TateAlgebra K d) f` has
`|f|_sup = σ(p)`; `q := p.map ψ` is monic (`Monic.map`), `q.eval₂ φ f = p.eval₂ (φ ∘ ψ) f = aeval f p = 0`
(`Polynomial.eval₂_map`, `minpoly.aeval`), and `σ(q) ≤ σ(p)` (T011 `supSpectralValue_map_le ψ`, instances T038) while
`|f|_sup ≤ σ(q)` (T010), so `|f|_sup = σ(q)`. General case: `haveI := hA.hasSupSeminorm`; minimal primes `𝔭_i`
(finite, nonempty); for each, `A ⧸ 𝔭_i` is an affinoid domain and `φ_i := (mkₐ K 𝔭_i).comp φ` is finite
(`RingHom.Finite.comp` with the surjection), so the domain case gives `q_i` monic with `q_i.eval₂ φ_i (mk f) = 0`,
i.e. `q_i.eval₂ φ f ∈ 𝔭_i` (`Ideal.Quotient.eq_zero_iff_mem`, `Polynomial.hom_eval₂`), and `|mk f|_sup = σ(q_i)`.
`q* := ∏ q_i` (`Finset.prod` over the finite set), `q*.eval₂ φ f ∈ ⋂ 𝔭_i = nilradical A` (`Polynomial.eval₂_prod`?/
`Polynomial.eval₂_finset_prod`, `Ideal.mul_mem_left`, `Ideal.sInf_minimalPrimes` + `Ideal.radical_bot`… `sInf (minimalPrimes A)
= (⊥).radical = nilradical A`), so some `e` with `(q*.eval₂ φ f)^e = 0` (`mem_nilradical`, `IsNilpotent`); `q := q*^e`
(monic, `eval₂_pow`). `σ(q) ≤ σ(q*) ≤ max_i σ(q_i) = max_i |mk f|_sup = |f|_sup` (T011 `pow_le`, `prod_le_of_forall_le`
with `C := |f|_sup` and `σ(q_i) = |mk 𝔭_i f|_sup ≤ |f|_sup` by T006), and `|f|_sup ≤ σ(q)` by T010.""",
  mathlib="""`Polynomial.Monic.map`, `Polynomial.eval₂_map`, `Polynomial.hom_eval₂`, `Polynomial.eval₂_finset_prod`,
`Polynomial.eval₂_pow`, `Polynomial.monic_prod_of_monic`, `Monic.pow`, `Ideal.Quotient.eq_zero_iff_mem`, `Ideal.sInf_minimalPrimes`,
`mem_nilradical`, `RingHom.Finite.comp`, `RingHom.Finite.of_surjective`; Layer 1 `IsAffinoidAlgebra.exists_finite_injective_comp`.""",
  sources="""BGR 6.2.2/4 and proof (`bgr-6.2-6.3.1.md`): "Theorem 6.1.2/1 provides us with a homomorphism `ψ: T_d → B` such that
`φ ∘ ψ … is an integral monomorphism … we have `|f|_sup = σ(p)` … Consider the polynomial `q ∈ B[X]` obtained from
`p` by replacing all its coefficients by their `ψ`-images in `B`. Clearly, `q(f) = p(f) = 0`, and `|f|_sup = σ(p) ≥
σ(q)`"; "If one defines `q* := ∏ q_i`, one gets a monic polynomial in `B[X]` such that `q*(f) ∈ ⋂ 𝔭_i = rad A`. Then
there is an exponent `e` … Setting `q := q*^e` … Proposition 1.5.4/1 gives us `σ(q) ≤ max σ(q_i) = max |π_i(f)|_sup =
|f|_sup`"; Bosch 1.4/13.""",
  gen="""`φ` finite (plan D10) instead of BGR's integral; `A` nontrivial in the general statement (BGR implicit).""")

# ---------------------------------------------------------------- Affinoid/PowerBounded.lean
t(id='T047', title='The subring `Å = {|f|_sup ≤ 1}` and its ideal `Ǎ = {|f|_sup < 1}` (BGR 6.2.3/1–2, 1.2.5/2, 1.2.5/7)', file=APB,
  deps='T003', par='yes (with T020–T046)', typ='defs+lemmas', leaves='L8.1–L8.4',
  decls=[(APB,'powerBounded'),(APB,'topologicallyNilpotent'),(APB,'topologicallyNilpotent_isRadical'),(APB,'algebraMap_mem_powerBounded')],
  sketch="""`powerBounded`: `mul_mem'`: `|fg| ≤ |f||g| ≤ 1` (`mul_le_one'`); `one_mem'`: `supSeminorm_one_le`; `add_mem'`:
`add_le_max` + `max_le`; `zero_mem'`: `supSeminorm_zero`; `neg_mem'`: `supSeminorm_neg`. `topologicallyNilpotent`:
`add_mem'`: `max_lt`; `zero_mem'`: `0 < 1`; `smul_mem'`: `|c • f| = |c f| ≤ |c| |f| < 1` (`mul_lt_one_of_nonneg_of_lt_one_right`).
`isRadical`: `Ideal.IsRadical` = `∀ f n, f^n ∈ I → f ∈ I`-type (`Ideal.isRadical_iff_pow_one_lt`? use
`Ideal.IsRadical` unfolding to `I.radical ≤ I`, `Ideal.mem_radical_iff`): `|f^n|_sup = |f|^n < 1` with `n ≠ 0` gives
`|f| < 1` (`pow_lt_one_iff_of_nonneg`). `algebraMap_mem`: `|algebraMap c|_sup = |c • 1| = ‖c‖ |1| ≤ ‖c‖ ≤ 1`
(`Algebra.algebraMap_eq_smul_one`, `supSeminorm_smul`, `supSeminorm_one_le`).""",
  mathlib="""`Subring`, `Ideal` structure fields, `mul_le_one'`, `max_lt`, `mul_lt_one_of_nonneg_of_lt_one_right`, `Ideal.IsRadical`,
`Ideal.mem_radical_iff`, `pow_lt_one_iff_of_nonneg`, `Algebra.algebraMap_eq_smul_one`.""",
  sources="""BGR 6.2.3/1–2 and 6.2.3/4 (`bgr-6.2-6.3.1.md`): "`Ã = {f ∈ A; |f|_sup ≤ 1}/{f ∈ A; |f|_sup < 1}`"; BGR 1.2.5/2
(`bgr-3.7.md:157`): "The set `Å` is a subring of `A` and `Ǎ` is an ideal in `Å`"; BGR 1.2.5/7 (`bgr-1.3-1.5.md`): "The rings
`Ã` and `~A` are reduced".""",
  gen="""Defined for any `[HasSupSeminorm K A]` (no norm, no affinoid hypothesis): roadmap §2.3.1 "`Å` form a subring independent
of the norm".""")

t(id='T048', title='Power-bounded ⇔ `|f|_sup ≤ 1` (BGR 6.2.3/1; Bosch 1.4/16) — first half of M3', file=APB,
  deps='T009, T024, T046, T047', par='no', typ='theorem', leaves='L8.5–L8.6',
  decls=[(APB,'isPowerBounded_iff_supSeminorm_le_one'),(APB,'isPowerBounded_iff_mem_powerBounded')],
  sketch="""`→`: T024 `IsPowerBounded.supSeminorm_le_one` (instance from `hA.hasSupSeminorm`). `←` (BGR's proof): presentation
`α : Tₙ →ₐ[K] A` surjective (finite: `RingHom.Finite.of_surjective`), continuous (Layer 1 `hA.continuous_presentation`),
so `∃ C, ∀ g, ‖α g‖ ≤ C ‖g‖` (`ContinuousLinearMap.exists_bound`/Layer 1 `exists_forall_norm_le_mul_of_continuous`). T046
gives monic `q ∈ Tₙ[X]` with `q.eval₂ α f = 0` and `σ(q) = |f|_sup ≤ 1`, so every coefficient has `|t_i|_sup = ‖t_i‖ ≤ 1`
(T009 `coeff_le_pow`, `supSeminorm_eq_norm`). Induction as in T027: `f^j = ∑_{i<n} α (c_i) f^i` with `‖c_i‖ ≤ 1`
(the coefficients stay in the unit ball of `Tₙ`: `norm_add_le_max`/ultrametric, `norm_mul_le`, `NormOneClass`), hence
`‖f^j‖ ≤ max_i ‖α c_i‖ ‖f^i‖ ≤ C max_{i<n} ‖f^i‖` for all `j`: `isPowerBounded_of_norm_pow_le`. `iff_mem`: rewrite with
`mem_powerBounded`.""",
  mathlib="""`PowerBounded.isPowerBounded_of_norm_pow_le`, `RingHom.Finite.of_surjective`, `IsUltrametricDist.norm_add_le_max`,
`norm_mul_le`, `IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty`; Layer 1 `IsAffinoidAlgebra.continuous_presentation`,
`MvPowerSeries.Restricted.exists_forall_norm_le_mul_of_continuous`.""",
  sources="""BGR 6.2.3/1 and proof (`bgr-6.2-6.3.1.md`): "We have only to show that `f` is power-bounded if `|f|_sup ≤ 1`. Choose
a finite homomorphism `φ: T_d → A` (for example, an epimorphism). Then due to Proposition 6.2.2/4, there is an integral
equation … We have `t₁, …, tₙ ∈ T̊_d` if `|f|_sup ≤ 1`. Induction on `ν` gives then `f^{n+ν} ∈ Σ φ(T̊_d) f^i`. Since
`φ(T̊_d)` is bounded in `A`, we see that `Σ φ(T̊_d) f^i` is bounded."; Bosch 1.4/16.""",
  gen="""Any complete `K`-algebra norm on the affinoid `A` (roadmap convention 3); no domain hypothesis (BGR's direct proof,
unlike the 3.8.2/6 route).""")

t(id='T049', title='Topologically nilpotent ⇔ `|f|_sup < 1` ⇔ `|f(x)| < 1` for all `x` (BGR 6.2.3/2; Bosch 1.4/17)', file=APB,
  deps='T042, T043, T048', par='no', typ='lemmas', leaves='L8.7–L8.9',
  decls=[(APB,'isTopologicallyNilpotent_iff_supSeminorm_lt_one'),(APB,'isTopologicallyNilpotent_iff_forall_evalNorm_lt_one'),
         (APB,'isTopologicallyNilpotent_iff_mem_topologicallyNilpotent')],
  sketch="""`iff_supSeminorm_lt_one`: `→`: `‖f^n‖ → 0` gives `‖f^m‖ < 1` for some `m ≥ 1`, and `|f|_sup^m = |f^m|_sup ≤ ‖f^m‖ < 1`
so `|f|_sup < 1` (`pow_lt_one_iff_of_nonneg`). `←`: if `|f|_sup = 0` then `f` is nilpotent (T044) hence topologically
nilpotent (`IsNilpotent.isTopologicallyNilpotent`?/eventually `0`). Else T043: `c, m` with `|c • f^m|_sup = 1`;
`‖c‖ > 1` since `|f|_sup^m < 1` (`‖c‖ = 1/|f|_sup^m`); `c • f^m` is power-bounded (T048), so `‖(c • f^m)^k‖ ≤ M`,
i.e. `‖f^{mk}‖ ≤ M ‖c‖^{-k} → 0`: `f^m` is topologically nilpotent, hence `f` (BGR 1.2.5/7 argument as in T027:
`n = mq + s`). `iff_forall_evalNorm_lt_one`: `|f|_sup < 1 ↔ ∀ x, |f(x)| < 1` by M2 (T042: the sup is attained; `←`
needs `[Nontrivial A]`) and `evalNorm_le_supSeminorm`. `iff_mem`: rewrite `mem_topologicallyNilpotent`.""",
  mathlib="""`pow_lt_one_iff_of_nonneg`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Metric.tendsto_atTop`, `norm_smul`, `norm_pow`,
`IsTopologicallyNilpotent` (Mathlib: `Tendsto (fun n ↦ x ^ n) atTop (𝓝 0)`), `Nat.div_add_mod`, `squeeze_zero`.""",
  sources="""BGR 6.2.3/2 and proof (`bgr-6.2-6.3.1.md`): "Statements (ii) and (iii) are equivalent due to the Maximum Modulus
Principle. Furthermore, statement (i) implies statement (iii), since any Banach norm on `A` dominates `| |_sup` and since
`| |_sup` is power-multiplicative. In order to verify the opposite direction, assume `|f|_sup < 1`. Then there exist a
constant `c ∈ k`, `|c| > 1`, and an integer `m > 0` such that `|cf^m|_sup ≤ 1` … We have `cf^m ∈ Å` by Proposition 1.
Therefore `f^m ∈ c⁻¹Å ⊂ Ǎ`, and we see that `f^m` and hence also `f` are topologically nilpotent."; Bosch 1.4/17.""",
  gen="""Three single-conclusion lemmas (BGR's (i)⇔(ii)⇔(iii) split per the statement-splitting rule).""")

t(id='T050', title='M3 — the spectral radius formula `|f|_sup = inf ‖fⁱ‖^{1/i}` (BGR 6.2.3/3)', file=APB, deps='T024, T043, T048',
  par='no', typ='theorem', leaves='L8.10', milestone='M3 ([RM] §2.3.1 + §2.3.3, with T048)', decls=[(APB,'supSeminorm_eq_smoothingFun')],
  sketch="""`≤`: T024 `supSeminorm_le_smoothingFun`. `≥` (indirect, BGR): suppose `|f|_sup < μ'(f) := smoothingFun f`. If
`|f|_sup = 0`: `f` nilpotent (T044), so `f^N = 0` and `μ'(f) ≤ ‖f^N‖^{1/N} = 0` (`smoothingFun_le`), contradiction.
Else T043: `c, m` with `|c • f^m|_sup = 1`; `g := c • f^m` has `μ'(g) = ‖c‖ μ'(f)^m`?? — `smoothingFun` is
power-multiplicative (`isPowMul_smoothingFun`) and `c • ·` is multiplicative for the norm (`norm_smul`), so
`μ'(c • f^m) = ‖c‖ μ'(f)^m` (`smoothingFun_of_map_mul_eq_mul`/`smoothingFun_apply_of_map_mul_eq_mul` for the constant
`algebraMap c`, which is norm-multiplicative in a `NormedAlgebra` + `NormOneClass`: `norm_algebraMap'`), while
`|g|_sup = ‖c‖ |f|_sup^m = 1`; hence `μ'(g) > 1 = |g|_sup`, so `‖g^i‖ ≥ μ'(g)^i → ∞` (`smoothingFun_le`:
`μ'(g) ≤ ‖g^i‖^{1/i}`; `tendsto_pow_atTop_atTop_of_one_lt`), i.e. `g` is not power-bounded
(`IsPowerBounded.exists_norm_pow_le`), contradicting T048 (`|g|_sup ≤ 1`).""",
  mathlib="""`smoothingFun_le`, `isPowMul_smoothingFun`, `smoothingFun_apply_of_map_mul_eq_mul`, `norm_algebraMap'`, `norm_smul`,
`tendsto_pow_atTop_atTop_of_one_lt`, `PowerBounded.IsPowerBounded.exists_norm_pow_le`; T044 for nilpotents.""",
  sources="""BGR 6.2.3/3 and proof (`bgr-6.2-6.3.1.md`): "Define `|f|' := inf |f^i|^{1/i} … it follows from Corollary 3.8.2/2
that `|f|_sup ≤ |f|'` … Assume that `|f|_sup < |f|'` for some `f ∈ A`. Proposition 6.2.1/4 (ii) allows us to assume
`|f|_sup = 1`, and hence `|f|' > 1`. This implies `|f^i| ≥ |f|'^i → ∞`, and therefore `f` cannot be power-bounded,
in contradiction to Proposition 1."; [RM] §2.3.3 ("the right-hand side is Mathlib's `smoothingSeminorm`").""",
  gen="""Any complete `K`-algebra norm on the affinoid `A`; `smoothingFun (SeminormedRing.toRingSeminorm A)` is Mathlib's
`inf_i ‖fⁱ‖^{1/i}`.""")

t(id='T051', title='`|·|_sup` is 1-Lipschitz; `Å` is open and closed; `Ǎ` is open (§2.4.3)', file=APB, deps='T003, T038',
  par='yes (with T052)', typ='lemmas', leaves='L8.11–L8.14',
  decls=[(APB,'lipschitzWith_supSeminorm'),(APB,'isClosed_powerBounded'),(APB,'isOpen_powerBounded'),(APB,'isOpen_setOf_supSeminorm_lt_one')],
  sketch="""`lipschitzWith`: `LipschitzWith.of_dist_le_mul`/`LipschitzWith.of_le_add`: `|f|_sup ≤ max (|f-g|_sup) (|g|_sup) ≤
|f - g|_sup + |g|_sup ≤ ‖f - g‖ + |g|_sup` (nonarchimedean, `f = (f - g) + g`, Layer 0 `supSeminorm_le_norm`) and symmetric;
`Real.dist_eq`, `abs_sub_le_iff`. `isClosed`: `{f | |f|_sup ≤ 1} = (supSeminorm K) ⁻¹' Iic 1`, closed by continuity
(`LipschitzWith.continuous`, `isClosed_Iic`). `isOpen_setOf_lt`: preimage of `Iio 1`. `isOpen_powerBounded`:
`Metric.ball 0 1 ⊆ Å` (`|f|_sup ≤ ‖f‖ < 1`), so `Å` (an `AddSubgroup`: `(powerBounded K A).toAddSubgroup`) contains a
neighbourhood of `0`, hence is open (`AddSubgroup.isOpen_of_mem_nhds`).""",
  mathlib="""`LipschitzWith.of_le_add`, `LipschitzWith.continuous`, `isClosed_Iic`, `isOpen_Iio`, `IsClosed.preimage`,
`AddSubgroup.isOpen_of_mem_nhds`, `Metric.ball_mem_nhds`, `Subring.toAddSubgroup`.""",
  sources="""[RM] §2.4.3 ("`Å` is the unit ball of a norm defining the topology … `Ǎ` is its open unit ball"); BGR 1.2.5/2
(`bgr-3.7.md:157`): "The subring `Å` is open and closed, `Ǎ` is open" (for a power-multiplicative norm; here through
`|·|_sup ≤ ‖·‖`).""",
  gen="""No reducedness needed (only `|·|_sup ≤ ‖·‖`); stated for any complete `K`-algebra norm on an affinoid `A`.""")

t(id='T052', title='Uniformity in norm form: `Å` bounded ⇔ `|·|_sup` equivalent to the norm; bounded `Å` forces reduced (§2.3.5)',
  file=APB, deps='T043, T044, T048', par='no', typ='lemmas', leaves='L8.15–L8.16',
  decls=[(APB,'exists_norm_le_mul_supSeminorm_iff_isBounded_powerBounded'),(APB,'isReduced_of_isBounded_powerBounded')],
  sketch="""`→`: `‖f‖ ≤ C |f|_sup ≤ C` on `Å`: PFA `TopologicalRing.isBounded_of_forall_norm_le`. `←` (BGR p. 181): PFA
`IsBounded.exists_norm_le_of_normedAlgebra` gives `M` with `‖g‖ ≤ M` on `Å`; `c : K` with `1 < ‖c‖`
(`NontriviallyNormedField.exists_one_lt_norm`). For `f` with `|f|_sup ≠ 0`: choose `m : ℤ` with `‖c‖^(m-1) < |f|_sup ≤ ‖c‖^m`
(`exists_mem_Ioc_zpow` for `‖c‖ > 1`, `|f|_sup > 0`); `g := c^(-m) • f` has `|g|_sup = ‖c‖^(-m) |f|_sup ≤ 1`
(`supSeminorm_smul`, `norm_zpow`), so `g ∈ Å`, `‖g‖ ≤ M`, and `‖f‖ = ‖c‖^m ‖g‖ ≤ M ‖c‖^m < M ‖c‖ |f|_sup`:
`C := M * ‖c‖`. For `|f|_sup = 0`: `c^(-m) • f ∈ Å` for every `m`, so `‖f‖ ≤ M ‖c‖^m` for all `m`, letting `m → -∞`
(`‖c‖^m → 0`: `tendsto_zpow_atTop_zero`/`zpow` with `1/‖c‖ < 1`) gives `f = 0`, so `‖f‖ = 0 ≤ C * 0`.
`isReduced_of…`: a nilpotent `f` has `|f|_sup = 0` (T044 `→` direction, no reducedness), so `‖f‖ ≤ C * 0 = 0`.""",
  mathlib="""`TopologicalRing.isBounded_of_forall_norm_le`, `TopologicalRing.IsBounded.exists_norm_le_of_normedAlgebra` (PFA),
`NontriviallyNormedField.exists_one_lt_norm`, `exists_mem_Ioc_zpow`, `norm_zpow`, `zpow_neg`, `tendsto_zpow_atTop_zero`,
`isReduced_iff`, `IsNilpotent`.""",
  sources="""BGR 3.8.3/6, end of proof (`bgr-3.8-proofs.md`): "Choose an element `c ∈ k` with `|c| > 1`. We claim that
`|f| ≤ |c| |f|_sup` for all `f ∈ A` … there exists an `m ∈ ℤ` such that `|c|^{m−1} < |f|_sup ≤ |c|^m`. Then
`|c^{−m}f|_sup ≤ 1` and `|c|^m < |c| |f|_sup`. Set `g := c^{−m}f` so that `g ∈ Å` … `|f| = |c^m g| ≤ |c|^m ≤ |c| |f|_sup`";
[RM] §2.3.5 ("`Å` is bounded in `A` exactly when `|·|_sup` is equivalent to the norm of `A`").""",
  gen="""The `IsUniform` bridge to the adic-spaces roadmap is a seam ticket for later (plan §7); here the norm form.
No `CharZero`.""")

# ---------------------------------------------------------------- Affinoid/Reduction.lean
t(id='T053', title='The reduction `Ã = Å ⧸ Ǎ` is a reduced `K̃`-algebra (BGR 6.2.3/4, 1.2.5/7)', file=RED, deps='T047',
  par='yes (with T054)', typ='defs+instances', leaves='L9.1–L9.4',
  decls=[(RED,'powerBounded.ofUnitClosedBall'),(RED,'powerBounded.ofUnitClosedBall_mem_topologicallyNilpotent'),
         (RED,'Reduction.ofResidueField'),(RED,'Reduction.isReduced')],
  sketch="""`ofUnitClosedBall`: the ring-hom fields are `Subtype.ext` + `map_one/map_mul/map_zero/map_add` of `algebraMap K A`
(the carrier is `algebraMap K A c` with `algebraMap_mem_powerBounded (Subring.norm_le_one c)`).
`…_mem_topologicallyNilpotent`: `|algebraMap c|_sup = ‖c‖ |1|_sup ≤ ‖c‖ < 1` (`mem_openUnitBallIdeal`,
`Algebra.algebraMap_eq_smul_one`, `supSeminorm_smul`, `supSeminorm_one_le`). `Reduction.ofResidueField`:
`IsLocalRing.ResidueField (unitClosedBall K) = unitClosedBall K ⧸ maximalIdeal _` and `maximalIdeal (unitClosedBall K) =
openUnitBallIdeal K` (PFA `NormedRing.maximalIdeal_unitClosedBall`), so `Ideal.Quotient.lift (maximalIdeal _)
((Reduction.mk K A).comp (ofUnitClosedBall K A)) (fun c hc ↦ Ideal.Quotient.eq_zero_iff_mem.2 (… (by rwa
[maximalIdeal_unitClosedBall] at hc)))`. `isReduced`: `Ideal.Quotient.isReduced_iff`?/`Ideal.isRadical_iff_quotient_reduced`:
`IsReduced (R ⧸ I) ↔ I.IsRadical`, with T047 `topologicallyNilpotent_isRadical`.""",
  mathlib="""`IsLocalRing.ResidueField`, `IsLocalRing.residue`, `Ideal.Quotient.lift`, `Ideal.Quotient.eq_zero_iff_mem`,
`Ideal.isRadical_iff_quotient_reduced` (verify name), `RingHom.toAlgebra`; PFA `NormedRing.maximalIdeal_unitClosedBall`,
`mem_openUnitBallIdeal`.""",
  sources="""BGR 6.2.3/4 (`bgr-6.2-6.3.1.md`): "`Ã = {f ∈ A; |f|_sup ≤ 1}/{f ∈ A; |f|_sup < 1}`"; BGR 1.2.5/6–7 (`bgr-1.3-1.5.md`);
[RM] §2.3.4 ("The reduction `Ã := Å ⧸ Ǎ` is a `K̃`-algebra").""",
  gen="""`Reduction K A` is an `abbrev` for the quotient (so the `CommRing` instance is found); the `K̃`-algebra structure
is `(Reduction.ofResidueField K A).toAlgebra` for any `[HasSupSeminorm K A]`.""")

t(id='T054', title='`T̃ₙ ≅ K̃[X₁, …, Xₙ]`: the reduction of the Tate algebra (BGR 6.2.3/4 + 5.1.2)', file=RED, deps='T038, T047',
  par='yes (with T053)', typ='lemma+def', leaves='L9.5–L9.6',
  decls=[(RED,'TateAlgebra.powerBounded_eq_unitClosedBall'),(RED,'TateAlgebra.reductionEquiv')],
  sketch="""`powerBounded_eq_unitClosedBall`: `Subring.ext fun f ↦ by simp [mem_powerBounded, Subring.mem_unitClosedBall,
supSeminorm_eq_norm]` (Layer 0). `reductionEquiv`: `e : powerBounded K (Tₙ) ≃+* unitClosedBall (Tₙ)` from the subring
equality (`RingEquiv.subringCongr`); under `e`, `topologicallyNilpotent K (Tₙ)` maps onto `openUnitBallIdeal (Tₙ)`
(`mem_topologicallyNilpotent` is `|f|_sup < 1 ↔ ‖f‖ < 1 = mem_openUnitBallIdeal`); `Ideal.quotientEquiv _ _ e (by ext; simp …)`
gives `Reduction K (Tₙ) ≃+* unitClosedBall (Tₙ) ⧸ openUnitBallIdeal _`, then compose with Layer 0
`MvPowerSeries.Restricted.reductionEquiv : … ≃+* MvPolynomial (Fin n) (ResidueField (unitClosedBall K))`.""",
  mathlib="""`RingEquiv.subringCongr`, `Ideal.quotientEquiv`, `Ideal.map`, `RingEquiv.trans`, `Subring.ext`; Layer 0
`MvPowerSeries.Restricted.reductionEquiv`, `supSeminorm_eq_norm`; PFA `mem_openUnitBallIdeal`, `Subring.mem_unitClosedBall`.""",
  sources="""[RM] §2.3.4 ("for `Tₙ` it is `K̃[X]` (§0.1.2)"); BGR 5.1.2 (Layer 0 `TateAlgebra/Reduction.lean`, "`T̃ₙ = k̃[X₁, …, Xₙ]`");
BGR 6.2.3/4 (`bgr-6.2-6.3.1.md`).""",
  gen="""`TateAlgebra K n` with the Gauss norm; the instance `Affinoid.TateAlgebra.instHasSupSeminorm` is used.""")

t(id='T055', title='`|·|_sup` is a valuation iff `A` is reduced and `Ã` is a domain (BGR 6.2.3/5, via 1.5.3/1)', file=RED,
  deps='T043, T044, T053', par='no', typ='lemmas', leaves='L9.7–L9.9',
  decls=[(RED,'supSeminorm_mul_of_isReduced_of_isDomain_reduction'),(RED,'isReduced_of_isValuation'),(RED,'isDomain_reduction_of_isValuation')],
  sketch="""`supSeminorm_mul…` (BGR 1.5.3/1's proof): by contradiction suppose `|fg| < |f||g|`; then `f, g ≠ 0` and `|f|, |g| ≠ 0`
(else both sides `0`; `|f| = 0 → f = 0` in the reduced `A`, T044). T043: `c_i, s_i ≥ 1` with `|c_i • f_i^{s_i}|_sup = 1`
(`f_1 := f`, `f_2 := g`); WLOG `s_2 ≥ s_1` (symmetric). `u := c_1 • f^{s_1}`, `v := c_2 • g^{s_2}` lie in `Å ∖ Ǎ`
(`|u| = 1`). `|u v|_sup = ‖c_1‖ ‖c_2‖ |f^{s_1} g^{s_2}|_sup ≤ ‖c_1‖‖c_2‖ |fg|^{s_1} |g|^{s_2 − s_1} < ‖c_1‖‖c_2‖ |f|^{s_1}
|g|^{s_2} = |u| |v| = 1` (`supSeminorm_smul`, `supSeminorm_mul_le`, `supSeminorm_pow`, strict `mul_lt_mul`), so
`u v ∈ Ǎ`, i.e. `τ(u) τ(v) = 0` in the domain `Ã` with `τ(u), τ(v) ≠ 0` (`Ideal.Quotient.eq_zero_iff_mem`,
`|u| = 1 ≮ 1`): contradiction with `mul_eq_zero`/`NoZeroDivisors`. `isReduced_of_isValuation`: nilpotent `f` has
`|f|_sup = 0` (T044 or power-multiplicativity) so `f = 0`. `isDomain_reduction_of_isValuation`:
`Ideal.Quotient.isDomain_iff_prime`: `Ǎ` is prime: `Ǎ ≠ ⊤` since `1 ∉ Ǎ` (`|1|_sup = 1`, `Nontrivial A`); `u v ∈ Ǎ →
|u||v| = |uv| < 1 → |u| < 1 ∨ |v| < 1` (`mul_lt_one_iff`-style with `|u|, |v| ≤ 1`).""",
  mathlib="""`Ideal.Quotient.isDomain_iff_prime`, `Ideal.IsPrime`, `Ideal.Quotient.eq_zero_iff_mem`, `mul_eq_zero`, `mul_lt_mul''`,
`pow_le_pow_left`, `isReduced_iff`, `IsNilpotent`.""",
  sources="""BGR 6.2.3/5 (`bgr-6.2-6.3.1.md`): "The supremum semi-norm is a valuation on `A` if and only if `A` is reduced and `Ã`
is an integral domain" ("using Propositions 1.5.3/1, 6.2.1/4, and the above Proposition 4"); BGR 1.5.3/1 and proof
(`bgr-1.3-1.5.md`): "Assume there are elements `a₁, a₂ ∈ A` such that `|a₁a₂| < |a₁| |a₂|` … `(m₁a₁^{s₁})(m₂a₂^{s₂}) ∈ A˅`.
However, this is in contradiction with the fact that, by condition (ii), the ideal `A˅` is prime in `A°`"; BGR 1.5.1
(`bgr-1.3-1.5.md`): "A valued ring is an integral domain. The ideal `Ǎ` is prime in `Å`; hence `Ã` is also an integral
domain".""",
  gen="""BGR's iff split into three single-conclusion lemmas; "valuation" = multiplicative + `|f|_sup = 0 → f = 0`
(BGR 1.5.1/1 (a) and (c)). No norm on `A` is needed.""")

# ---------------------------------------------------------------- Affinoid/FunctionAlgebra.lean
t(id='T056', title='BGR 6.2.4/1 for affinoid domains (`[CharZero K]`)', file=AFA, deps='T037, T038', par='yes (with T057)',
  typ='theorem', leaves='L10.1', decls=[(AFA,'isBanachFunctionAlgebra_of_isDomain')],
  sketch="""Noether normalisation `φ : TateAlgebra K d →ₐ[K] A` finite injective (Layer 1); `letI := φ.toAlgebra`, tower,
`Module.Finite` (`hfin`), `FaithfulSMul` (`hinj`); `hcont : Continuous (algebraMap _ A)` = Layer 1
`AlgHom.continuous_of_isAffinoidAlgebra' (tateAlgebra d) hA φ`. Apply T037 `IsBanachFunctionAlgebra.of_finite_domain` with
`B := TateAlgebra K d`: `NormMulClass` (Layer 0), `IsDomain`, `IsIntegrallyClosed` (Rueckert), `IsNoetherianRing`
(Layer 1), `HasSupSeminorm` (T038), `hBsup := supSeminorm_eq_norm` (Layer 0), `hws := Affinoid.TateAlgebra.isWeaklyStable_fractionRing K d`
(Layer 0, `[CharZero K]`; its statement is exactly the `letI := IsFractionRing.normedField …; IsWeaklyStable …` form).""",
  mathlib="""`RingHom.toAlgebra`, `IsScalarTower.of_algebraMap_eq`, `faithfulSMul_iff_algebraMap_injective`, `Module.Finite` from
`RingHom.Finite`; Layer 0 `Affinoid.TateAlgebra.isWeaklyStable_fractionRing`; Layer 1 `exists_finite_injective`,
`AlgHom.continuous_of_isAffinoidAlgebra'`, `isNoetherianRing`.""",
  sources="""BGR 6.2.4/1, proof (`bgr-6.2-6.3.1.md`): "Let us first consider the case, where `A` is an integral domain. Choose a
finite normalization monomorphism `φ: T_d → A` for a suitable `d ≥ 0`. Then `φ` is torsion-free, and the assertion
follows immediately from Theorem 3.8.3/7, because the field of fractions `Q(T_d)` is weakly stable (Theorem 5.3.1/1)."
""",
  gen="""`[CharZero K]` (plan D2) and `A : Type u` with `K : Type u` (D12).""")

t(id='T057', title='The diagonal map `A → ∏ A ⧸ 𝔭ᵢ`: continuous scalar action, closed range, open-mapping bound', file=AFA,
  deps='T030', par='yes (with T056)', typ='lemmas', leaves='L10.2–L10.4',
  decls=[(AFA,'continuousSMul_pi_quotient'),(AFA,'isClosed_range_pi_quotient_mk'),(AFA,'exists_norm_le_mul_norm_pi_quotient_mk')],
  sketch="""Instances: `Ideal.Quotient.normedCommRing (𝔭 i)` (closed ideals: Layer 1 `hA.isClosed_ideal`), `Pi.normedCommRing`,
`Ideal.Quotient.normedAlgebra`, `Pi.normedAlgebra`, `Pi.completeSpace` (each quotient complete:
`QuotientAddGroup.completeSpace`/`Submodule.Quotient.completeSpace` for closed subgroups of a complete group).
`continuousSMul`: `a • x = fun i ↦ mk a * x i` (`Pi.smul_apply`, `Submodule.Quotient.mk_smul`/`Ideal.Quotient.mk_smul`?
— for `A ⧸ I` as an `A`-module, `a • mk b = mk (a * b)`); continuity from `continuous_pi`, `Continuous.mul`,
`Ideal.Quotient.continuous_mk`-type (`continuous_quot_mk`). `isClosed_range`: the range of `RingHom.pi (mk ∘ 𝔭)` is the
image of the `A`-submodule `⊤` under the `A`-linear map `LinearMap.pi (fun i ↦ (𝔭 i).mkQ)`, a submodule of the finite
`A`-module `∀ i, A ⧸ 𝔭 i` (`Module.Finite.pi`, each quotient finite: `Module.Finite.quotient`), so closed by T030
`Submodule.isClosed_of_isNoetherianRing_of_finite K` (`IsNoetherianRing A` from Layer 1; `NormedSpace K (Pi)`,
`IsScalarTower K A (Pi)` instances: `Pi.isScalarTower`). `exists_norm_le…`: the `K`-linear map `π : A →L[K] ∀ i, A ⧸ 𝔭 i`
is continuous, injective (`h`: kernel `= ⨅ 𝔭 i = ⊥`, `LinearMap.ker_pi`/`Submodule.iInf`), with closed range; open mapping
onto the range (`ContinuousLinearMap.exists_preimage_norm_le`) gives `‖f‖ ≤ C ‖π f‖` (uniqueness of the preimage).""",
  mathlib="""`Ideal.Quotient.normedCommRing`, `Ideal.Quotient.normedAlgebra`, `Pi.normedCommRing`, `Pi.normedAlgebra`, `Pi.completeSpace`,
`QuotientAddGroup.completeSpace`, `continuous_pi`, `continuous_quot_mk`, `LinearMap.pi`, `Submodule.mkQ`, `Module.Finite.pi`,
`Module.Finite.quotient`, `LinearMap.ker_pi`, `Submodule.ker_mkQ`, `ContinuousLinearMap.exists_preimage_norm_le`,
`IsClosed.completeSpace_coe`; Layer 1 `IsAffinoidAlgebra.isClosed_ideal`, `isNoetherianRing`.""",
  sources="""BGR 6.2.4/1, proof (`bgr-6.2-6.3.1.md`): "the canonical homomorphism `π: A → A' := ⊕ A/𝔭_i` is injective … Provide
`A'` with the maximum norm … Then `A'` is complete under `| |` … Viewing `A` as a submodule of the finite `A`-module
`A'`, we see by Proposition 3.7.3/1 that `A` is closed in `A'`."
""",
  gen="""Stated for an arbitrary finite family of ideals `𝔭 : ι → Ideal A` (the minimal primes are the instance); the
`haveI` for closedness is part of the statements so that the quotient normed-ring instances exist.""")

t(id='T058', title='M4 — REDUCED AFFINOID ALGEBRAS ARE BANACH FUNCTION ALGEBRAS (BGR 6.2.4/1)', file=AFA, deps='T006, T056, T057',
  par='no', typ='theorem', leaves='L10.5', milestone='M4 ([RM] §2.4.1, BGR 6.2.4/1)', decls=[(AFA,'isBanachFunctionAlgebra_of_isReduced')],
  sketch="""`ι := hfin.toFinset` with `hfin := minimalPrimes.finite_of_isNoetherianRing A` (a `Fintype` via `Finset`-subtype),
`𝔭 i := (i : Ideal A)`. `⨅ i, 𝔭 i = sInf (minimalPrimes A) = (⊥).radical = nilradical A = ⊥` (`Ideal.sInf_minimalPrimes`,
`nilradical_eq_zero` for reduced). T057 gives `C₀` with `‖f‖ ≤ C₀ ‖π f‖`. For each `i`, `A ⧸ 𝔭 i` is an affinoid domain
(`hA.quotient`, `Ideal.Quotient.isDomain` from `IsPrime`) with the residue norm, so T056 gives `C_i` with
`‖mk f‖ ≤ C_i |mk f|_sup ≤ C_i |f|_sup` (T006 `supSeminorm_mk_le`). `‖π f‖ = ⨆ i, ‖mk_i f‖ ≤ (max_i C_i) |f|_sup`
(`pi_norm_le_iff_of_nonneg`, `Finset.sup'`/`Finset.le_sup'`). `C := C₀ * max_i C_i` (use `Finset.sup' _ nonempty` when
`ι` nonempty, else `A` is trivial and any `C` works).""",
  mathlib="""`minimalPrimes.finite_of_isNoetherianRing`, `Ideal.sInf_minimalPrimes`, `nilradical_eq_zero`, `Ideal.Quotient.isDomain`,
`pi_norm_le_iff_of_nonneg`, `Finset.sup'`, `Finset.le_sup'`, `Set.Finite.toFinset`, `Fintype` on a finset coerced to type.""",
  sources="""BGR 6.2.4/1 (`bgr-6.2-6.3.1.md`): "Every reduced `k`-affinoid algebra `A` is a Banach function algebra; i.e., `| |_sup`
is a complete norm on `A`. It is equivalent to every other complete `k`-algebra norm on `A`." and its proof ("due to
Lemma 6.2.1/3, the norm `| |` induces the supremum norm on `A`"); [RM] §2.4.1.""",
  gen="""`[CharZero K]` (D2), `A : Type u` (D12), any complete `K`-algebra norm on `A`; the conclusion is the norm inequality
(D3).""")

t(id='T059', title='Consequences of M4: `Å` is bounded for reduced `A`; continuous maps out of reduced `A` are `|·|_sup`-bounded (§2.3.5, §2.4.3)',
  file=AFA, deps='T052, T058', par='no', typ='lemmas', leaves='L10.6–L10.7',
  decls=[(AFA,'isBounded_powerBounded_of_isReduced'),(AFA,'exists_norm_map_le_mul_supSeminorm')],
  sketch="""`isBounded_powerBounded_of_isReduced`: `(hA.exists_norm_le_mul_supSeminorm_iff_isBounded_powerBounded).1
(hA.isBanachFunctionAlgebra_of_isReduced)` (T052, T058). `exists_norm_map_le…`: `hφ` gives `C₁` with `‖φ f‖ ≤ C₁ ‖f‖`
(Layer 1 `exists_forall_norm_le_mul_of_continuous` or `ContinuousLinearMap.exists_bound` on `φ.toLinearMap`), M4 gives
`C₂`; `C := C₁ * C₂`.""",
  mathlib="""`ContinuousLinearMap.exists_bound`, `AlgHom.toLinearMap`, `LinearMap.mkContinuous`; Layer 1
`MvPowerSeries.Restricted.exists_forall_norm_le_mul_of_continuous`.""",
  sources="""[RM] §2.3.5 ("deduce from §2.4.1 that a reduced affinoid algebra is uniform") and §2.4.3; BGR 6.2.4/1 ("It is
equivalent to every other complete `k`-algebra norm on `A`").""",
  gen="""`[CharZero K]` inherited from M4; the `IsUniform` seam (plan §7) is left for the adic roadmap.""")

# ---------------------------------------------------------------- Affinoid/ReductionFunctor.lean
t(id='T060', title='The reduction functor on homomorphisms: `φ̊`, `φ̃`, functoriality, `K̃`-linearity (BGR 6.3 introduction)', file=RF,
  deps='T005, T053', par='yes (with T056–T059)', typ='defs+lemmas', leaves='L11.1–L11.7',
  decls=[(RF,'powerBoundedMap'),(RF,'powerBoundedMap_mem_topologicallyNilpotent'),(RF,'reductionMap'),(RF,'reductionMap_mk'),
         (RF,'reductionMap_id'),(RF,'reductionMap_comp'),(RF,'reductionAlgHom')],
  sketch="""`powerBoundedMap`: membership `|φ b|_sup ≤ |b|_sup ≤ 1` (T005 `supSeminorm_map_le`); ring-hom fields by `Subtype.ext`
and `map_*` of `φ`. `_mem_topologicallyNilpotent`: `|φ b|_sup ≤ |b|_sup < 1`. `reductionMap`: `Ideal.Quotient.lift
(topologicallyNilpotent K B) ((Reduction.mk K A).comp (powerBoundedMap φ))` with the kernel condition from the previous
lemma (`Ideal.Quotient.eq_zero_iff_mem`). `reductionMap_mk`: `Ideal.Quotient.lift_mk`. `reductionMap_id`,
`reductionMap_comp`: `RingHom.ext` + `Ideal.Quotient.ind`/`Quotient.inductionOn'` + `reductionMap_mk` + `rfl` on the
underlying elements. `reductionAlgHom`: `commutes'`: both sides are `Reduction.mk _ (ofUnitClosedBall …)` on residue
classes (`IsLocalRing.residue` surjective: `Ideal.Quotient.mk_surjective`), and `φ (algebraMap K B c) = algebraMap K A c`
(`φ.commutes`).""",
  mathlib="""`Ideal.Quotient.lift`, `Ideal.Quotient.lift_mk`, `Ideal.Quotient.eq_zero_iff_mem`, `Ideal.Quotient.mk_surjective`,
`RingHom.ext`, `AlgHom.commutes`, `AlgHom.mk`, `RingHom.toAlgebra`.""",
  sources="""BGR 6.3 introduction (`bgr-6.2-6.3.1.md`): "each such `φ` maps power-bounded elements into power-bounded elements and
topologically nilpotent elements into topologically nilpotent elements. Thus `φ` gives rise to a homomorphism
`φ̊: B̊ → Å` and furthermore, by reducing modulo topologically nilpotent elements, to a homomorphism `φ̃: B̃ = B̊/B̌ → Ã = Å/Ǎ`";
[RM] §2.5.1 ("Prove functoriality").""",
  gen="""For any `K`-algebra homomorphism between algebras with `HasSupSeminorm` (BGR: affinoid algebras; the contraction is
3.8.1/4); `reductionAlgHom` records `K̃`-linearity.""")

t(id='T061', title='Isometries and injective reductions (BGR 6.3.1/1–3)', file=RF, deps='T043, T044, T049, T060', par='no',
  typ='lemmas', leaves='L11.8–L11.10',
  decls=[(RF,'isometry_iff_forall_supSeminorm_eq_one_imp'),(RF,'injective_reductionMap_iff_isometry'),(RF,'ker_le_nilradical_of_injective_reductionMap')],
  sketch="""`isometry_iff…`: `→` trivial. `←` (BGR 6.3.1/1): for `g` with `|g|_sup = 0`, `|φ g|_sup ≤ |g|_sup = 0`. Else T043 (on `B`):
`c, m` with `|c • g^m|_sup = 1`, so `|φ(c • g^m)|_sup = 1` by hypothesis; `φ(c • g^m) = c • (φ g)^m`, hence `‖c‖ |φ g|^m = 1
= ‖c‖ |g|^m`, so `|φ g|^m = |g|^m` and `|φ g| = |g|` (`pow_left_injective` on nonnegatives, `m ≠ 0`).
`injective_reductionMap_iff_isometry` (BGR 6.3.1/2): `φ̃` injective ↔ `ker φ̃ = ⊥` ↔ `∀ b ∈ B̊, |φ b|_sup < 1 → |b|_sup < 1`
(`Ideal.Quotient.lift_injective_iff`-style / `RingHom.injective_iff_ker_eq_bot` + `Ideal.Quotient.eq_zero_iff_mem` +
`reductionMap_mk`). `→`: for `|g|_sup = 1` (so `g ∈ B̊`), if `|φ g|_sup < 1` then `τ g ∈ ker φ̃ = 0`, so `|g|_sup < 1`,
contradiction; hence `|φ g| = 1` (`≤ 1` by contraction); conclude by the first lemma. `←`: `|φ b| = |b|`, so `|φ b| < 1 → |b| < 1`.
`ker_le_nilradical…` (BGR 6.3.1/3): `φ g = 0 → |g|_sup = |φ g|_sup = 0 → g` nilpotent (T044 `supSeminorm_eq_zero_iff_isNilpotent`,
`mem_nilradical`).""",
  mathlib="""`pow_left_injective`/`pow_left_inj₀`, `RingHom.injective_iff_ker_eq_bot`, `Ideal.Quotient.eq_zero_iff_mem`, `Ideal.Quotient.mk_surjective`,
`mem_nilradical`, `RingHom.mem_ker`.""",
  sources="""BGR 6.3.1/1–3 and proofs (`bgr-6.2-6.3.1.md`): "If `|g|_sup ≠ 0`, choose `c ∈ k*` and `m ∈ ℕ` such that `|cg^m|_sup = 1`
(Proposition 6.2.1/4). Then `|c| |φ(g)|_sup^m = |φ(cg^m)|_sup = 1 = |cg^m|_sup = |c| |g|_sup^m`, and hence `|φ(g)|_sup = |g|_sup`";
"The map `φ̃: B̃ → Ã` is injective if and only if `φ: B → A` is an isometry"; "We have `rad B = {g ∈ B; |g|_sup = 0}` by
Proposition 6.2.1/4. Consequently, the kernel of any isometry `φ: B → A` is contained in `rad B`."
""",
  gen="""Affinoid `A`, `B` without norms (6.2.1/4 (ii) is the only input).""")

t(id='T062', title='BGR 6.3.1/4: for `φ` strict, `τ⁻¹(ker φ̃) = rad (B̌ + ker φ̊)` and `ker φ̃ = rad (τ(ker φ̊))`', file=RF,
  deps='T049, T051, T053, T060', par='no', typ='lemmas', leaves='L11.11–L11.12',
  decls=[(RF,'comap_ker_reductionMap_eq_radical_of_isStrictMap'),(RF,'ker_reductionMap_eq_radical_map_of_isStrictMap')],
  sketch="""First equation. `⊇`: `B̌ + ker φ̊ ≤ τ⁻¹(ker φ̃)` (both generators map to `0` under `φ̃ ∘ τ = τ_A ∘ φ̊`), and
`τ⁻¹(ker φ̃)` is radical because `Ã` is reduced (T053: `g^n ∈ τ⁻¹(ker φ̃) → φ̃(τ g)^n = 0 → φ̃(τ g) = 0`), so
`Ideal.radical_le_of_isRadical`?/`Ideal.IsRadical.radical_le_iff`. `⊆`: let `g ∈ B̊` with `φ̃(τ g) = 0`, i.e.
`φ g ∈ Ǎ`, i.e. `φ g` topologically nilpotent (T049 on `A`), i.e. `(φ g)^n → 0`. The set `U := {b | |b|_sup < 1}` is open
in `B` (T051) and contains `0`; strictness gives that `φ '' U` is open in `range φ` (as a subset of the subtype `range φ`),
and contains `φ 0 = 0`; the sequence `φ(g)^n = φ(g^n)` lies in `range φ` and tends to `0`, so for `n ≥ N`,
`φ(g^n) ∈ φ '' U` (`IsOpen.mem_nhds` + `Filter.Tendsto` in the subtype topology: `tendsto_subtype_rng`), i.e.
`φ(g^n) = φ(b)` with `|b|_sup < 1`; then `g^n - b ∈ ker φ`, and `g^n - b ∈ B̊` (`g^n ∈ B̊`, `b ∈ B̌ ⊆ B̊`), so
`g^n = b + (g^n - b) ∈ B̌ + ker φ̊` (`Ideal.mem_sup`), i.e. `g ∈ rad (B̌ + ker φ̊)` (`Ideal.mem_radical_iff`). Second
equation: `τ` is surjective with `ker τ = B̌ ≤ B̌ + ker φ̊`, so `map τ (rad I) = rad (map τ I)` (`Ideal.map_radical_of_surjective`;
verify the name, else prove via `Ideal.comap_radical` and `Ideal.map_comap_of_surjective`), and `map τ (B̌ + ker φ̊) = map τ (ker φ̊)`
(`Ideal.map_sup`, `map τ B̌ = ⊥`: `Ideal.map_quotient_self`/`Ideal.mk_ker`); finally `ker φ̃ = map τ (comap τ (ker φ̃))`
(`Ideal.map_comap_of_surjective`).""",
  mathlib="""`Ideal.mem_radical_iff`, `Ideal.IsRadical`, `Ideal.mem_sup`, `Ideal.map_radical_of_surjective`?, `Ideal.comap_radical`,
`Ideal.map_comap_of_surjective`, `Ideal.map_sup`, `Ideal.mk_ker`, `Ideal.map_quotient_self`, `IsOpen.mem_nhds`,
`Filter.Tendsto.eventually`, `tendsto_subtype_rng`, `Set.mem_image`.""",
  sources="""BGR 6.3.1/4 and proof (`bgr-6.2-6.3.1.md`): "Obviously, we have `B̌ + ker φ̊ ⊂ τ⁻¹(ker φ̃)` and therefore also
`rad (B̌ + ker φ̊) ⊂ τ⁻¹(ker φ̃)`. If `φ` is strict, this inclusion relation is just an equality … Then `φ(B̌)` is open
in `φ(B)`. Consider an arbitrary element `g ∈ τ⁻¹(ker φ̃) = φ̊⁻¹(Ǎ)`. From `lim φ(g)ⁿ = 0`, we conclude `φ(g)ⁿ ∈ φ(B̌)` and
hence `gⁿ ∈ B̌ + ker φ̊` for `n` big enough … The second equation is a consequence of the first one, since the formation of
the nilradical commutes with the map `τ: B̊ → B̃` for those ideals in `B̊` which contain `B̌ = ker τ`."
""",
  gen="""`A`, `B` affinoid with complete norms (strictness is topological); `IsStrictMap` as defined in `Affinoid/ReductionFunctor.lean`
(BGR 1.1.9: "the image of an open set is open in the image").""")

t(id='T063', title='BGR 6.3.1/5 and 6.3.1/6 (i) ⇒ (iii): strict maps with nilpotent kernel have injective reduction', file=RF,
  deps='T044, T047, T062', par='no', typ='lemmas', leaves='L11.13–L11.14',
  decls=[(RF,'injective_reductionMap_of_isStrictMap_of_ker_le_nilradical'),(RF,'injective_reductionMap_of_injective_of_isStrictMap')],
  sketch="""6.3.1/5: `ker φ̊ ≤ B̌`: for `b ∈ B̊` with `φ b = 0`, `b ∈ ker φ ≤ nilradical B`, so `b` is nilpotent and `|b|_sup = 0 < 1`
(T044 → direction). Hence `B̌ + ker φ̊ = B̌` (`sup_eq_left`), and `rad B̌ = B̌` (T047 `topologicallyNilpotent_isRadical`,
`Ideal.IsRadical.radical`); by T062 `τ⁻¹(ker φ̃) = B̌ = ker τ`, so `ker φ̃ = map τ (ker τ) = ⊥`
(`Ideal.map_comap_of_surjective`, `Ideal.mk_ker`), i.e. `φ̃` injective (`RingHom.injective_iff_ker_eq_bot`). (i) ⇒ (iii):
`ker φ = ⊥ ≤ nilradical B` (`RingHom.ker_eq_bot_iff_eq_zero`/`RingHom.injective_iff_ker_eq_bot`) and 6.3.1/5.""",
  mathlib="""`sup_eq_left`, `Ideal.IsRadical.radical`, `Ideal.map_comap_of_surjective`, `Ideal.mk_ker`, `RingHom.injective_iff_ker_eq_bot`,
`mem_nilradical`, `Ideal.Quotient.mk_surjective`.""",
  sources="""BGR 6.3.1/5 and proof (`bgr-6.2-6.3.1.md`): "If `ker φ ⊂ rad B`, then a fortiori `ker φ̊ ⊂ rad B̊`. Since `B̌` is a reduced
ideal, one has `rad (B̌ + ker φ̊) = B̌`. Now the preceding observation implies `ker φ̃ = 0`."; BGR 6.3.1/6 proof: "statement
(i) implies (iii) by Proposition 5. So far we did not use the fact that `B` is reduced".""",
  gen="""No reducedness (BGR: "So far we did not use the fact that `B` is reduced").""")

t(id='T064', title='M5 — BGR 6.3.1/6 (ii) ⇒ (i): for reduced `B`, an isometry is injective and strict', file=RF,
  deps='T044, T058, T061', par='no', typ='theorem', leaves='L11.15–L11.16', milestone='M5 ([RM] §2.5.3, BGR 6.3.1/6)',
  decls=[(RF,'injective_of_isometry'),(RF,'isStrictMap_of_isometry')],
  sketch="""`injective_of_isometry`: `φ g = 0 → |g|_sup = |φ g|_sup = |0|_sup = 0 → g = 0` (T044 `eq_zero_of_supSeminorm_eq_zero`,
`B` reduced); `injective_iff_map_eq_zero`. `isStrictMap_of_isometry`: M4 on `B` (T058, `[CharZero K]`): `‖g‖_B ≤ C |g|_sup
= C |φ g|_sup ≤ C ‖φ g‖_A` (Layer 0 `supSeminorm_le_norm` on `A`); and `φ` is continuous (Layer 1
`AlgHom.continuous_of_isAffinoidAlgebra' hB hA φ`), so `‖φ g‖ ≤ C' ‖g‖`. Hence `φ : B → range φ` is a bi-Lipschitz
bijection, i.e. a homeomorphism onto its image (`Homeomorph` from `AntilipschitzWith` + `LipschitzWith`, or directly: for
`U` open in `B`, `Subtype.val ⁻¹' (φ '' U)` is open in `range φ` because `φ⁻¹ : range φ → B` is continuous
(`AntilipschitzWith.isClosedEmbedding`/`LipschitzWith` of the inverse: `‖φ⁻¹ y - φ⁻¹ y'‖ ≤ C ‖y - y'‖`), and
`Subtype.val ⁻¹' (φ '' U) = (φ⁻¹) ⁻¹' U` on the range). Unfold `IsStrictMap`.""",
  mathlib="""`injective_iff_map_eq_zero`, `AntilipschitzWith`, `LipschitzWith`, `AntilipschitzWith.isClosedEmbedding`?,
`Topology.IsEmbedding`, `Set.rangeFactorization`, `Equiv.ofInjective`, `IsOpen.preimage`, `Metric.isOpen_iff`; Layer 0
`Affinoid.supSeminorm_le_norm`; Layer 1 `AlgHom.continuous_of_isAffinoidAlgebra'`.""",
  sources="""BGR 6.3.1/6 and proof (`bgr-6.2-6.3.1.md`): "We know from Theorem 6.2.4/1 that `B` is a Banach function algebra, i.e.,
that `| |_sup` is a complete norm on `B`. Therefore, any isometry `φ: B → A` with respect to `| |_sup` is injective. It
remains to verify that `φ` is also strict. Fix a Banach norm `| |` on `A`. Then `| |` dominates `| |_sup` on `A` and
`|g|_sup = |φ(g)|_sup ≤ |φ(g)|` for all `g ∈ B`. Since the supremum norm `| |_sup` induces the given Banach topology on
`B` and since `φ` is continuous anyway, we see that `φ` is strict."; [RM] §2.5.3.""",
  gen="""`[CharZero K]` (D2) and `B : Type u` (D12) for the strictness; injectivity needs neither. (ii) ⇔ (iii) is T061,
(i) ⇒ (iii) is T063: together the three-way equivalence of 6.3.1/6, never bundled (statement-splitting rule).""")

# ---------------------------------------------------------------- Affinoid/SupExamples.lean
t(id='T065', title='Examples in `Tₙ`: `|Xᵢ|_sup = 1`, `|m|_sup = ‖m‖`, `X` power-bounded, `c • X` topologically nilpotent', file=EX,
  deps='T003, T038, T048, T049', par='yes (with T066–T069)', typ='lemmas', leaves='L12.1–L12.4',
  decls=[(EX,'supSeminorm_X'),(EX,'supSeminorm_natCast'),(EX,'isPowerBounded_X'),(EX,'isTopologicallyNilpotent_smul_X')],
  sketch="""`supSeminorm_X`: `supSeminorm_eq_norm` (Layer 0) + `Affinoid.TateAlgebra.norm_X` (Layer 1 `TateAlgebra/Examples.lean`).
`supSeminorm_natCast`: `(m : Tₙ) = algebraMap K _ (m : K)` (`map_natCast`), `supSeminorm_algebraMap` (`Nontrivial Tₙ`).
`isPowerBounded_X`: Layer 1 `MvPowerSeries.Restricted.isPowerBounded_X` (Affinoid/Extend.lean) or T048 with `supSeminorm_X`.
`isTopologicallyNilpotent_smul_X`: T049 (`|c • X|_sup = ‖c‖ < 1`) or directly `‖(c • X)^n‖ = ‖c‖^n → 0`.""",
  mathlib="""`map_natCast`, `norm_smul`, `norm_pow`; Layer 1 `Affinoid.TateAlgebra.norm_X`, `MvPowerSeries.Restricted.isPowerBounded_X`.""",
  sources="""[RM] Examples ("`|X|_sup = 1` and `|p|_sup = p⁻¹` in `ℚ_p⟨X⟩` … `X` is power-bounded and `pX` is topologically nilpotent in
`K⟨X⟩`").""",
  gen="""Over any `K`; the `ℚ_p` instances follow by specialisation (`‖(p : ℚ_p)‖ = p⁻¹` is Mathlib `padicNormE.norm_p`).""")

t(id='T066', title='Examples in quotients of `K⟨X⟩`: `(X − a)`, `(X²)`, `(X² − a)`', file=EX, deps='T016, T017, T044, T052', par='yes (with T065, T067–T069)',
  typ='lemmas', leaves='L12.5–L12.9',
  decls=[(EX,'supSeminorm_mk_X_span_X_sub_C'),(EX,'supSeminorm_mk_X_span_X_sq'),(EX,'norm_mk_X_span_X_sq'),
         (EX,'not_isBounded_powerBounded_span_X_sq'),(EX,'supSeminorm_mk_X_span_X_sq_sub_C')],
  sketch="""`(X − a)`: Layer 1 `Affinoid/Examples.lean` has `ker_aeval_eq_span (ha : ‖a‖ ≤ 1) : RingHom.ker (eval at a) = span {X − C a}`
and `nonempty_algEquiv_quotient_X_sub`: the quotient is `≃ₐ[K] K` with `mk X ↦ a`; the unique point of `K` gives
`supSeminorm K (mk X) = ‖a‖` (T015 `supSeminorm_eq_spectralNorm` on `K`, transported along the `AlgEquiv` by
`supSeminorm_map_le` both ways, `spectralNorm_extends`). `(X²)`: `(mk X)^2 = mk (X^2) = 0` so `mk X` is nilpotent and
`|mk X|_sup = 0` (T044 with `tateAlgebra_quotient`). `norm_mk_X_span_X_sq`: the residue norm of `mk X` is
`inf_{g} ‖X + g X²‖` (Layer 1 `exists_norm_quotient_mk_eq`/`norm_quotient_mk_le`); `‖X + g X²‖ ≥ ‖coeff₁(X + gX²)‖ = 1`
(`norm_coeff_le`, the `X`-coefficient of `g X²` is `0`), and `‖X‖ = 1`: use `Ideal.Quotient.norm_mk_eq_norm_of_forall_le`
(Layer 1 NormedQuotient: `(∀ a ∈ I, ‖f‖ ≤ ‖f - a‖) → ‖mk f‖ = ‖f‖`). `not_isBounded…`: `isReduced_of_isBounded_powerBounded`
(T052) would make `T₁ ⧸ (X²)` reduced, but `mk X` is a nonzero nilpotent (`mk X ≠ 0` since `X ∉ span {X²}`: degree/coefficient
argument, e.g. by the residue norm `1 ≠ 0` from the previous lemma). `(X² − a)`: Layer 1 `isAffinoidAlgebra_quotient_X_sq_sub`
and (for `‖a‖ < 1`) `finrank_quotient_X_sq_sub`; in general `T₁ ⧸ (X² − C a) ≃ₐ[K] AdjoinRoot (X² − C a : K[X])` by
Weierstrass division (Layer 0 `TateAlgebra/Distinguished.lean`/`Finiteness.lean`: `X² − a` is `X`-distinguished of degree 2 for
`‖a‖ ≤ 1`; or Layer 1's `exists_algEquiv_quotient_X_norm_eq`-type lemma — check `Affinoid/Examples.lean` lines 56–130 for the
exact available statements). Then T016/T017 on `AdjoinRoot (X² − C a)` over `L := K`: `sup = supSpectralValue K (X² − C a) =
‖a‖^(1/2)` (the only nonzero term: coefficient `-a` at index `0`, exponent `1/2`, `supSeminorm_neg`, `supSeminorm_algebraMap`).""",
  mathlib="""`Ideal.Quotient.eq_zero_iff_mem`, `Ideal.mem_span_singleton`, `IsNilpotent`, `spectralNorm_extends`, `Real.rpow_natCast`;
Layer 1 `Affinoid.Examples.ker_aeval_eq_span`, `nonempty_algEquiv_quotient_X_sub`, `isAffinoidAlgebra_quotient_X_sq_sub`,
`exists_norm_quotient_mk_eq`, `Ideal.Quotient.norm_mk_eq_norm_of_forall_le`; Layer 0 Weierstrass division
(`TateAlgebra/Distinguished.lean`, `TateAlgebra/Finiteness.lean`).""",
  sources="""[RM] Examples ("`|X|_sup = |a|` in `K⟨X⟩/(X − a)`; the nilpotent `ε` in `K⟨X⟩/(X²)` has `|ε|_sup = 0` and residue norm `1`;
in `K⟨X⟩/(X² − p)` the element `X` has `|X|_sup = p^{−1/2} ∉ |K^×|`; … `K⟨X⟩/(X²)` is not uniform").""",
  gen="""`a` with `‖a‖ ≤ 1` (the ideals must be proper and `X`-distinguished); the "`∉ |ℚ_p^×|`" remark is not formalised
(it is immediate from `‖a‖^{1/2}` with `‖p‖ = p⁻¹`).""")

t(id='T067', title='The annulus algebra `K⟨X, Y⟩/(XY − c)`: `|f₁|_sup = |f₂|_sup = 1`, `|f₁f₂|_sup = ‖c‖` (BGR 6.2.3, example)', file=EX,
  deps='T002, T038', par='yes (with T065, T066, T068, T069)', typ='lemmas', leaves='L12.10–L12.13',
  decls=[(EX,'supSeminorm_mk_X_annulus'),(EX,'supSeminorm_mk_Y_annulus'),(EX,'supSeminorm_mk_X_mul_Y_annulus'),(EX,'not_forall_supSeminorm_mul_annulus')],
  sketch="""Points: the evaluation `ev₁ : T₂ →ₐ[K] K` at `(1, c)` (Layer 1 `extendAlgHom (Algebra.ofId K K) _ ![1, c] _` with
`‖1‖, ‖c‖ ≤ 1`; `extendAlgHom_X`) kills `XY − C c` (`1 · c − c = 0`), so it factors through `A := T₂ ⧸ annulusIdeal c`
(`Ideal.Quotient.liftₐ`), giving `ψ₁ : A →ₐ[K] K` with `ψ₁ (mk X) = 1`; its kernel is a maximal ideal `x₁` (Layer 0
`isMaximal_ker_of_isAlgebraic`) with `evalNorm K x₁ (mk X) = ‖ψ₁ (mk X)‖ = 1` (Layer 0 `evalNorm_eq_norm_algHom` with `L := K`).
Hence `|mk X|_sup ≥ 1`; and `≤ 1` by T038 `supSeminorm_le_norm_of_eq` with `‖X‖ = 1`. Symmetric for `Y` at `(c, 1)`.
`mk X * mk Y = mk (X Y) = mk (C c) = algebraMap K A c` (`XY − C c ∈ annulusIdeal`, `Ideal.Quotient.eq`), and
`|algebraMap c|_sup = ‖c‖` needs `Nontrivial A`, i.e. `annulusIdeal c ≠ ⊤`: `XY − C c` is not a unit of `T₂` (Layer 0
`isUnit_iff_norm_coeff_lt`: a unit has a dominant constant term; here `‖coeff_{XY}‖ = 1 ≥ ‖c‖`), so `span ≠ ⊤`
(`Ideal.span_singleton_eq_top`). `not_forall…`: `1 * 1 = 1 ≠ ‖c‖` when `‖c‖ < 1`.""",
  mathlib="""`Ideal.Quotient.liftₐ`, `Ideal.Quotient.eq`, `Ideal.mem_span_singleton_self`, `Ideal.span_singleton_eq_top`, `isUnit_iff_exists`;
Layer 1 `MvPowerSeries.Restricted.extendAlgHom`, `extendAlgHom_X`; Layer 0 `Affinoid.isMaximal_ker_of_isAlgebraic`,
`Affinoid.evalNorm_eq_norm_algHom`, `MvPowerSeries.Restricted.isUnit_iff_norm_coeff_lt`.""",
  sources="""BGR 6.2.3, the example after 6.2.3/5 (`bgr-6.2-6.3.1.md`): "The ideals `(X − 1, Y − c)` and `(X − c, Y − 1)` are maximal
ideals in `k⟨X, Y⟩` containing the ideal `(XY − c)` … Since `f₁(x₁) = 1 = f₂(x₂)`, we see that `|f₁|_sup = 1 = |f₂|_sup`.
However `|f₁f₂|_sup = |c|_sup = |c| < 1`. Consequently, `| |_sup` cannot be a valuation on `A`."
""",
  gen="""Our points are kernels of evaluation maps (no need to show `(X − 1, Y − c)` is maximal in `T₂`); that `A` is a domain
is plan D4 (not formalised).""")

t(id='T068', title='BGR 6.3.1 Example 2: `T₁ → K × K`, `X ↦ (c, 0)` is surjective but its reduction is not', file=EX,
  deps='T038, T044, T060', par='yes (with T065–T067, T069)', typ='lemmas+def', leaves='L12.14–L12.18',
  decls=[(EX,'isAffinoidAlgebra_prod'),(EX,'prodHom'),(EX,'prodHom_X'),(EX,'surjective_prodHom'),(EX,'not_surjective_reductionMap_prodHom')],
  sketch="""Instances on `K × K`: `Prod.normedCommRing`, `Prod.normedAlgebra`, `Prod.completeSpace`, PFA `Prod.instIsUltrametricDist`,
`Prod.normOneClass`. `prodHom`'s field: `‖(c, 0)‖ = max ‖c‖ 0 ≤ 1` (`Prod.norm_def`). `prodHom_X`: `extendAlgHom_X`.
`isAffinoidAlgebra_prod`: `IsAffinoidAlgebra.of_surjective (tateAlgebra 1) (prodHom K (c := 1) …)`-free: use the map with
`c := 1` (`‖1‖ ≤ 1`) and `surjective_prodHom` for `c = 1`, so first prove surjectivity for any `c ≠ 0`: `(1, 0) = φ (c⁻¹ • X)`
(`map_smul`, `prodHom_X`, `Prod.smul_mk`) and `(0, 1) = φ 1 - φ (c⁻¹ • X)`; `(u, v) = u • (1,0) + v • (0,1)` (`Prod.ext`).
`not_surjective_reductionMap…`: suppose `φ̃` surjective. The element `τ(1, 0) ∈ Reduction K (K × K)` (`(1,0) ∈ Å`:
`|(1,0)|_sup ≤ ‖(1,0)‖ = 1`) has a preimage `τ(g)`, `g ∈ T̊₁`; write `g = C g₀ + X h` (`Layer 0: coefficient extraction`:
`g - C (coeff 0 g)` is divisible by `X` in `T₁`: `MvPowerSeries.Restricted` shift… — alternative route avoiding division:
`|φ g - algebraMap (g₀)|_sup < 1` where `g₀ := coeff 0 g`: since `φ g = (g(c), g(0)) = (Σ gₙ cⁿ, g₀)` (`extendAlgHom_apply`:
`φ g = ∑ gₙ (c,0)ⁿ` as a convergent sum), `φ g - (g₀, g₀) = (Σ_{n≥1} gₙ cⁿ, 0)` has norm `≤ max_{n≥1} ‖gₙ‖ ‖c‖ⁿ ≤ ‖c‖ < 1`
(`‖gₙ‖ ≤ 1`); so `τ(φ̊ g) = τ(algebraMap g₀ · 1)`, i.e. `φ̃(τ g) ∈ range (Reduction.ofResidueField)`; but `τ(1, 0)` is not
in that range: `(1, 0) - (a, a) ∈ Ǎ` would give `‖(1 - a, -a)‖ < 1`, i.e. `‖1 - a‖ < 1` and `‖a‖ < 1`, contradicting
`‖1‖ = 1 ≤ max` (`IsUltrametricDist.norm_add_le_max`). (`|·|_sup` on `K × K` is `‖·‖`: two points, residue fields `K`;
prove `supSeminorm K (u, v) = max ‖u‖ ‖v‖` via the two projections as `AlgHom`s to `K` and Layer 0 `evalNorm_eq_norm_algHom`,
plus `supSeminorm_le_norm`.)""",
  mathlib="""`Prod.normedCommRing`, `Prod.normedAlgebra`, `Prod.norm_def`, `Prod.normOneClass`, `Prod.ext`, `Prod.smul_mk`, `map_smul`,
`IsUltrametricDist.norm_add_le_max`; PFA `Prod.instIsUltrametricDist`; Layer 1 `extendAlgHom`, `extendAlgHom_X`,
`extendAlgHom_apply` (the sum formula), `IsAffinoidAlgebra.of_surjective`; Layer 0 `evalNorm_eq_norm_algHom`.""",
  sources="""BGR 6.3.1 Example 2 (`bgr-6.2-6.3.1.md`): "Set `B := T₁ = k⟨X⟩` and `A := k ⊕ k` (ring-theoretic normed direct sum of
two copies of `k`). Choose a constant `c ∈ k`, `0 < |c| < 1`, and consider the homomorphism `φ: B → A`, `X ↦ (c, 0)`. It
is easily verified that `φ` is surjective. However `φ̃: k̃[X] → k̃ ⊕ k̃` cannot be surjective, since `|φ(X)|_sup = |c| < 1`
and hence `φ̃(X) = 0`."
""",
  gen="""`K × K` with the sup norm is BGR's "ring-theoretic normed direct sum"; `0 < ‖c‖ < 1` split into `hc0` (surjectivity)
and `hc : ‖c‖ < 1` (non-surjectivity of the reduction).""")

t(id='T069', title='BGR 6.3.1 Example 1 (hypothesis form, plan D5): finite extensions are affinoid, `K̃ → L̃` is injective, `K → L` is not surjective',
  file=EX, deps='T038, T061', par='yes (with T065–T068)', typ='lemmas', leaves='L12.19–L12.21',
  decls=[(EX,'isAffinoidAlgebra_of_finiteDimensional'),(EX,'injective_reductionMap_ofId'),(EX,'not_surjective_algebraMap_of_one_lt_finrank')],
  sketch="""`isAffinoidAlgebra_of_finiteDimensional`: `letI := spectralNorm.normedField K L; letI := spectralNorm.normedAlgebra K L`
(Layer 0 pattern; `IsUltrametricDist L`, `CompleteSpace L` by `spectralNorm.completeSpace`); a `K`-basis `v` of `L`
(`Module.finBasis`), scaled into the unit ball (`c • v i` with `‖c • v i‖ ≤ 1`, `NontriviallyNormedField.exists_norm_lt`-type
scaling, Layer 1 `exists_forall_norm_smul_le_one`); `extendAlgHom (Algebra.ofId K L) _ (scaled basis) _ : Tₙ →ₐ[K] L` is
surjective (its range is a `K`-subspace containing a basis: `Submodule.span_eq_top`), so `IsAffinoidAlgebra.of_surjective
(tateAlgebra n)`. `injective_reductionMap_ofId`: T061 `injective_reductionMap_iff_isometry` with `|algebraMap c|_sup = ‖c‖ =
|c|_sup` (`supSeminorm_algebraMap`, T015 on the fields `K` and `L`: `supSeminorm K c = spectralNorm K K c = ‖c‖`).
`not_surjective_algebraMap…`: a surjective `algebraMap K L` makes `L` one-dimensional (`finrank_eq_one_iff_of_nonzero'`/
`Module.finrank_le_one_iff`), contradicting `1 < finrank`.""",
  mathlib="""`spectralNorm.normedField`, `spectralNorm.normedAlgebra`, `spectralNorm.completeSpace`, `Module.finBasis`, `Submodule.span_eq_top`?,
`Module.finrank_le_one_iff`, `Algebra.ofId`; Layer 1 `extendAlgHom`, `exists_forall_norm_smul_le_one`, `IsAffinoidAlgebra.of_surjective`.""",
  sources="""BGR 6.3.1 Example 1 (`bgr-6.2-6.3.1.md`): "viewing `k` and `K` as `k`-affinoid algebras, the injection `φ: k ↪ K` is a
homomorphism of `k`-affinoid algebras which is not surjective. However, the residue homomorphism `φ̃: k̃ → K̃` is bijective,
since `f(K/k) = 1`."; plan D5 for the hypothesis form.""",
  gen="""Bijectivity of `φ̃` under "residue degree `1`" is not stated (it would need the identification `Reduction K L ≃+* L̃`);
injectivity holds unconditionally (an isometry), non-surjectivity of `φ` for `[L : K] > 1`.""")

t(id='T070', title='Chain-root gate: import `Affinoid.SupExamples` into `PhD/TauCeti.lean`, full build, lint, axioms', file='PhD/TauCeti.lean',
  deps='T001–T069, all CLEANUP-* of the twelve files', par='no', typ='gate', leaves='—',
  decls=[], statement_override="""-- PhD/TauCeti.lean: add
import PhD.TauCeti.Code.RigidAnalyticGeometry.Affinoid.SupExamples
-- then: ~/.elan/bin/lake build PhD.TauCeti   (no warnings, no sorries)
--       lake exe runLinter on each of the twelve Layer 2 modules
--       python3 .mathlib-quality/tauceti-rag-layer2/scratch/axioms.py on M1–M5""",
  sketch="""1. Add the import line (alphabetical position after `Affinoid.Examples`). 2. `lake build PhD.TauCeti` must report no
`sorry` and no warnings. 3. `lake exe runLinter PhD.TauCeti.Code.RigidAnalyticGeometry.<Module>` for the twelve modules.
4. `#print axioms` on `Affinoid.supSeminorm_eq_supSpectralValue_minpoly`, `IsAffinoidAlgebra.exists_evalNorm_eq_supSeminorm`,
`IsAffinoidAlgebra.isPowerBounded_iff_supSeminorm_le_one`, `IsAffinoidAlgebra.supSeminorm_eq_smoothingFun`,
`IsAffinoidAlgebra.isBanachFunctionAlgebra_of_isReduced`, `IsAffinoidAlgebra.isStrictMap_of_isometry` — standard only.
5. Never `import PhD.Main.*` (grep the twelve files).""",
  mathlib="""—""", sources="""[RM] Layer 2 dependencies; `tauceti-rag-layer1` gate ticket T064 (precedent).""",
  gen="""The chain root imports only the leaf file (it transitively imports the whole layer).""")
