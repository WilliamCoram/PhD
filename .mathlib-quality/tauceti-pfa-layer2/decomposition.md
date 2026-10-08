# Decomposition: p-adic functional analysis, Layer 2 (the model space and orthonormal bases)

Board `.mathlib-quality/tauceti-pfa-layer2/`. Written 2026-10-06 against the skeleton that builds with
`lake build PhD.TauCeti.Code.PadicFunctionalAnalysis.ModelSpace.Examples` (2 688 jobs, 0 errors, 256 declarations,
262 `sorry`s). References as in `plan.md` ([RM], [Sch], [Bel], [Buz07], [JN], [Col], [Lud], [L0], [L1], [NP], [SRC]);
line locators are into `references/*.txt` (copies of the Layer 0/1 reference texts) and the README.

Disposition: adversarial. Every leaf below carries a verbatim source quote, a Lean ↔ source match paragraph, an
attack log (three or more attacks), and a provability check against the pinned Mathlib (`scratch/names*.lean`,
≈ 420 names elaborated). Rejected leaves are recorded with the fix. The prior `b2_log.jsonl` (8 entries, boards
NewtonPolygon₀ and LWX) names no declaration of this board.

## Step 1 — the prose proofs (one per top-level result)

**R1 (§2.1, model space).** `C₀(I, E)` on a discrete `I` is the space of families tending to `0` cofinitely with
the sup norm `‖f‖ = sup ‖f i‖`, attained; it is ultrametric when `E` is and a bounded `R`-module when `E` is; the
`single i x` have norm `‖x‖`, the partial sums `∑_{i ∈ s} single i (f i)` are the truncations of `f` and converge
to `f`, so finitely supported families are dense and `eval i` has norm `1`. A bounded family `m : I → M` in a complete
ultrametric module gives `f ↦ ∑' f i • m i` (summable since the terms tend to `0`), of norm `sup ‖m i‖`, sending
`single i 1 ↦ m i`; a map out of `C₀(I, R)` is determined on the `single i 1` by the expansion, and over a Tate ring
its values there are bounded by `‖u‖`. Reindexing, disjoint unions, products and finite index sets give the four
isometries; a bounded ring homomorphism acts coordinatewise. [Sch] §3 and l. 2905–2947, [Buz07] l. 238–254, [Bel]
l. 2017–2027.

**R2 (§2.2, families, ON-ability, (Pr)).** With orthonormal = `‖∑ aᵢ eᵢ‖ = max ‖aᵢ‖` (E19), orthonormal ⟹ orthogonal
⟹ `t`-orthogonal; an orthonormal family gives the isometry `C₀(I, R) → M`; for an orthonormal basis every vector has a
unique expansion, the coefficients are continuous functionals, and the basis property is Bellaïche's/Colmez's
condition. `M` is ON-able iff it has an ON basis: the basis gives a surjective isometry (density + completeness),
the isometry gives the basis `Φ⁻¹(single i 1)`. The three notions are stable under transport, finite products and
`C₀(J, −)`; (Pr) is the lifting property (lift the images of the `single i 1` with the OMT bound; conversely lift
the identity along the surjection `C₀(unit ball, R) → M`), and a f.g. module with (Pr) splits a surjection from
`Rⁿ`, hence is projective. For `S ⊆ I`, the truncation transported along `Φ` is a norm-`1` projection onto the closed
span of `e|_S`. [Bel] II.1.5–II.1.7, II.1.19–II.1.20; [Buz07] l. 222–248; [JN] Def 2.1.5; [Sch] Prop 10.5.

**R3 (§2.3, Serre).** Under `‖R×‖ = ‖ϖ‖^ℤ` and `‖M‖ ⊆ ‖R‖`: the reduction of an ON basis is a basis of `M̃`
(relations reduce to norm `< 1`, hence coefficients in `ϖR⁰`; spanning by keeping the finitely many unit
coefficients); conversely LI reductions give the norm identity after scaling by `ϖⁿ`, and spanning reductions give
expansions by `ϖ`-adic successive approximation, with coefficients converging in the complete `R`. Hence `M` ON-able
iff `M̃` free; with the rescaled norm every module becomes potentially ON-able when all `R̃`-modules are free, e.g.
`R̃` a field, which is the case for a discretely valued field (`ϖ.ideal` = the maximal ideal); ON-able on the nose
iff `‖M‖ ⊆ ‖K‖`. The index of `C₀(I, K)` is invariant: finite case by dimension, infinite case by the
countable-support argument `|J| ≤ |I|·ℵ₀ = |I|`. [Bel] II.1.11–II.1.13; [Col] Prop 1.1.5; [Sch] Prop 10.1, Remark
10.2, Lemma 10.3, Lemma 1.4.

**R4 (§2.4, countable type).** From a countable set with dense span extract a linearly independent sequence `u`
with the same span; for the finite-dimensional closed `Vₙ = span(u₀..uₙ₋₁)` and `uₙ ∉ Vₙ` choose `vₙ ∈ uₙ + Vₙ`
realising the distance to `Vₙ` up to `rₙ/rₙ₊₁`; the two-term inequality `‖a vₙ + w‖ ≥ ρₙ max(‖a vₙ‖, ‖w‖)` and
induction give `‖∑ aᵢvᵢ‖ ≥ t·max ‖aᵢvᵢ‖`; rescale into `(‖ϖ‖, 1]`. The induced `f : c₀(ℕ) → V` is bounded below,
so has closed range, which is dense; `f` is a topological isomorphism (OMT). Quotients are of countable type;
closed subspaces are complemented by lifting the identity of the quotient (which has (Pr) by Prop 10.4 or by Serre
over a discretely valued field); a closed subspace is then a quotient, hence of countable type. [Sch] Prop 10.4,
Prop 10.5 and their proofs l. 3029–3140.

**R5 (§2.5, dual).** `λ ↦ (λ(single i 1))ᵢ` is an isometry onto `ℓ^∞` by R1 (uniqueness, `ofBounded`, the norm
formula); the pairing is bounded by `‖λ‖‖f‖` (ultrametric tsum bound); evaluation into `(ℓ^∞)'` attains `‖f i‖` at
`δᵢ`; transposes have transposed matrices by the expansion of `u(single j 1)`. [Sch] §3 example l. 617–700.

**R6 (§2.6, matrices).** `matrixCoeff u i j = u(single j 1) i`: columns tend to `0` (they are elements of `C₀`),
entries are bounded by `‖u‖`, `(u f) i = ∑' a i j f j` (expand `f`, apply `u`, evaluate), `‖u‖ = sup |a i j|`
(ultrametric tsum bound), `ofMatrix` is `ofBounded` of the columns, composition is the matrix product with a
bounded-times-null middle sum. Diagonal operators: norm `sup ‖dᵢ‖`, isometric for multiplicative units of norm `1`,
injective for non-zero-divisors, dense range for units. Base change: the matrix `φ(a i j)`. Truncations: norm ≤ 1,
closed complemented range, finite free range for finite `S`, pointwise convergence; Bellaïche II.1.8 by the OMT on
`Rʳ → P`; Buzzard 2.3 (a) by Noetherianity of the column module, (b) by closedness of submodules of `R^S` (Layer 1
M2) and continuity of linear maps out of f.g. Banach modules (Layer 1 Buzzard 2.2). [Buz07] l. 272–303, 335–392;
[Bel] II.1.8; [JN] 2.1.8.

**R7 (§2.7, unitriangular).** `T = ofMatrix a`; `‖Tf‖ = ‖f‖` by the largest index `j₀` with `‖f j₀‖ = ‖f‖`: the
diagonal term of `(Tf) j₀` has norm `‖f‖`, the lower terms norm `≤ q‖f‖`, the upper terms norm `< ‖f‖`; surjectivity:
solve the upper unitriangular system exactly on a finite truncation of `g` by backward substitution (finite
columns), the lower part contributes `≤ q‖g‖`, iterate with factor `max q ½`. A family `f j = ∑ a i j e i` in an ON
basis is then the image of the canonical basis under the isometry `Φ ∘ T`. [RM] §2.7; [SRC] 06_Unitriangular.

## Step 2 — the leaves (ticket ↔ leaves), with quotes, matches, attacks, provability

Format per ticket: **Q** verbatim source quote(s) with locator · **M** Lean ↔ source match · **A** attacks attempted
(outcome) · **P** provability (Mathlib / project / API gap) · **LOC** estimate.

### T001 (L1.1–L1.4) redefinition of `IsOrthonormalFamily`
- **Q** [Bel] l. 2010–2015: "An orthonormal basis for the module `M` is a family `(e_i)_{i∈I}` of elements of `M` such
  that `|e_i| = 1` for every `i ∈ I`, and such that for every element `m ∈ M` there exists a unique sequence `(a_i)` of
  elements of `R` converging to zero such that `m = ∑ a_i e_i` and `|m| = sup_i |a_i|`." [Buz07] l. 229–233: "If
  `m = ∑ a_i e_i` then `|m| = max_{i∈I} |a_i|`." [Col] l. 108–109: "(ii) `v_B(x) = inf_{i∈I} v_p(a_i)`."
- **M** the second conjunct `‖∑ aᵢ • eᵢ‖₊ = s.sup ‖aᵢ‖₊` for finite combinations is the finite case of the three quotes;
  the first conjunct `‖eᵢ‖ = 1` is Bellaïche's first condition (redundant under `NormOneClass`, kept for the roadmap's
  wording). The old convention-5 form `max ‖aᵢ • eᵢ‖` is Schneider's *orthogonal* notion plus `‖eᵢ‖ = 1`.
- **A** (1) *Is the old form really insufficient?* Yes: `R = ℚ_p⟨X⟩`, `M = ℚ_p` with `X ↦ 0`, `e = {1}`: `‖a • 1‖ = ‖a(0)‖`
  while `‖a‖_Gauss ≥ ‖a(0)‖`; `{1}` is orthonormal in the old sense, `M` is torsion, `C₀(I, R)` is torsion-free, so
  §2.2.3 fails. Rejected the old definition. (2) *Does the new form break the RAG consumers?* Their three proof sites
  prove the identity with `‖aᵢ • eᵢ‖₊ = ‖aᵢ‖₊` available (`nnnorm_smul` + `‖eᵢ‖ = 1`); only proofs change. (3) *Do the
  ring-generalised lemmas still hold?* `exists_hasSum`'s Cauchy argument uses only `‖aᵢ‖ ≤ ‖∑‖` and completeness of
  `R` — fine. (4) *Equivalence over fields?* `‖aᵢ • eᵢ‖ = ‖aᵢ‖‖eᵢ‖ = ‖aᵢ‖` — the two definitions agree, so nothing
  proved by the RAG board changes meaning.
- **P** project-only; the RAG files compile after the described edits (checked by reading the three proof sites).
- **LOC** ≈ 40 changed lines.

### T002 (L2.1–L2.7) sup norm · **Q** [RM] §2.1.1 ("the sup-norm formula `‖f‖ = ⨆ i, ‖f i‖`, that the supremum is attained
when `f ≠ 0`, that `f → 0` cofinitely"); [Sch] l. 617–700 ("each `Y_x` is finite or countable"). · **M** `norm_eq_iSup`
is Mathlib's `BoundedContinuousFunction.norm_eq_iSup_norm` through the isometry `toBCF`; `tendsto_cofinite` is
`zero_at_infty'` with `cocompact_eq_cofinite`; `countable_support` is Schneider's observation. · **A** (1) attained for
`f = 0`? the statement takes `[Nonempty I]` and any `i` works; (2) attained for `I` infinite? Layer 0's
`exists_norm_eq_iSup` handles it from the cofinite tendsto; (3) `sum_apply` needs an additive-hom coercion — none exists
for `C₀`, so induction (verified: `coeFnAddMonoidHom` absent). · **P** Mathlib names verified; L0 lemma verified. · **LOC** 45.

### T003 (L3.1–L3.3) instances · **Q** [RM] §2.1.1 ("`IsUltrametricDist`, and for a normed ring `R` with bounded action on
`E`, `Module R C₀(I, E)` with `IsBoundedSMul R C₀(I, E)` (and `NormSMulClass` when `E` has it)"). · **M** exactly the
three instances; `Module R C₀(I, E)` is Mathlib's (needs `ContinuousConstSMul R E`, which `IsBoundedSMul` provides).
· **A** (1) diamond with Mathlib's `NormedSpace 𝕜 C₀`? `NormedSpace` extends `Module` with `norm_smul_le` and has no
`IsBoundedSMul` field; `IsBoundedSMul R C₀` is a Prop class with no Mathlib instance for `C₀` (`#synth` fails), so no
diamond; (2) ultrametricity for non-discrete `I`? the proof is coordinatewise, so true for any `I`; (3) `NormSMulClass`
needs `Real.mul_iSup_of_nonneg` with `0 ≤ ‖r‖` — fine, including `I` empty (both sides `0`). · **P** Mathlib. · **LOC** 35.

### T004 (L4.1–L4.6) `single` · **Q** [Buz07] l. 238–243 ("`e_i` to be the function sending `j ∈ I` to `0` if `i ≠ j`, and to
`1` if `i = j`"). · **M** `single i x = Pi.single i x` as an element of `C₀`; `norm_single` is the sup over a
one-point support. · **A** (1) `Pi.single` needs `DecidableEq` — carried as an instance argument; (2) `norm_single` for
`x = 0`: both sides `0`; (3) `smul_single` over a noncommutative ring: `r • (x)` at `i` is `r • x`, matches `Pi.single_smul`.
· **P** Mathlib. · **LOC** 30.

### T005 (L5.1–L5.5) expansion · **Q** [RM] §2.1.2 ("the expansion `f = ∑' i, f i • single i 1`, convergent in norm;
finitely supported families are dense"); [Bel] footnote l. 2024–2027 ("When the sequence `(m_i)` converges to `0`, … the
sequence `(∑_{i∈J} m_i)_{J∈F(I)}` converges to some limit in `M`"). · **M** `hasSum_single_apply` is the footnote for the
family `single i (f i)`, proved directly (the partial sums are truncations); `norm_evalCLM` is "`eval i` of norm `1`".
· **A** (1) *Completeness needed?* No — the limit `f` is given; rejected adding `[CompleteSpace E]`. (2) *`HasSum` vs
`Tendsto` along `atTop (Finset I)`*: `HasSum` is by definition this tendsto. (3) *`norm_evalCLM` for `R` with `‖1‖ ≠ 1`?*
false (`‖single i 1‖ = ‖1‖`), hence `[NormOneClass R]`. · **P** `Finset.sum_pi_single'`, `le_opNorm_of_bound` verified.
· **LOC** 70.

### T006 (L6.1–L6.3) uniqueness · **Q** [Sch] l. 2905–2947 ("`f` is uniquely determined by its values on the `1_x`");
[Buz07] l. 274–280. · **M** `ext_single` is the uniqueness; `exists_bound_single` is "`|φ(e_i)| ≤ |φ|`". · **A**
(1) uniqueness over a non-complete `R`? Only continuity and the expansion are used — holds. (2) boundedness without
Tate? false in general (Layer 1 §1.1.2: continuous ≠ bounded over `ℤ_p` with the squared norm), hence `[IsTate R]`.
(3) `HasSum.mapL` for semilinear maps? we use linear maps only. · **P** Mathlib/L1. · **LOC** 25.

### T007 (L7.1–L7.5) `ofBounded` · **Q** [Sch] l. 2905–2947 ("for any map `x ↦ v_x` into a bounded subset of `V` there is a
unique continuous linear map `f : c₀(X) → V` with `f(1_x) = v_x`" and "`‖f()‖ ≤ sup ‖v_x‖ · ‖‖_∞`"); [Buz07] l. 280–283.
· **M** `ofBounded R m hm` with `norm_tsum_smul_le` as the bound; the `mkContinuous` constant is `⨆ ‖m i‖`. · **A**
(1) *summability over a non-ultrametric `M`?* fails (`∑ 1/n` type counterexamples), so `[IsUltrametricDist M]`; (2) *`I`
empty*: `⨆` over empty is `0`, and `C₀(I, R)` is `0`: the bound `‖0‖ ≤ 0 * ‖f‖` holds; (3) *`tsum_const_smul` needs
summability*: provided by L7.1. · **P** names verified (`Summable.tsum_const_smul`, `norm_tsum_le_of_forall_le`). · **LOC** 60.

### T008 (L8.1–L8.3) norm and converse · **Q** [Buz07] l. 280–283 ("`|φ| = sup_{i∈I} |n_i|`"); [RM] §2.1.3. · **M** `norm_ofBounded`
is the equality, `eq_ofBounded` the bijection of the universal property (the inverse direction). · **A** (1) equality for
`R` without `‖1‖ = 1`? `‖single i 1‖ = ‖1‖` enters: `[NormOneClass R]` required — for a general `R` only `≤` holds;
(2) does `≥` need Tate? No: `le_opNorm_of_bound` works from any explicit bound; (3) `eq_ofBounded` universe/`DecidableEq`:
fine. · **P** L1. · **LOC** 30.

### T009–T011 (L9–L11) reindexing · **Q** [RM] §2.1.4 (the four isometries, quoted in the tickets). · **M** `reindex`,
`sumEquiv`, `prodEquiv`, `piEquiv`, `blockEquiv := prodEquiv.trans piEquiv`, `setSumComplEquiv := reindex.trans sumEquiv`.
· **A** (1) *`Sum.elim` tends to `0`?* bad set = image of two finite sets — true; (2) *`prodEquiv`'s outer tendsto*: this is
exactly Layer 0's `iSup_norm_cofinite_left` (verified name and statement), and the inverse direction is
`tendsto_cofinite_prod_of_tendsto_iSup_norm` — both present, so no new infrastructure; (3) *`piEquiv` with `Finite` vs
`Fintype`*: Mathlib's Pi norm needs `Fintype`; (4) *`congrRight` continuity of the inverse*: isometric inverse — fine.
· **P** Mathlib/L0. · **LOC** 70 + 120 + 70.

### T012 (L12) `compL`, `congrRightL` · **Q** [RM] §2.2.3 (stability under `C₀(J, −)`). · **M** post-composition. · **A**
(1) *without Tate?* an unbounded continuous `u` gives an unbounded post-composition (same counterexample as T006), so
`[IsTate R]` — rejected the Tate-free version (seam S3); (2) the `≃L` inverse is `compL e.symm` — composition identities
by `ext`. · **P** L1. · **LOC** 40.

### T013 (L13) `map φ` · **Q** [RM] §2.1.5 (quoted in the ticket). · **M** coordinatewise `φ`. · **A** (1) *`mkContinuous` with
a negative `C`*: the obligation `‖map f‖ ≤ C‖f‖` fails for `C < 0` (both sides: `0 ≤ C‖f‖` false) — **rejected the
skeleton's first version; fixed to `max C 0`** (the fix is in the skeleton); (2) semilinearity: `φ (r * x) = φ r * φ x`
— `→SL[φ]` is the right type; (3) isometry when `‖φ r‖ = ‖r‖`: sandwich. · **P** Mathlib. · **LOC** 50.

### T014–T016 (L14–L16) truncations · **Q** [RM] §2.6.3; [Bel] l. 2038–2042 ("`π_S : M → M` the projection of `M` onto `M_S`
sending `e_i` to `e_i` if `i ∈ S`, and `e_i` to `0` if `i ∉ S`"); [Bel] l. 2062–2064 ("the sequence `(π_S ∘ φ)` converges").
· **M** `truncation S` for any `S`; `range_truncation_finset` is `M_S`; `tendsto_truncation_finset` is the pointwise
convergence. · **A** (1) *closed complemented range*: the projector is the truncation itself (idempotent) — fine;
(2) *`range_truncation_finset` ⊆ direction*: `truncation ↑s g = ∑_{i∈s} g i • single i 1` is a finite identity;
(3) *tendsto along `Finset I` with `atTop`*: `Finset` is a lattice, `atTop` is the filter of finite subsets. · **P**
Mathlib. · **LOC** 70 + 60 + 25.

### T017 (L17) implications · **Q** [RM] §2.2.1; [Sch] l. 3080–3083 (scaling). · **M** per lemma. · **A** (1) *LI of an orthogonal
family with nonzero members over a ring?* FALSE without multiplicativity: `R = ℤ_p[ε]/(ε²)` with the max norm, `e = {ε}`,
`ε • ε = 0` — **rejected the roadmap's statement; `[NormSMulClass R M]` added (E21)**; (2) *orthonormal ⟹ orthogonal
needs `IsBoundedSMul`?* no: `‖a • eᵢ‖ = ‖a‖` comes from the identity at a singleton; (3) *reindexing a basis*: the span
of `e ∘ σ` equals the span of `e` for a bijection — `Surjective.range_comp`. · **P** Mathlib. · **LOC** 110.

### T018 (L18) isometric embedding · **Q** [Sch] l. 2975–2976 ("A continuity argument now shows that we have `‖f()‖ = ‖‖_∞`").
· **M** `norm_ofBounded_apply`. · **A** (1) *the `≥` direction when the sup of `‖f i‖` is not attained*: it is attained
(`exists_norm_apply_eq_norm`) — needs `Nonempty I`, handled by the empty case; (2) `≤` by the ultrametric tsum bound
without `⨆` manipulation; (3) over a ring with `‖1‖ ≠ 1`: `‖eᵢ‖ = 1` is in the definition, so fine. · **P** L0/T001.
· **LOC** 35.

### T019–T020 (L19–L20) coefficients and the Bellaïche–Colmez form · **Q** [Bel] l. 2010–2015; [Col] l. 95–112. · **M** `coeff`
via choice, `coeffCLM`, `isOrthonormalBasis_iff`. · **A** (1) *is uniqueness among expansions needed as a hypothesis in
`isOrthonormalBasis_of_forall_hasSum`?* no — the norm formula for every expansion implies it (difference has norm `0`);
the statement is weaker than Bellaïche's and still sufficient (checked both directions); (2) *`‖eᵢ‖ = 1` from the
norm formula*: with `a = Pi.single i 1` it gives `‖eᵢ‖ = ⨆ ‖Pi.single i 1 j‖ = ‖1‖` — needs `NormOneClass`; (3) *the
`Finset.sup`/`iSup` conversion*: both inequalities elementary. · **P** Mathlib/T001. · **LOC** 70 + 70.

### T021–T022 (L21–L22) ON-ability basics and stability · **Q** [Bel] Ex II.1.7 l. 2017–2024 ("The Banach `R`-module `c_I(R)` …
is orthonormalizable. There is even a canonical orthonormal basis … A Banach `R`-module `M` is orthonormalizable (resp.
potentially orthonormalizable) if and only if it is isometric (resp. isomorphic) to `c_I(R)`"); [JN] l. 537–545;
[Buz07] l. 246–248. · **M** the three definitions follow [JN]; `isONable_zeroAtInfty` is Ex II.1.7. · **A** (1) *universe
of the index*: `C₀(J, R) : Type (max w u)` while the definition wants `I` in that universe — `ULift` (verified
discrete-topology instance on `ULift`); (2) *`HasPr` as a retract vs direct summand*: equivalent (T024); (3) *injectivity
of an orthonormal family over a ring*: the combination `eᵢ − eⱼ` has sup norm `‖1‖ = 1` — needs `NormOneClass`;
(4) *`IsPotentiallyONable.zeroAtInfty` without Tate*: `congrRightL` needs Tate (S3). · **P** Mathlib/T009–T012. · **LOC** 110 + 110.

### T023 (M1) · **Q** [RM] §2.2.3 ("`IsONable R M ↔ ∃ (I : Type) (e : I → M), IsOrthonormalBasis e`"); [Sch] l. 2977–2981
("As an isometry `f` in particular is injective and has a complete and hence closed image. For the surjectivity of `f`
it therefore suffices to show that the vector subspace `V₀` is dense"). · **M** surjectivity via expansions (completeness
of `R` and `M`), reindexing along `Set.range e` for the universe. · **A** (1) *the topology on `Set.range e`*: the subtype
inherits `M`'s topology, which is not discrete — **the proof must `letI := ⊥`**; recorded in the sketch; (2) *`I : Type v`
in the iff's right-hand side*: the ⟹ direction produces exactly that; (3) *does the ⟸ direction need `CompleteSpace R`?*
yes (expansions); Schneider has a field. · **P** Mathlib/T019. · **LOC** 45.

### T024–T027 (L24–L27) complements and lifting · **Q** [Bel] II.1.6 l. 2223–2225, Ex II.1.19 l. 2226–2228 ("`P` has property
(Pr) if and only if for every continuous surjection `f : M → N`, and every continuous map `α : P → N` there exists a
continuous map `β : P → M` such that `fβ = α`"), Prop II.1.20 l. 2229–2235; [Sch] Prop 10.5 l. 3128–3137 (the lift of
the `1_x` with bound `c⁻¹`); [RM] §2.2.5. · **M** `exists_lift` is Schneider's construction (OMT bound + universal
property); `exists_surjective_zeroAtInfty` provides the surjection Bellaïche's exercise presupposes; `projective` is
II.1.20 verbatim (`of_split`). · **A** (1) *universes in the characterisation*: `N := C₀(I, R)` lives in `Type (max u v)`
and `N' := M` in `Type v` — **the first skeleton quantified both in `Type (max u v)` and could not be applied; fixed
to `(N : Type (max u v)) (N' : Type v)`**; (2) *the surjection from a model space without Tate*: scaling into the unit
ball needs a pseudo-uniformiser — `[IsTate R]`; (3) *`projective` needs `Fin n → R` Banach ultrametric*: `CompleteSpace R`,
`IsUltrametricDist R` added; (4) *§2.2.5's projection norm*: `‖T (Φ⁻¹ x)‖ ≤ ‖x‖` — fine. · **P** L1 OMT, `of_split`
verified, `closedComplemented_ker_of_rightInverse` verified. · **LOC** 50 + 120 + 110 + 40.

### T028–T030 (L28–L30) Bellaïche II.1.12 · **Q** [Bel] l. 2082–2105 (full lemma and proof, quoted in the tickets); [Col]
l. 136–171. · **M** `residueFamily` is `ẽ`; the three leaves are the "only if" (LI + spanning), the norm identity and the
successive approximation. · **A** (1) *the norm identity without division*: Schneider divides by `a₁`; Bellaïche
multiplies by `πⁿ` — the ring proof uses `ϖ.unit ^ (-n)`, which needs `hR` (checked: `‖a i₀‖ = ‖ϖ‖ ^ n` exists); (2) *the
"only if" needs `hM`*: `mem_ideal_smul_top_iff_norm_lt_one` has `hM` as hypothesis in Layer 0 — carried; (3) *spanning
needs only finitely many unit coefficients*: `a → 0` cofinitely and `‖a i‖ ∈ ‖ϖ‖^ℤ ∪ {0}` by `hR`, so `‖a i‖ < 1 ⟹ ≤ ‖ϖ‖`;
(4) *convergence of the coefficient sequence*: `‖aⁿ_i − aⁿ⁺¹_i‖ ≤ ‖ϖ‖ⁿ` — geometric, `R` complete. · **P** L0 names
verified (`mem_ideal_smul_top_iff_norm_lt_one`, `ideal_eq_openUnitBallIdeal`, `mem_ideal_iff`). · **LOC** 90 + 100 + 200.

### T031–T032 (M2) Serre · **Q** [Bel] l. 2086–2087, Thm II.1.13 l. 2108–2114 ("Set `|m|' = inf_{r∈p^ℤ, r≥|m|} r`. Then `||'` is
a norm on `M` which is equivalent to `||` and satisfies Hypothesis II.1.11"); [Sch] Prop 10.1 l. 2952–2960 and Remark
10.2 l. 3003–3006; [Sch] Lemma 1.4 l. 291–312. · **M** `isONable_iff_free_residueModule`; the rescaled norm is Layer 0's
`Rescaled`; the field form uses `IsRankOneDiscrete` (convention 8). · **A** (1) *is `ϖ.ResidueRing` a field for a
discretely valued field?* `ϖ.ideal = openUnitBallIdeal = maximalIdeal` (Layer 0 names verified) — yes; (2) *the uniformiser
from `IsRankOneDiscrete`*: Mathlib gives a generator `γ < 1` of the value group and `generator_mem_range`; the `zpow`
representation of every norm is [NP]'s `exists_zpow_generator_eq` (verified in the NP file); (3) *`isONable_iff_forall_exists_norm_eq`
⟸ for `M` with `I` empty*: the `hM` hypothesis is vacuous and `Module.Free` of the zero module holds. · **P** Mathlib/L0/NP.
· **LOC** 90 + 90.

### T033 (L33) Lemma 10.3 · **Q** [Sch] l. 3007–3028 (quoted in the ticket). · **M** finite case via `finrank`, infinite case via
`countable_support` and cardinal arithmetic. · **A** (1) *`#(⋃ Y_x) ≤ #I · ℵ₀`*: `Cardinal.mk_iUnion_le_sum_mk` then
`sum_le_iSup`/bound by `ℵ₀` — verified names; (2) *`I`, `J` in different universes*: not supported by `Cardinal.mk`
without `lift`; stated in one universe; (3) *the finite case needs `K` complete?* finite-dimensional subspaces are closed
over a complete field, but here only linear algebra is used. · **P** Mathlib. · **LOC** 100.

### T034–T036 (M3) Schneider 10.4 · **Q** [Sch] l. 3029–3101 (full proof, quoted in the tickets). · **M** `exists_add_mem_forall_mul_norm_le`
is the distance step, `norm_smul_add_ge_mul_max` the two-term inequality, `exists_isTOrthogonalFamily_nat` properties
(a)–(d), `exists_continuousLinearEquiv_nat` the conclusion. · **A** (1) *Schneider assumes `dim Vₙ = n`*: a countable set
with dense span need not be linearly independent — extract a LI subfamily with `exists_linearIndependent` (verified) and
enumerate it (`Denumerable` from countable + infinite, verified); (2) *is the recursion well-founded?* `Vₙ` depends on `u`
only, so no recursion on `v` is needed — a simplification over the prose; (3) *scaling in a non-discretely-valued `K`*:
`existsUnique_zpow_norm_smul_mem_Ioc_one` gives norms in `(‖ϖ‖, 1]`, which is all (d) needs; (4) *closed range*:
`AntilipschitzWith.isClosed_range` (verified) replaces "complete hence closed"; (5) *the finite-dimensional case*:
Mathlib's `ofFinrankEq`. · **P** Mathlib/L0/L1. · **LOC** 60 + 250 + 110.

### T037 (L37) Prop 10.5 · **Q** [Sch] l. 3120–3137 (quoted). · **M** the lift of the identity of `V ⧸ U` is Schneider's
`f ∘ g`; closed subspaces of countable type via complementation (E25). · **A** (1) *Schneider's (b) needs `V/U` infinite
dimensional for 10.4*: our `isPotentiallyONable` covers the finite-dimensional case; (2) *quotient instances*: Mathlib's
quotient norm needs `IsClosed ↑U` as an instance — carried as `[IsClosed (U : Set V)]`; ultrametricity of the quotient is
Layer 0's instance (verified); (3) *`U ≃L V ⧸ ker P`*: Layer 1's `quotKerEquivRangeL` needs the range closed — `range P = ⊤`.
· **P** Mathlib/L0/L1. · **LOC** 110.

### T038–T042 (L38–L42) matrices · **Q** [Buz07] l. 272–303 (quoted), [Bel] l. 2029–2034, [JN] l. 655–660, [RM] §2.6.2.
· **M** convention 7 orientation (`matrixCoeff u i j = u(single j 1) i`); Buzzard's `a_{i,j}` is our `a j i`. · **A**
(1) *order of multiplication over a noncommutative ring*: `(f j • u(single j 1)) i = f j * a i j` — the roadmap's
`a i j * f j` needs commutativity — **matrix products stated over `NormedCommRing` (E27)**; (2) *`opNorm_eq_iSup_matrixCoeff`
without completeness*: the sum `∑' a i j f j` is given by `HasSum` (no summability-from-null needed) — `CompleteSpace R`
dropped from that statement; (3) *dense range of `diag(d)` for non-zero-divisors*: FALSE (`diag(p)` on `C₀(ℕ, ℤ_p)`) —
**rejected; units required (E22)**; (4) *`norm_diagonal` for `I` empty*: `⨆` over empty is `0 = ‖0‖` — fine; (5) *base change
needs `φ` continuous for `baseChange_map`*: from the bound. · **P** Mathlib/L0/L1. · **LOC** 40 + 90 + 40 + 130 + 70.

### T043–T045 (L43–L45) dual · **Q** [Sch] l. 617–700 ("`c₀(X)' = ℓ^∞(X)`"); [RM] §2.5. · **M** `dualEquivLp` is R1's bijection
restricted to `M = R`; `toBidual` the evaluation. · **A** (1) *`lp` over a normed ring*: `Module 𝕜 (lp E p)` and
`IsBoundedSMul` exist for `[NormedRing 𝕜]` (verified by `#synth`); (2) *the operator-norm instance on `lp … →L[R] R`*: Layer 1's
scoped `NormedAddCommGroup` needs `[IsTate R]` — **the skeleton's first `toBidual` failed to elaborate without it; fixed
by explicit binders**; (3) *`‖lp.single ∞ i 1‖ = 1`*: `lp.norm_eq_ciSup` + `single_apply` + `NormOneClass`; (4) *continuity of
the pairing*: bilinear with the bound, ε-δ. · **P** Mathlib/L1. · **LOC** 90 + 110 + 60.

### T046–T047 (M4) Bellaïche II.1.8 and Buzzard 2.3 · **Q** [Bel] l. 2043–2056 (quoted); [Buz07] l. 335–369 (quoted); [Lud] l. 371–395.
· **M** `exists_truncation_near` is II.1.8 with Layer 1's OMT corollary `exists_forall_exists_eq_sum_smul_norm_le`; Buzzard
2.3(a) is `exists_truncation_injOn`, (b) is `isClosed_of_fg`. · **A** (1) *II.1.8 without closedness*: FALSE — the
counterexample T055 (`P = R·(pⁿδₙ)` in `C₀(ℕ, ℓ^∞)`), consistent with the roadmap's warning; (2) *Buzzard's (b) cites BGR
3.7.3/1 (submodules of `A^S` closed)*: Layer 1's M2 `Submodule.isClosed_of_isNoetherianRing` — verified statement
(`[IsNoetherianRing R] [Module.Finite R M]`); (3) *continuity of the inverse*: Buzzard's Lemma 2.2 = Layer 1's
`continuous_of_finite` (needs the source complete and ultrametric: `Q` closed in `C₀`, fine); (4) *is `P` complete ⟹ closed*:
`completeSpace_coe_iff_isComplete` + `IsComplete.isClosed`. · **P** L1. · **LOC** 70 + 150.

### T048–T051 (M5) unitriangular · **Q** [RM] §2.7 (quoted in the tickets); [L1] OpenMapping l. 136–180 (the iteration). · **M**
`toCLM = ofMatrix a`; `norm_toCLM_apply` = largest index; `exists_forall_tsum_eq_of_finite` = backward substitution;
`surjective_toCLM` = iteration. · **A** (1) *is `T` surjective with factor `q` when `q = 0`?* the truncation error cannot be
made `0` for infinitely supported `g`, so the contraction factor is `max q ½` — **rejected the literal `q`; the statement
uses `max q 2⁻¹`**; (2) *backward substitution on an infinite system is not well-founded*: solved on finitely supported
targets only (finite columns make each row a finite sum) — this is why the one-step lemma truncates `g`; (3) *the largest
index exists*: `{j | ‖f j‖ = ‖f‖}` is finite and nonempty for `f ≠ 0`; (4) *the family criterion needs coordinate
functionals?* no: the expansions `hf` are hypotheses. · **P** L0 `norm_tsum_eq_of_forall_lt` verified. · **LOC** 70 + 80 + 170 + 50.

### T052–T055 examples · **Q** [RM] Layer 2 Examples and §2.3.5, §2.6.4. · **M** per example. · **A** (1) *`C(ℤ_p, ℚ_p)` norm
values in `‖ℚ_p‖`*: sup attained on a compact — fine (instances verified: ultrametric `C(ℤ_[p], ℚ_[p])`, `CompactSpace ℤ_[p]`);
(2) *the `ℂ_p` value group*: not in Mathlib — **hypothesis (E23)**; the `ℚ_p` version is proved; (3) *the `ℚ_p` dual
example*: Mathlib's and the scoped instance differ as terms — **stated as `Nonempty` for Mathlib's instance (E28)**;
(4) *`ℓ^∞(ℕ, ℚ_p)` Tate*: constant `p` is a multiplicative unit (`lp.norm_const_smul` over the division ring `ℚ_p`);
(5) *the non-closed `P`*: `g = (p^{⌈n/2⌉}δₙ)` is in the closure (truncations are `rₖ • v`) and not in `P` (the would-be
coefficient `p^{⌈n/2⌉−n}` is unbounded) — checked by hand. · **P** Mathlib/L1. · **LOC** 60 + 110 + 70 + 150.

### T056 integration · tooling only.

## Step 4 — provability summary

| Discharge | Count |
|---|---|
| Leaves discharged by Mathlib lemmas (names verified) | 71 |
| Leaves discharged by Layer 0/1/NP code (names verified) | 33 |
| Leaves needing a project proof of 50–250 lines (listed above) | 17 |
| API gaps requiring new infrastructure | 0 |
| Leaves rejected during the pass (fixed in the skeleton or recorded as errata) | 7 (E19, E21, E22, `map` bound, `toBidual` instances, lifting universes, `max q ½`) |
| Leaves taken off the board | 1 (E24: §2.4.2's discretely valued orthogonal basis — no source text) |

## Step 5 — confidence gate

1. Every leaf has a verbatim quote or is a definitional/transport step whose content is the quoted definition — ✓.
2. Every Mathlib name in a sketch was elaborated against the pinned Mathlib or is marked with a fallback — ✓.
3. No leaf requires infrastructure absent from Mathlib beyond the project's own layers — ✓ (the longest leaves are
   the successive approximation, the `t`-orthogonal sequence, Buzzard 2.3(b) and the backward substitution, each a
   transcription of its source).
4. Every false-as-stated roadmap claim found was rejected and recorded (E19, E21, E22) — ✓.
5. The skeleton builds with `sorry` only — ✓ (2 688 jobs).
6. The shared-file change (T001) is isolated, first, and its three downstream proof repairs are identified by line — ✓.
7. The one unsourced clause (§2.4.2, discrete case) is off the board, not ticketed — ✓.

Feasibility: the decomposition is a transcription of Schneider §10, Bellaïche §II.1, Buzzard §2 and Colmez 1.1, with
every analytic input (OMT, ultrametric sums, scaling, residue rings, rescaled norms) already in Layers 0–1. Expected
execution: 56 proof tickets, the five long ones splitting into sub-tickets.
