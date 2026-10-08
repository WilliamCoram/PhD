
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
