# Development Plan: rigid analytic geometry, Layer 1 (affinoid algebras)

Board: `.mathlib-quality/tauceti-rag-layer1/` (named; the default board path belongs to another
project — always pass this path to `/beastmode`, and never touch a sentinel that names another
board). Specification: `PhD/TauCeti/Roadmaps/RigidAnalyticGeometry/README.md`, Layer 1 (§1.1–§1.5)
and its Examples. Code: `PhD/TauCeti/Code/RigidAnalyticGeometry/`, module prefix
`PhD.TauCeti.Code.RigidAnalyticGeometry`, importing Mathlib and the Tau Ceti chain only — never
`PhD.Main.*` (CI-gated two-chain rule). Planned 2026-10-05, on top of the completed Layer 0 board
(`.mathlib-quality/tauceti-rag-layer0/`, 117/117 tickets, sorry-free).

## Goal

Everything BGR's §6.1 (with §3.7 behind it) says about affinoid algebras that Layers 2–8 consume:

```lean
-- §1.1.1  affinoid algebras (Affinoid/Basic.lean)
def IsAffinoidAlgebra (K A : Type*) [NormedField K] [IsUltrametricDist K] [CommRing A] [Algebra K A] :
    Prop := ∃ (n : ℕ) (α : TateAlgebra K n →ₐ[K] A), Function.Surjective α
-- the residue norm: Mathlib's quotient norm on `TateAlgebra K n ⧸ I`, a Banach `K`-algebra with
-- `IsUltrametricDist`, `NormOneClass` for `I ≠ ⊤`, values in `‖K‖` (NormedQuotient.lean, Basic.lean)
-- §1.1.3  the universal property of `A⟨X⟩` (Affinoid/Extend.lean)                 BGR 6.1.1/4
noncomputable def MvPowerSeries.Restricted.extendAlgHom (φ : A →ₐ[K] B) (hφ : Continuous φ)
    (b : σ → B) (hb : ∀ i, IsPowerBounded (b i)) : Restricted A (1 : σ → ℝ) →ₐ[K] B
theorem extendAlgHom_unique … (hψ : Continuous ψ) (hC : ∀ a, ψ (C 1 a) = φ a)
    (hX : ∀ i, ψ (X A 1 i) = b i) : ψ = extendAlgHom φ hφ b hb
-- §1.2.1  Noether normalisation (Affinoid/Noether.lean)                            MILESTONE M2
theorem IsAffinoidAlgebra.exists_finite_injective (hA : IsAffinoidAlgebra K A) [Nontrivial A] :
    ∃ (d : ℕ) (φ : TateAlgebra K d →ₐ[K] A), φ.toRingHom.Finite ∧ Function.Injective φ
theorem IsAffinoidAlgebra.ringKrullDim_eq_of_finite_injective … : ringKrullDim A = d
theorem IsAffinoidAlgebra.finiteDimensional_quotient_of_radical_isMaximal (hA) (𝔮 : Ideal A)
    (h : 𝔮.radical.IsMaximal) : FiniteDimensional K (A ⧸ 𝔮)
theorem IsAffinoidAlgebra.isJapaneseRing [CharZero K] [IsDomain A] (hA) : IsJapaneseRing A
-- §1.3  continuity (BanachAlgebra/Continuity.lean, Affinoid/Continuity.lean)        MILESTONE M3
theorem AlgHom.continuous_of_forall_isClosed_of_finiteDimensional (Φ : A →ₐ[K] B) (𝔅 : Set (Ideal B))
    (hB) (hA) (hfin : ∀ 𝔟 ∈ 𝔅, FiniteDimensional K (B ⧸ 𝔟)) (hinf : sInf 𝔅 = ⊥) : Continuous Φ
theorem AlgHom.continuous_of_isAffinoidAlgebra [IsNoetherianRing A] (hB : IsAffinoidAlgebra K B)
    (Φ : A →ₐ[K] B) : Continuous Φ
theorem AlgEquiv.continuous_symm_of_isAffinoidAlgebra (hA) (hB) (e : A ≃ₐ[K] B) : Continuous e.symm
theorem IsAffinoidAlgebra.exists_algEquiv_quotient_norm_comp_le (hA) (hB) (φ : B →ₐ[K] A) :
    ∃ n I (e : (Restricted B 1 ⧸ I) ≃ₐ[K] A), Continuous e ∧ Continuous e.symm ∧ ∀ b, ‖e.symm (φ b)‖ ≤ ‖b‖
-- §1.1.5  the affinoid tensor product (Affinoid/Tensor.lean)                       MILESTONE M4
abbrev Affinoid.TensorQuotient K A 𝔟₁ 𝔟₂ := Restricted A (1 : σ ⊕ τ → ℝ) ⧸ tensorIdeal K A 𝔟₁ 𝔟₂
theorem Affinoid.isAffinoidTensorProduct_tensorQuotient … : IsAffinoidTensorProduct … tensorInl tensorInr
-- §1.4  generalised rings of fractions (Affinoid/Fractions.lean)                   MILESTONE M5
abbrev Affinoid.GeneralisedFractions A f g := Restricted A 1 ⧸ fractionIdeal A f g   -- A⟨f, g⁻¹⟩
theorem Affinoid.isGeneralisedFractions_toFractions (hA) : IsGeneralisedFractions (toFractions K A f g) f g
abbrev Affinoid.RationalFractions A f g := Restricted A 1 ⧸ rationalIdeal A f g         -- A⟨f/g⟩
theorem Affinoid.isRationalFractions_toRational (hA) (hgen) : IsRationalFractions (toRational K A f g) f g
-- §1.1.6, §1.5  base change and polydiscs (Affinoid/BaseChange.lean, Affinoid/Polydisc.lean)
noncomputable def Affinoid.TateAlgebra.baseChangeEquiv : K' ⊗[K] TateAlgebra K n ≃ₐ[K'] TateAlgebra K' n
theorem IsAffinoidAlgebra.baseChange (hA : IsAffinoidAlgebra K A) : IsAffinoidAlgebra K' (K' ⊗[K] A)
theorem MvPowerSeries.Restricted.isAffinoidAlgebra_of_forall_exists_pow_eq_norm
    (h : ∀ i, ∃ (s : ℕ) (c : K), s ≠ 0 ∧ c ≠ 0 ∧ ρ i ^ s = ‖c‖) : IsAffinoidAlgebra K (Restricted K ρ)
```

together with: the sum and renaming isomorphisms of restricted power series and `Tₙ⟨Y_m⟩ ≅ T_{m+n}`
(§1.1.3); affinoid generating systems and BGR 6.1.1/5 (§1.1.3); the closedness of ideals in noetherian
Banach algebras (BGR 3.7.2, the nonarchimedean Nakayama lemma) and BGR 3.7.5/1–3 in general
(§1.3); the independence of the Banach topology, of power-boundedness and of topological nilpotence
from the residue norm (§1.3.3); the roadmap's worked examples.

**Milestone M1** is the restoration of Layer 0: the three floor files generalised in place
(`Restricted/Algebra.lean`, `TateAlgebra/Eval.lean`, `PadicFunctionalAnalysis/PowerBounded.lean`)
are sorry-free again, so that `lake build PhD.TauCeti` is sorry-free below this board.

**Not on this board** (decomposition, "Unticketed sub-trees"): BGR 6.1.1/6 and 6.1.3/4 (existence of
Banach topologies on finite extensions), 3.7.2/2 "only if" and 3.7.3, direct sums, the
seminorm-completion models of §1.4.2 and the isometry of the two models, §1.4.3–1.4.4 (the adic-spaces
chain is not in this repository), the "only if" of BGR 6.1.5/4 and 6.1.5/5 (Layer 2), characteristic
`p` Japaneseness.

## References

- **[BGR]** Bosch–Güntzer–Remmert, *Non-Archimedean Analysis*: §6.1.1–6.1.5 (pp. 221–236), §3.7
  (pp. 163–168), §1.2.4–1.2.5 (pp. 26–28), §7.2.5 (p. 287). Hand transcriptions from the scan:
  `references/bgr-6.1.1.md`, `bgr-6.1.2.md` (from Layer 0), `bgr-6.1.3-6.1.5.md`, `bgr-3.7.md`. PDF
  page = book page + 6 (ch. 6), + 8 (§3.7), + 4 (§7.2.5); renders in the scratchpad `bgr1/`.
- **[Bo]** Bosch, *Lectures on Formal and Rigid Geometry*, §1.4 (Definition 1, Propositions 2–4,
  Lemma 18, Proposition 19), §1.2/10–12, §1.8/7: `references/bosch-lectures.txt`.
- **[RM]** the roadmap README, Layer 1, and its conventions 1–3 (ground field, Tate algebra, affinoid
  algebras as a `Prop` without topology).
- **[L0]** the Layer 0 board: `plan.md`, `decomposition.md` (seam traps), the memory entry
  `tauceti-rag-layer0-board`.

## Mathlib inventory (pin bbc4475e, lean4 v4.33.0-rc1)

Present and used: `Ideal.Quotient.normedCommRing` (needs `[IsClosed (I : Set R)]` — `IsClosed` is a
class), `Ideal.Quotient.normedAlgebra`, `Ideal.Quotient.semiNormedCommRing`, `Submodule.Quotient.completeSpace`,
`QuotientAddGroup.norm_mk`, `norm_lt_iff`, `le_norm_iff`, `isQuotientMap_mk`, `isOpenMap_coe`;
`isUnit_one_sub_of_norm_lt_one`; `SemilinearMapClass.bound_of_continuous`;
`ContinuousLinearMap.exists_preimage_norm_le`, `LinearEquiv.continuous_symm`,
`LinearMap.continuous_of_seq_closed_graph`, `LinearMap.continuous_of_finiteDimensional`,
`FiniteDimensional.complete`; `Submodule.le_of_le_smul_of_le_jacobson_bot` (Nakayama), `Ideal.closure`,
`Ideal.mem_iInf_smul_pow_eq_bot_iff` (Krull), `Ideal.exists_ltSeries_of_hasGoingUp`,
`Algebra.HasGoingUp.of_isIntegral`, `Ideal.exists_ideal_over_prime_of_isIntegral`,
`ringKrullDim_eq_zero_of_isField`, `Algebra.IsIntegral.isField_iff_isField`,
`isField_of_isIntegral_of_isField'`, `Ideal.Quotient.maximal_of_isField`, `FiniteDimensional.of_injective`,
`Module.Finite.trans`, `Module.Finite.of_isLocalization`, `FractionRing.liftAlgebra` (local instance),
`isIntegral_trans`, `IsIntegral.tower_top`, `Module.Finite.of_restrictScalars_finite`;
`isNoetherianRing_of_surjective`, `isJacobsonRing_of_surjective`, `Ideal.quotientKerAlgEquivOfSurjective`,
`Ideal.Quotient.liftₐ`, `Ideal.Quotient.mkₐ`, `Ideal.quotientMapₐ`, `Ideal.Quotient.factor`,
`Ideal.radical_pow`; `Algebra.TensorProduct.lift`, `Algebra.TensorProduct.map_surjective`,
`Algebra.TensorProduct.tensorQuotientEquiv`, `Module.Basis.sum_repr`; `IsLocalization.Away.liftAlgHom`;
`NormedField.exists_norm_lt_one`, `exists_pow_lt_of_lt_one`, `exists_mem_Ico_zpow`,
`Summable.of_norm_bounded`, `Padic.norm_p_lt_one`. PFA: `isPowerBounded_of_norm_pow_le`,
`isPowerBounded_of_norm_le_one`, `openUnitBallIdeal_le_jacobson_bot`, `isUnit_of_norm_one_sub_lt_one`,
`unitClosedBall`, `openUnitBallIdeal`.

Absent (built here): the ultrametric quotient seminorm and `‖1̄‖ = 1` (G1); `A⟨X ⊕ Y⟩ ≅ A⟨Y⟩⟨X⟩`
(G2); evaluation along a bounded coefficient map (G0); power-boundedness in normed algebras (G0);
"ideals of a noetherian Banach algebra are closed" (G5); BGR 3.7.5/1–3 (G6); going-up for Krull
dimension (`ringKrullDim_le_of_isIntegral_of_injective`); the fraction field of a finite extension of
domains as a localisation (`IsFractionRing.isLocalization_algebraMapSubmonoid_of_isIntegral`); a linear
map into a finite-dimensional space with closed kernel is continuous.

Names that do not exist at the pin (recorded so nobody searches again): `RingEquiv.ofHomInv` (use
`RingEquiv.ofRingHom f g h₁ h₂`), `isUnit_of_mul_eq_one` (use `IsUnit.of_mul_eq_one`), `Basis` at the
root (it is `Module.Basis`), `IsLocalization.of_le` goes from a smaller to a larger submonoid (L7.16
needs the constructor), `Ideal.mem_iInf_smul_pow_eq_bot_iff` and `Module.Finite.of_isLocalization`
need their files imported (`Mathlib.RingTheory.Filtration`, `Mathlib.RingTheory.Localization.Finiteness`).

## Name check

Every Mathlib name in the tickets' "Mathlib lemmas needed" blocks is collected by
`scratch/extract_names.py` into `scratch/names_tickets_mathlib.lean` and elaborated against the pin
(0 errors, 0 deprecations at the time of planning); floor, chain and board names into
`scratch/names_tickets_chain.lean` (0 errors). The planning-time spot checks are in `scratch/t2.lean`.
The elaborated signatures of all 153 open declarations are in `scratch/signatures.txt`
(`scratch/fullnames.py`), used for the dropped-section-variable audit.

## File structure and dependency graph

```text
G0  Restricted/Algebra.lean, TateAlgebra/Eval.lean, PadicFunctionalAnalysis/PowerBounded.lean   (Layer 0 cone; M1)
G1  NormedQuotient.lean                        ← PFA UnitBall
G2  Restricted/Sum.lean                        ← Eval
G3  Affinoid/Basic.lean                        ← NormedQuotient, TateAlgebra/Rueckert, StrictlyClosed
G4  Affinoid/Extend.lean                       ← Basic, Sum, PowerBounded
G5  BanachAlgebra/Noetherian.lean              ← PFA UnitBall, Mathlib Banach + Nakayama
G6  BanachAlgebra/Continuity.lean              ← Noetherian
G7  Affinoid/Noether.lean                      ← Basic, TateAlgebra/Stable (Japanese)        [M2]
G8  Affinoid/Continuity.lean                   ← Extend, Noether, BanachAlgebra/Continuity    [M3]
G9  Affinoid/Tensor.lean                       ← Continuity                                   [M4]
G10 Affinoid/Fractions.lean                    ← Continuity                                   [M5]
G11 Affinoid/BaseChange.lean                   ← Basic
G12 Affinoid/Polydisc.lean                     ← Extend, Restricted/PowerSeries/Basic
G13 Affinoid/Examples.lean                     ← BaseChange, Fractions, Polydisc, Tensor, TateAlgebra/Examples
chain root PhD/TauCeti.lean                    ← Affinoid/Examples (one import line, the final gate)
```

Tau Ceti homes are recorded in each module docstring (`TauCeti/RingTheory/Affinoid/*`,
`TauCeti/Analysis/Normed/Algebra/*`, `TauCeti/Analysis/Normed/Group/Quotient/Ultra.lean`).

## API design and generality decisions

1. **`IsAffinoidAlgebra K A : Prop`** (root namespace, convention 3): a surjective `K`-algebra
   homomorphism from some `TateAlgebra K n`, no topology, zero algebra allowed. Theorems whose
   statement needs a norm take `[NormedCommRing A] [NormedAlgebra K A] [CompleteSpace A]` and are
   proved for every such norm (the continuity theorem makes them all equivalent).
2. **Banach algebra conventions.** `K` is `[NontriviallyNormedField K] [IsUltrametricDist K]
   [CompleteSpace K]` wherever Banach's theorem or power-boundedness enters (convention 1), and
   `[NormedField K]` only where Layer 0 suffices (`Basic`, `Noether`, `BaseChange`). Banach algebras
   are `[NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A] [CompleteSpace A]`, and
   `[NormOneClass A]` where the unit-ball subring is used (BGR's standing `|1| = 1`; G5–G6, and
   through them the continuity theorems of G8). Residue norms of nonzero affinoid algebras satisfy all
   of these (`Affinoid/Basic.lean`); the zero algebra is excluded from the continuity theorems only,
   and handled by `Subsingleton` arguments where it matters (L8.11).
3. **`eval₂` generalised in place** (D1 of the planning): bounded `φ` (`‖φ r‖ ≤ Cφ ‖r‖`) and bounded
   monomials (`‖x^t‖ ≤ Cx c^t`), constants `{Cφ Cx : ℝ}` implicit; `aeval` unchanged; the
   contractive form `norm_eval₂_le` is the case `1`. Call sites must pin `(Cφ := 1)` when the
   bound is a `by simp` term (Lean cannot infer the constant from a tactic block).
4. **`A⟨X⟩` is `Restricted A (1 : σ → ℝ)`** over any normed commutative `K`-algebra `A`
   (`IsUltrametricDist A`), a normed `K`-algebra by the general `Algebra K (Restricted S c)` instance
   (`Restricted/Algebra.lean`, generalised from the floor's `S = K` case; `Module K (Restricted R c)`
   is now the single general instance, so no diamond with the `R`-module structure).
5. **Universal properties as predicates** (`IsAffinoidTensorProduct`, `IsGeneralisedFractions`,
   `IsRationalFractions`): the pushout/fraction property among `K`-Banach algebras with continuous
   maps, with a universe parameter for the test algebra; the models by presentations satisfy them for
   every universe, uniqueness and associativity are theorems about the predicates, so nested
   constructions (`A⟨f, g⁻¹⟩⟨f', g'⁻¹⟩`) never need instances on a quotient.
6. **Residue (semi)norms on quotients**: the `abbrev`s `TensorQuotient`, `GeneralisedFractions`,
   `RationalFractions` are quotients of `Restricted A 1` and inherit Mathlib's seminormed instances;
   they are normed (and Banach) once the ideal is closed, which holds for affinoid `A`
   (`IsAffinoidAlgebra.restricted` + `isClosed_ideal`); statements needing the norm say `(hA :
   IsAffinoidAlgebra K A)` and supply the `IsClosed` instance by `haveI`.
7. **Two-norm statements** are made for an `A ≃ₐ[K] B` between two Banach algebras (3.7.5/3,
   6.1.3/2); contractive renorming (6.1.3/3) is an isomorphism onto a residue norm of a presentation
   over `B`.
8. **Noether normalisation** is stated for an arbitrary finite `β : Tₙ →ₐ[K] A` (BGR's (i)) by
   induction, with the chart hidden in `ψ : T_d →ₐ[K] Tₙ`; `Nontrivial A` as in BGR.
9. **Going-up** for the Krull dimension is a general lemma (`ringKrullDim_le_of_isIntegral_of_injective`),
   the companion of Layer 0's `ringKrullDim_le_of_isIntegral`.

## Seam notes (binding, in addition to Layer 0's)

- `Submodule.Quotient.completeSpace` does **not** fire for `Restricted R c ⧸ I` (its `[Ring R] [Module
  R M]` arguments are found along `instRingRestricted` while the ideal's module structure is spelled
  through the `NormedCommRing` instance); the shortcut `instCompleteSpaceQuotient` in
  `Affinoid/Basic.lean` records the quotient-group form. Expect the same for any instance with a
  separate `[Module R M]` argument on `Restricted`.
- `renameEquiv` is stated at the unit polyradius only; `c ∘ e.symm` is never produced.
- `Tₙ⟨Y_m⟩ ≅ T_{m+n}` is built from evaluations (no `finSumFinEquiv`, no `Fin.tail`).
- `extendAlgHom_unique` is a *ring*-level ext (`ringHom_ext_of_continuous`) with the constants
  hypothesis `hC`; `algHom_ext_of_continuous` applies only when the coefficient ring is `K`.
- `Restricted.map` (coefficientwise along a norm-nonincreasing map) is the floor's; `mapAlgHom` (along a
  bounded `K`-algebra map) is built from `extendAlgHom` and has `coeff_mapAlgHom`.
- The floor's `PowerSeries.IsRestricted` shadows Mathlib's: never import
  `Mathlib.RingTheory.PowerSeries.Restricted` in a file that imports `Restricted/PowerSeries/Basic.lean`
  (`Polydisc.lean` uses the floor's).
- `Basis` is `Module.Basis`; `padicNormE.norm_p_lt_one` is `Padic.norm_p_lt_one`.

## Deviations from the roadmap (recorded, not applied to the README)

- **V1 (§1.3.2)**: the proof is BGR 3.7.5/1–2 (closed graph theorem) rather than "along Bosch
  1.4/18", whose argument uses the supremum norm (Bosch 1.4, Theorem 16 and Proposition 6; Layer 2);
  Bosch's two inputs (finite-dimensional `B ⧸ 𝔪^ν`, `⋂ 𝔪^ν = 0`) are exactly the ones used.
- **V2 (§1.4.2)**: the seminorm-completion model and the isometry of the two models are not built;
  only the density of `A[g⁻¹] → A⟨f/g⟩` is proved. The completion needs the PFA roadmap's completion
  of seminormed algebras.
- **V3 (§1.4.3–1.4.4)**: not on the board (the adic-spaces chain is not in this repository).
- **V4 (§1.5.2)**: BGR 6.1.5/4's own finite monomorphism `Tₙ → T_{n,ρ}`, `Xᵢ ↦ cᵢ Xᵢ^{sᵢ}`, replaces
  the roadmap's rescaling through a Weierstrass domain of the unit polydisc; the "only if" and the
  supremum-norm statement (6.1.5/5) are deferred to Layer 2 as the roadmap's ⚠ remark anticipates.
- **V5 (§1.1.5)**: the universal property is proved for all `K`-Banach algebras with continuous maps
  (stronger than "in the category of affinoid algebras"); the completed tensor product with its norm
  is not built, as the roadmap's ⚠ says.
- **V6 (§1.2.5)**: Japaneseness of affinoid domains in characteristic zero only (Layer 0's `T_d`).
- **V7 (§1.1.6)**: `K' ⊗̂_K A := K' ⊗_K A` with `K'` on the left (BGR's `k′ ⊗̂_k Tₙ(k)`); no norm on
  the tensor product is defined (affinoidness is ring-theoretic).

## Roadmap errata (found while planning; the README is not edited)

- **E1 (§1.1.1)**: "`Ideal.Quotient.normedCommRing` for the closed ideal `ker α`" needs `IsClosed` as
  an *instance*; Layer 0's theorem is registered as one (`Affinoid.TateAlgebra.instIsClosed`), and
  completeness needs a shortcut instance (seam note).
- **E2 (§1.1.3)**: "`A⟨X⟩ ≅ (A ⊗̂_K T_m)`" is not provable without the completed tensor product; what is
  proved is `A⟨X⟩` affinoid (via `Tₙ⟨X⟩ ≅ T_{m+n}` and the surjection `Tₙ⟨X⟩ ↠ A⟨X⟩`), which is what
  the later layers use.
- **E3 (§1.2.4)**: "the preimage of a maximal ideal under a `K`-algebra map of affinoid algebras is
  maximal" needs only the *target* affinoid (`Ideal.isMaximal_comap_of_isAffinoidAlgebra`).
- **E4 (§1.3.1)**: `⋂ 𝔪^ν = 0` needs noetherianity only, not the Jacobson property (BGR's proof).
- **E5 (§1.3.2)**: see V1.
- **E6 (§1.5.2)**: the roadmap's hypothesis "`ρᵢ ∈ √|K^×|`" is "`ρᵢ^s ∈ |K^×|` for some `s ≥ 1`"
  (BGR's `|k_a^*|` characterisation, `bgr-6.1.3-6.1.5.md:196–197`); the example of the open disc holds
  for every `ρ > 0` (it is about `T_{1,ρ}`, not about `P_ρ(K)`).

## Build protocol

- Build with `lake build PhD.TauCeti.Code.RigidAnalyticGeometry.<Module>` (or the PFA module), never
  `lake build PhD`; the final gate is `lake build PhD.TauCeti` after the chain-root import. No
  `timeout` binary: use the tool timeout and check exit codes. One Lean process at a time.
- Lint with `lake exe runLinter PhD.TauCeti.Code.RigidAnalyticGeometry.<Module>`.
- `scratch/sorries.py` (open declarations → `sorries.json`), `scratch/fullnames.py` + `lake env lean
  scratch/signatures.lean` (elaborated signatures), `scratch/gen_tickets.py` (regenerates `tickets.md`
  from `tickets_data.py`; it would drop Status/Progress lines, so run it only before execution starts),
  `scratch/mark.py` (status updates during execution), `scratch/axioms.py` (`#print axioms`).
- Cleanup tickets are done inline by the main agent; sentinels: `cat` before `rm`, delete only one
  that names this board.
