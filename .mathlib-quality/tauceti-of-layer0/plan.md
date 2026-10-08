# Development Plan: overconvergent automorphic forms, Layer 0 (the adelic setting)

Board: `.mathlib-quality/tauceti-of-layer0/` (named; other boards, including the parallel
`tauceti-pfa-layer0/` and `tauceti-co-layer0/`, belong to other runs). Specification:
`PhD/TauCeti/Roadmaps/OverconvergentForms/README.md`, Layer 0 (§0.1–§0.5) and its Examples. Code:
`PhD/TauCeti/Code/OverconvergentForms/`, module prefix `PhD.TauCeti.Code.OverconvergentForms`, never
importing `PhD.Main.*` (CI-gated). The chain root `PhD/TauCeti.lean` is **not** touched until the
last ticket, so that the chain stays sorry-free while the board is worked.

## Goal

The adelic group of a definite quaternion algebra, its compact open levels, class sets and Hecke
pairs, and the complete running example `ℍ[ℚ]`, `p = 3`, `U₁(9)`:

```lean
-- the adelic group (Adelic/Basic.lean), for any F-algebra D over a number field F
abbrev Df : Type _ := D ⊗[F] FiniteAdeleRing (𝓞 F) F        -- 𝔸_F^f-module topology (scoped)
abbrev Dfx : Type _ := (Df F D)ˣ
def unitsIncl : Dˣ →* Dfx F D
instance : LocallyCompactSpace (Dfx F D)                       -- and totally disconnected

-- components and rigidifications (Adelic/Components.lean)
class RigidificationAt : Type _ where
  equiv : D ⊗[F] v.adicCompletion F ≃ₐ[v.adicCompletion F] Matrix (Fin 2) (Fin 2) (v.adicCompletion F)
def toGL : Dfx F D →* GL (Fin 2) (v.adicCompletion F)          -- θ_v
def unitAt : GL (Fin 2) (v.adicCompletion F) →* Dfx F D        -- ι_v, with θ_v ∘ ι_v = id

-- levels, class sets, Fujisaki's conclusion as a property of (F, D)
def U0 (b : Basis ι F D) (hb : IsOrderBasis b) : Subgroup (Dfx F D)     -- compact open
def U0Level, U1Level                                                       -- U₀(𝔫), U₁(𝔫)
abbrev classSet (U) := DoubleCoset.Quotient (globalUnits F D) U
class HasFiniteClassSets : Prop                                            -- discharged for ℍ[ℚ]

-- the norm class (Adelic/Norm.lean), for D = ℍ[F,a,b]
def normClass : Dfx F ℍ[F,a,b] →* ℝ                                       -- |nrd(g)|_f
theorem normClass_unitsIncl : normClass (unitsIncl x) = |N_{F/ℚ}(nrd x)|⁻¹

-- the local structure and the Hecke pair (Level/Local.lean, Level/HeckePair.lean)
theorem LocalLevel.bijOn_etaRep      -- U η U = ∐_α U ((ϖ 0), (αϖ^t 1)) for Iw₁₁ ≤ U ≤ Iw
theorem bijOn_etaAdelicRep           -- the same in D_f^×
theorem isHeckeTriple_wildMonoidOf   -- (Δ_t, U) is a Hecke triple

-- the running example (Hamilton/)
theorem Hamilton.exists_factor       : ∀ g, ∃ d ∈ D^×, ∃ u ∈ U₀(1), g = d * u   -- no Jacquet–Langlands
theorem Hamilton.isSection_classRep  : IsSection classRep U1_9                  -- three classes
theorem Hamilton.stabilizer_classRep : stabilizer (classRep i) U1_9 = ⊥
theorem Hamilton.bijOn_etaRep3       -- U₁(9) η₃ U₁(9) is three right cosets
theorem Hamilton.factorisation       : classRep i * (etaRep3 t)⁻¹ = d(i,t) * classRep (σ i t) * u(i,t)
```

## References

| Tag | Reference | Used for |
|---|---|---|
| [RM] | `PhD/TauCeti/Roadmaps/OverconvergentForms/README.md`, Layer 0 | the specification; every leaf is a numbered clause there |
| [Buz07] | K. Buzzard, *Eigenvarieties*, §9 (pp. 67–70) and the proof of Lemma 12.1; text in `references/buzzard.txt` (lines 2620–2760, 3216–3235) | `D_f`, `M_t`, wild level, `Γ_λ`, `U₀(𝔫)`/`U₁(𝔫)`, `[UηU]`, the coset decomposition |
| [Jac03] | D. Jacobs, *Slopes of compact Hecke operators* (thesis), §1.4, Definition 1.20, Proposition 1.21, Lemma 1.22, Theorem 2.1, Lemmas 2.2–2.5, §B.1; text in `references/jacobs_thesis.txt` (font-damaged: `ν`, `ξ`, `×` are dropped by the extraction) | the running example |
| [Voi21] | J. Voight, *Quaternion Algebras*, GTM 288: 3.2.9, Lemma 11.1.2, §11.2, Lemma 11.3.2, Proposition 11.3.4, Lemma 27.6.8, 27.6.6–27.6.12; text in `references/voight.txt` (pdf pages marked) | standard involution and reduced norm, the Hurwitz order, the idelic dictionary, the idelic norm |
| [Loe11] | D. Loeffler, *Overconvergent algebraic automorphic forms*, §3.1, Propositions 3.1.1–3.1.4; `references/loeffler.txt` lines 735–760 | finiteness of double quotients, discreteness, the stabilisers |
| [Mathlib] | `RingTheory/DedekindDomain/FiniteAdeleRing`, `Topology/Algebra/RestrictedProduct/*`, `Topology/Algebra/Module/ModuleTopology`, `Topology/Algebra/Valued/LocallyCompact`, `NumberTheory/NumberField/{Completion/FinitePlace,ProductFormula}`, `Algebra/Quaternion`, `NumberTheory/HeckeRing/Defs`, `GroupTheory/DoubleCoset`, `GroupTheory/Commensurable` | library inputs, every name checked by elaboration of the skeleton |
| [SRC] | `PhD/Main/QMF/{03_Quaternionic,04_Level,04_UpiElement,04_Finiteness}.lean`, `PhD/Main/JacobsSlash/U3/{1_Hurwitz,1_Setting,2_Level,2_LevelTopology,3_ClassSet,3_EtaDecomposition,5_Factorisations}.lean`, `PhD/Main/JacobsSlash/CN1/*.lean`, `PhD/Main/LWX/23_QuaternionData.lean` at commit `7586051` | **read-only reference for proof ideas**; sorry-free there. Never imported, never mirrored: its topology rests on 92 vendored FLT files by other authors, which this chain cannot use |
| [FLT] | the FLT project, `NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset` (K. Buzzard et al.) | the owner of Fujisaki's lemma; **not used**, see decision 2 |

## Mathlib inventory

| Concept | Mathlib status at the pin | Our action |
|---|---|---|
| Finite adele ring | `IsDedekindDomain.FiniteAdeleRing`, ring, topology, `Algebra K`, `isUnit_iff`, `Fact` that `𝒪_v` is open | USE |
| Compactness of `𝒪_v`, the subring `∏ 𝒪_v`, local compactness / T2 / total disconnectedness of `𝔸_F^f` | **absent** (FLT has them); criterion `compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField`, `RestrictedProduct.locallyCompactSpace_of_group`, `isOpenEmbedding_structureMap` present | PROVE in `Adelic/FiniteAdeles.lean` (seam with the global-number-fields roadmap) |
| `R`-algebra structure on `D ⊗[F] R` | `Algebra.TensorProduct.rightAlgebra`, a non-instance; `right_isScalarTower`, `SMulCommClass` follow once it is on | SCOPE it (`AdelicAlgebra.RightAlgebra`); PROVE finiteness, freeness, basis by transport along `TensorProduct.comm` |
| Module topology | `moduleTopology`, `IsModuleTopology`, `IsModuleTopology.isTopologicalRing`, `continuous_of_linearMap`, `continuous_of_linearMapₛₗ`, `instPi` | USE |
| Units topology | `Units.isClosedEmbedding_embedProduct`, `Units.continuous_val`, `Units.continuous_coe_inv` | USE |
| Quaternion algebras | `ℍ[R,c₁,c₂,c₃]`, `star`, `basisOneIJK`, `QuaternionAlgebra.Basis`, `Quaternion.normSq` (Hamilton only) | USE; DEFINE `nrd`, `trd` on `ℍ[R,a,b]` |
| Reduced norm of a central simple algebra, orders, Hurwitz order, definiteness | **absent** | DEFINE what Layer 0 consumes (decision 3) |
| Norm on `F_v`, product formula | `instNormedFieldValuedAdicCompletion`, `FinitePlace.prod_eq_inv_abs_norm`, `equivHeightOneSpectrum` | USE for `ideleNorm_algebraMap` |
| Double cosets, Hecke triples | `DoubleCoset.Quotient`, `DoubleCoset.eq`, `Subgroup.Commensurable`, `commensurator`, `IsHeckeTriple.of_diagonal`, `HeckeCoset.mk`, `HeckeCosetModule.of` | USE |
| `ℚ_p` as an adic completion | `Rat.HeightOneSpectrum.primesEquiv`, `adicCompletion.padicEquiv`, `adicCompletionIntegers.padicIntEquiv`, Hensel's lemma for `ℤ_[p]` | USE in `Hamilton/Setting.lean` |
| Fujisaki's lemma, Haar characters of rings | **absent** | NOT PROVED HERE (decision 2) |

## File structure (as for a Tau Ceti PR; Tau Ceti home noted in each module docstring)

| File | Roadmap | Contents |
|---|---|---|
| `Quaternion/ReducedNorm.lean` | §0.1.1 | `trd`, `nrd` on `ℍ[R,a,b]`, quadratic relation, units, independence of the splitting, `mapRingHom` |
| `Quaternion/Definite.lean` | §0.1.2 | `IsTotallyDefinite`, positivity, division ring, integrality in orders, Hamilton |
| `Quaternion/BaseChange.lean` | §0.1.1, §0.2.4 | `ℍ[F,a,b] ⊗[F] R ≃ₐ[R] ℍ[R,a,b]`, `nrdBaseChange`, naturality, `det = nrd` for a split base change |
| `Quaternion/Hurwitz.lean` | §0.1.4 | the Hurwitz order, 24 units, Euclidean division, principal right ideals, maximality |
| `Adelic/RightBaseChange.lean` | §0.2.1 | the scope `RightAlgebra`, `rightBasis`, `rightCoordsL`, `continuous_map_id` |
| `Adelic/FiniteAdeles.lean` | §0.2.1, §0.2.3 | `𝒪_v` compact, `integralAdeles`, `𝔸_F^f` locally compact, T2, totally disconnected |
| `Adelic/Basic.lean` | §0.2.1 | `Df`, `Dfx`, `unitsIncl`, injectivity, the topology of `D_f` and `D_f^×` |
| `Adelic/Components.lean` | §0.1.3, §0.2.2 | `toLocal`, `RigidificationAt`, `toGL`, `extendZero`, `localIncl`, `unitAt`, commutation |
| `Adelic/IntegralAdeles.lean` | §0.1.4, §0.2.3 | `IsOrderBasis`, `orderOf`, `adelicOrder`, `localOrder`, `localUnits`, `U0`, integral rigidifications |
| `Adelic/Norm.lean` | §0.2.4 | `ideleNorm`, product formula, `adelicNrd`, `normClass` |
| `Level/Local.lean` | §0.4.1–2 | `monoidM`, `iwahori`, `iwahoriOne`, `iwahoriPrincipal`, residues, `η`, the two coset decompositions, the norm form |
| `Level/Standard.lean` | §0.3.1 | `levelAt`, `standardLevel`, `U0Level`, `U1Level`, normality and the quotient |
| `Level/ClassSet.lean` | §0.2.1, §0.3.1–3 | commensurability, `classSet`, `HasFiniteClassSets`, sections, stabilisers, discreteness for `F = ℚ` |
| `Level/HeckePair.lean` | §0.3.4, §0.4.3–5 | double cosets, `IsHeckeTriple`, `etaAdelic`, `wildMonoid(Of)`, the adelic decomposition, diamonds, `heckeElement` |
| `Hamilton/Splitting.lean` | §0.1.2–3 | `splitHom`, `splitEquiv`, solvability of `ν² + ξ² = −1` in `ℤ_q`, ramification at `2` |
| `Hamilton/Setting.lean` | §0.1.3, §0.5 | `padicPlace`, `v₃`, `K₃`, `ν₃`, `theta3`, `rigidificationOfOdd` |
| `Hamilton/Level.lean` | §0.5 | `hurwitzBasis`, `U0`, `theta3_isIntegral`, `U1_9` |
| `Hamilton/ClassNumberOne.lean` | §0.3.5, §0.5.1 | the denominator ideal, `exists_factor`, `hasFiniteClassSets` |
| `Hamilton/ClassSet.lean` | §0.5.2–3 | `classRep`, reduction mod 9, three orbits, trivial stabilisers |
| `Hamilton/EtaDecomposition.lean` | §0.5.4 | `eta3`, `etaRep3`, `bijOn_etaRep3` |
| `Hamilton/Factorisations.lean` | §0.5.5 | `sigmaTable`, `dTable`, `uCand_mem`, `factorisation` |
| `Examples.lean` | Examples | the roadmap's examples as `example`s |

Import graph: `ReducedNorm ← Definite ← Hurwitz`; `RightBaseChange ← {BaseChange, Basic}`;
`FiniteAdeles ← Basic ← Components ← IntegralAdeles ← {Norm, Standard, ClassSet}`;
`Local ← Standard ← HeckePair → ClassSet`; `Splitting ← Setting ← Level ← ClassNumberOne ← ClassSet
(Hamilton) ← EtaDecomposition ← Factorisations ← Examples`.

## Dependency graph (by ticket group)

```text
G1 Quaternion (§0.1) ─────────────────────────────┐
G2 RightBaseChange + FiniteAdeles ──→ G3 Adelic group (§0.2.1–3) ──→ G4 Norm (§0.2.4)  [needs G1 BaseChange]
G5 Local level (§0.4.1–2)  [Mathlib only] ──┐
G3 ──→ G6 Standard levels (§0.3.1) ←────────┘
G3 ──→ G7 Class sets (§0.3.2–3)   [Definite part needs G1]
G6, G7 ──→ G8 Hecke pair (§0.3.4, §0.4.3–5)          ── CLEANUP-ALL-1 ── M1 (general theory)
G1, G3 ──→ G9 Hamilton setting + level ──→ G10 class number one ──→ G11 class set of U₁(9)
G8, G11 ──→ G12 η-decomposition + nine factorisations + Examples ── CLEANUP-ALL-2 ── M2 ── CLEANUP-FINAL
```

G1, G2 and G5 are independent of one another and can be worked in any order.

## Generality and design decisions (binding for the tickets)

1. **`D_f = D ⊗[F] 𝔸_F^f`, coefficients on the right** ([RM] §0.2.1, [Buz07, p. 68], [FLT]). Mathlib's
   base-change API is left-handed and `Algebra.TensorProduct.rightAlgebra` is deliberately not a global
   instance. The scope `AdelicAlgebra.RightAlgebra` turns it on (`attribute [scoped instance]`) and
   adds `Module.Finite`, `Module.Free`, the module topology, `IsModuleTopology` and
   `IsTopologicalRing`; every file of `Adelic/`, `Level/` and `Hamilton/` opens it. The instances are
   written afresh from Mathlib; nothing is copied from FLT's `RightActionInstances`. **Flagged for
   the user**: the alternative `𝔸_F^f ⊗[F] D` needs no scoped instances at all, at the price of
   departing from the roadmap, the literature and FLT's statement of Fujisaki's lemma. The skeleton
   compiles with the right-handed choice, so this plan keeps it.
2. **Fujisaki's lemma is a hypothesis, named `HasFiniteClassSets F D`.** Its proof in the source
   development is FLT's (Haar characters of `D ⊗ 𝔸`), by other authors and outside Mathlib at the pin;
   the chain cannot import it. **Authorship, corrected 2026-09-21**: the user is a co-author of the top
   file (`DivisionAlgebra/Finiteness.lean`, Buzzard–Coram, 1128 lines) and of `GroupTheory/DoubleCoset`
   and `Topology/HomToDiscrete`, about 1,660 lines; the remaining 88 files and 13,950 lines of its
   import cone (the full adele ring with `K` discrete and cocompact, base change of completions and
   adeles, `ringHaarChar` and the Haar characters of `𝔸_K`, `ℝ`, `ℂ`, `ℚ_p`) are by some twenty other
   authors, and none of `ringHaarChar`, discreteness or cocompactness of `K ⊂ 𝔸_K` is in the pinned
   Mathlib. Bringing Fujisaki in is therefore a development of its own (see "Fujisaki options"). Layer 0 therefore states
   the *conclusion* as a `Prop`-class, proves the transfer lemmas that make it a property of one
   compact open level (`hasFiniteClassSets_of_finite`), and **discharges it for `ℍ[ℚ]`** from class
   number one (`Hamilton.hasFiniteClassSets`). Every later layer takes `[HasFiniteClassSets F D]`.
   When Fujisaki's lemma reaches Mathlib or Tau Ceti, one instance closes the gap. **Flagged for the
   user.**
3. **The reduced norm lives on Mathlib's `ℍ[R,a,b]`** ([RM] §0.1.1: "state the theory for `ℍ[F, a, b]`
   first"). `nrd x = re² − a·imI² − b·imJ² + ab·imK²` is a `→*₀`, `trd` a linear map, and the
   splitting-independence theorem `det (φ x) = nrd x` holds for **every** algebra homomorphism into
   `M₂(S)` with `2, a, b` invertible in `S` — an elementary Cayley–Hamilton argument, no
   Skolem–Noether. The adelic reduced norm and the norm class are for `D = ℍ[F,a,b]`, through
   `baseChangeEquiv`. The rest of the adelic theory (§0.2.1–3, §0.3, §0.4) is for an arbitrary
   `F`-algebra `D`, as in [SRC]. An abstract quaternion algebra is reached by transport along a
   presentation `ℍ[F,a,b] ≃ₐ[F] D`; no such transport is ticketed here.
4. **`RigidificationAt` is an `F_v`-algebra isomorphism** ([RM] §0.1.3), not [SRC]'s `F`-algebra
   isomorphism with an `IsCompletionLinear` mixin. With the scoped right algebra the correct notion
   is statable, continuity is `IsModuleTopology.continuous_of_linearMap`, and
   `toMatrix_unitsIncl_algebraMap` is `F_v`-linearity. `RigidificationAt.moduleFinite` derives
   `Module.Finite F D`, so the continuity statements carry no finiteness hypothesis.
5. **Orders are presented by a basis** (`IsOrderBasis b`: the coordinates of `1` and the structure
   constants are in `𝓞 F`). `orderOf`, `adelicOrder`, `localOrder`, `localUnits` are defined by
   integrality of coordinates, so compactness and openness are statements about `(∏ 𝒪_v)^ι` under the
   coordinate homeomorphism, and membership is local by construction. This covers every order when
   `F = ℚ` and every `𝓞 F`-free order in general; a non-free maximal order (class number of `F`
   greater than one) would replace the basis by a generating family, with the same proofs of
   compactness and openness.
6. **Levels are `U₀(1)` cut down at finitely many places** (`standardLevel b hb w H`, `w : κ → places`
   with an instance family `[∀ k, RigidificationAt F D (w k)]`, thresholds `levelThreshold t ∈ ℤᵐ⁰`).
   The quotient `U₀(𝔫)/U₁(𝔫)` is stated in the local form `∏_k (𝒪_{w k}/𝔞)^×`; the identification with
   `(𝒪_F/𝔫)^×` is the global-number-fields roadmap's CRT and is not needed by any later clause.
7. **The local theory is over any `[Valued K Γ₀]` with a threshold `γ : Γ₀`**, in Buzzard's
   right-action normalisation (`v(d) = 1`, `v(c) ≤ γ`), which is [SRC]'s `Sigma0'` of the slash fork,
   not the left-handed `Sigma0`. The norm form of [RM] §0.4.1 is `mem_monoidM_iff_norm`.
8. **The coset decomposition holds for `Iw₁₁(γ) ≤ U ≤ Iw(γ)`**, where `Iw₁₁` is the kernel of the
   diagonal residues. **Roadmap erratum, fixed in the README**: [RM] §0.4.2 asked for
   `Iw(𝔭^{t'}) ⊆ U ⊆ Iw(𝔭^t)`, which `U₁`-type subgroups do not satisfy and under which the
   representatives `((ϖ 0), (αϖ^t 1))` are wrong for `U = Iw(𝔭^{t'})`, `t' > t`. The proof is organised
   around `inv_mul_etaGL_mul_mem_iwahoriPrincipal`, which also transports the decomposition to
   `D_f^×` under the two hypotheses `θ_v(U) ⊆ Iw(γ)` and `ι_v(Iw₁₁(γ)) ⊆ U`.
9. **The number of right cosets `U x` in `U η U` is `[U : U ∩ η⁻¹ U η]`.** **Roadmap erratum, fixed**:
   [RM] §0.3.4 had `η U η⁻¹`. The two indices agree in a unimodular group, but only the corrected one
   has an elementary proof, and it needs no topology.
10. **The bijective forms carry `hr1 : ∀ i, v (r i) ≤ 1`.** The adversarial pass found that
    `bijOn_etaRep` is false without it: a residue system in the sense of `hr` may contain
    non-integral junk values, which never occur as the unique residue but do occur in the range.
11. **The seam with the global-number-fields roadmap is one file**, `Adelic/FiniteAdeles.lean`, with
    its Tau Ceti home in that tree. It is proved here because the chain must be self-contained.
12. **One conclusion per declaration.** Unit groups of local orders are the subgroup `localUnits`, so
    that "integral with integral inverse" is one membership; `baseChangeEquiv_map` is one equation of
    coordinate tuples; integrality of `trd` and `nrd` are two theorems.
13. **Citation erratum, fixed in the README**: Voight's 11.3.2 and 27.6.8 are Lemmas and 11.3.4 is a
    Proposition; maximality of the Hurwitz order is Lemma 11.1.2.

## Fujisaki options (decided 2026-09-21: **C now, A as future work**)

The user chose option C for this board. Option A is recorded as future work: the user may discuss a
Tau Ceti roadmap for Fujisaki's lemma with their supervisor and with Kevin Buzzard before any port is
planned. Do not start a `tauceti-fujisaki/` board unprompted.

- **A, recommended: a sibling board `tauceti-fujisaki/`.** Port the user's own three files into
  `PhD/TauCeti/Code/Fujisaki/`, with the inputs owned by others entering as one named seam (the adele
  ring locally compact with `K` discrete and cocompact; `ringHaarChar` with its product formula on
  `D_𝔸 = D_∞ × D_f` and its triviality on `D^×`). Its last ticket is the instance
  `HasFiniteClassSets F D` for every finite-dimensional division algebra. Layer 0 is unchanged and can
  start now.
- **B: the whole cone, 91 files.** Needs the agreement of every author or a Mathlib bump that
  contains their upstreamed versions; about five times the size of this board.
- **C: as planned.** The class only, discharged for `ℍ[ℚ]`.

## Scope boundary (clauses of Layer 0 that this board does not ticket)

- **Fujisaki's lemma itself** ([RM] §0.3.2): decision 2.
- **Finiteness of `Γ_λ / (Γ_λ ∩ F^×)` for general totally real `F`** ([RM] §0.3.3, last sentence):
  it needs Dirichlet's unit theorem and the finiteness of norm-one units of a totally definite order
  over `𝓞 F`. Proved here for `F = ℚ` (`finite_stabilizer`); Layer 2's §2.6 takes the general
  statement as a hypothesis on the level.
- **Existence and local conjugacy of maximal orders** ([RM] §0.1.4, first sentence; [Voi21, Ch. 10]):
  cited in the roadmap, consumed by nothing.
- **`D ⊗_{F,v} ℝ ≅ ℍ`** as the definition of definiteness: replaced by the equivalent positivity of
  the reduced norm at every real embedding (`isTotallyDefinite_iff_nrd_pos`).
- **The Jacquet–Langlands route to class number one** ([Jac03, Lemma 1.22]): not used, per [RM]
  convention 8 and the standing JL-audit rule.

## Validation

The `chatgpt-math` MCP server failed to connect in this session, so the optional second opinion of
Phase 1h was skipped. The adversarial pass of `decomposition.md` found four defects, all repaired
before ticketing (decisions 8, 9, 10 and the unnecessary finiteness hypotheses of decision 4).

## Milestones

- **M1 — the general theory of Layer 0 (2026-10-01).** `Quaternion/` (4 files), `Adelic/` (6),
  `Level/` (4) build sorry-free with 0 warnings; `runLinter` passes on every module. Declarations:
  482 (321 public, 161 private) in 14 files. `#print axioms` on `AdelicAlgebra.bijOn_etaAdelicRep`,
  `isHeckeTriple_wildMonoidOf`, `normClass_unitsIncl`, `hasFiniteClassSets_of_finite`,
  `finite_stabilizer`: `[propext, Classical.choice, Quot.sound]` only. The four `import Mathlib` roots
  were replaced by per-file Mathlib imports (CLEANUP-ALL-1): `lake shake` needs `module` files, so the
  imports were computed from the constants each file uses (instances excluded, then the four
  instance-only modules a build asked for added back: `RingTheory.TensorProduct.Finite`,
  `NumberField.Completion.FinitePlace`, `MetricSpace.Ultra.TotallySeparated`, `Data.Pi.Interval`).
- **M2 — Layer 0 complete (2026-10-01).** `import PhD.TauCeti.Code.OverconvergentForms.Examples` added
  to the chain root; `lake build PhD.TauCeti` succeeds (3454 jobs, no `sorry`, 0 warnings). All 22 files
  sorry-free with 705 declarations (482 general theory, 223 Hamilton) and 8 acceptance examples.
  `#print axioms` on `Hamilton.exists_factor`, `isSection_classRep`, `stabilizer_classRep`,
  `bijOn_etaRep3`, `factorisation` (and 49 further results): standard axioms only. No file imports
  `PhD.Main.*`.
