# Decomposition — Quaternionic modular forms of general weight (QMF)

**BOARD PATH: `.mathlib-quality/qmf/`** — this project's tickets/plan/decomposition live
HERE, not at the default `.mathlib-quality/` path (that is the parallel NewtonPolygon
board; never touch it from QMF work).

## Skeleton location (all `lake build` clean, sorries only — verified 2026-08-03)
- `PhD/QMF/HeckeMonoid.lean` (139 lines) — submonoid Hecke operators
- `PhD/QMF/AutomorphicFunction.lean` (159) — abstract `L(U,A)`
- `PhD/QMF/Decomposition.lean` (79) — class-set decomposition
- `PhD/QMF/Sigma0.lean` (85) — local monoid `Σ₀(γ)`
- `PhD/QMF/WeightModule.lean` (124) — classical weight modules
- `PhD/QMF/Quaternionic.lean` (155) — global instantiation
Build: `lake build PhD.QMF.Quaternionic` (imports the whole chain).

## Sources
- [Buz07] Buzzard, *Eigenvarieties*, LMS Lecture Notes 320 (2007), §§9–11.  Text
  extracted verbatim this session from the author's PDF (pp. 67–74).
- [Loe11] Loeffler, *Overconvergent algebraic automorphic forms*, Proc. LMS 102 (2011),
  Def. 3.3.2 (left-handed convention, monoid action).
- [FLT] ImperialCollegeLondon/FLT at WilliamCoram/FLT branch `samsWork` (local clone
  `/Users/nkw24xru/Desktop/Lean/FLT`, lean v4.32.0-rc1) — weight-2 architecture
  (`WeightTwoAutomorphicForm`, `AbstractHeckeOperator`), Fujisaki finiteness
  (`FLT/DivisionAlgebra/Finiteness.lean`, Buzzard–**Coram**), DoubleCoset extensions
  (`FLT/Mathlib/GroupTheory/DoubleCoset.lean`, **Coram**–Buzzard–Yang).
- [PS] Pollack–Stevens `Σ₀(p)` convention for the left-handed monoid (unit `a`-entry).

## Handedness convention (project-wide, binding)
[Buz07] uses right `Mₜ`-modules (`f|u (g) = f(gu⁻¹).uₚ`, monoid `π^t ∣ c, π ∤ d`).
We use left actions throughout ([Loe11] Def 3.3.2 shape: `φ(gu) = uₚ⁻¹ ∘ φ(g)`), which is
mathlib/FLT-idiomatic.  Dictionary: the adjugate `g ↦ adj g` is an anti-isomorphism
`Mₜ → Σ₀` (Buzzard's monoid onto ours, `π^t ∣ c, π ∤ a`), carrying right `Mₜ`-modules to
left `Σ₀`-modules; determinants are preserved.  Verified by hand this session:
`adj (a b; c d) = (d −b; −c a)`, and `(1 0; 0 π) = adj (π 0; 0 1)` is our `Sigma0.eta`.
Similarly the transposed substitution `P ↦ P(aX+cY, bX+dY)` is a left action because
`subst_γᵀ ∘ subst_δᵀ = subst_(γδ)ᵀ`.

## Result R1: `L(U, A)` and its transformation law
Lean: `AutomorphicFunction` structure + `Δ`-action + `levelSubmodule`
(`AutomorphicFunction.lean`).

Source claim (verbatim, [Buz07] §9 p. 69):
> "Say t ∈ ℤ^J_{≥1}, U is a compact open of wild level ≥ πᵗ, and A is any right
> Mₜ-module, with action written (a,m) ↦ a.m.  If f : D×_f → A and u ∈ U then define
> f|u : D×_f → A by (f|u)(g) := f(gu⁻¹).uₚ.  Now set
> L(U,A) := { f : D×\D×_f → A : f|u = f for all u ∈ U }."

Lean ↔ source match: `AutomorphicFunction G Γ A` = functions `D×\D×_f → A` (left
`Γ`-invariance field); the `Δ`-action `(δ • φ)(g) = δ • φ(g·δ)` is the left-handed form
of `f|u`; `levelSubmodule R U hU` = the `U`-fixed points = `L(U,A)`; `hU : ↑U ⊆ Δ` is
exactly "wild level ≥ πᵗ" (p. 68: "U ⊂ D×_f has wild level ≥ πᵗ if the projection
U → D×_p is contained within Mₜ").

Leaves (all in skeleton, each = one sorry group):
- **L1.1** structure instances (Zero/Add/SMul/AddCommMonoid/Module) — boilerplate,
  discharged by pointwise `simp` (template: FLT `WeightTwoAutomorphicForm` §add_comm_group).
- **L1.2** `Δ`-action laws.  KEY CHECK (done by hand this session, recorded here):
  `((δ₁δ₂)•φ)(g) = (δ₁δ₂)•φ(g·δ₁δ₂) = δ₁•δ₂•φ((g·δ₁)·δ₂) = (δ₁•(δ₂•φ))(g)` — left action
  law holds because the coefficient action is a LEFT action; with a right coefficient
  action it would fail (that was Buzzard's right action).  Attacks: [edge] δ=1 ✓;
  [law-direction] verified as above; [drift] Loe11 Def 3.3.2 has identical shape ✓.
- **L1.3** `mem_levelSubmodule_iff`, `apply_mul_coe` — unfold + `u⁻¹ ∈ U ⊆ Δ`,
  `⟨u⁻¹,_⟩ * ⟨u,_⟩ = 1` in `Δ`.  Attacks: [hyp] needs U subgroup (u⁻¹ ∈ U), not just
  submonoid — correct, U is a `Subgroup` ✓; [edge] u = 1 ✓.

## Result R2: submonoid Hecke operator `[UgV]`
Lean: `AbstractHeckeOperator.{fixedPointsOfLE, mul_singleton_mul_subset,
out_mem_mul_singleton_mul, heckeOperator, heckeOperator_eq_finsetSum,
finite_image_doubleCoset_of_isCompact_of_isOpen}` (`HeckeMonoid.lean`).

Source claim (verbatim, [Buz07] §9 p. 69):
> "If η ∈ D×_f and ηₚ ∈ Mₜ then one can define an endomorphism [UηU] of L(U,A) as
> follows: decompose UηU = ∐ᵢ U xᵢ (a finite union) and define f|[UηU] := ∑ᵢ f|xᵢ."

Template proof: FLT `AbstractHeckeOperator` (verbatim copy at
`PhD/QMF/FLTstuff/HeckeOperators/Abstract.lean`, group case) — well-definedness under
`gᵢ ↦ gᵢv` uses `a ∈ A^V`; `U`-invariance because left mult by `u` permutes the cosets
`gᵢV`.  Our generalisation: every representative lies in `UgV ⊆ Δ`
(**L2.1** `mul_singleton_mul_subset`: `Submonoid.mul_mem` chain;
**L2.2** `out_mem_mul_singleton_mul`: `Quotient.out` lies in its class `x·V ⊆ (Ug)·V`),
so the monoid action suffices.  Attacks: [non-invertibility] η = eta has no inverse in Δ —
the proof never inverts η, only elements of U, V ✓ (this is the point of the design);
[finiteness] finsum junk-value without `h` — `h` is a hypothesis of the def ✓;
[drift] FLT proof shape transfers line-by-line, checked against the copy ✓.
- **L2.3** compact/open finiteness.  Source (verbatim, FLT Abstract.lean header):
  > "Note that if `G` is a topological group and `U`, `V` are compact open subgroups
  > of `G`, then our finiteness hypothesis is automatically satisfied for all `g ∈ G`,
  > because `g⁻¹Ug ∩ V` is open in compact `g⁻¹Ug` and hence has finite index, and so by
  > the second isomorphism theorem `g⁻¹UgV` is a finite union of left cosets of `V`."
  Discharge: mathlib `IsCompact.elim_finite_subcover` on the open cover by `V`-cosets
  (pattern used in FLT `finiteDoubleCoset`, Finiteness.lean:1091).

## Result R3: `Σ₀(γ)` is a monoid; `L_{n,v}` is a module over it
Lean: `Sigma0` + `WeightModule` files.

Source claims (verbatim, [Buz07] §9 p. 68):
> "define Mₜ to be the elements (γⱼ) of M₂(Oₚ) … det(γⱼ) ≠ 0, πⱼ^{tⱼ} divides cⱼ, and πⱼ
> does not divide dⱼ.  Then Mₜ is a monoid under multiplication."
> "define the right M₁-module L_{n,v} to be the K-vector space Lₙ equipped with the action
> of M₁ … send ∏ᵢ Zᵢ^{mᵢ} to ∏ᵢ (cᵢZᵢ+dᵢ)^{nᵢ}(aᵢdᵢ−bᵢcᵢ)^{vᵢ}((aᵢZᵢ+bᵢ)/(cᵢZᵢ+dᵢ))^{mᵢ}"
> "Note that in fact the same definition gives an action of GL₂(Fₚ) on L_{n,v}, but we
> never use this action."

Lean ↔ source: one place, left-handed (see dictionary above); threshold `γ < 1`
generalises `γ = v(π)^t`; the module is the two-variable homogeneous model
(`h(z) = P(z,1)` dictionary), substitution action `P ↦ P(aX+cY, bX+dY)` twisted by an
abstract character `ν` (Buzzard's `det^v` = `Sigma0.detChar`).  Per the last quote the
substitution action needs no integrality — defined for the full matrix monoid ✓
(`matrixSubst`).
- **L3.1** `Sigma0.mul_mem` — ultrametric: `v(a₁a₂)=1`, `v(b₁c₂) ≤ γ < 1` ⇒
  `v(a₃)=1`; `v(c₃) ≤ max ≤ γ`; `det` multiplicative.  HAND-CHECKED this session;
  the hypothesis `γ < 1` is NECESSARY (attack: at `γ = 1` the `a`-entry unit condition
  is not preserved: `(1 0; 1 1)² `-type examples) — recorded as a genuine hypothesis.
- **L3.2** `matrixSubst_mul` — `aeval` composition; hand-checked
  `subst'_γ ∘ subst'_δ = subst'_{γδ}` (transpose reverses the failure of the naive
  substitution to be a left action).  Discharge: `MvPolynomial.aeval_algHom_comp`-style
  lemmas / `MvPolynomial.aeval_X` + `algHom_ext`.
- **L3.3** homogeneity preservation — substitution by linear forms preserves degree-`n`
  homogeneity; discharge via `MvPolynomial.IsHomogeneous` API (induction on monomials if
  no ready lemma; small).
- **L3.4** `WeightModule` action laws — from L3.2 + `ν` multiplicativity (commuting
  scalar twist).

## Result R4: the space `S^D` and its Hecke operators (global instantiation)
Lean: `QMF.{Dfx, unitsIncl, globalUnits, evalAlgHom, toLocal, RigidificationAt,
toMatrix, levelMonoid, levelMonoidToSigma0, Space, heckeOperator}` (`Quaternionic.lean`).

Source claims (verbatim, [Buz07] §9 pp. 67–70):
> "Now let D be a quaternion algebra over F ramified at all infinite places.  Let us
> assume that D is split at all places above p."  [footnote 5: "One can almost certainly
> develop some of the theory as long as at least one place above p is split…"]
> "Let O_D denote a fixed maximal order of D, and fix an isomorphism
> O_D ⊗_{O_F} O_{F_v} = M₂(O_{F_v}) for all finite places v of F where D splits."
> "**Definition.** The space of classical automorphic forms S^D_{k,w}(U) of weight (k,w)
> and level U for D is the space L(U, L_{n,v})."

Lean ↔ source: FLT-style mock-up (`[Ring D] [Algebra F D]` + garbage-note comment);
the fixed isomorphism is the `RigidificationAt` class (local-at-`v` analogue of FLT's
global `WithRigidification`, weaker hypothesis: split at `v` only, per footnote 5);
`Space F D v γ hγ n ν U hU := levelSubmodule …` is literally `L(U, L_{n,ν})`.
Central character: NOT imposed — [Buz07] imposes none (checked pp. 68–70); FLT's
`trivial_central_char` field is deliberately dropped (with nontrivial κ the centre acts
through the weight).
- **L4.1** `evalAlgHom.commutes'` — `algebraMap F (𝔸_F^∞)` followed by `evalRingHom v` is
  `algebraMap F F_v`; discharge from mathlib `RestrictedProduct.evalRingHom` +
  FiniteAdeleRing algebra-map lemmas.
- **L4.2** `levelMonoidToSigma0` hom laws — subtype transport of `toMatrix` (rfl-adjacent).
- **L4.3** `SMulCommClass` transport — via `DistribMulAction.compHom` unfold.

## Result R5: `L(U,A) ≅ ∏_λ A^{Γ_λ}` (class-set decomposition)
Lean: `AutomorphicFunction.{stabilizerAt, evalAtReps, bijective_evalAtReps,
bijective_eval_of_trivial_smul}` (`Decomposition.lean`).

Source claim (verbatim, [Buz07] §9 p. 69):
> "Say D×_f = ∐_{λ=1}^{μ} D×τ_λU.  Then the groups Γ_λ := τ_λ⁻¹D×τ_λ ∩ U …
> Note that f ∈ L(U,A) is determined by f(τ_λ) for 1 ≤ λ ≤ μ, and one checks easily
> that the map f ↦ (f(τ_λ))_{1≤λ≤μ} induces an isomorphism L(U,A) → ⊕_{λ=1}^{μ} A^{Γ_λ}."

Lean ↔ source: `stabilizerAt Γ U τ = {u ∈ U : τuτ⁻¹ ∈ Γ} = τ⁻¹Γτ ∩ U = Γ_λ`; the map is
`evalAtReps` (evaluation at a section `σ` of the double-coset projection);
`bijective_evalAtReps` is the displayed isomorphism, stated for the product (no
finiteness needed for the bijection; finiteness turns `∏` into `⊕` and is Fujisaki
— see API gaps).  Well-definedness attack (done): for `u ∈ Γ_λ`, `φ(τu) = φ(γτ) = φ(τ)`
and `φ(τu) = u⁻¹•φ(τ)`, so `φ(τ) ∈ A^{Γ_λ}` ✓.  Template for the inverse: FLT
`LevelStruct.formEquivOfSection` (copy at `PhD/QMF/FLTstuff/Basic.lean:747` — the
`σ`/`δ`/`u` decomposition data), simplified since we have no character `χ`.
- **L5.1** `mem_stabilizerAt_iff` — `MulAut.conj` unfold (rfl-adjacent).
- **L5.2** membership of `evalAtReps` values in the invariants — argument above.
- **L5.3** `bijective_evalAtReps` — injectivity: `φ` determined on `Γ\G/U` by
  transformation; surjectivity: FLT formEquivOfSection construction.
- **L5.4** weight-2 bridge — with trivial action the invariants are everything;
  degenerates to functions on the class set ✓ (FLT weight-2 sanity anchor).

## API gaps (recorded, NO tickets in this tranche)
- **AG1 — overconvergent module `A_{κ,r}`** ([Buz07] §10 pp. 70–72, quotes extracted:
  `A_{κ,r} := O(B_r × X)` with the `Mₜ`-action
  `(h.γ)(z,x) := n(cz+d, x)(v(det γ)(x)) h((az+b)/(cz+d), x)`, "good `t`" thickening
  condition, norm-decreasing).  Intended carrier: `PhD/ForMathlib` restricted power
  series + GaussNorm.  Its own /develop tranche after this board; feeds property (Pr)
  (p. 69: "the main reason for extending Coleman's theory … to modules with property
  (Pr)" — the PhD/TateFredholm/Pr.lean hookup) and `U_π` compactness.
- **AG2 — Fujisaki finiteness** (`Finite (DoubleCoset.Quotient ↑Γ ↑U)`): PROVEN in FLT
  (`NumberField.FiniteAdeleRing.DivisionAlgebra.finiteDoubleCoset`,
  `FLT/DivisionAlgebra/Finiteness.lean:1088`, authors Buzzard–Coram).  Discharge route =
  port (ticket T016, sized: file is 1100+ lines with a HaarChar/measure-theory closure).
  Nothing in this tranche depends on it (the R5 bijection is finiteness-free).
- **AG3 — multi-place `p`** (Buzzard's `J`-indexed products): current skeleton is
  single-place `v`; product generalisation deferred.

## Prior-B2 log: `.mathlib-quality/b2_log.jsonl` checked (4 entries, all Weierstrass
project) — no name or shape matches with any QMF leaf.

---

# AG-B tranche (opened 2026-08-05): the identification `U₃ = the transcribed matrix`

**Goal.** Discharge the identification debt of `PhD/Jacobs/U3Data.lean` (its module
header, "Assumed input"): prove that the generating-function operators transcribed there
ARE the matrix of the Hecke operator `U₃ = [U₁(9)·η₃·U₁(9)]` acting on the weight-`κ`
automorphic forms of the definite quaternion algebra `D = ℚ(i,j)`.
Source: [Jac] = Jacobs, *Slopes of Compact Hecke Operators* (thesis PDF at
`~/Desktop/Papers/`; verified text extraction with page markers at the planning session's
scratchpad `jacobs.txt` — NB the extraction drops minus signs, so all numeric tables are
RE-DERIVED in Lean, never transcribed).  Chapter 1 §§1.4–1.6 pp. 13–21 (framework),
Chapter 2 §2.1 pp. 22–30 (the computation), §B.1 pp. 44–48 (the PARI certificates).

**Skeleton** (canonical statements; `lake build` green, 3594 jobs, sorries only —
verified 2026-08-05):
- `PhD/QMF/HeckeMatrix.lean` — 1 sorry (generic, stays in QMF: sibling of
  `Decomposition.lean`)
- `PhD/Jacobs/U3/Setting.lean` (14), `KappaAction.lean` (7), `Hurwitz.lean` (14),
  `Level.lean` (13), `ClassSet.lean` (8), `EtaDecomposition.lean` (9),
  `Factorisations.lean` (8), `Matrix.lean` (8)

**Convention seam (binding for every worker).**  The QMF library is LEFT-handed
(Pollack–Stevens `Σ₀`, actions `(δ • φ)(g) = δ • φ(g·δ)`, Hecke sums over the image of
`U·{η}` in `G ⧸ U`, i.e. cosets `w·U`); [Jac] is RIGHT-handed (`(φ|u)(g) = φ(gu⁻¹)|κ u_p`,
sums over `U\UηU`, factorisations of `cᵢvₜ⁻¹`).  The dictionary is the adjugate
anti-isomorphism `g ↦ adj g`.

WHY (design note, user-raised 2026-08-05; full version in `PhD/QMF/Sigma0.lean`'s header,
with pointers from `AutomorphicFunction.lean`, `U3/EtaDecomposition.lean`,
`U3/Factorisations.lean`).  Both conventions are standard and belong to neighbouring
literatures: the classical slash `f∣_k γ` is a RIGHT action (Shimura, Diamond–Shurman,
Buzzard's *Eigenvarieties*, [Jac]); Pollack–Stevens' `Σ₀(p)` is an equally established
LEFT-action monoid (overconvergent modular symbols, Ash–Stevens).  We take left because
mathlib's `Module`/`DistribMulAction`/`SMulCommClass` are left-handed — a right module is
an `Mᵐᵒᵖ`-module, which would put `MulOpposite` into every statement and instance search
— the same reason FLT chooses left.  The adjugate is not an arbitrary anti-automorphism:
`g ↦ g⁻¹` is UNAVAILABLE (`Σ₀` is a monoid, not a group — `η = (1 0; 0 ϖ)` is not
invertible in it, which is the whole point of `U_ϖ`), and the transpose sends the level
condition `π^t ∣ c` to `π^t ∣ b`, the wrong congruence subgroup.  The adjugate
`(a b; c d) ↦ (d −b; −c a)` carries Buzzard's "`d` unit, `π^t ∣ c`" to "`a` unit,
`π^t ∣ c`" = exactly Pollack–Stevens' `Σ₀(p)`; it is the anti-automorphism preserving the
level structure.  CONSEQUENCE (already the L4.3 adversarial note): `adj g * g = det g`, so
transported weight actions carry a `det^v` twist — a scalar mismatch downstream is this,
and is a recorded statement amendment, never a proof-side patch.  Consequences used in the skeleton:
Jacobs `η₃ = (3 0; 0 1)` ↦ library `eta = (1 0; 0 3)`; Jacobs's `U(3 0;0 1)U = ⊔ U(3 0;9t 1)`
(Uv-cosets) ↦ a `wₜ·U` decomposition; the factorisations become factorisations of
`classRep i * etaRep t`.  EVERY concrete table (σ-table, d/u-tables, ε-matrices) must be
recomputed in the left convention — the thesis's tables are the right-handed shadows.

## Result R-B (endpoint): `Jacobs.U3.heckeU3_apply_classRep` + `eval_classRep_injective`

### Prose proof (mirrors [Jac pp. 20–21, 25–28])
Write `T = [UηU]` with `U = U₁(9)`, `η = η₃`.  By Lemma 2.3 (R2) the double coset is
`⊔_{t<3} wₜU`, so by the library's `heckeOperator_eq_finsetSum`, `Tφ = Σₜ ⟨wₜ⟩ • φ`,
i.e. `(Tφ)(cᵢ) = Σₜ wₜ • φ(cᵢ·wₜ)`.  By the certificates (R4),
`cᵢ·wₜ = d(i,t)·c_{σ(i,t)}·u(i,t)` with `d ∈ Γ`, `u ∈ U`; left-invariance kills `d`, the
level transformation law turns `u` into an action factor:
`(Tφ)(cᵢ) = Σₜ ⟨wₜ·u(i,t)⁻¹⟩ • φ(c_{σ(i,t)})` — this is `heckeOperator_apply_rep`
(R3, generic).  Grouping by `j = σ(i,t)` and evaluating the `Δ`-action through the
κ-module structure (R5) gives `(Tφ)(cᵢ) = Σⱼ blockOp i j (φ(cⱼ))` with
`blockOp i j = Σ_{σ(i,t)=j} kappaOp((wₜ·u⁻¹)₃)`; by R4's ε-identification + R5's
Prop 2.6-by-design, `matrixCoeff (blockOp i j) = coeff (h_{i,j})` — the U3Data
transcription.  [Jac p. 28]: "Thus, the matrix of U₃ will have the form A = (ε_{i,j})".
Completeness: under HCN1, Thm 2.1 (R1) + Lemma 2.2 make `(cᵢ)` a full section with
trivial stabilisers, so evaluation is injective (`bijective_evalAtReps`).

### Source quote (verbatim, [Jac p. 21])
> "(Up φ)(ci) = Σ_{t∈T} φ(ci v_t^{-1})|κ v_{t,p} = Σ_{t∈T} φ(c(i,t))|κ (u(i,t)v_t)_p."

Lean ↔ source: `heckeU3_apply_classRep` is this displayed identity, transported to the
left convention (the acting element is `wₜ·u(i,t)⁻¹`, whose adjugate parameters are the
thesis's `(u(i,t)vₜ)₃`), with the blocks named by generating function.

## R1 [Jac Thm 2.1 + Lemma 2.2 + Ch. 1 §1.4] — `ClassSet.lean`

Prose (source pp. 16–18, 23–24): (1.4.4) `D_f^× = D^× U₀(1)` reduces the class set by the
double-coset first-isomorphism (Lemma 1.23) to `𝓞_D^×\U₀(1)/U₁(9)`; triviality away from
`3` and surjectivity of `GL₂(ℤ₃) → GL₂(ℤ/9)` reduce to `𝓞̄_D^×\SL₂(ℤ/9)/H₃`
((1.4.8)–(1.4.10)), which by the `G`-set bookkeeping (Props 1.24/1.25: stabiliser of
`(1,0)ᵀ` is `H₃`, orbit = primitive vectors) is `𝓞̄_D^×\{72 primitive vectors}`; "an
unilluminating calculation shows" [p. 24] there are 3 orbits, reps `(1,0),(5,0),(7,0)`;
lifts give `c₀,c₁,c₂` [(1.4.12)].  Γᵢ-triviality [Lemma 2.2 p. 24 quote below] is a
24-unit check.

- **L1.1 = HCN1** (`Level.lean: HClassNumberOne, hClassNumberOne`) — [Jac Lemma 1.22
  (1.4.4) p. 16], verbatim:
  > "The shortest way is to use the Jacquet-Langlands correspondence: we know that there
  > are no cusp forms of weight 2 … Since the former space is zero, we obtain one coset."
  ADVERSARIAL FINDING (recorded): this proof is NOT formalisable here (JL + dimension
  formulas).  Fallback chain applied → cross-reference [Voight, *Quaternion Algebras*,
  GTM 288]: 11.3.1 (Hurwitz order is norm-Euclidean), ideal-principality, 27.6.8-style
  idelic dictionary.  FLT states this exact statement (`FLT/Data/HurwitzRatHat.lean:96
  completed_units`) and leaves it `sorry` — independent evidence of both correctness of
  the formulation and genuine difficulty.  USER DECISION (2026-08-05): FLT is expected
  to cover `completed_units` upstream — this leaf is NOT ours to fill yet; R-CN1's
  discharge tickets (B06/B18) are DEFERRED, and the accepted end state of the tranche
  is `hClassNumberOne` sorried with every consumer hypothesis-gated (T016 precedent).
  INTERFACE FACTORING (same day): the fallback chain was moved OFF the live chain into
  the unimported `PhD/Jacobs/U3/ClassNumberOneFallback.lean`, so the live chain's ONLY
  CN1 sorry is the interface `hClassNumberOne` (contract in its docstring); primed
  convenience corollaries (e.g. `eval_classRep_injective'`) consume it with exactly one
  sorry-source.  When FLT's proof lands, port it into the interface and re-audit the
  formulation (their live framework is FiniteAdeleRing-based — the old
  `completed_units` file is ẐHat-era; our statement may already be the near-verbatim
  match).
- **L1.2** (`Level.lean: unitsIncl_mem_U0_iff`) — [Jac (1.4.7) p. 17]: "One easily
  verifies that `O_D^× = D^× ∩ U₀(1)`".  Discharge: "integral everywhere-locally ⟹
  integral" for the ℤ-lattice `𝓞_D ⊆ D`, coordinate-wise on the Hurwitz basis
  (mathlib: `Rat.isInteger_of_forall_padic`-style denominators argument — the exact
  route is elementary; no single mathlib lemma, small composition).
- **L1.3** (`ClassSet.lean: classRep, toMatrix_classRep`) — [(1.4.12) p. 18] lifts; the
  construction is `UpiElement`'s `singleₗ`-pattern (diagonal unit at `3`).  Discharge:
  project code (`PhD/QMF/UpiElement.lean` `etaAdelic`-construction, adapted).
- **L1.4** (`ClassSet.lean: unitsMod9, card_primitiveVectors, orbits_unitsMod9`) —
  [Thm 2.1 proof p. 23–24], verbatim:
  > "In this case, |G:x| = 72, and an unilluminating calculation shows that O_D^×\G:x
  > consists of three elements. … s₀ = (1 0), s₁ = (5 0), s₂ = (7 0)."
  Discharge: finite computation — 24 units (from L6.2) mapped through `θ₃ mod 9`
  (`ν₃ ≡ 4 mod 9`, derived), acting on the 72-element Finset; `decide`-guarded
  enumeration (NO native_decide — axiom discipline).  |G·x| check: 81 − 9 = 72 ✓.
- **L1.5** (`ClassSet.lean: classRep_complete, exists_classRep_section`) — assembly of
  L1.1–L1.4 along [(1.4.5)–(1.4.11)]; the group-theory step is [Jac Lemma 1.23 p. 16]
  ("First Isomorphism Theorem" for double cosets), discharged by the ported
  `FLTstuff/Mathlib/GroupTheory/DoubleCoset.lean` API + a mirrored right-quotient form
  (small new lemma inside the ticket).
- **L1.6** (`ClassSet.lean: stabilizerAt_classRep`) — [Jac Lemma 2.2 p. 24], verbatim:
  > "Γ₀ = D ∩ U, and as U is contained in U₀(1), Γ₀ is a subgroup of O_D^×. If u ∈ U,
  > then u ∈ O_D^× and u₃ ≡ (∗ ∗; 0 1), and from the proof of Theorem 2.1, we see that
  > the only possibility for Γ₀ is the trivial group."
  Discharge: L1.2 + the 24-unit mod-9 check (same computation substrate as L1.4).

## R2 [Jac Lemma 2.3] — `EtaDecomposition.lean`

Source [p. 25], verbatim:
> "G (3 0; 0 1) G = G (3 0; 0 1) ⊔ G (3 0; 9 1) ⊔ G (3 0; 18 1)"  — proof marked "□"
(omitted, "it suffices to prove the following elementary result").  EXPANSION (ours,
recorded per the source-gap rule, right-handed form; adjugate-transport to the skeleton's
left form is part of the tickets): membership: `(3 0; 9t 1) = (3 0; 0 1)·(1 0; 9t 1)` and
`(1 0; 9t 1) ∈ G`; disjointness: `(3 0; 9s 1)(3 0; 9t 1)⁻¹ = (1 0; 3(s−t) 1) ∈ G ⟺ 3∣s−t`;
covering: for `u = (a b; c d) ∈ G`, `η·u = (3a 3b; c d)` and with `t ≡ c/9·d⁻¹ mod 3` one
solves `η·u = u′·(3 0; 9t 1)` with `u′ ∈ G` (2×2 arithmetic; `d` unit, `9 ∣ c`).
- **L2.1** local identity (`bijOn_etaRep`'s 3-component core) — discharge: the expansion
  above, elementary `Matrix (Fin 2)` arithmetic over `𝒪₃`.
- **L2.2** adelic transport (`etaRep`, `bijOn_etaRep`, `etaRep_injective`) — η trivial
  away from `3` (`etaAdelic` = `iotaV`-single), `U₁(9)` product-shaped (R-GLOB Level) —
  discharge: `UpiElement` API + L2.1.
- **L2.3** `finite_image_eta3` — free from L2.2 (3-element image; no topology).

## R3 [Jac Ch. 1 §1.6 pp. 20–21] — `PhD/QMF/HeckeMatrix.lean: heckeOperator_apply_rep`

Verbatim source: the R-B quote above (p. 21 display).  Generic statement over
`(G, Γ, Δ, U, A)`.  Discharge: `heckeOperator_eq_finsetSum` (HeckeMonoid, proved) +
`left_invt'` + `apply_mul_coe` (AutomorphicFunction, proved) + `mul_smul` bookkeeping —
all project code; ~60 LOC.  (Source proves it in ~15 displayed lines.)

## R4 [Jac Lemmas 2.4/2.5 + pp. 26–27 + §B.1] — `Factorisations.lean`

PLANNING DECISION (recorded): formalise the nine CERTIFICATES, not the search.  Lemmas
2.4/2.5 as existence statements are subsumed by exhibiting the factorisations; the
thesis itself computes them by machine (§B.1 PARI listing pp. 44–48, whose output IS the
pp. 26–27 tables — cross-checked in planning).  Verbatim sample [p. 26]:
> "c₀v₀⁻¹ = (−1/3 − 1/3 i + 1/3 j)(7 0; 0 4)(1/21 ν₃ − 1/21, 2/7; 0, −1/4 ν₃ − 1/4)"
- **L4.1** `sigmaTable`(+`_ne`), `dTable`(+`_mem`), `uTable` — the left-convention data;
  right-handed shadow (for orientation only, from pp. 26–27): σ(0,·)=(2,1,1),
  σ(1,·)=(0,2,2), σ(2,·)=(1,0,0); diagonal never hit ⟹ `ε_{i,i} = 0`, trace 0 [p. 28].
- **L4.2** `factorisation` (3 tickets, one per `t`-column): each identity checked at `3`
  through `θ₃` (2×2 arithmetic in `ℚ(ν₃)` using `ν₃² = −2` only) and away from `3` by
  `d(i,t)`-unit integrality (`N(d) = ±3^k`, Hurwitz-integral entries; at `l = 2` the
  half-integer coordinates ARE Hurwitz-integral).  `u ∈ U₁(9)` memberships need
  `ν₃ mod 27` (e.g. `v₃((ν₃−1)/21) = 0` from `ν₃ ≡ 4 mod 9`) — supplied by `ν₃_near`
  (`2695 ≡ 22 mod 27`).  Discharge: finite arithmetic; `Setting` + `Hurwitz` + `Level`.
- **L4.3** `sum_weightGenFun_eq_h` — the ε-products `(wₜ·u⁻¹)₃`-parameter matrices summed
  per block equal `Jacobs.h01 … h21` [p. 28 displays (2.1.4)–(2.1.9) via the p. 28
  ε-tables; transcription = U3Data, misprint corrected there].  ADVERSARIAL NOTE
  (charCoeff_M22op_eq b2-precedent, scalar bookkeeping): the adjugate carries a
  determinant twist (`adj g = det g · g⁻¹`); if the identification surfaces a `κ(det)`
  scalar mismatch against U3Data's normalisation, the fix is a RECORDED statement
  amendment on this leaf, not a silent proof-side patch.

## R5 [Jac Def 1.27 + p. 29 + Prop 2.6] — `KappaAction.lean` + `Setting.lean: Sigma1`

Verbatim [Def 1.27 p. 19]: the R-headline quote (`z^k ↦ κ(cz+d)(cz+d)^{−2ν}(…)^k`);
[p. 29]: "κ(cx + d) = (cx + d)^t = exp₃(t log(cx + d))" (1-unit reduction — this is why
`Σ₁(9)` and not `Σ₀`: on `Σ₀` alone κ needs Teichmüller, generality deferred);
[Prop 2.6 p. 29]: the R-B generating function quote.
DESIGN (recorded): `kappaOp g := ofGenFun (weightGenFun t (adjParams g))` — Prop 2.6
becomes definitional (`matrixCoeff_kappaOp` = `Jacobs.matrixCoeff_ofGenFun`), the content
moves to the action laws (thesis: "It is an easy check that Σν is a monoid and that |κ is
a right-action" — expanded honestly as the substitution-cocycle computation at the
generating-function level).
- **L5.1** `Sigma1`, `mem_sigma1_iff`, `sigma1_le_sigma0`, `γ₉_lt_one` — closure under
  multiplication: `d″ = cb′ + dd′ ≡ 1 mod 9` (right-form) — elementary valued-field
  arithmetic; mirrors `Sigma0.mul_mem'` (project code).
- **L5.2** `norm_coeff_weightGenFun_le_one` + `tendsto_coeff_weightGenFun` — the
  `ofGenFun` input pair.  ADVERSARIAL CATCH (2026-08-05, planning): the first draft
  claimed `‖3‖^m` row decay — FALSE at `g = 1` (`weightGenFun = 1/(1−xy)`,
  `(m,m)`-coefficient `1`); the decay is special to η-composed matrices ([Jac Lemma 2.7]
  = U3Data/AG-W's rowInt family) and is NOT needed for the identification.  Skeleton
  corrected before ticketing.  Discharge: U3Data's `kappaSeries₂`/geometric-inverse
  machinery + [Kob84 Ch. IV] convergence facts already in `PadicAnalytic`.
- **L5.3** `kappaOp`, `kappaOp_mul`, `kappaOp_one` — the cocycle: at genFun level,
  `wGF(g)·substituted-wGF(h) = wGF(gh)` after clearing the geometric denominators;
  per-column route (mirrors Def 1.27's "continuous linear extension"): both sides are
  continuous, agree on basis columns by the substitution chain rule
  `κ((c₁z′+d₁))∘γ₂ · κ(c₂z+d₂) = κ((c″z+d″))` (uses `unitPow_mul`, `unitPow_add`-family
  from `PadicAnalytic` — project code).  The single heaviest B-LOC proof.
- **L5.4** `kappaModuleAction` (+ the `levelMonoid1`-compHom assembly in `Matrix.lean`,
  `kappaForms`, `heckeU3`) — mirrors `Quaternionic.lean`'s `DistribMulAction.compHom`
  pattern verbatim (project code); `kappaForms := levelSubmodule` at the composed action.

## R-CN1 [(1.4.4) replacement; Voight GTM 288] — `Hurwitz.lean` + `Level.lean`

Prose: `𝓞 = ℤ⟨i, j, ω_H⟩` (ω_H = (1+i+j+k)/2) is norm-Euclidean: for `x ∈ ℍ(ℚ)` there is
`q ∈ 𝓞` with `N(x − q) ≤ 1/2 < 1` (round coordinates; the Hurwitz lattice contains
`ℤ⁴ ∪ (ℤ+½)⁴`, covering radius² = 1/2), so division with remainder holds and every right
ideal is principal by norm descent.  Dictionary: for `g ∈ D_f^×` the "denominator ideal"
`I_g = {x ∈ 𝓞 : ∀w, x ∈ g_w·𝓞_w}` is a nonzero right ideal (common-denominator sandwich
`N₁𝓞 ⊆ I_g ⊆ 𝓞`), and if `I_g = x𝓞` then `x⁻¹g` is everywhere integrally invertible
(CRT approximation at the finitely many bad places), i.e. `g ∈ D^×·U₀(1)`.
[Voight 11.3.1 + 11.1.8 + 27.6.8; the thesis's JL proof replaced per L1.1's finding.]
- **L6.1** `hurwitzOrder` + subring axioms — mul closure: `ω_H`-products; finite ring
  arithmetic (`Quaternion.ext` + `ring`); mathlib `ℍ[ℚ]` API.
- **L6.2** `exists_norm_eq_natCast`, `hnorm(_mul/_eq_zero_iff)`,
  `isUnit_iff_hnorm_eq_one`, `card_units_hurwitzOrder` — [Jac p. 22] verbatim (the
  24-unit list); discharge: `Quaternion.normSq` API + finite enumeration (the
  coordinates are in `{0, ±1/2, ±1}` when `N = 1`).
- **L6.3** `exists_div_rem` — the rounding argument; discharge: elementary; the bound
  `∑(xᵢ−qᵢ)² ≤ 4·(1/4) = 1` for integer rounding NEEDS the half-lattice: rounding to
  `ℤ⁴` alone gives exactly `1` (fails strictness at e.g. `(½,½,½,½)`), rounding to the
  nearer of `ℤ⁴`/`(ℤ+½)⁴` gives `≤ 1/2` — the classical Hurwitz point; this is why `𝓞`
  must be the Hurwitz (not Lipschitz) order and is an attack-verified strictness check.
- **L6.4** `right_ideal_principal` — norm descent via L6.3; mathlib `Submodule`-span API.
- **L6.5** `latticeOf(_ne_bot)`, `inv_generator_mul_mem_U0`, `hClassNumberOne` — the
  dictionary; THE infrastructure leaf (CRT approximation over bad places; sub-decomposed
  in its ticket: local sandwiches `3^k𝓞_w ⊆ g_w𝓞_w ⊆ 3^{−k}𝓞_w`, finite-index reduction,
  elementwise approximation).  Fallback recorded: if the dictionary resists at this
  granularity, `/develop --continue` splits it against [Voight 27.6.8]'s proof line by
  line.  Until discharged, `HClassNumberOne` is an explicit hypothesis everywhere.

## R-SET [instantiation leaves] — `Setting.lean`

- **L7.1** typeclass pack at `K₃` (`IsUltrametricDist`, `CompleteSpace`, `CharZero`,
  `NontriviallyNormedField`-on-top-of-mathlib's-`NormedField`, `norm_three_lt_one`) —
  discharge: mathlib `Valued.toNormedField` + `Mathlib.NumberTheory.Padics.
  HeightOneSpectrum`'s `ℚ_[p]`-comparison (`v.adicCompletion ℚ ≃A[ℚ] ℚ_[primesEquiv v]`,
  in mathlib at this rev — verified) + `ℚ_[3]`-side instances.
- **L7.2** `ν₃`, `sq_ν₃`, `ν₃_near` — mathlib `hensels_lemma` at `x²+2`, `a = 1`
  (`‖f(1)‖ = ‖3‖ < 1 = ‖f′(1)‖²`), transported along the comparison; the location by the
  ultrametric factorisation `(ν−2695)(ν+2695) = −3¹¹·41` — the argument of
  `PhD/Jacobs/Instance.lean: exists_sqrt_neg_two_near`, which transports verbatim
  (project code precedent; `2695 ≡ 1 mod 3` pins the sign to the Hensel root).
- **L7.3** `theta` + the `RigidificationAt` instance — [Jac p. 14] verbatim (the
  displayed map); discharge: 4×4 structure-constant check (`i² = j² = −1`, `ij = k`
  under the map — hand-verified in planning: `θ(i)² = (ν²+ξ²)·1 = −1` ✓), inverse given
  explicitly by §B.1's `th1` [p. 44]; the instance-path alignment (v4.33 defeq seam,
  Setting.lean:110 note) is part of this ticket.
- **L7.4** `γ₉_lt_one` — `ℤᵐ⁰` coercion arithmetic (mathlib `WithZero` API).

## Attacks summary (Step 4.5; per-node logs abbreviated — 3+ categories each)

Every leaf attacked via: (1) counterexample search against project+mathlib (`lean_loogle`
on negations where meaningful; the L5.2 catch came from edge-case instantiation `g = 1`);
(2) edge cases (`t`-boundary `‖t‖ < 1` — `t = 0` legal and degenerate-checked;
`m = 0` rows; `i = j` diagonal blocks; `s ≡ t mod 3` coset collisions);
(3) hypothesis strength (ν₃ mod-precision audit: mod 27 needed by L4.2, mod 3¹⁰ carried —
slack recorded; `HClassNumberOne` isolated as the ONLY global hypothesis; `Σ₀ vs Σ₁`
necessity — κ undefined on `Σ₀`, attack produced the `Sigma1` design);
(4) source drift (all quotes re-checked against the extraction WITH the sign-loss caveat;
numeric tables marked derive-don't-transcribe; the p. 28 misprint already covered by
U3Data finding 1);
(5) discharge checks (`heckeOperator_eq_finsetSum`, `left_invt'`, `apply_mul_coe`,
`matrixCoeff_ofGenFun`, `hensels_lemma`, `primesEquiv`, mathlib `NormedField
(adicCompletion)` — all verified present at this rev during planning).
SURVIVING RISKS (named, ticketed): determinant-twist normalisation (L4.3 note);
left-convention data tables pending recomputation (L4.1); v4.33 instance-path seams
(L7.3, board-precedented).

## Prior-B2 consultation (Step 4.6)

`.mathlib-quality/qmf/` has no b2 log (this tranche starts one).  Consulted the jacobs
board's log (4 entries) + default board's (2 entries):
- `norm_coeff_M22genFun_le` / `M22half` family (hypotheses missing on parameters /
  hidden in proof holes): SHAPE MATCH with this tranche's parametrised defs — addressed
  at skeleton time: `kappaForms/heckeU3/blockOp/kappaOp/kappaModuleAction` all carry
  `(t) (ht)` explicitly (a first-draft `variable`-binding slip was caught and fixed
  during the skeleton build); `ν₃` is a fixed def, not a parameter.
- `charCoeff_M22op_eq` (scalar-normalisation drift): inherited as the L4.3 adversarial
  note (determinant twist).
- `isCompactoid_restrictOp` (`[IsTate R]`): no match (`K₃` nontrivially normed).
- NewtonPolygon junk-representation entries: no shape match.

## Confidence gate (Step 5) — status

(1) every leaf discharged-or-API-gap ✓ (API gaps: L6.5 dictionary — own sub-plan in its
ticket; NO REVIEW-PENDING leaves); (2) skeleton compiles ✓ (3594 jobs, sorries only);
(3) verbatim quotes per leaf ✓ (above; page-cited); (4) adversarial pass ✓ (logs above;
two real catches recorded); (5) prior-B2 ✓ (addressed, above); (6) tree mirrors the
source ✓ (R1–R5 = the thesis's own lemma chain; R-CN1 is the RECORDED source-replacement
per the fallback chain; LOC estimates in tickets cite source line counts);
(7) single-conclusion ✓ (certificate groups are per-`t`-column tickets into one
declaration family each; no ∧-bundles).
GATE PASSES for ticket creation, with `HClassNumberOne`-gated statements explicitly
hypothesised.  (R-CN1's own discharge is exempted from the gate by the user's deferral
decision — FLT will cover `completed_units`; the sub-tree stays recorded for the port.)
