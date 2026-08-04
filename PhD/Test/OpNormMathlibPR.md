# Proposal: generalise `ContinuousLinearMap.opNorm` away from field scalars

**Audience.** An agent working in a `mathlib4` checkout. This document is self-contained:
it does not assume access to the repository the proposal came from. Every Lean snippet
below has been compiled against mathlib at commit-era `v4.33.0-rc1` (Lean toolchain
`leanprover/lean4:v4.33.0-rc1`), in a downstream project, in the namespace `MathlibPR`
rather than `ContinuousLinearMap` so that it could sit alongside the current definitions.

**One-line summary.** `ContinuousLinearMap.opNorm` and roughly a dozen lemmas around it
are stated for `NontriviallyNormedField` scalars and `NormedSpace` modules, but their
proofs use neither. They hold for `Semiring` scalars and `Module` modules. A second tier
of results (`bounds_nonempty` and everything downstream) does need scalars, but needs far
less than a field.

---

## 1. Current state

In `Mathlib/Analysis/Normed/Operator/Basic.lean`:

```lean
-- file-scope variables (≈ line 45–54)
variable {𝕜 𝕜₂ 𝕜₃ E F Fₗ G 𝓕 : Type*}
variable [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] …
variable [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] … {σ₁₂ : 𝕜 →+* 𝕜₂} …

-- ≈ line 173
def opNorm (f : E →SL[σ₁₂] F) :=
  sInf { c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖ }

instance hasOpNorm : Norm (E →SL[σ₁₂] F) := ⟨opNorm⟩
```

`#check @ContinuousLinearMap.opNorm` currently reports

```
[SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [NontriviallyNormedField 𝕜]
[NontriviallyNormedField 𝕜₂] [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] {σ₁₂ : 𝕜 →+* 𝕜₂}
```

The `sInf` expression mentions no scalar norm, no scalar multiplication, and no
completeness. `E →SL[σ₁₂] F` typechecks for `[Semiring 𝕜] [Semiring 𝕜₂] [Module 𝕜 E]
[Module 𝕜₂ F]` plus topologies, which seminormed groups supply.

Precedent that the same formula is wanted at other generalities: `NormedAddGroupHom.opNorm`
(`Mathlib/Analysis/Normed/Group/Hom.lean`, ≈ line 183) is the identical `sInf` expression
over two `SeminormedAddCommGroup`s with **no scalars at all**, and
`ContinuousMultilinearMap.opNorm` (`Mathlib/Analysis/Normed/Module/Multilinear/Basic.lean`,
≈ line 343) is the `∏`-variant. No API relates them; they simply live on different carriers.

---

## 2. Proposed tiering

### Tier 1 — `Semiring` scalars, `Module` modules

No norm on the scalars, no `IsBoundedSMul`, no `NormedSpace`.

```lean
variable {R S E F : Type*} [Semiring R] [Semiring S] {σ : R →+* S}
  [SeminormedAddCommGroup E] [Module R E] [SeminormedAddCommGroup F] [Module S F]
```

Declarations verified to compile at this generality, with **Mathlib's existing proof text
unchanged** unless noted:

| Declaration | current line (approx.) | note |
|---|---|---|
| `opNorm` | 173 | — |
| `hasOpNorm` | 176 | — |
| `norm_def` | 179 | `rfl` |
| `bounds_bddBelow` | 189 | — |
| `opNorm_le_bound` | 199 | Mathlib's proof, `bounds_bddBelow` inlined or not |
| `opNorm_le_bound'` | 204 | needs `norm_image_of_norm_eq_zero`, also tier 1 |
| `opNorm_eq_of_bounds` | 210 | — |
| `opNorm_nonneg` | 219 | — |
| `opNorm_zero` | 223 | — |
| `norm_id_le` | 228 | — |
| `norm_image_of_norm_eq_zero` | 94 | pure topology; see §5 |

### Tier 1b — `Ring` scalars

Mathlib puts `Neg`/`Sub` on continuous linear maps in a `Ring`-scalars section
(`Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean`, `section Ring` at line 801),
so exactly the lemmas mentioning them move one notch up:

| Declaration | note |
|---|---|
| `opNorm_neg` | Mathlib's proof verbatim |
| `opNorm_sub_rev` | **new**; currently obtained from the `SeminormedAddCommGroup` structure, which is unavailable at this generality |

### Tier 2 — continuity ⇒ boundedness

`bounds_nonempty` (≈ line 184) is the first statement that genuinely needs scalars: it
asserts that a continuous linear map is bounded, via `ContinuousLinearMap.bound`. Its proof
rescales a vector into a shell by a scalar of controlled norm and unscales afterwards, which
needs

* a supply of units of arbitrarily small nonzero norm, and
* exact norm scaling by those units.

A `NontriviallyNormedField` supplies both. So does a normed ring with a **topologically
nilpotent unit whose norm is multiplicative** — a *pseudo-uniformizer* `ϖ`, `0 < ‖ϖ‖ < 1`.
This is the Banach–Tate setting (Huber; Johansson–Newton Def. 2.1.2), and the field case is
an *instance* of it, not a parallel argument: any `x` with `0 < ‖x‖ < 1` in a
`NontriviallyNormedField` is a unit and the norm is multiplicative, so every
`NontriviallyNormedField` is Tate.

Concretely, tier 2 wants

```lean
[NormedRing R] [NormOneClass R] [«IsTate» R] [Module R E] [IsBoundedSMul R E]
```

in place of `[NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]`, where `«IsTate» R` is a new
class (see §4). Note **`NormedRing`, not `NormedCommRing`**: commutativity is unused. Note
also that only `ϖ` needs multiplicative norm — the ambient norm stays submultiplicative.

Everything downstream of `bounds_nonempty` (`isLeast_opNorm`, `le_opNorm`, `opNorm_add_le`,
`toSeminormedAddCommGroup`, …) follows tier 2 automatically.

---

## 3. Recommended PR staging

**PR 1 — tier 1 + 1b only.** Pure hypothesis weakening. No new classes, no new axioms, no
downstream breakage (weaker hypotheses are always source-compatible), no deprecations. This
is the PR to open first and it should be uncontroversial.

Two structural options:

* **(a) In place.** Add a `section` before the existing field-scalar `variable` block with
  its own weaker binders and move the tier-1 declarations into it. Smallest diff; the file
  keeps its heavy imports.
* **(b) New file — recommended.** `Mathlib/Analysis/Normed/Operator/OpNorm/Defs.lean`
  holding tier 1 + 1b, imported by `Operator/Basic.lean`. The definition then needs only
  `Mathlib/Topology/Algebra/Module/ContinuousLinearMap/Basic.lean` and
  `Mathlib/Analysis/Normed/Group/Basic.lean`, instead of inheriting
  `Mathlib.Analysis.LocallyConvex.WithSeminorms`, `Mathlib.Analysis.Normed.Module.Convex`
  and `Mathlib.Algebra.Algebra.Tower` from `Operator/Basic.lean`. Import minimisation is a
  standard, well-received justification, and it makes the operator norm available to files
  that cannot currently reach it.

**PR 2 — tier 2.** Requires a new typeclass and a design discussion. **Raise it on the Zulip `#mathlib4` stream before writing
it** — a new typeclass in the normed-ring hierarchy is a design decision, not a refactor. Do not bundle it with PR 1.

---

## 4. The tier-2 class question

Mathlib has no Tate-ring class today. Searching turns up only:

* `IsTopologicallyNilpotent` (`Mathlib/Topology/Algebra/TopologicallyNilpotent.lean`, ≈ line 46)
  — a predicate on an element, `Tendsto (a ^ ·) atTop (𝓝 0)`; no unit, no norm condition.
* `NontriviallyNormedField`, `DenselyNormedField` (`Mathlib/Analysis/Normed/Field/Basic.lean`,
  ≈ lines 166, 173) — field-only.
* `NormSMulClass` (`Mathlib/Analysis/Normed/MulAction.lean`, ≈ line 95) — `‖r • x‖ = ‖r‖‖x‖`,
  the right notion for exact scaling, but a class on an action rather than a single element.

A minimal shape, adapted from the Banach–Tate development this proposal came from:

```lean
/-- A multiplicative pseudo-uniformizer: a unit `ϖ` with `‖ϖ‖ < 1` whose norm is
multiplicative. -/
structure PseudoUniformizer (A : Type*) [Norm A] [Monoid A] where
  unit : Aˣ
  norm_lt_one : ‖(unit : A)‖ < 1
  isMultiplicative : ∀ x : A, ‖(unit : A) * x‖ = ‖(unit : A)‖ * ‖x‖

/-- A normed ring is *Tate* if it admits a multiplicative pseudo-uniformizer. -/
class IsTate (A : Type*) [NormedRing A] : Prop where
  nonempty_pseudoUniformizer : Nonempty (PseudoUniformizer A)

instance (K : Type*) [NontriviallyNormedField K] : IsTate K :=
  let ⟨x, hx_pos, hx_lt⟩ := NormedField.exists_norm_lt_one K
  ⟨⟨Units.mk0 x (by simpa using hx_pos.ne'), hx_lt, fun y => norm_mul _ _⟩⟩
```

That instance is the linchpin: it is what makes the field case a specialisation rather than
a duplicate. Design questions for Zulip, not to be decided unilaterally:

* class vs. structure vs. a `Nonempty`-wrapped mixin;
* whether to reuse `IsTopologicallyNilpotent` for `norm_lt_one`;
* whether `isMultiplicative` should be `NormSMulClass`-flavoured;
* whether mathlib wants Tate rings at all before the adic-spaces machinery lands.

---

## 5. Two real gaps in tier 2

Both are noted honestly because a reviewer will find them.

**Seminormed modules.** The Tate proof of `le_opNorm` as written splits on `‖y‖ = 0` via
`norm_pos_iff` and so wants `NormedAddCommGroup`, whereas Mathlib's `bound` handles
seminorms. This is a small edit, not new mathematics: the degenerate case needs no scaling
at all, because

```lean
theorem norm_image_of_norm_eq_zero (f : E →SL[σ] F) {x : E} (hx : ‖x‖ = 0) : ‖f x‖ = 0 := by
  rw [← mem_closure_zero_iff_norm, ← specializes_iff_mem_closure, ← map_zero f] at *
  exact hx.map f.continuous
```

is pure topology and already compiles at tier 1 (it is Mathlib's own proof of
`norm_image_of_norm_eq_zero`, ≈ line 94, with the field hypotheses dropped). The shell
argument then only has to handle `0 < ‖y‖`.

**Semilinearity.** For `f : E →SL[σ] F` the unscaling happens in `F` against `σ(ϖ)`, so one
needs `‖σ(ϖ)⁻¹ • w‖ = ‖σ(ϖ)‖⁻¹ ‖w‖`. Submultiplicativity gives only `‖a⁻¹‖ ≥ ‖a‖⁻¹` — the
wrong direction — so `RingHomIsometric σ` is **not** sufficient at tier-2 generality: one
additionally needs `σ` to carry pseudo-uniformizers to pseudo-uniformizers. Over a field
this is automatic since the norm is multiplicative. Options: add the hypothesis, or restrict
tier 2 to `σ = RingHom.id` and keep the semilinear statements at field generality.

---

## 6. Risks

* **Instance generality.** `hasOpNorm` will fire in strictly more situations. Check no other
  `Norm (E →SL[σ] F)` instance exists that could now form a diamond, and watch typeclass
  search timings on the `Analysis` subtree.
* **Unification cost.** In the source project, having a *second* `Norm` instance on
  `E →SL[σ] F` (defeq but syntactically distinct) caused `rw [ContinuousLinearMap.opNorm_zero]`
  to fail to find `‖0‖` in `‖0‖ = 0`, and `norm_add_le u v` to hit a deterministic `isDefEq`
  timeout at 200000 heartbeats. That is an argument *for* this PR — generalise in place
  rather than let downstream users define their own — but also a warning that instance
  duplication here is expensive.
* **`@`-applications.** Weakening a binder changes the instance-argument list, so explicit
  `@ContinuousLinearMap.opNorm …` applications inside mathlib will need updating. Grep for
  them.
* **Binder order.** Keep the *order* of remaining instance binders stable where possible to
  minimise churn.

---

## 7. Verification checklist

```bash
lake exe cache get
lake build Mathlib.Analysis.Normed.Operator.Basic
lake build Mathlib.Analysis.Normed.Operator          # whole subtree
lake build                                           # full, before pushing
```

Then confirm the point of the exercise — that this is a weakening and not a redefinition:

```lean
-- with the PR applied, in a scratch file
example {𝕜 𝕜₂ E F : Type*} [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂]
    {σ : 𝕜 →+* 𝕜₂} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [SeminormedAddCommGroup F]
    [NormedSpace 𝕜₂ F] (f : E →SL[σ] F) :
    ‖f‖ = sInf {c | 0 ≤ c ∧ ∀ x, ‖f x‖ ≤ c * ‖x‖} := rfl
```

and that a genuinely scalar-poor instance now typechecks:

```lean
example (E F : Type) [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]
    (f : E →L[ℤ] F) : 0 ≤ ‖f‖ := ContinuousLinearMap.opNorm_nonneg f
```

Also run `lake exe shake` and the style linters; if option (b) is taken, add the new file to
`Mathlib.lean` and check the import-graph tooling is happy.

---

## 8. Companion artifact

The tiering above was developed and compiled as a single Lean file in the originating
project (`PhD/Test/OpNormMathlibPR.lean`, ~200 lines). If it can be supplied alongside this
document it is the fastest way to see the proposal work: it states tiers 1 and 1b in full,
and proves by `rfl` that the generalised instance is definitionally both Mathlib's
`ContinuousLinearMap.hasOpNorm` and the Banach–Tate project's own operator norm. It is not
required — everything needed to reconstruct the PR is in §2 and §5.
