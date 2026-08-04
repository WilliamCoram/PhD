# Additive valuations: `-log ‖·‖` in all its forms

Three things share the slogan "*take minus the logarithm of the size*", and until recently the
repository had them tangled together or duplicated:

1. the **additive valuation of a multiplicative valuation** — `Valuation.addVal` and its `ℤ`-,
   `ℚ`- and `ℝ`-valued refinements;
2. the **additive reading of a norm** on a ring whose norm is merely submultiplicative — no
   valuation exists there, so nothing in (1) applies;
3. the **normalisation** `v_ϖ(ϖ) = 1` of (2) at a pseudo-uniformizer, which is what the Newton
   polygon machinery actually consumes.

This note records what each of them is, where it lives, and why the boundaries fall where they
do. It supersedes the description of `PhD/Test/addVals2.lean` (replaced 2026‑07‑30) and of the
single-file `PhD/ForMathlib/RingTheory/Valuation/AddVal.lean` (split, same day).

---

## 0. The three settings, and why they cannot be merged

| | ambient object | multiplicativity | additive object |
| --- | --- | --- | --- |
| (1) | `Valuation R Γ₀` | `v (xy) = v x · v y` | an honest `AddValuation` |
| (2) | `[NormedRing A]` | `‖xy‖ ≤ ‖x‖‖y‖` | superadditive only |
| (3) | `[NormedRing A]` + `ϖ` | as (2) | as (2), normalised at `ϖ` |

Mathlib's `AddValuation R Γ` requires `v (x*y) = v x + v y`. Under a merely submultiplicative
norm that equality is false — one has `v (x*y) ≥ v x + v y` — so the type is simply unavailable
in settings (2) and (3), and no amount of API sharing can change that. Conversely (1) cannot be
*defined* in setting (2), because there is no `Valuation` to feed it: `NormedField.valuation`
needs a field with a multiplicative norm.

So (1) and (2) are genuinely two constructions. What they are *not* is two unrelated
constructions: where both apply — over an ultrametric normed field — they agree up to a scalar,
and that agreement is proved rather than assumed (§3).

---

## 1. Setting (1): `Valuation.addVal` and friends

Formerly one 980-line file; now nine, each sitting at the path its content would occupy in
mathlib.

```
Algebra/Order/GroupWithZero/WithZero.lean       WithZero.negLog, negLogOrderAddIso, expMap
Data/Real/WithZero.lean                         NNReal.toRealMultZero, WithZeroMulReal.toNNReal
Algebra/Order/Group/Commensurable.lean          AddCommGroup.IsCommensurableWith, ratLog
RingTheory/Valuation/AddVal/Basic.lean          Valuation.addVal, addValValueGroup
RingTheory/Valuation/AddVal/RankOne.lean        RankOne.realValuation, RankOne.addVal
RingTheory/Valuation/AddVal/Commensurable.lean  IsCommensurable, addValQ, the ℚ→ℝ square
RingTheory/Valuation/AddVal/Discrete.lean       IsRankOneDiscrete.addValZ, the ℤ→ℚ square
Topology/Algebra/Valued/AddVal.lean             NormedField.normAddVal / normAddValZ / normAddValQ
NumberTheory/Padics/AddVal.lean                 the ℚ_p verification
```

(All paths relative to `PhD/ForMathlib/`.)

### Dependency order

```
Algebra/Order/GroupWithZero/WithZero.lean        Data/Real/WithZero.lean
              │                                            │
              └──────────► RingTheory/Valuation/AddVal/Basic.lean
                                        │
                                        ▼
                           RingTheory/Valuation/AddVal/RankOne.lean ◄── Data/Real/WithZero.lean
                                        │
    Algebra/Order/Group/Commensurable.lean ──────┤
                                        ▼
                       RingTheory/Valuation/AddVal/Commensurable.lean
                                        │
                                        ▼
                        RingTheory/Valuation/AddVal/Discrete.lean
                                        │
                                        ▼
                         Topology/Algebra/Valued/AddVal.lean
                                        │
                                        ▼
                          NumberTheory/Padics/AddVal.lean
```

### Why these cuts

The split is by **mathlib destination**, not by size. Three of the nine files contain nothing
about valuations at all:

* `Algebra/Order/GroupWithZero/WithZero.lean` is pure `WithZero` API — `negLog` is
  `WithZero.log` with the junk value `log 0 = 0` replaced by the genuine `⊤` and the order
  reversed. It compiles against ~600 mathlib jobs; the monolith needed ~2400.
* `Data/Real/WithZero.lean` is the real analogue of the existing
  `Mathlib/Data/Int/WithZero.lean`, and holds both directions `ℝ≥0 ↔ ℝᵐ⁰`.
* `Algebra/Order/Group/Commensurable.lean` is ordered-group theory: a linearly ordered abelian
  group all of whose elements are commensurable with a fixed `a₀ < 0` admits a unique
  `M →+ ℚ` sending `a₀ ↦ -1`. That is the whole content of "rational rank one"; the valuation
  file only applies it to a value group.

Within the valuation directory the cuts follow mathlib's own `RingTheory/Valuation/Discrete/`
precedent (`Basic.lean` + `RankOne.lean` in a directory named for the hypothesis). Each of
`RankOne`, `Commensurable`, `Discrete` is one hypothesis on the valuation and one codomain:
`WithTop ℝ`, `WithTop ℚ`, `WithTop ℤ`.

Two placements were forced by where mathlib puts the thing being used, not by taste:

* `Valuation.norm` is defined in `Mathlib/Topology/Algebra/Valued/NormedValued.lean`, so
  `RankOne.addVal_apply_of_ne_zero` (the field statement `addVal v x = -log (v.norm x)`) had to
  move out of `AddVal/RankOne.lean` and into `Topology/Algebra/Valued/AddVal.lean`. Its
  `Ring`-level sibling `addVal_apply_of_val_ne_zero`, which speaks of `RankOne.hom` instead,
  stays upstream.
* `WithZeroMulInt.toNNReal` lives in `Mathlib/Data/Int/WithZero.lean`, which is why
  `AddVal/Discrete.lean` imports it directly rather than getting it transitively.

### One declaration was deleted, not moved

`Rat.castAddHom` and `Rat.coe_castAddHom` are gone. Mathlib already has `Rat.castHom : ℚ →+* K`
for `[DivisionRing K] [CharZero K]`, and `(Rat.castHom ℝ).toAddMonoidHom` is *definitionally*
the old `Rat.castAddHom ℝ` (checked by `rfl`). Re-deriving it would have been a duplicate, which
is exactly the kind of thing this split exists to surface. The single use site,
`IsCommensurable.toRankLeOne`, now goes through the mathlib hom.

Nothing else changed: a declaration-level diff of the monolith against the nine files shows
every other name preserved, and all of them still check against
`propext, Classical.choice, Quot.sound` only.

### What this development gives you

Given a valuation `v : Valuation R Γ₀`:

* always — `v.addValValueGroup`, values in `WithTop` of `v`'s own value group;
* `[RankOne v]` — `RankOne.addVal v : AddValuation R (WithTop ℝ)`, `x ↦ -log ‖x‖`,
  **unnormalised**;
* `v.IsCommensurable π` — `v.addValQ π : AddValuation R (WithTop ℚ)`, normalised by
  `addValQ v π π = 1`. The workhorse is `addValQ_eq_of_zpow`: any witness `v x ^ n = v π ^ m`
  computes `addValQ v π x = m / n`;
* `[v.IsRankOneDiscrete]` — `IsRankOneDiscrete.addValZ v : AddValuation R (WithTop ℤ)`, the
  honest integer-valued object.

with the two compatibility squares `addValQ_eq_map_addValZ` (`WithTop ℤ → WithTop ℚ`) and
`RankOne.addVal_eq_map_addValQ` (`WithTop ℚ → WithTop ℝ`, rescaling by `-log ‖π‖`), and the two
norm-recovery theorems `‖x‖ = ‖π‖ ^ q` and `‖x‖ = e ^ (-d)`. Note that neither carries an
exponential base as a hypothesis: the normalisation at `π` pins the base to `‖π‖⁻¹`.

`IsCommensurable` is deliberately a `Prop` carrying the normalising *element* `π` rather than a
structure carrying a chosen generator. A dense rank-one value group has no canonical generator,
so the normalisation cannot come from the group; making `π` an explicit argument is the honest
encoding. For `ℂ_p` one takes `π = p`.

The last file is the sanity check: on `ℚ_p` the abstract `normAddValZ` is *proved equal* to
`Padic.addValuationDef`. It also supplies the `IsCyclic` and `Nontrivial` instances for the
value group of the `p`-adic norm, which is what makes `ℚ_p` discretely valued in mathlib's sense.

---

## 2. Setting (2): `negLogNorm`

`PhD/ForMathlib/Analysis/Normed/Ring/NegLogNorm.lean`.

```lean
noncomputable def negLogNorm [Norm E] (r : E) : WithTop ℝ :=
  if ‖r‖ = 0 then ⊤ else ((-Real.log ‖r‖ : ℝ) : WithTop ℝ)
```

Defined for bare `[Norm E]`; the hypotheses arrive lemma by lemma. The headline facts:

| statement | hypotheses |
| --- | --- |
| `negLogNorm_le_negLogNorm : negLogNorm r ≤ negLogNorm s ↔ ‖s‖ ≤ ‖r‖` | `SeminormedAddGroup` |
| `add_negLogNorm_le_negLogNorm_mul` (`≤`, not `=`) | `NormedRing` |
| `negLogNorm_mul` (`=`) | `+ NormMulClass` |
| `le_negLogNorm_add` (ultrametric `min` bound) | `+ IsUltrametricDist` |
| `negLogNorm_nonneg_iff : 0 ≤ negLogNorm r ↔ ‖r‖ ≤ 1` | `+ NormOneClass` |

The order reversal is the workhorse — every "this element is smaller" step in a slope argument
goes through it — and it is the one that pays for the `WithTop`, since it holds *including* at
`0` with no side condition.

`negLogNorm_mul` is the exact seam: it says the inequalities of this file become equalities
precisely when the norm is multiplicative, which is precisely when setting (1) becomes available.

This file deliberately does **not** import anything from §1. It cannot: its whole point is to
exist where no valuation does, so defining it through `WithZero.negLog` would restrict it to the
case it was written to escape. It also keeps the import weight off everything downstream —
§1 pulls in `Padic`, `RankOne` and `NormedValued`, and `NegLogNorm` needs three analysis files.

---

## 3. Setting (3): `v_ϖ` on a Banach–Tate ring, and the seam

`PhD/TateFredholm/Tate.lean` defines, for a multiplicative pseudo-uniformizer `ϖ`,

```lean
def PseudoUniformizer.val (ϖ : PseudoUniformizer A) (r : A) : WithTop ℝ :=
  (AddMonoidHom.mulRight (-Real.log ‖(ϖ : A)‖)⁻¹).withTopMap (negLogNorm r)
```

i.e. `negLogNorm` rescaled so that `v_ϖ(ϖ) = 1` ([JN] Definition 2.1.2). Going through
`AddMonoidHom.withTopMap` rather than a raw `WithTop.map` buys additivity across `⊤` for free,
so each `negLogNorm` lemma transfers in one step given `-log ‖ϖ‖ > 0`.

### Why `WithTop ℝ` and not `ℝ`

The previous version was `ℝ`-valued with `Real.log 0 = 0` giving `v_ϖ(0) = 0`. That is not a
cosmetic defect. `PhD/ForMathlib/NumberTheory/NewtonPolygon/Construction.lean` takes its input
as `v : ℕ → WithTop Γ` with `[CommSemiring Γ] [Algebra Γ ℝ]`; feeding it a valuation that reports
`0` for a vanishing coefficient would place every such coefficient on the polygon at height `0`
instead of dropping it from the lower convex hull. For `charPowerSeries` of a finite-rank
operator *all but finitely many* coefficients vanish, so the old shape would have been wrong in
the generic case, silently. With the current definition
`newtonPolygon (fun n ↦ ϖ.val (f n))` typechecks directly at `Γ = ℝ`.

The lemma set: `val_zero`, `val_eq_top`, `val_of_ne_zero`, `val_one`, `val_self`,
`val_le_val_iff` / `val_lt_val_iff`, `val_mul_le` (`≤`) and `val_mul` (`=`, under
`NormMulClass`), `le_val_add`, `val_nonneg_iff`, `norm_zpow` + `val_zpow_self` (`v_ϖ` attains
every integer, on the integer powers of `ϖ` — the source of the polygon's vertices), and
`norm_eq_rpow_val` (`‖r‖ = ‖ϖ‖ ^ q`, mirroring `norm_eq_norm_rpow_normAddValQ`).

### The seam

`PhD/TateFredholm/AddVal.lean` is a leaf that nothing depends on. It exists only to pin (2) and
(3) to (1):

```lean
theorem negLogNorm_eq_negLog (r : E) :
    negLogNorm r = negLog (NNReal.toRealMultZero ‖r‖₊)

theorem negLogNorm_eq_normAddVal (K) [NontriviallyNormedField K] [IsUltrametricDist K] (x : K) :
    negLogNorm x = NormedField.normAddVal K x

theorem PseudoUniformizer.val_eq_map_normAddVal (K) … (ϖ : PseudoUniformizer K) (x : K) :
    ϖ.val x = WithTop.map (· * (-Real.log ‖(ϖ : K)‖)⁻¹) (NormedField.normAddVal K x)
```

The first says the two constructions are literally the same map, so neither can drift without
the other noticing. The third says `v_ϖ` is not a rival definition but `normAddVal` rescaled —
by the same `-log ‖π‖` that appears in `RankOne.addVal_eq_map_addValQ`. If the field's valuation
is additionally commensurable at `ϖ`, `addValQ` refines `v_ϖ` to a `WithTop ℚ`-valued honest
`AddValuation`; the ring-level object is that one's unnormalised shadow.

You can delete this file and the development still builds. Then the two halves stop being
checked against each other, which is the whole reason it is there.

---

## 4. Status and what is left

Everything above is sorry-free and depends only on `propext, Classical.choice, Quot.sound`.
All nine `ForMathlib` files, `NegLogNorm.lean`, and the whole `TateFredholm` chain
(`Tate → … → BaseChange`, plus `Noetherian` and `AddVal`) build.

Before any of this goes upstream:

* **Import minimisation.** Imports were chosen by compiling and adding what the errors asked
  for. They are honest but not certified minimal; a `#min_imports` pass is the pre-PR step.
* **`AddVal/Commensurable.lean` is 264 lines** and holds both the `ℚ`-valued theory and the
  `ℚ → ℝ` square. If a reviewer wants it smaller, the compatibility section at the bottom is the
  natural second file.
* **`PhD/Test/CompactOperatorsJohanssonNewton.lean`** still contains the old `ℝ`-valued
  `PseudoUniformizer.val`. That file is a frozen source blueprint and was left alone
  deliberately.
* Two pre-existing `overlappingInstances` linter warnings in `Tate.lean`, on `IsMultiplicative`
  and `instCoeHeadPseudoUniformizer` (`[NormedRing A]` together with `[Norm A]` / `[Mul A]`).
  They predate this work and are a one-line fix each.

## References

`[JN]` Johansson–Newton, *Extended eigenvarieties for overconvergent cohomology*,
arXiv:1604.07739v4, §2.1 (Definitions 2.1.1–2.1.2: multiplicative elements, pseudo-uniformizers,
`v_ϖ`). Mathlib precedents used as models: `Mathlib/Data/Int/WithZero.lean` for
`Data/Real/WithZero.lean`, and `Mathlib/RingTheory/Valuation/Discrete/` for the shape of
`RingTheory/Valuation/AddVal/`.
