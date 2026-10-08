# -*- coding: utf-8 -*-
"""Ticket data for the board `tauceti-np-layer2`, part B (SupportValue … Examples, T039–T072), plus the
cleanup tickets and the board order."""

SV = 'SupportValue.lean'
GN = 'GaussNorm.lean'
PU = 'Pure.lean'
DI = 'Distinguished.lean'
PA = 'Padic.lean'
EXA = 'Examples.lean'

T = []

def t(**kw):
    T.append(kw)

SRC_NOTE = ("[SRC] is read-only: port the idea to the `(v, e, b)` form, never `import PhD.Main.*`.")
DEC = "Decomposition entry: "

# ---------------------------------------------------------------- G7 SupportValue
t(id='T039', title='`toEReal`: `WithTop ℝ` inside `EReal`', file=SV, deps='none',
  par='yes (with T001, T010)', typ='def API', leaves='L7.1–L7.6',
  defs=[(SV, 'toEReal')],
  decls=[(SV, 'toEReal_ne_bot'), (SV, 'toEReal_le_toEReal'), (SV, 'toEReal_lt_toEReal'), (SV, 'toEReal_injective'),
         (SV, 'toEReal_eq_top_iff'), (SV, 'toEReal_of_ne_top')],
  sketch="""`toEReal x = WithBot.some x` and `EReal = WithBot (WithTop ℝ)` (a `def`; `toEReal_coe`, `toEReal_top` are `rfl`).
1. `toEReal_ne_bot := WithBot.coe_ne_bot`; `toEReal_le_toEReal := WithBot.coe_le_coe`; `toEReal_lt_toEReal := WithBot.coe_lt_coe`; `toEReal_injective := WithBot.coe_injective`. If the `EReal` instances do not unfold automatically, `show (WithBot.some x : WithBot (WithTop ℝ)) ≤ WithBot.some y ↔ _` first.
2. `toEReal_eq_top_iff`: `(⊤ : EReal) = toEReal ⊤` (`toEReal_top.symm`), then `toEReal_injective.eq_iff`.
3. `toEReal_of_ne_top`: `rw [← WithTop.coe_untop₀_of_ne_top hx]` on the left, `toEReal_coe`.
""" + DEC + "L7.1–L7.6.",
  mathlib="`WithBot.coe_ne_bot`, `WithBot.coe_le_coe`, `WithBot.coe_lt_coe`, `WithBot.coe_injective`, `Function.Injective.eq_iff`, `WithTop.coe_untop₀_of_ne_top`, `EReal`.",
  sources="[RM] §2.3.1 (the supporting value as an infimum; plan decision 5 for the `EReal` codomain).",
  gen="Pure order bookkeeping.")

t(id='T040', title='`supportValue`: lattice bounds, finiteness, monotonicity, admissibility', file=SV, deps='T039',
  par='yes (with T001, T010)', typ='def API', leaves='L7.7–L7.13',
  defs=[(SV, 'supportValue')],
  decls=[(SV, 'supportValue_le'), (SV, 'le_supportValue_iff'), (SV, 'coe_le_supportValue_iff'), (SV, 'supportValue_ne_bot_iff'),
         (SV, 'supportValue_eq_top_iff'), (SV, 'supportValue_mono'), (SV, 'isAdmissible_iff_exists_supportValue_ne_bot')],
  sketch="""`supportValue h m = ⨅ k, (toEReal (h k) - ↑(m * k))` (no `sorry`).
1. `supportValue_le := iInf_le _ k`; `le_supportValue_iff := le_iInf_iff`.
2. `coe_le_supportValue_iff`: 1, then per `k`: `rcases eq_or_ne (h k) ⊤`: `⊤` gives `toEReal ⊤ - ↑_ = ⊤` (`toEReal_top`, `EReal.top_sub_coe`), `le_top` on both sides; else write `h k = ↑r` (`WithTop.ne_top_iff_exists`), `toEReal_coe`, `← EReal.coe_sub`, `EReal.coe_le_coe_iff`, `le_sub_iff_add_le`, `WithTop.coe_le_coe`.
3. `supportValue_ne_bot_iff`: `EReal.eq_bot_iff_forall_lt` negated: `s ≠ ⊥ ↔ ∃ y : ℝ, ¬ s < ↑y`, i.e. `∃ y, ↑y ≤ s` (`not_lt`); then 2.
4. `supportValue_eq_top_iff`: `iInf_eq_top`; per `k`, `toEReal (h k) - ↑(mk) = ⊤ ↔ h k = ⊤` (`⊤` case by `EReal.top_sub_coe`; finite case: `← EReal.coe_sub`, `EReal.coe_ne_top`).
5. `supportValue_mono`: `iInf_mono fun k ↦ ?_`; `EReal.sub_le_sub (toEReal_le_toEReal.mpr (hgh k)) le_rfl` (if that name is absent at the pin, use `sub_eq_add_neg` on `EReal` and `add_le_add_right`).
6. `isAdmissible_iff_exists_supportValue_ne_bot`: `NewtonPolygon.isAdmissible_iff_exists_line`, 3, `exists_comm`.
""" + DEC + "L7.7–L7.13.",
  mathlib="`iInf_le`, `le_iInf_iff`, `EReal.top_sub_coe`, `le_top`, `WithTop.ne_top_iff_exists`, `EReal.coe_sub`, `EReal.coe_le_coe_iff`, `le_sub_iff_add_le`, `WithTop.coe_le_coe`, `EReal.eq_bot_iff_forall_lt`, `not_lt`, `iInf_eq_top`, `EReal.coe_ne_top`, `iInf_mono`, `EReal.sub_le_sub`, `add_le_add_right`, `sub_eq_add_neg`, `NewtonPolygon.isAdmissible_iff_exists_line`, `exists_comm`.",
  sources="[Ked07] §2 (Q-Ked-vr: \"v_r … is the y-intercept of the supporting line of the Newton polygon of slope r\"); [RM] §2.3.1–§2.3.2.",
  gen="Generic over `h : ℕ → WithTop ℝ`, any real slope.")

t(id='T041', title='The points and their polygon have the same supporting value', file=SV, deps='T040',
  par='yes (with T001, T010)', typ='theorem', leaves='L7.14',
  decls=[(SV, 'supportValue_newtonPolygon')],
  sketch="""`le_antisymm`.
1. `≤`: `supportValue_mono (NewtonPolygon.newtonPolygon_le (exists_isConvexMinorant_iff_isAdmissible.mpr hv)) m`.
2. `≥`: `rcases` on `supportValue v m` being `⊥` (`bot_le`), `⊤`, or `↑r` (`EReal.eq_bot_iff_forall_lt`/`EReal.coe_toReal` — or `induction supportValue v m using EReal.rec`). `⊤`: `supportValue_eq_top_iff` gives `∀ k, v k = ⊤`, so `v = fun _ ↦ ⊤` and `newtonPolygon v = v` (`newtonPolygon_eq_self isConvexSeq_top`), hence equal. `↑r`: `coe_le_supportValue_iff` gives the line `↑(r + mk) ≤ v k`; `(isNewtonPolygonOf_newtonPolygon …).line_le` gives it below the polygon; `coe_le_supportValue_iff` back.
""" + DEC + "L7.14.",
  mathlib="`NewtonPolygon.newtonPolygon_le`, `NewtonPolygon.exists_isConvexMinorant_iff_isAdmissible`, `NewtonPolygon.isNewtonPolygonOf_newtonPolygon`, `NewtonPolygon.IsNewtonPolygonOf.line_le`, `NewtonPolygon.newtonPolygon_eq_self`, `NewtonPolygon.isConvexSeq_top`, `EReal.rec`, `bot_le`, `le_antisymm`.",
  sources="[Ked07] §2 (Q-Ked-vr); [RM] §2.3.1 (\"the supporting value is the infimum over k of h k - k·m\").",
  gen="Admissible `v`.")

t(id='T042', title='Attainment at a point of contact; piecewise affinity', file=SV, deps='CLEANUP-15',
  par='yes (with T001, T010)', typ='theorems', leaves='L7.15–L7.17',
  decls=[(SV, 'supportValue_eq_of_line_le'), (SV, 'IsConvexSeq.supportValue_eq_of_unitSlope'), (SV, 'IsConvexSeq.supportValue_eq_of_unitSlope_le_le')],
  sketch="""1. `supportValue_eq_of_line_le`: `le_antisymm (supportValue_le h m n) (le_iInf fun k ↦ ?_)`: with `h n = ↑η` (`WithTop.ne_top_iff_exists`, `WithTop.coe_untop₀_of_ne_top`), `hline k` reads `↑(η + m (k - n)) ≤ h k`; if `h k = ⊤` the target is `_ ≤ ⊤ - ↑_ = ⊤`; else `h k = ↑r` and `η - mn ≤ r - mk` (`EReal.coe_sub`, `EReal.coe_le_coe_iff`, `linarith` from `η + m(k - n) ≤ r`).
2. `IsConvexSeq.supportValue_eq_of_unitSlope`: `(NewtonPolygon.IsConvexSeq.line_le_iff hh hn m).mpr ⟨h₁, h₂⟩` gives `hline`; then 1.
3. `IsConvexSeq.supportValue_eq_of_unitSlope_le_le`: apply 2 at `n := j + 1`. `h j ≠ ⊤`: from `h₁`, `unitSlope h j ≠ ⊤` (`ne_top_of_le_ne_top WithTop.coe_ne_top`), `unitSlope_ne_top_iff`. `h₁'`: for `i < j + 1` with `h i ≠ ⊤`, `i ≤ j` and `hh.monotoneOn (mem_finiteSupport.mpr hi) (mem_finiteSupport.mpr hj') hij : unitSlope h i ≤ unitSlope h j ≤ ↑m`. `h₂'`: for `i ≥ j + 1`, if `h i = ⊤` then `unitSlope h i = ⊤ ≥ ↑m` (`unitSlope_eq_top_iff`, `le_top`); else `hh.monotoneOn` from `j + 1` to `i` and `h₂`.
""" + DEC + "L7.15–L7.17.",
  mathlib="`iInf_le`, `le_iInf`, `WithTop.ne_top_iff_exists`, `WithTop.coe_untop₀_of_ne_top`, `EReal.coe_sub`, `EReal.coe_le_coe_iff`, `EReal.top_sub_coe`, `le_top`, `NewtonPolygon.IsConvexSeq.line_le_iff`, `ne_top_of_le_ne_top`, `WithTop.coe_ne_top`, `NewtonPolygon.unitSlope_ne_top_iff`, `NewtonPolygon.unitSlope_eq_top_iff`, `NewtonPolygon.IsConvexSeq.monotoneOn`, `NewtonPolygon.mem_finiteSupport`, `le_antisymm`.",
  sources="[Ked07] §2 (Q-Ked-vr); [RM] §0.5.1 (supporting lines), §2.3.4 (\"piecewise affine with the unit slopes as its breakpoints\").",
  gen="Statement 1 needs no convexity (the hypothesis `hh` was removed at planning); 2–3 need `IsConvexSeq h`.")

t(id='T043', title='Attainment at the endpoints of the face', file=SV, deps='T042',
  par='yes (with T001, T010)', typ='theorems', leaves='L7.18–L7.20',
  decls=[(SV, 'IsConvexSeq.supportValue_eq_faceRight'), (SV, 'IsConvexSeq.supportValue_eq_faceLeft'), (SV, 'IsConvexSeq.supportValue_ne_bot')],
  sketch="""1. `supportValue_eq_faceRight := supportValue_eq_of_line_le (NewtonPolygon.ne_top_faceRight h0 m) (NewtonPolygon.IsConvexSeq.faceRight_line_le hh h0 hu m)`.
2. `supportValue_eq_faceLeft`: same with `ne_top_faceLeft`, `IsConvexSeq.faceLeft_line_le`.
3. `supportValue_ne_bot`: `rw [hh.supportValue_eq_faceRight h0 hu m, toEReal_of_ne_top (ne_top_faceRight h0 m), ← EReal.coe_sub]`, `EReal.coe_ne_bot`.
""" + DEC + "L7.18–L7.20.",
  mathlib="`NewtonPolygon.ne_top_faceRight`, `NewtonPolygon.ne_top_faceLeft`, `NewtonPolygon.IsConvexSeq.faceRight_line_le`, `NewtonPolygon.IsConvexSeq.faceLeft_line_le`, `EReal.coe_sub`, `EReal.coe_ne_bot`.",
  sources="[Ked07] proof of Cor. 2 (Q-Ked-C2); [RM] §2.3.1 (\"the attained form\"), §0.5.3.",
  gen="Layer 0's face hypotheses: anchored at `0` and `SlopesUnbounded` (Layer 0 decision 5).")

t(id='T044', title='Attained at a point iff a vertex lies on the supporting line', file=SV, deps='T043',
  par='yes (with T001, T010)', typ='theorem', leaves='L7.21',
  decls=[(SV, 'IsNewtonPolygonOf.exists_eq_supportValue_iff')],
  sketch="""Let `s := supportValue v m`; `s ≠ ⊤` from `hv` (`supportValue_eq_top_iff`), so `s = ↑r` (`EReal.coe_toReal hs' hs`).
(←) `⟨k, hk, heq⟩`: `hh.eq_of_isVertex hk : h k = v k`, rewrite.
(→) `⟨k, hk⟩`. The line `L j := ↑(r + m j)` is below the points (`coe_le_supportValue_iff` at `r`), hence below `h` (`hh.line_le`), and `L k = v k ≥ h k ≥ L k`, so `h k = v k = L k`. Let `F := {j | toEReal (h j) - ↑(m j) = ↑r}` (the polygon's contact set); `k ∈ F`. By `IsConvexSeq.line_le_iff hh.convex (h k ≠ ⊤) m` (→) applied to the line through `(k, h k)` (which is `L`), the unit slopes before `k` (finite) are `≤ m` and those from `k` on are `≥ m`. Let `j₁ := Nat.find ⟨k, hk'⟩` (the least element of `F`). Claim `IsVertex h j₁`: `h j₁ ≠ ⊤` (it is on the line). If `j₁ = anchor h` done (`Or.inl`). Else `anchor h < j₁`, so `h (j₁ - 1) ≠ ⊤` (the finiteness set is an interval, `hh.convex.ordConnected`) and `j₁ - 1 ∉ F` (`Nat.find_min'`), i.e. `h (j₁ - 1)` lies strictly above `L` (it is `≥ L` since `L ≤ h`); hence `unitSlope h (j₁ - 1) = h j₁ - h (j₁ - 1) < L j₁ - L (j₁ - 1) = m`, while `unitSlope h j₁ ≥ m` (`h (j₁ + 1) ≥ L (j₁ + 1)`): `Or.inr` with `WithTop.coe_lt_coe` arithmetic. Finally `toEReal (h j₁) - ↑(m j₁) = ↑r` by `j₁ ∈ F`.
""" + DEC + "L7.21 (two attacks and their repairs are recorded there: the contact set must be the polygon's, not the points', and `hv` is needed).",
  mathlib="`EReal.coe_toReal`, `NewtonPolygon.IsNewtonPolygonOf.eq_of_isVertex`, `NewtonPolygon.IsNewtonPolygonOf.line_le`, `NewtonPolygon.IsNewtonPolygonOf.le_points`, `NewtonPolygon.IsConvexSeq.line_le_iff`, `NewtonPolygon.IsConvexSeq.ordConnected`, `Set.OrdConnected.out`, `NewtonPolygon.IsVertex`, `NewtonPolygon.anchor_le`, `NewtonPolygon.eq_top_of_lt_anchor`, `Nat.find`, `Nat.find_spec`, `Nat.find_min'`, `NewtonPolygon.unitSlope_nat`, `WithTop.coe_lt_coe`, `WithTop.coe_le_coe`, `EReal.coe_sub`, `EReal.coe_eq_coe_iff`, `le_antisymm`.",
  sources="[RM] §2.3.3 (\"the Gauss norm is attained at an index exactly when the polygon has a vertex on the supporting line\"); [Gou20] p. 254 (Q-Gou-first: \"i is the largest integer such that ‖f(X)‖_c = |a_i| c^i\").",
  gen="`v` with a point (`hv`) and a finite-from-below supporting value; `h` its polygon.")

t(id='T045', title='The slopes with finite supporting value form an interval; concavity', file=SV, deps='CLEANUP-16',
  par='yes (with T001, T010)', typ='theorems', leaves='L7.22–L7.23',
  decls=[(SV, 'convex_setOf_supportValue_ne_bot'), (SV, 'concaveOn_toReal_supportValue')],
  sketch="""1. `convex_setOf_supportValue_ne_bot`: `convex_iff_ordConnected.mpr ⟨fun m₁ h₁ m₂ h₂ m hm ↦ ?_⟩`; from `supportValue_ne_bot_iff` get `y₂` with `↑(y₂ + m₂ k) ≤ h k`; then `↑(y₂ + m k) ≤ ↑(y₂ + m₂ k)` since `m ≤ m₂` and `(k : ℝ) ≥ 0` (`mul_le_mul_of_nonneg_right hm.2 (Nat.cast_nonneg k)`, `WithTop.coe_le_coe`), so `supportValue h m ≠ ⊥`.
2. `concaveOn_toReal_supportValue`: `by_cases hall : ∀ k, h k = ⊤`. If so, `supportValue h m = ⊤` for all `m` (`supportValue_eq_top_iff`), `EReal.toReal_top`, `concaveOn_const`. Otherwise fix `k₀` with `h k₀ ≠ ⊤`; on `S := {m | supportValue h m ≠ ⊥}` the value is real. Show `(supportValue h m).toReal = ⨅ k : NewtonPolygon.finiteSupport h, ((h k).untop₀ - m * k)` for `m ∈ S`: both are the greatest lower bound of `{(h k).untop₀ - m k | h k ≠ ⊤}` (use `coe_le_supportValue_iff` and `le_ciInf`/`ciInf_le` with `BddBelow` from `S`; `EReal.coe_toReal`). Then `-(⨅ …) = ⨆ k : finiteSupport h, (m * k - (h k).untop₀)` (`Real.sSup_neg`-style, or prove the identity via `le_antisymm` and `neg_le`), and `convexOn_ciSup` (the root lemma in Layer 0's `ConvexSeq.lean`, `Nonempty (finiteSupport h)` from `k₀`) with each `m ↦ m * k - c` convex (`(convexOn_id _).smul`-style: `ConvexOn.add (convexOn_const _ _)`; a linear function is convex: `LinearMap.convexOn`, or `convexOn_iff_forall_pos` directly) and bounded above on `S` (`bddAbove_def` from the bound `-(supportValue h m).toReal`); finally `neg_convexOn_iff`/`ConcaveOn.neg` and `ConcaveOn.congr`.
""" + DEC + "L7.22–L7.23.",
  mathlib="`convex_iff_ordConnected`, `Set.OrdConnected`, `mul_le_mul_of_nonneg_right`, `Nat.cast_nonneg`, `WithTop.coe_le_coe`, `EReal.toReal_top`, `concaveOn_const`, `EReal.coe_toReal`, `le_ciInf`, `ciInf_le`, `Real.sSup_neg`, `convexOn_ciSup`, `ConvexOn.add`, `convexOn_const`, `LinearMap.convexOn`, `convexOn_iff_forall_pos`, `neg_convexOn_iff`, `ConcaveOn.neg`, `ConcaveOn.congr`, `bddAbove_def`, `neg_le`.",
  sources="[Ked07] §2 (Q-Ked-vr: `v_r` is a minimum of affine functions of `r`; \"r ↦ v_r(P) is continuous\"); [RM] §2.3.4 (\"is concave\").",
  gen="Any sequence `h` (no convexity): concavity of an infimum of affine functions.")

t(id='T046', title='The biconjugate: the polygon is the supremum of its supporting lines', file=SV, deps='T045',
  par='yes (with T001, T010)', typ='theorem', leaves='L7.24',
  decls=[(SV, 'iSup_supportValue_add')],
  sketch="""Let `h := newtonPolygon v`, `hh := isNewtonPolygonOf_newtonPolygon (exists_isConvexMinorant_iff_isAdmissible.mpr hv)`. `le_antisymm`:
1. `≤`: `iSup_le fun m ↦ ?_`: `supportValue v m ≤ supportValue h m` is an equality (`supportValue_newtonPolygon hv m`); `supportValue h m ≤ toEReal (h k) - ↑(mk)` (`supportValue_le`); add `↑(mk)`: `EReal.sub_add_cancel`-style for a real summand (`toEReal (h k) - ↑r + ↑r = toEReal (h k)`: cases `h k = ⊤` (`EReal.top_sub_coe`, `EReal.top_add_coe`) or finite (`EReal.coe_sub`, `EReal.coe_add`, `sub_add_cancel`)); `add_le_add_right` on `EReal`.
2. `≥`: three cases.
   (i) `h k ≠ ⊤`: choose a supporting slope `σ`: if `h (k+1) ≠ ⊤`, `σ := (unitSlope h k).untop₀`; `IsConvexSeq.line_le_iff hh.convex hk σ` (←) holds (`hh.convex.monotoneOn`: earlier finite unit slopes `≤ unitSlope h k`, later `≥`), so `supportValue h σ = toEReal (h k) - ↑(σ k)` (`IsConvexSeq.supportValue_eq_of_unitSlope`), i.e. `supportValue v σ + ↑(σ k) = toEReal (h k)` (T041 and the cancellation of 1); `le_iSup _ σ`. If `h (k+1) = ⊤` and `anchor h < k`: `σ := (unitSlope h (k-1)).untop₀` (finite by the interval property), same argument (later unit slopes are `⊤`). If `k = anchor h` and `h (k+1) = ⊤` (a single point): any `σ`, `line_le_iff` trivially.
   (ii) `h k = ⊤`, `anchor h ≤ k`, and `v` has a last finite index `d < k` (`h d ≠ ⊤`, `h (d+1) = ⊤`; exists since the finiteness set is an interval not containing `k`): for `m ≥ (unitSlope h (d-1)).untop₀` (or any `m` if `d = anchor`), `supportValue h m = toEReal (h d) - ↑(md)` (T042), so `supportValue v m + ↑(mk) = ↑((h d).untop₀ + m (k - d))`, unbounded in `m` (`k > d`): `EReal.eq_top_iff_forall_lt` and `le_iSup` with `exists_nat_gt`-style choice of `m`.
   (iii) `h k = ⊤`, `k < anchor h =: a`: for `m ≤ (unitSlope h a).untop₀` (if finite; else any `m`), `supportValue h m = toEReal (h a) - ↑(ma)` (`line_le_iff` at `a`: no earlier finite slopes), so the term is `↑((h a).untop₀ + m (k - a))` with `k - a < 0`, unbounded as `m → -∞`.
   The remaining case (`h k = ⊤`, `k ≥ a`, infinite finiteness set) is impossible (`hh.convex.ordConnected`).
""" + DEC + "L7.24 (a worker may split case (i) off as a sub-ticket `exists_supporting_slope`).",
  mathlib="`iSup_le`, `le_iSup`, `EReal.top_sub_coe`, `EReal.top_add_coe`, `EReal.coe_sub`, `EReal.coe_add`, `sub_add_cancel`, `add_le_add_right`, `NewtonPolygon.IsConvexSeq.line_le_iff`, `NewtonPolygon.IsConvexSeq.monotoneOn`, `NewtonPolygon.IsConvexSeq.ordConnected`, `NewtonPolygon.anchor_le`, `NewtonPolygon.eq_top_of_lt_anchor`, `NewtonPolygon.anchor_mem`, `EReal.eq_top_iff_forall_lt`, `exists_nat_gt`, `WithTop.untop₀`, `WithTop.coe_untop₀_of_ne_top`, `NewtonPolygon.isNewtonPolygonOf_newtonPolygon`, `NewtonPolygon.exists_isConvexMinorant_iff_isAdmissible`.",
  sources="[Ked07] §1 (Q-Ked-def: \"the intersection of every closed halfplane lying above some nonvertical line containing all the points\"); [RM] §2.3.4 (\"the polygon and the Gauss norm function determine each other\").",
  gen="Admissible `v`; the identity is in `EReal` so that the `⊤` cases are honest.")

# ---------------------------------------------------------------- G8 GaussNorm
t(id='T047', title='The bridge to `Polynomial.gaussNorm`; the term as a power of the base', file=GN, deps='CLEANUP-13, CLEANUP-17',
  par='yes (with T063)', typ='theorems', leaves='L8.1–L8.3',
  decls=[(GN, 'gaussNorm_toAbsoluteValue'), (GN, 'exists_gaussNorm_coe_eq'), (GN, 'norm_coeff_mul_rpow_pow_eq_rpow')],
  sketch="""1. `gaussNorm_toAbsoluteValue`: `(Polynomial.gaussNorm_coe_powerSeries (NormedField.toAbsoluteValue K) f hc).symm` and `⇑(NormedField.toAbsoluteValue K) = norm` (`rfl`; `show` or `simp only [NormedField.toAbsoluteValue]` if needed).
2. `exists_gaussNorm_coe_eq`: `Polynomial.exists_eq_gaussNorm (NormedField.toAbsoluteValue K) c f` gives `k` with `f.gaussNorm _ c = ‖f.coeff k‖ * c ^ k`; rewrite with 1.
3. `norm_coeff_mul_rpow_pow_eq_rpow := v.norm_mul_rpow_pow_eq_rpow hγ m k`.
""" + DEC + "L8.1–L8.3.",
  mathlib="`Polynomial.gaussNorm_coe_powerSeries`, `NormedField.toAbsoluteValue`, `Polynomial.exists_eq_gaussNorm`.",
  sources="[RM] convention 11 (\"Polynomial.gaussNorm_coe_powerSeries is the bridge\"), §2.3.3 (\"for a polynomial it is always attained\").",
  gen="`0 ≤ c` as in Mathlib.")

t(id='T048', title='Bounded at `b ^ m` iff the supporting value at `m` is finite', file=GN, deps='T047',
  par='yes (with T063)', typ='theorems', leaves='L8.4–L8.5',
  decls=[(GN, 'hasGaussNorm_rpow_iff'), (GN, 'hasGaussNorm_iff_supportValue_ne_bot')],
  sketch="""1. `hasGaussNorm_rpow_iff := (hasGaussNorm_rpow_iff_exists_line v m).trans (NewtonPolygon.supportValue_ne_bot_iff).symm` (the two line forms coincide syntactically: `∃ y, ∀ k, ↑(y + m k) ≤ coeffVal v f k`).
2. `hasGaussNorm_iff_supportValue_ne_bot`: `rw [← v.rpow_logb hc]` on the left, then 1.
""" + DEC + "L8.4–L8.5.",
  mathlib="`Iff.trans`, `Iff.symm`.",
  sources="[RM] §2.3.2 (\"Prove HasGaussNorm norm c f is equivalent to the supporting value being finite\").",
  gen="Radius form and slope form.")

t(id='T049', title='[M3] The Gauss norm is `b ^ (−s)`: infimum, real and polygon forms', file=GN, deps='CLEANUP-ALL-3',
  par='no', typ='theorems', leaves='L8.6–L8.9', milestone='M3 ([RM] §2.3.1–§2.3.2)',
  decls=[(GN, 'gaussNorm_rpow_eq_of_supportValue_eq'), (GN, 'gaussNorm_rpow_eq_rpow_neg_toReal'), (GN, 'supportValue_coeffVal_eq_neg_logb'), (GN, 'supportValue_newtonPolygon_eq')],
  sketch="""1. `gaussNorm_rpow_eq_of_supportValue_eq` (`hs : supportValue (coeffVal v f) m = ↑s`): `PowerSeries.gaussNorm_eq`; `hbd : HasGaussNorm norm (b^m) f` from T048 (`hs ▸ EReal.coe_ne_bot s`). `le_antisymm`:
   - `ciSup_le fun k ↦ ?_`: if `coeff k f = 0` the term is `0 ≤ b ^ (-s)` (`Real.rpow_nonneg`); else `v (coeff k f) = ↑γ`, `norm_coeff_mul_rpow_pow_eq_rpow`, and `↑s ≤ toEReal (coeffVal v f k) - ↑(mk)` (`supportValue_le`, `hs ▸`) gives `s ≤ e γ - mk` (`EReal.coe_sub`, `EReal.coe_le_coe_iff` after `coeffVal_apply`, `embedTop_coe`, `toEReal_coe`), so `b ^ (mk - eγ) ≤ b ^ (-s)` (`Real.rpow_le_rpow_left_iff v.one_lt_base`, `linarith`).
   - `≥`: `le_of_forall_lt`-style: for `t < b ^ (-s)` write `t < b ^ (-(s+ε))` for some `ε > 0` (continuity of `rpow` in the exponent, or: if `t ≤ 0` trivial since the supremum is `≥ 0`; else `ε := -s - Real.logb b t > 0`), then `↑(s + ε) > supportValue …` so some `k` has `toEReal (coeffVal v f k) - ↑(mk) < ↑(s + ε)` (`iInf_lt_iff`); that `k` has `coeff k f ≠ 0` (else the term is `⊤`), and its term is `b ^ (mk - eγ) > b ^ (-(s+ε)) > t`; `lt_of_lt_of_le _ (le_ciSup hbd k)`.
2. `gaussNorm_rpow_eq_rpow_neg_toReal`: `hs' : supportValue _ m ≠ ⊤` (`supportValue_eq_top_iff` with `exists_coeffVal_ne_top v hf`); `EReal.coe_toReal hs' hs` and 1.
3. `supportValue_coeffVal_eq_neg_logb`: from 2, `Real.logb_rpow v.base_pos v.one_lt_base.ne'`, `neg_neg`, `EReal.coe_toReal`.
4. `supportValue_newtonPolygon_eq := NewtonPolygon.supportValue_newtonPolygon hf m` (T041).
""" + DEC + "L8.6–L8.9 (the sign check of [RM] §2.3.1 is recorded there).",
  mathlib="`PowerSeries.gaussNorm_eq`, `ciSup_le`, `le_ciSup`, `Real.rpow_nonneg`, `Real.rpow_le_rpow_left_iff`, `Real.rpow_lt_rpow_left_iff`, `EReal.coe_ne_bot`, `EReal.coe_sub`, `EReal.coe_le_coe_iff`, `EReal.coe_lt_coe_iff`, `iInf_lt_iff`, `le_of_forall_lt`, `Real.logb_rpow`, `Real.rpow_logb`, `EReal.coe_toReal`, `NewtonPolygon.supportValue_newtonPolygon`, `neg_neg`, `lt_of_lt_of_le`.",
  sources="[Ked07] §2 (Q-Ked-vr, multiplicative reading); [RM] §2.3.1 (\"gaussNorm norm c f = b ^ (-(the supporting value of the polygon at slope m)) … the Gauss norm is the Legendre transform of the polygon … ⚠ Check the sign against a worked example\": `1 − pX`, `m = 2`, Gauss norm `p`, `h 1 − 1·2 = −1`).",
  gen="The infimum form takes the real value `s` as a hypothesis; the `toReal` form takes `s ≠ ⊥` and `f ≠ 0`.")

t(id='T050', title='The attained form: the Gauss norm is the term at the face endpoints', file=GN, deps='CLEANUP-18',
  par='yes (with T063)', typ='theorems', leaves='L8.10–L8.11',
  decls=[(GN, 'gaussNorm_rpow_eq_norm_coeff_faceRight', 0), (GN, 'gaussNorm_rpow_eq_norm_coeff_faceLeft')],
  sketch="""Let `h := newtonPolygon v f`, convex (T021), `h 0 ≠ ⊤` (`newtonPolygon_zero_eq` + `coeffVal_ne_top_iff`).
1. `faceRight`: `R := faceRight h m`; `IsConvexSeq.supportValue_eq_faceRight (isConvexSeq_newtonPolygon v hf) h0' hu m : supportValue h m = toEReal (h R) - ↑(mR)`; `h R = coeffVal v f R` (`(isNewtonPolygonOf_newtonPolygon v hf).eq_of_faceRight h0' hu m`), finite, so `coeff R f ≠ 0`, `v (coeff R f) = ↑γ`; hence `supportValue (coeffVal v f) m = ↑(e γ - mR)` (T049's polygon form, `toEReal_coe`, `EReal.coe_sub`); `gaussNorm_rpow_eq_of_supportValue_eq` gives `b ^ (-(eγ - mR)) = b ^ (mR - eγ) = ‖coeff R f‖ (b^m)^R` (`norm_coeff_mul_rpow_pow_eq_rpow`, `neg_sub`).
2. `faceLeft`: identical with `supportValue_eq_faceLeft`, `eq_of_faceLeft`.
""" + DEC + "L8.10–L8.11.",
  mathlib="`NewtonPolygon.IsConvexSeq.supportValue_eq_faceRight`, `NewtonPolygon.IsConvexSeq.supportValue_eq_faceLeft`, `NewtonPolygon.IsNewtonPolygonOf.eq_of_faceRight`, `NewtonPolygon.IsNewtonPolygonOf.eq_of_faceLeft`, `EReal.coe_sub`, `neg_sub`, `WithTop.ne_top_iff_exists`.",
  sources="[Gou20] pp. 258–259 (Q-Gou-second: \"the maximum is realized at the degree k term\"); [RM] §2.3.1 (\"the attained form … which is the one the later layers use\").",
  gen="`coeff 0 f ≠ 0` (anchored at `0`) and `SlopesUnbounded` — Layer 0's face hypotheses.")

t(id='T051', title='The Gauss norm is attained iff a vertex lies on the supporting line', file=GN, deps='T050',
  par='yes (with T063)', typ='theorem', leaves='L8.12',
  decls=[(GN, 'exists_gaussNorm_rpow_eq_iff')],
  sketch="""`hadm : IsAdmissible (coeffVal v f)` from `hs` (`NewtonPolygon.isAdmissible_iff_exists_supportValue_ne_bot`); `hs' : supportValue _ m ≠ ⊤` (`exists_coeffVal_ne_top v hf`); `r := (supportValue _ m).toReal`, `supportValue _ m = ↑r` (`EReal.coe_toReal`); `gaussNorm = b ^ (-r)` (T049).
Per `k`: `gaussNorm = ‖coeff k f‖ (b^m)^k ↔ toEReal (coeffVal v f k) - ↑(mk) = ↑r`: if `coeff k f = 0` both sides are false (`b ^ (-r) > 0` by `Real.rpow_pos_of_pos`, `norm_zero`; `⊤ - ↑_ = ⊤ ≠ ↑r`); else `v (coeff k f) = ↑γ`, `norm_coeff_mul_rpow_pow_eq_rpow`, injectivity of `t ↦ b ^ t` (`Real.rpow_le_rpow_left_iff` both ways / `le_antisymm_iff`), `EReal.coe_sub`, `EReal.coe_eq_coe_iff`, `sub_eq_iff_eq_add`, `neg_eq_iff_eq_neg`, `linarith`.
Then `exists_congr` this with `NewtonPolygon.IsNewtonPolygonOf.exists_eq_supportValue_iff (isNewtonPolygonOf_newtonPolygon v hadm) ⟨k₀, _⟩ hs` (T044), rewriting `supportValue` by `↑r` where needed.
""" + DEC + "L8.12.",
  mathlib="`NewtonPolygon.isAdmissible_iff_exists_supportValue_ne_bot`, `EReal.coe_toReal`, `Real.rpow_pos_of_pos`, `norm_zero`, `Real.rpow_le_rpow_left_iff`, `le_antisymm_iff`, `EReal.coe_sub`, `EReal.coe_eq_coe_iff`, `EReal.top_sub_coe`, `EReal.top_ne_coe`, `sub_eq_iff_eq_add`, `exists_congr`, `NewtonPolygon.IsNewtonPolygonOf.exists_eq_supportValue_iff`.",
  sources="[RM] §2.3.3; [Gou20] p. 254 (Q-Gou-first).",
  gen="`s ≠ ⊥` (bounded) and `f ≠ 0`.")

t(id='T052', title='`m ↦ −log_b ‖f‖_{b^m}`: concave, piecewise affine, and recovering the polygon', file=GN, deps='T051',
  par='yes (with T063)', typ='theorems', leaves='L8.13–L8.15',
  decls=[(GN, 'concaveOn_neg_logb_gaussNorm'), (GN, 'neg_logb_gaussNorm_eq_of_unitSlope_le_le'), (GN, 'toEReal_newtonPolygon_eq_iSup')],
  sketch="""1. `concaveOn_neg_logb_gaussNorm`: `{m | HasGaussNorm norm (b^m) f} = {m | supportValue (coeffVal v f) m ≠ ⊥}` (`Set.ext`, T048); on it `-Real.logb v.base (gaussNorm norm (b^m) f) = (supportValue _ m).toReal` (T049's `supportValue_coeffVal_eq_neg_logb` read backwards: `EReal.toReal_coe`, `neg_neg`); `(NewtonPolygon.concaveOn_toReal_supportValue).congr` (T045).
2. `neg_logb_gaussNorm_eq_of_unitSlope_le_le`: `hf' : f ≠ 0` (from `hj`: `h (j+1) ≠ ⊤` while `newtonPolygon v 0 = ⊤`); `supportValue (coeffVal v f) m = supportValue h m` (T049 polygon form) `= toEReal (h (j+1)) - ↑(m (j+1))` (`IsConvexSeq.supportValue_eq_of_unitSlope_le_le (isConvexSeq_newtonPolygon v hf) hj h₁ h₂`, T042) `= ↑((h (j+1)).untop₀ - m (j+1))` (`toEReal_of_ne_top hj`, `EReal.coe_sub`); then `supportValue_coeffVal_eq_neg_logb` (with `hs` from this real value, `EReal.coe_ne_bot`) and `EReal.coe_eq_coe_iff`; `Nat.cast_succ`.
3. `toEReal_newtonPolygon_eq_iSup := (NewtonPolygon.iSup_supportValue_add hf k).symm` (T046).
""" + DEC + "L8.13–L8.15.",
  mathlib="`Set.ext`, `EReal.toReal_coe`, `neg_neg`, `ConcaveOn.congr`, `NewtonPolygon.concaveOn_toReal_supportValue`, `NewtonPolygon.IsConvexSeq.supportValue_eq_of_unitSlope_le_le`, `EReal.coe_sub`, `EReal.coe_ne_bot`, `EReal.coe_eq_coe_iff`, `Nat.cast_succ`, `NewtonPolygon.iSup_supportValue_add`.",
  sources="[RM] §2.3.4 (\"m ↦ -log_b (gaussNorm norm (b ^ m) f) is concave and piecewise affine with the unit slopes as its breakpoints — the polygon and the Gauss norm function determine each other\"); [Ked07] §1–§2 (Q-Ked-def, Q-Ked-vr).",
  gen="`f ≠ 0` for the concavity statement (the set is otherwise all of `ℝ` with the junk value `0`); admissibility for the other two.")

t(id='T053', title='Polynomials: finite supporting value, the attained form', file=GN, deps='CLEANUP-19',
  par='yes (with T063)', typ='theorems', leaves='L8.16–L8.17',
  decls=[(GN, 'supportValue_coeffVal_ne_bot'), (GN, 'gaussNorm_rpow_eq_norm_coeff_faceRight', 1)],
  sketch="""1. `supportValue_coeffVal_ne_bot`: `(PowerSeries.hasGaussNorm_rpow_iff v m).mp (hasGaussNorm_coe v (v.base ^ m))` after rewriting `coeffVal_coe`.
2. `gaussNorm_rpow_eq_norm_coeff_faceRight` (polynomial): `rw [← newtonPolygon_coe]`; `PowerSeries.gaussNorm_rpow_eq_norm_coeff_faceRight v hadm h0' hu m` with `hadm` from `isAdmissible_coeffVal v` (through `coeffVal_coe`), `h0'` from `Polynomial.coeff_coe` and `h0`, `hu := slopesUnbounded_newtonPolygon v` (through `newtonPolygon_coe`); finish with `Polynomial.coeff_coe`.
""" + DEC + "L8.16–L8.17.",
  mathlib="`Polynomial.coeff_coe`.",
  sources="[RM] §2.3.1, §2.3.3.",
  gen="`coeff 0 f ≠ 0` for the attained form.")

# ---------------------------------------------------------------- G9 Pure
t(id='T054', title='Pure series: the line controls the coefficients, the Gauss norm is the constant term', file=PU, deps='CLEANUP-20',
  par='yes (with T063)', typ='def API', leaves='L9.1–L9.3',
  defs=[(PU, 'IsPure'), (PU, 'HasFirstBreak')],
  decls=[(PU, 'IsPure.le_coeffVal', 0), (PU, 'IsPure.norm_coeff_mul_rpow_pow_le', 0), (PU, 'IsPure.gaussNorm_rpow_eq')],
  sketch="""The generator prints both the `PowerSeries` and `Polynomial` definitions of `IsPure`/`HasFirstBreak`; this ticket is the `PowerSeries` API.
1. `IsPure.le_coeffVal`: `h := newtonPolygon v f`, `h 0 = coeffVal v f 0` (`newtonPolygon_zero_eq hf h0`), so `anchor h = 0`. For `k` with `h k ≠ ⊤`: `NewtonPolygon.eq_add_nsmul_of_forall_unitSlope_eq (a := 0) (k := k)` with `hp.2` (every unit slope `j < k` is finite, since the finiteness set is an interval containing `0` and `k`, hence `= ↑m`) gives `h k = h 0 + k • ↑m`; `newtonPolygon_le hf k` and `WithTop.coe_nsmul`, `nsmul_eq_mul`, `mul_comm`. For `h k = ⊤`: `coeffVal v f k = ⊤` (`top_le_iff.mp (newtonPolygon_le hf k ▸ le_top)`), `le_top`.
2. `IsPure.norm_coeff_mul_rpow_pow_le`: `v.norm_mul_rpow_pow_le_iff (coeff k f) (coeff 0 f) m k 0` (T005) with `pow_zero`, `mul_one`, `Nat.cast_zero`, `sub_zero`, and 1.
3. `IsPure.gaussNorm_rpow_eq`: `gaussNorm_eq`; `le_antisymm (ciSup_le (fun k ↦ by simpa using IsPure.norm_coeff_mul_rpow_pow_le …))`; `≥`: `le_ciSup hbd 0` with the term at `0` being `‖coeff 0 f‖` (`pow_zero`, `mul_one`) and `hbd` from 2 (`bddAbove_def`).
""" + DEC + "L9.1–L9.3.",
  mathlib="`NewtonPolygon.eq_add_nsmul_of_forall_unitSlope_eq`, `NewtonPolygon.IsPure`, `WithTop.coe_nsmul`, `nsmul_eq_mul`, `mul_comm`, `top_le_iff`, `le_top`, `pow_zero`, `mul_one`, `Nat.cast_zero`, `sub_zero`, `PowerSeries.gaussNorm_eq`, `ciSup_le`, `le_ciSup`, `bddAbove_def`.",
  sources="[Gou20] Definition 7.4.1 (Q-Gou-D741); [Gou20] p. 254 (Q-Gou-first: \"there are no points below the line y = mx\"); [RM] §2.4.1.",
  gen="Series with `coeff 0 f ≠ 0` (anchored at `0`) and an admissible sequence.")

t(id='T055', title='Purity of a genuine series in Gauss-norm terms', file=PU, deps='T054',
  par='yes (with T063)', typ='theorem', leaves='L9.4',
  decls=[(PU, 'isPure_iff_of_infinite')],
  sketch="""`h := newtonPolygon v f`, convex, `h 0 = coeffVal v f 0 ≠ ⊤`. Infinite support: every `h k ≠ ⊤` (if `h k = ⊤` for some `k` then `coeffVal v f j = ⊤` for all `j ≥ k` by `IsConvexSeq.eq_top_of_le` + `newtonPolygon_le`, contradicting `hinf` — `Set.Infinite.exists_gt`).
(→) first clause: T054. Second: for `c > b^m` write `c = b ^ m'` (`v.rpow_logb`), `m' > m` (`Real.rpow_lt_rpow_left_iff`); if `HasGaussNorm norm c f`, T017 gives `y` with `↑(y + m' k) ≤ coeffVal v f k`, hence `≤ h k` (`IsNewtonPolygonOf.line_le`), and `h k = h 0 + k • ↑m` (pure, as in T054); so `y + m' k ≤ η + m k` for all `k` (`WithTop.coe_le_coe`), i.e. `(m' - m) k ≤ η - y`, false for `k` large (`exists_nat_gt`, `linarith`).
(←) `⟨hle, hunb⟩`. The line `L k := ↑(η + m k)` is below the points (`hle` via `v.norm_mul_rpow_pow_le_iff`) hence below `h` (`line_le`), and `L 0 = h 0`. Unit slopes are `≥ m`: if `unitSlope h j < ↑m` for some `j`, by `IsConvexSeq.monotoneOn` all `i ≤ j` have `unitSlope h i < m` and `NewtonPolygon.eq_add_sum_unitSlope` gives `h (j+1) < η + m (j+1) = L (j+1) ≤ h (j+1)`, contradiction. If some unit slope is `> m`, let `j := Nat.find` the least; unit slopes `= m` before `j`, `≥ unitSlope h j` after; pick `m' ∈ (m, (unitSlope h j).untop₀)` (`exists_between`); `IsConvexSeq.line_le_iff hh (hj) m'` (←) holds, so the line of slope `m'` through `(j, h j)` is below `h` hence below the points: `HasGaussNorm norm (b ^ m') f` by T017 (←), with `b ^ m' > b ^ m` (`Real.rpow_lt_rpow_left_iff`), contradicting `hunb`. Hence every unit slope is `m`; one exists (`h 0`, `h 1` finite): `IsPure`.
""" + DEC + "L9.4 (plan D5).",
  mathlib="`NewtonPolygon.IsConvexSeq.eq_top_of_le`, `Set.Infinite.exists_gt`, `Real.rpow_lt_rpow_left_iff`, `NewtonPolygon.IsNewtonPolygonOf.line_le`, `WithTop.coe_le_coe`, `exists_nat_gt`, `NewtonPolygon.IsConvexSeq.monotoneOn`, `NewtonPolygon.eq_add_sum_unitSlope`, `Nat.find`, `Nat.find_spec`, `Nat.find_min'`, `exists_between`, `NewtonPolygon.IsConvexSeq.line_le_iff`, `NewtonPolygon.IsPure`, `WithTop.ne_top_iff_exists`, `WithTop.coe_untop₀_of_ne_top`.",
  sources="[Kob84] IV §4 (Q-Kob-ps, cases (2)–(3)); [Gou20] p. 261 (Q-Gou-ex1); [RM] §2.4.1 corrected (plan D5).",
  gen="Series with infinitely many nonzero coefficients; the polynomial case is T060.")

t(id='T056', title='The first break: line bounds (`≥` everywhere, `=` at the break, `>` beyond)', file=PU, deps='T055',
  par='yes (with T063)', typ='theorems', leaves='L9.5–L9.8',
  decls=[(PU, 'HasFirstBreak.le_coeffVal'), (PU, 'HasFirstBreak.coeffVal_eq'), (PU, 'HasFirstBreak.lt_coeffVal'), (PU, 'HasFirstBreak.coeff_ne_zero')],
  sketch="""`hh := isNewtonPolygonOf_newtonPolygon v hf`; `hb` unfolds to `NewtonPolygon.HasFirstBreak (newtonPolygon v f) m l`; `(hh.hasFirstBreak_iff ⟨0, _⟩ m l).mp hb` gives `0 < l`, (A) `∀ k ≥ anchor h, v (anchor h) + (k - anchor h) • ↑m ≤ coeffVal v f k`, (B) `coeffVal v f (anchor h + l) = coeffVal v f (anchor h) + l • ↑m`, (C) `∃ m' > m, ∀ k ≥ anchor h + l, coeffVal v f (anchor h + l) + (k - (anchor h + l)) • ↑m' ≤ coeffVal v f k`. The anchor is `0`: `hh.anchor_eq_sInf` and `Nat.sInf_eq_zero` with `0 ∈ finiteSupport` (`coeffVal_ne_top_iff.mpr h0`), or `le_antisymm (anchor_le h0') (zero_le _)`.
1. `le_coeffVal k`: (A) at `k` (`zero_le`), `Nat.sub_zero`, `WithTop.coe_nsmul`, `nsmul_eq_mul`, `mul_comm`.
2. `coeffVal_eq`: (B) with `zero_add`.
3. `lt_coeffVal hk`: (C) at `k`: `coeffVal v f k ≥ coeffVal v f l + (k - l) • ↑m'`; with (B), `coeffVal v f l = ↑(η + m l)` finite, so the right side is `↑(η + m l + (k - l) m')` and `η + m l + (k - l) m' > η + m k` since `m' > m`, `k > l` (`Nat.cast_sub hk.le`, `mul_lt_mul_of_pos_left`, `linarith`); `lt_of_lt_of_le` with `WithTop.coe_lt_coe`.
4. `coeff_ne_zero`: 2 gives `coeffVal v f l = ↑η + ↑(m l) ≠ ⊤` (`WithTop.add_ne_top`, `WithTop.coe_ne_top`), `coeffVal_ne_top_iff`.
""" + DEC + "L9.5–L9.8 (plan D6).",
  mathlib="`NewtonPolygon.IsNewtonPolygonOf.hasFirstBreak_iff`, `NewtonPolygon.HasFirstBreak`, `NewtonPolygon.IsNewtonPolygonOf.anchor_eq_sInf`, `Nat.sInf_eq_zero`, `NewtonPolygon.anchor_le`, `zero_le`, `Nat.sub_zero`, `WithTop.coe_nsmul`, `nsmul_eq_mul`, `mul_comm`, `zero_add`, `Nat.cast_sub`, `mul_lt_mul_of_pos_left`, `WithTop.coe_lt_coe`, `lt_of_lt_of_le`, `WithTop.add_ne_top`, `WithTop.coe_ne_top`.",
  sources="[Gou20] p. 254 (Q-Gou-first: \"v_p(a_j) ≥ mj for every j … v_p(a_i) = mi … v_p(a_j) > mj if j > i\"); [RM] §2.4.2 corrected (plan D6).",
  gen="Series with `coeff 0 f ≠ 0` and an admissible sequence; the break length `l` is Layer 0's.")

t(id='T057', title='The first break in Gauss-norm terms', file=PU, deps='CLEANUP-21',
  par='yes (with T063)', typ='theorems', leaves='L9.9–L9.12',
  decls=[(PU, 'HasFirstBreak.norm_coeff_mul_rpow_pow_le'), (PU, 'HasFirstBreak.norm_coeff_mul_rpow_pow_eq'), (PU, 'HasFirstBreak.norm_coeff_mul_rpow_pow_lt'), (PU, 'HasFirstBreak.gaussNorm_rpow_eq')],
  sketch="""1–3. `v.norm_mul_rpow_pow_le_iff / _eq_iff / _lt_iff (coeff k f) (coeff 0 f) m k 0` (T005) with `pow_zero`, `mul_one`, `Nat.cast_zero`, `sub_zero`, and T056's `le_coeffVal` / `coeffVal_eq` / `lt_coeffVal` (for `_eq_iff` the right-hand side is `coeffVal v f l = coeffVal v f 0 + ↑(m l)`).
4. `gaussNorm_rpow_eq`: as T054's `IsPure.gaussNorm_rpow_eq` with 1 for the bound and the term at `0`.
""" + DEC + "L9.9–L9.12.",
  mathlib="`pow_zero`, `mul_one`, `Nat.cast_zero`, `sub_zero`, `PowerSeries.gaussNorm_eq`, `ciSup_le`, `le_ciSup`, `bddAbove_def`.",
  sources="[Gou20] p. 254 (Q-Gou-first: \"|a_j|(p^m)^j ≤ 1 … = 1 … < 1 if j > i … ‖f(X)‖_c = 1\").",
  gen="As T056.")

t(id='T058', title='Polynomials: purity and first breaks through the coercion; the leading term', file=PU, deps='T057',
  par='yes (with T063)', typ='theorems', leaves='L9.13–L9.17',
  decls=[(PU, 'isPure_coe_iff'), (PU, 'hasFirstBreak_coe_iff'), (PU, 'IsPure.le_coeffVal', 1), (PU, 'IsPure.norm_coeff_mul_rpow_pow_le', 1), (PU, 'IsPure.norm_coeff_natDegree_mul_rpow_pow_eq')],
  sketch="""1. `isPure_coe_iff`, `hasFirstBreak_coe_iff`: unfold both sides and `rw [newtonPolygon_coe]` (`Iff.rfl`).
2. `IsPure.le_coeffVal`, `IsPure.norm_coeff_mul_rpow_pow_le`: `(isPure_coe_iff v).mpr hp` and the series lemmas (T054) with `hadm` from `isAdmissible_coeffVal v` (via `coeffVal_coe`), `h0` via `Polynomial.coeff_coe`; rewrite `coeffVal_coe`, `Polynomial.coeff_coe`.
3. `IsPure.norm_coeff_natDegree_mul_rpow_pow_eq`: `d := natDegree f`, `f ≠ 0` (`h0`); `h d = coeffVal v f d` (`newtonPolygon_natDegree`), `h 0 = coeffVal v f 0`, and `h d = h 0 + d • ↑m` (`NewtonPolygon.eq_add_nsmul_of_forall_unitSlope_eq` with `hp.2`: the unit slopes on `[0, d)` are finite (`slopeIndices_newtonPolygon`) hence `= m`); so `coeffVal v f d = coeffVal v f 0 + ↑(m d)`; `v.norm_mul_rpow_pow_eq_iff` at `j = 0` (T005).
""" + DEC + "L9.13–L9.17.",
  mathlib="`Iff.rfl`, `Polynomial.coeff_coe`, `NewtonPolygon.eq_add_nsmul_of_forall_unitSlope_eq`, `WithTop.coe_nsmul`, `nsmul_eq_mul`, `mul_comm`, `pow_zero`, `mul_one`.",
  sources="[Gou20] Definition 7.4.1 and remark (Q-Gou-D741: \"|b_n|c^n = 1\").",
  gen="`coeff 0 f ≠ 0`.")

t(id='T059', title='Purity from the bounds (the chord argument)', file=PU, deps='T058',
  par='yes (with T063)', typ='theorem', leaves='L9.18',
  decls=[(PU, 'isPure_of_bounds')],
  sketch="""`d := natDegree f`, `η := (coeffVal v f 0).untop₀` (finite by `h0`), `L := (Set.Iic d).piecewise (NewtonPolygon.affineFrom 0 η m) ⊤` (the line through `(0, η)` of slope `m` on `[0, d]`, `⊤` beyond).
1. `L` is convex: `isConvexSeq_affineFrom`, `IsConvexSeq.piecewise_top` with `Set.ordConnected_Iic`.
2. `L ≤ coeffVal v f`: for `k ≤ d`, `↑(η + m k) ≤ coeffVal v f k` is `hle k` through `v.norm_mul_rpow_pow_le_iff … k 0` (T005; `affineFrom_of_le`, `Nat.cast_zero`, `sub_zero`); for `k > d`, `L k = ⊤`? — no: `L k = ⊤` must be `≤ coeffVal v f k`, which holds because `coeff k f = 0` (`Polynomial.coeff_eq_zero_of_natDegree_lt`), `coeffVal_eq_top_iff`.
3. Greatest: for a convex `g ≤ coeffVal v f`: `g 0 ≤ coeffVal v f 0 = L 0`, `g d ≤ coeffVal v f d = L d` (`heq` via `v.norm_mul_rpow_pow_eq_iff … d 0`), and for `0 ≤ k ≤ d`, `IsConvexSeq.le_chord hg (zero_le k) hkd : (d - 0) • g k ≤ (d - k) • g 0 + k • g d ≤ (d - k) • L 0 + k • L d = d • L k` (`WithTop` nsmul arithmetic; `Nat.card_Ico`, `WithTop.coe_nsmul`, `nsmul_eq_mul`, the affine identity `(d - k) η + k (η + m d) = d (η + m k)` by `ring`), so `g k ≤ L k` (`nsmul_le_nsmul_iff_left`-style: divide by `d > 0` — `WithTop.coe_le_coe` after rewriting; `hd : 0 < d`). Beyond `d`, `L k = ⊤`.
4. Hence `IsNewtonPolygonOf (coeffVal v f) L`, so `newtonPolygon v f = L` (`IsNewtonPolygonOf.eq_newtonPolygon`, symm). `IsPure`: unit slopes of `L` on `[0, d)` are `↑m` (`unitSlope_affineFrom`, `Set.piecewise_eq_of_mem`), `⊤` from `d` on; existence from `hd` (`unitSlope L 0 ≠ ⊤`).
""" + DEC + "L9.18. [SRC] `FirstBreak.isPureSeries_of_bounds` is the same argument on the legacy structure. " + SRC_NOTE,
  mathlib="`Set.piecewise`, `Set.piecewise_eq_of_mem`, `Set.piecewise_eq_of_notMem`, `Set.ordConnected_Iic`, `NewtonPolygon.affineFrom`, `NewtonPolygon.affineFrom_of_le`, `NewtonPolygon.isConvexSeq_affineFrom`, `NewtonPolygon.unitSlope_affineFrom`, `NewtonPolygon.IsConvexSeq.piecewise_top`, `NewtonPolygon.IsConvexSeq.le_chord`, `NewtonPolygon.IsNewtonPolygonOf.eq_newtonPolygon`, `Polynomial.coeff_eq_zero_of_natDegree_lt`, `Nat.card_Ico`, `WithTop.coe_nsmul`, `nsmul_eq_mul`, `WithTop.coe_le_coe`, `WithTop.coe_untop₀_of_ne_top`, `NewtonPolygon.IsPure`.",
  sources="[Gou20] Problem 341 (Q-Gou-D741, ⇐); [RM] §2.4.1.",
  gen="`coeff 0 f ≠ 0`, `0 < natDegree f`; collinear interior points allowed (plan D5).")

t(id='T060', title='Purity of a polynomial: the three characterisations', file=PU, deps='CLEANUP-22',
  par='yes (with T063)', typ='theorems', leaves='L9.19–L9.21',
  decls=[(PU, 'isPure_iff'), (PU, 'isPure_iff_gaussNorm'), (PU, 'isPure_iff_hasFirstBreak')],
  sketch="""1. `isPure_iff`: `⟨fun hp ↦ ⟨hp.norm_coeff_mul_rpow_pow_le v h0, hp.norm_coeff_natDegree_mul_rpow_pow_eq v h0⟩, fun ⟨hle, heq⟩ ↦ isPure_of_bounds v h0 hd hle heq⟩` (T058, T059).
2. `isPure_iff_gaussNorm` (`h0 : coeff 0 = 1`): `h0' : f.coeff 0 ≠ 0`; `‖f.coeff 0‖ = 1` (`norm_one`). (→) `IsPure.gaussNorm_rpow_eq` (via `isPure_coe_iff`, T054) gives `gaussNorm = ‖coeff 0‖ = 1`, and `norm_coeff_natDegree_mul_rpow_pow_eq` gives the other. (←) every term `≤ gaussNorm = 1 = ‖coeff 0‖` (`PowerSeries.le_gaussNorm` with `hasGaussNorm_coe`, `Polynomial.coeff_coe`) and `‖coeff d‖ c^d = 1`: `isPure_of_bounds`.
3. `isPure_iff_hasFirstBreak`: `hf : f ≠ 0`; `anchor h = 0` (`anchor_newtonPolygon v hf`, `Polynomial.natTrailingDegree_eq_zero`-style: `natTrailingDegree f = 0` from `h0`, `Polynomial.natTrailingDegree_le_of_ne_zero h0`); `NewtonPolygon.HasFirstBreak` unfolds to `0 < d ∧ (∀ j < d, unitSlope h (0 + j) = ↑m) ∧ unitSlope h (0 + d) ≠ ↑m`; `slopeIndices_newtonPolygon v hf` says the finite unit slopes are exactly `j < d`, and `unitSlope h d = ⊤` (`mem_slopeIndices_iff` negated), `WithTop.top_ne_coe`. Both directions are this bookkeeping (`zero_add`).
""" + DEC + "L9.19–L9.21.",
  mathlib="`norm_one`, `PowerSeries.le_gaussNorm`, `Polynomial.coeff_coe`, `Polynomial.natTrailingDegree_le_of_ne_zero`, `NewtonPolygon.HasFirstBreak`, `NewtonPolygon.IsPure`, `NewtonPolygon.mem_slopeIndices_iff`, `WithTop.top_ne_coe`, `zero_add`, `Nat.le_zero`.",
  sources="[Gou20] Problem 341 (Q-Gou-D741); [Gou20] p. 252 (Q-Gou-feat); [RM] §2.4.1.",
  gen="`coeff 0 f ≠ 0` (resp. `= 1`) and `0 < natDegree f`.")

# ---------------------------------------------------------------- G10 Distinguished
t(id='T061', title='Distinguished series: the unit clause is automatic; first break ⟹ distinguished; degree = `faceRight`', file=DI, deps='CLEANUP-23',
  par='yes (with T063)', typ='theorems', leaves='L10.1–L10.3',
  decls=[(DI, 'isMulDistinguished_iff'), (DI, 'HasFirstBreak.isMulDistinguished', 0), (DI, 'isMulDistinguished_rpow_iff_faceRight_eq', 0)],
  sketch="""1. `isMulDistinguished_iff`: (→) `⟨h.gaussNorm_eq, h.gaussTerm_lt⟩`. (←) `⟨?unit, h₁, h₂⟩`: from `h₂ (i+1) (lt_add_one i)` and `mul_nonneg (norm_nonneg _) (pow_nonneg … )` (if `c ^ (i+1) < 0` the inequality still forces `0 < ‖coeff i f‖ * c ^ i`, since the left side is `≥ 0` when `c ≥ 0`; for `c < 0` argue `‖coeff i f‖ ≠ 0` from `h₂` with `i + 2` as well — or simply: `‖coeff i f‖ * c ^ i ≠ 0` because `x < y` with `x = ‖a‖ c^{i+1}` and `y = ‖a_i‖ c^i`, and `y = 0` would need `x < 0`, i.e. `‖coeff (i+1) f‖ c^{i+1} < 0`, impossible when `c ≥ 0`; **state and use `0 ≤ c`? no — the skeleton has no such hypothesis.** Route: if `‖coeff i f‖ = 0` then `y = 0`, and `h₂ (i+1)` reads `‖a_{i+1}‖ c^{i+1} < 0`, while `h₂ (i+2)` reads `‖a_{i+2}‖ c^{i+2} < 0`; multiplying, `c^{i+1}` and `c^{i+2}` are both negative, impossible (`c^{i+2} = c · c^{i+1}` with `c < 0` gives `c^{i+2} > 0`). Simpler: `‖coeff (i+1) f‖ * c ^ (i+1) < 0` and `‖coeff (i+2) f‖ * c ^ (i+2) < 0` force `c^(i+1) < 0` and `c^(i+2) < 0` (`mul_neg_iff`, `norm_nonneg`), but `c ^ (i+2) = c ^ (i+1) * c` and the signs of `c^(i+1)`, `c` cannot both make this negative (`pow_succ`, `mul_neg_iff`, `pow_lt_zero`-free case analysis). Then `coeff i f ≠ 0` (`norm_ne_zero_iff`), `isUnit_iff_ne_zero.mpr`, `IsUnit.isNormMulUnit` ([RAG], `NormMulClass K`).
2. `HasFirstBreak.isMulDistinguished`: `(isMulDistinguished_iff).mpr ⟨_, _⟩`: `gaussNorm = ‖coeff 0 f‖` (T057 `gaussNorm_rpow_eq`) `= ‖coeff l f‖ (b^m)^l` (T057 `norm_coeff_mul_rpow_pow_eq`, symm); for `t > l`, `‖coeff t f‖ (b^m)^t < ‖coeff 0 f‖ = ‖coeff l f‖ (b^m)^l` (T057 `_lt`).
3. `isMulDistinguished_rpow_iff_faceRight_eq`: `R := faceRight h m`, `h := newtonPolygon v f` convex, `h 0 ≠ ⊤`. Facts: (a) `gaussNorm norm (b^m) f = ‖coeff R f‖ (b^m)^R` (T050); (b) for `t > R`: `h t > h R + (t - R) m` (`IsConvexSeq.faceRight_line_lt`), `coeffVal v f t ≥ h t` (`newtonPolygon_le`), `h R = coeffVal v f R` (`eq_of_faceRight`), so `‖coeff t f‖ (b^m)^t < ‖coeff R f‖ (b^m)^R` (`v.norm_mul_rpow_pow_lt_iff`). (←) `rfl ▸ (isMulDistinguished_iff).mpr ⟨a, b⟩`. (→) `hd : IsMulDistinguished (b^m) f i`; `rcases lt_trichotomy i R`: `i < R`: `hd.gaussTerm_lt R hiR : ‖a_R‖c^R < ‖a_i‖c^i = gaussNorm = ‖a_R‖c^R` (`hd.gaussNorm_eq`, (a)), `lt_irrefl`; `R < i`: (b) at `t := i` gives `‖a_i‖c^i < ‖a_R‖c^R = gaussNorm = ‖a_i‖c^i`, `lt_irrefl`; `i = R` ✓.
""" + DEC + "L10.1–L10.3.",
  mathlib="`PowerSeries.IsMulDistinguished`, `PowerSeries.IsMulDistinguished.gaussNorm_eq`, `PowerSeries.IsMulDistinguished.gaussTerm_lt`, `PowerSeries.IsMulDistinguished.isNormMulUnit_coeff`, `IsUnit.isNormMulUnit`, `isUnit_iff_ne_zero`, `norm_ne_zero_iff`, `mul_neg_iff`, `norm_nonneg`, `pow_succ`, `lt_add_one`, `NewtonPolygon.IsConvexSeq.faceRight_line_lt`, `NewtonPolygon.IsNewtonPolygonOf.eq_of_faceRight`, `lt_trichotomy`, `lt_irrefl`.",
  sources="[BGR] 5.2.1/1 (Q-BGR-521: \"|g_s| = |g| and |g_s| > |g_ν| for all ν > s\"); [Gou20] Proposition 7.2.3 (Q-Gou-P723) and p. 254 (Q-Gou-first: \"i is the largest integer such that …\"); [Ked07] Cor. 2 proof (Q-Ked-C2); [SRC] `FirstBreak.isMulDistinguished_of_hasFirstBreak`. " + SRC_NOTE,
  gen="`IsMulDistinguished` over any `NormedCommRing`; here `K` a normed field, where the unit clause is automatic (T061.1 needs no sign hypothesis on `c` — the strict domination of two later terms excludes `c < 0` with `‖coeff i f‖ = 0`). `hu` for the face.")

t(id='T062', title='[M4] Polynomials: first break ⟹ distinguished; pure ⟹ distinguished of its degree; degree = `faceRight`', file=DI, deps='CLEANUP-ALL-4',
  par='no', typ='theorems', leaves='L10.4–L10.6', milestone='M4 ([RM] §2.4.3)',
  decls=[(DI, 'HasFirstBreak.isMulDistinguished', 1), (DI, 'IsPure.isMulDistinguished'), (DI, 'isMulDistinguished_rpow_iff_faceRight_eq', 1)],
  sketch="""1. `Polynomial.HasFirstBreak.isMulDistinguished`: `(hasFirstBreak_coe_iff v).mpr hb` (T058) and `PowerSeries.HasFirstBreak.isMulDistinguished v hadm h0' hb'` (T061) with `hadm` from `isAdmissible_coeffVal v` via `coeffVal_coe` and `h0'` via `Polynomial.coeff_coe`.
2. `IsPure.isMulDistinguished`: `(isPure_iff_hasFirstBreak v h0 hd).mp hp` (T060) then 1.
3. `Polynomial.isMulDistinguished_rpow_iff_faceRight_eq`: `rw [← newtonPolygon_coe]`; `PowerSeries.isMulDistinguished_rpow_iff_faceRight_eq v hadm h0' (slopesUnbounded_newtonPolygon v …)` (T061) with `newtonPolygon_coe` for the `SlopesUnbounded` hypothesis.
""" + DEC + "L10.4–L10.6.",
  mathlib="`Polynomial.coeff_coe`.",
  sources="[RM] §2.4.3 (\"a polynomial whose first break is at index i with slope m is distinguished at radius c = b ^ m of degree i, in the sense that its Gauss norm at c is attained at i and nowhere later\"); [Gou20] (Q-Gou-first, Q-Gou-P723).",
  gen="`coeff 0 f ≠ 0`; no `SlopesUnbounded` hypothesis for polynomials (automatic).")

# ---------------------------------------------------------------- G11 Padic
t(id='T063', title='`Padic.normedAddValuation`: `v p = 1`, base `p`, the cast embedding', file=PA, deps='CLEANUP-3',
  par='yes (with T016–T062)', typ='def API', leaves='L11.1–L11.6',
  defs=[(PA, 'normedAddValuation')],
  decls=[(PA, 'normedAddValuation_apply'), (PA, 'normedAddValuation_embed'), (PA, 'normedAddValuation_embed_apply'), (PA, 'normedAddValuation_base'), (PA, 'normedAddValuation_natCast_prime'), (PA, 'scale_normedAddValuation_ofNormAddVal')],
  sketch="""`normedAddValuation p = ofNormAddValZ ℚ_[p] isUniformizer_p` (no `sorry`).
1. `normedAddValuation_apply`: `show normAddValZ ℚ_[p] x = _` (`ofNormAddValZ_apply`), `NormedField.normAddValZ_padic_apply`.
2. `normedAddValuation_embed := rfl` (`ofNormAddValZ_embed`); `normedAddValuation_embed_apply`: `rw [normedAddValuation_embed]`, `Int.coe_castAddHom` (or `Int.castAddHom` unfolds by `rfl`).
3. `normedAddValuation_base`: `show ‖(p : ℚ_[p])‖⁻¹ = p` (`ofNormAddValZ_base`), `Padic.norm_p`, `inv_inv`.
4. `normedAddValuation_natCast_prime := ofNormAddValZ_apply_isUniformizer ℚ_[p] Padic.isUniformizer_p` (T008).
5. `scale_normedAddValuation_ofNormAddVal`: `scale_ofNormAddValZ_ofNormAddVal ℚ_[p] Padic.isUniformizer_p` (T008) gives `-Real.log ‖(p : ℚ_[p])‖`; `Padic.norm_p`, `Real.log_inv`, `neg_neg`.
""" + DEC + "L11.1–L11.6.",
  mathlib="`NormedField.normAddValZ_padic_apply`, `Int.coe_castAddHom`, `Padic.norm_p`, `inv_inv`, `Padic.isUniformizer_p`, `Real.log_inv`, `neg_neg`.",
  sources="[RM] Acceptance (\"normAddValZ ℚ_[p] = Padic.addValuation\"), Examples (\"normAddValZ p = 1 … normAddVal ℚ_[p] is log p times normAddValZ\"), §2.2.8.",
  gen="Any prime `p` (`[Fact p.Prime]`).")

# ---------------------------------------------------------------- G12 Examples
t(id='T064', title='Examples: `1 − X` (slope `0`) and `1 − pX` (slope `1`)', file=EXA, deps='CLEANUP-14, CLEANUP-24, CLEANUP-25',
  par='no', typ='examples', leaves='L12.1–L12.4',
  decls=[(EXA, 'isPure_one_sub_X'), (EXA, 'newtonSlopes_one_sub_X'), (EXA, 'isPure_one_sub_p_mul_X'), (EXA, 'newtonSlopes_one_sub_p_mul_X')],
  sketch="""`𝓥 := Padic.normedAddValuation p`, base `p` (T063).
1. `isPure_one_sub_X`: `isPure_of_bounds 𝓥 (h0 : (1 - X).coeff 0 ≠ 0) (hd : 0 < natDegree (1 - X)) hle heq` at `m = 0`: `(𝓥.base) ^ (0:ℝ) = 1` (`Real.rpow_zero`), `one_pow`, `mul_one`. Coefficients: `Polynomial.coeff_sub`, `coeff_one`, `coeff_X` — `coeff 0 = 1`, `coeff 1 = -1`, else `0` (`norm_one`, `norm_neg`, `norm_zero`). `natDegree (1 - X) = 1`: `Polynomial.natDegree_sub_eq_right_of_natDegree_lt` (`natDegree_one`, `natDegree_X`) or `Polynomial.natDegree_X_sub_C`-style after `← neg_sub`, `natDegree_neg`.
2. `newtonSlopes_one_sub_X`: `NewtonPolygon.isPure_iff_slopeMultiset (slopeIndices_newtonPolygon_finite 𝓥) 0 |>.mp` (unfold `IsPure`, `newtonSlopes_def`) gives `slopeMultiset = Multiset.replicate card 0`; `card_newtonSlopes`: `natDegree = 1`, `natTrailingDegree = 0` (`Polynomial.natTrailingDegree_le_of_ne_zero` at index `0`, `Nat.le_zero`); `Multiset.replicate_one`.
3. `isPure_one_sub_p_mul_X`, `newtonSlopes_one_sub_p_mul_X`: as 1–2 with `coeff 1 = -(p : ℚ_[p])` (`Polynomial.coeff_C_mul`, `coeff_X`), `‖-p‖ * (p ^ (1:ℝ)) ^ 1 = p⁻¹ * p = 1` (`norm_neg`, `Padic.norm_p`, `Real.rpow_one`, `pow_one`, `inv_mul_cancel₀`, `Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero`), `natDegree (1 - C p * X) = 1` (`Polynomial.natDegree_C_mul_X` with `p ≠ 0`).
""" + DEC + "L12.1–L12.4.",
  mathlib="`Real.rpow_zero`, `Real.rpow_one`, `one_pow`, `pow_one`, `mul_one`, `Polynomial.coeff_sub`, `Polynomial.coeff_one`, `Polynomial.coeff_X`, `Polynomial.coeff_C_mul`, `norm_one`, `norm_neg`, `norm_zero`, `Polynomial.natDegree_sub_eq_right_of_natDegree_lt`, `Polynomial.natDegree_one`, `Polynomial.natDegree_X`, `Polynomial.natDegree_C_mul_X`, `NewtonPolygon.isPure_iff_slopeMultiset`, `Multiset.replicate_one`, `Polynomial.natTrailingDegree_le_of_ne_zero`, `Nat.le_zero`, `Padic.norm_p`, `inv_mul_cancel₀`, `Nat.cast_ne_zero`, `Nat.Prime.ne_zero`.",
  sources="[RM] Examples and Acceptance (\"The polygon of 1 - X is the single unit segment of slope 0, and 1 - pX has slope 1\").",
  gen="Any prime `p`.")

t(id='T065', title='Example: `1 + pX + p³X²` has slopes `{1, 2}`', file=EXA, deps='T064',
  par='no', typ='example', leaves='L12.5',
  decls=[(EXA, 'newtonSlopes_one_add_p_mul_X_add_p_cube_mul_X_sq')],
  sketch="""`f := 1 + C p * X + C (p^3) * X^2`. Coefficients: `coeff 0 = 1`, `coeff 1 = p`, `coeff 2 = p^3`, else `0` (`Polynomial.coeff_add`, `coeff_one`, `coeff_C_mul`, `coeff_X`, `coeff_X_pow`; `simp` with `Polynomial.coeff_C_mul_X_pow`). Heights: `coeffVal 𝓥 f = w` with `w := (0, 1, 3, ⊤, …)` (`coeffVal_apply`, `Padic.normedAddValuation_apply`, `Padic.addValuation.apply`, `Padic.valuation_one`, `Padic.valuation_p`, `Padic.valuation_pow`, `Padic.normedAddValuation_embed_apply`; `funext`, `match k` on `0, 1, 2, k+3`). `w` is convex: `NewtonPolygon.isConvexSeq_iff_midpoint` or directly `⟨ordConnected of Iic 2, monotoneOn of (1, 2, ⊤, …)⟩` (`unitSlope_nat`, `WithTop` arithmetic), so `newtonPolygon 𝓥 f = w` (`newtonPolygon_def`, `NewtonPolygon.newtonPolygon_eq_self`). `slopeIndices w = {0, 1}` (`mem_slopeIndices_iff`), `slopeMultiset w = {1, 2}`: unfold `slopeMultiset` (`dif_pos`), `Set.Finite.toFinset` of `{0, 1}` is `{0, 1}` (`Set.toFinset_insert`, `Set.toFinset_singleton`), `Multiset.insert_eq_cons`, `Multiset.map_cons`, `Multiset.map_singleton`, `unitSlope_nat`, `WithTop.untop₀_coe`.
""" + DEC + "L12.5.",
  mathlib="`Polynomial.coeff_add`, `Polynomial.coeff_one`, `Polynomial.coeff_C_mul`, `Polynomial.coeff_X`, `Polynomial.coeff_X_pow`, `Polynomial.coeff_C_mul_X_pow`, `Padic.addValuation.apply`, `Padic.valuation_one`, `Padic.valuation_p`, `Padic.valuation_pow`, `NewtonPolygon.isConvexSeq_iff_midpoint`, `NewtonPolygon.newtonPolygon_eq_self`, `NewtonPolygon.mem_slopeIndices_iff`, `NewtonPolygon.slopeMultiset`, `NewtonPolygon.unitSlope_nat`, `Set.toFinset_insert`, `Set.toFinset_singleton`, `Multiset.insert_eq_cons`, `Multiset.map_cons`, `Multiset.map_singleton`, `WithTop.untop₀_coe`.",
  sources="[RM] Examples (\"1 + pX + p³X² (slopes 1, 2)\"), Acceptance.",
  gen="Any prime `p`.")

t(id='T066', title='Example: the collinear `1 + pX + p²X²`', file=EXA, deps='T065',
  par='no', typ='examples', leaves='L12.6–L12.8',
  decls=[(EXA, 'newtonPolygon_one_add_p_mul_X_add_p_sq_mul_X_sq_one'), (EXA, 'not_isVertex_one_add_p_mul_X_add_p_sq_mul_X_sq_one'), (EXA, 'newtonSlopes_one_add_p_mul_X_add_p_sq_mul_X_sq')],
  sketch="""As T065 with `w := (0, 1, 2, ⊤, …)`, convex (affine on `[0, 2]`), so `newtonPolygon 𝓥 f = coeffVal 𝓥 f` (`newtonPolygon_eq_self`), which gives the first statement at `1`. `IsVertex`: unfold `NewtonPolygon.IsVertex`; `anchor (newtonPolygon 𝓥 f) = 0` (`anchor_newtonPolygon` with `f ≠ 0`; `natTrailingDegree = 0`), so `1 = anchor` is false; `unitSlope w 0 = 1 = unitSlope w 1` (`unitSlope_nat`, `WithTop` arithmetic), `lt_irrefl`. `newtonSlopes = {1, 1}`: as T065 (`Multiset.replicate 2 1` if the `{1, 1}` notation needs `Multiset.insert_eq_cons`, `Multiset.replicate_succ`).
""" + DEC + "L12.6–L12.8.",
  mathlib="`NewtonPolygon.IsVertex`, `NewtonPolygon.newtonPolygon_eq_self`, `NewtonPolygon.unitSlope_nat`, `lt_irrefl`, `Multiset.insert_eq_cons`, `Multiset.replicate_succ`, `Polynomial.coeff_add`, `Polynomial.coeff_C_mul_X_pow`, `Padic.valuation_pow`.",
  sources="[RM] Examples (\"a polynomial with a collinear interior point\"), Acceptance (\"its polygon has … points on it that are not vertices, and the slope multiset is nevertheless correct\").",
  gen="Any prime `p`.")

t(id='T067', title='Examples: `Φ_p` is flat; the coefficients of `Φ_p(X + 1)`', file=EXA, deps='CLEANUP-26',
  par='no', typ='examples', leaves='L12.11–L12.13',
  decls=[(EXA, 'newtonPolygon_cyclotomic'), (EXA, 'isPure_cyclotomic'), (EXA, 'coeff_cyclotomic_comp_X_add_one')],
  sketch="""1. Coefficients of `Φ_p`: `Polynomial.cyclotomic_prime ℚ_[p] p : cyclotomic p ℚ_[p] = ∑ i ∈ range p, X ^ i`; `Polynomial.finset_sum_coeff`, `Polynomial.coeff_X_pow`, `Finset.sum_ite_eq'`, `Finset.mem_range`: `coeff i = if i < p then 1 else 0`. Heights: `0` for `i < p` (`Padic.valuation_one`/`AddValuation.map_one`), `⊤` beyond. The sequence `w := fun k ↦ if k < p then 0 else ⊤` is convex (`IsConvexSeq.piecewise_top isConvexSeq_zero_fun` on `Set.Iio p`, `Set.ordConnected_Iio`; or `isConvexSeq_iff_midpoint`), so `newtonPolygon 𝓥 Φ_p = w` and `newtonPolygon_cyclotomic hk` follows.
2. `isPure_cyclotomic`: unit slopes of `w` are `0` for `k + 1 < p`, `⊤` from `p - 1`; `natDegree Φ_p = p - 1 ≥ 1` (`Polynomial.natDegree_cyclotomic`, `Nat.totient_prime`, `Nat.Prime.one_lt`) — or `isPure_of_bounds` at `m = 0` with all terms `≤ 1` and the leading term `1`.
3. `coeff_cyclotomic_comp_X_add_one`: from `Polynomial.cyclotomic_prime_mul_X_sub_one ℚ_[p] p : Φ_p * (X - 1) = X ^ p - 1`, compose with `X + 1`: `Polynomial.mul_comp`, `sub_comp`, `X_comp`, `one_comp`, `pow_comp`, `add_sub_cancel_right`: `Φ_p.comp (X + 1) * X = (X + 1) ^ p - 1`; apply `Polynomial.coeff_mul_X` at `i + 1`: `coeff (Φ_p.comp (X+1)) i = coeff ((X + 1) ^ p - 1) (i + 1) = p.choose (i + 1) - 0` (`Polynomial.coeff_sub`, `Polynomial.coeff_X_add_one_pow`, `Polynomial.coeff_one`, `Nat.succ_ne_zero`, `sub_zero`).
""" + DEC + "L12.11–L12.13.",
  mathlib="`Polynomial.cyclotomic_prime`, `Polynomial.finset_sum_coeff`, `Polynomial.coeff_X_pow`, `Finset.sum_ite_eq'`, `Finset.mem_range`, `NewtonPolygon.IsConvexSeq.piecewise_top`, `NewtonPolygon.isConvexSeq_zero_fun`, `Set.ordConnected_Iio`, `NewtonPolygon.newtonPolygon_eq_self`, `Polynomial.natDegree_cyclotomic`, `Nat.totient_prime`, `Nat.Prime.one_lt`, `Polynomial.cyclotomic_prime_mul_X_sub_one`, `Polynomial.mul_comp`, `Polynomial.sub_comp`, `Polynomial.X_comp`, `Polynomial.one_comp`, `Polynomial.pow_comp`, `add_sub_cancel_right`, `Polynomial.coeff_mul_X`, `Polynomial.coeff_sub`, `Polynomial.coeff_X_add_one_pow`, `Polynomial.coeff_one`, `Nat.succ_ne_zero`, `sub_zero`.",
  sources="[RM] Acceptance (\"Φ_p itself has polygon flat at height 0 and all its roots are units\"; \"Φ_p(X + 1) / p, where Φ_p is the p-th cyclotomic polynomial\").",
  gen="Any prime `p` (for `p = 2`, `Φ₂ = X + 1`).")

t(id='T068', title='Examples: rescaling the `ℚ_p` polygon by `log p`; the pure series `∑ pⁱXⁱ`', file=EXA, deps='T067',
  par='no', typ='examples', leaves='L12.15–L12.16',
  decls=[(EXA, 'newtonPolygon_ofNormAddVal_eq_scaleHeight'), (EXA, 'isPure_mk_p_pow')],
  sketch="""1. `newtonPolygon_ofNormAddVal_eq_scaleHeight`: `Polynomial.newtonPolygon_eq_scaleHeight 𝓥 (ofNormAddVal ℚ_[p])` (T036) and `Padic.scale_normedAddValuation_ofNormAddVal` (T063).
2. `isPure_mk_p_pow`: `coeffVal 𝓥 (mk fun i ↦ p ^ i) = fun i ↦ ((i : ℝ) : WithTop ℝ)` (`funext`, `coeffVal_apply`, `PowerSeries.coeff_mk`, `Padic.normedAddValuation_apply`, `Padic.addValuation.apply` (`p ^ i ≠ 0`), `Padic.valuation_pow`, `Padic.valuation_p`, `mul_one`, `Padic.normedAddValuation_embed_apply`, `Int.cast_natCast`); this is the affine sequence `0 + 1 * i` (`NewtonPolygon.isConvexSeq_affine 0 1`), its own polygon (`NewtonPolygon.newtonPolygon_affine`); unit slopes `1` (`NewtonPolygon.unitSlope_coe`, `Nat.cast_succ`, `add_sub_cancel_left`), all finite: `IsPure` (`NewtonPolygon.IsPure`, `WithTop.coe_ne_top`).
""" + DEC + "L12.15–L12.16.",
  mathlib="`PowerSeries.coeff_mk`, `Padic.addValuation.apply`, `Padic.valuation_pow`, `Padic.valuation_p`, `Int.cast_natCast`, `NewtonPolygon.isConvexSeq_affine`, `NewtonPolygon.newtonPolygon_affine`, `NewtonPolygon.unitSlope_coe`, `NewtonPolygon.IsPure`, `Nat.cast_succ`, `add_sub_cancel_left`, `WithTop.coe_ne_top`, `pow_ne_zero`.",
  sources="[RM] §2.2.8 (\"the polygon for normAddValZ on ℚ_p is the polygon for normAddVal divided by log p\"), Examples (\"1 + pX + p²X² + ⋯ (a pure series of slope 1)\"); [Gou20] p. 261 (Q-Gou-ex1).",
  gen="Any prime `p`.")

t(id='T069', title='Example: the entire series `∑ pⁱ² Xⁱ` with unit slopes `1, 3, 5, …`', file=EXA, deps='T068',
  par='no', typ='examples', leaves='L12.17–L12.21',
  decls=[(EXA, 'isRestricted_mk_p_pow_sq'), (EXA, 'coeffVal_mk_p_pow_sq'), (EXA, 'newtonPolygon_mk_p_pow_sq'), (EXA, 'unitSlope_newtonPolygon_mk_p_pow_sq'), (EXA, 'slopesUnbounded_newtonPolygon_mk_p_pow_sq')],
  sketch="""1. `isRestricted_mk_p_pow_sq`: `PowerSeries.isRestricted_iff'` ([RAG]); terms `‖(p : ℚ_[p]) ^ (i^2)‖ * c ^ i = (p : ℝ) ^ (-(i^2 : ℤ)) * c ^ i` (`PowerSeries.coeff_mk`, `Padic.norm_p_pow`) `= (c / p ^ i) ^ i` (`zpow_neg`, `zpow_natCast`, `pow_mul`, `sq`, `div_pow`, `inv_mul_eq_div`). Choose `N` with `2 * c ≤ p ^ N` (`pow_unbounded_of_one_lt` with `(1 : ℝ) < p`); for `i ≥ N`, `c / p ^ i ≤ 1 / 2` (`div_le_iff₀`, `pow_le_pow_right₀`), so the term is `≤ (1/2) ^ i` (`pow_le_pow_left₀`, `div_nonneg`). `squeeze_zero'` with `Filter.eventually_atTop.mpr ⟨N, _⟩`, `Filter.Eventually.of_forall (fun i ↦ mul_nonneg …)`, and `tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)`.
2. `coeffVal_mk_p_pow_sq`: `funext k`; `coeffVal_apply`, `PowerSeries.coeff_mk`, `Padic.normedAddValuation_apply`, `Padic.addValuation.apply (pow_ne_zero _ _)`, `Padic.valuation_pow`, `Padic.valuation_p`, `mul_one`, `Padic.normedAddValuation_embed_apply`, `Int.cast_natCast`, `Nat.cast_pow`.
3. `newtonPolygon_mk_p_pow_sq`: `newtonPolygon_def`, 2, `NewtonPolygon.newtonPolygon_sq` ([L0] Examples).
4. `unitSlope_newtonPolygon_mk_p_pow_sq`: 3 and `NewtonPolygon.unitSlope_sq` (or `unitSlope_newtonPolygon_sq`).
5. `slopesUnbounded_newtonPolygon_mk_p_pow_sq`: `NewtonPolygon.SlopesUnbounded`; given `σ`, `exists_nat_gt σ` gives `j` with `σ < 2 j + 1`; 4 and `WithTop.coe_lt_coe`. (Or `slopesUnbounded_newtonPolygon_of_forall_isRestricted` with 1.)
""" + DEC + "L12.17–L12.21.",
  mathlib="`PowerSeries.isRestricted_iff'`, `PowerSeries.coeff_mk`, `Padic.norm_p_pow`, `zpow_neg`, `zpow_natCast`, `pow_mul`, `sq`, `div_pow`, `inv_mul_eq_div`, `pow_unbounded_of_one_lt`, `div_le_iff₀`, `pow_le_pow_right₀`, `pow_le_pow_left₀`, `div_nonneg`, `squeeze_zero'`, `Filter.eventually_atTop`, `Filter.Eventually.of_forall`, `tendsto_pow_atTop_nhds_zero_of_lt_one`, `Padic.addValuation.apply`, `Padic.valuation_pow`, `Padic.valuation_p`, `Int.cast_natCast`, `Nat.cast_pow`, `NewtonPolygon.newtonPolygon_sq`, `NewtonPolygon.unitSlope_sq`, `NewtonPolygon.unitSlope_newtonPolygon_sq`, `NewtonPolygon.SlopesUnbounded`, `exists_nat_gt`, `WithTop.coe_lt_coe`, `pow_ne_zero`, `Nat.one_lt_cast`.",
  sources="[RM] Examples (\"∑ pⁱ² Xⁱ, an entire series with unit slopes 1, 3, 5, …\"), Acceptance; [L0] Examples (`newtonPolygon_sq`).",
  gen="Any prime `p`; every positive radius for restrictedness.")

t(id='T070', title='Example: bounded but not restricted at radius `1`', file=EXA, deps='CLEANUP-27',
  par='no', typ='examples', leaves='L12.22–L12.23',
  decls=[(EXA, 'hasGaussNorm_one_mk_ite'), (EXA, 'not_isRestricted_one_mk_ite')],
  sketch="""`f := mk fun i ↦ if i = 0 then 1 else p`; terms at radius `1`: `‖coeff i f‖ * 1 ^ i = ‖coeff i f‖` (`one_pow`, `mul_one`, `PowerSeries.coeff_mk`).
1. `hasGaussNorm_one_mk_ite`: `HasGaussNorm` is `BddAbove (Set.range …)`; `bddAbove_def.mpr ⟨1, _⟩`: `split_ifs`; `norm_one` or `Padic.norm_p` with `(p : ℝ)⁻¹ ≤ 1` (`inv_le_one_of_one_le₀`, `Nat.one_le_cast.mpr (Fact.out : p.Prime).one_lt.le`).
2. `not_isRestricted_one_mk_ite`: `PowerSeries.isRestricted_iff'` ([RAG]); suppose `Tendsto (fun i ↦ ‖coeff i f‖ * 1 ^ i) atTop (𝓝 0)`; the sequence is eventually the constant `(p : ℝ)⁻¹` (`Filter.eventually_atTop.mpr ⟨1, fun i hi ↦ by simp [coeff_mk, Nat.pos_iff_ne_zero.mp hi, Padic.norm_p]⟩`), so by `Filter.Tendsto.congr'` the constant tends to `0`, and `tendsto_nhds_unique (tendsto_const_nhds) _` gives `(p : ℝ)⁻¹ = 0`, contradicting `inv_pos.mpr (Nat.cast_pos.mpr (Fact.out : p.Prime).pos)` (`ne_of_gt`).
""" + DEC + "L12.22–L12.23.",
  mathlib="`PowerSeries.HasGaussNorm`, `bddAbove_def`, `PowerSeries.coeff_mk`, `one_pow`, `mul_one`, `norm_one`, `Padic.norm_p`, `inv_le_one_of_one_le₀`, `Nat.one_le_cast`, `Nat.Prime.one_lt`, `PowerSeries.isRestricted_iff'`, `Filter.eventually_atTop`, `Filter.Tendsto.congr'`, `tendsto_nhds_unique`, `tendsto_const_nhds`, `inv_pos`, `Nat.cast_pos`, `Nat.Prime.pos`, `Nat.pos_iff_ne_zero`, `ne_of_gt`.",
  sources="[RM] §2.3.2 (\"These are not the same condition … give the example separating them\"); [Gou20] p. 262 (Q-Gou-ex2: \"if |x| = 1, then the series does not converge\").",
  gen="Any prime `p`.")

t(id='T071', title='[M5] Acceptance: `1 + 3^{2j+1}X²` pure of slope `j + ½`; `Φ_p(X+1)/p` pure of slope `−1/(p−1)`', file=EXA, deps='CLEANUP-ALL-5',
  par='no', typ='examples', leaves='L12.9–L12.10, L12.14', milestone='M5 ([RM] Acceptance examples)',
  decls=[(EXA, 'isPure_one_add_three_pow_mul_X_sq'), (EXA, 'newtonSlopes_one_add_three_pow_mul_X_sq'), (EXA, 'isPure_C_inv_mul_cyclotomic_comp_X_add_one')],
  sketch="""1. `isPure_one_add_three_pow_mul_X_sq`: `isPure_of_bounds (Padic.normedAddValuation 3)` (`Nat.fact_prime_three`) at `m := (j : ℝ) + 1/2`. `coeff 0 = 1 ≠ 0`; `natDegree = 2` (`Polynomial.natDegree_add_eq_right_of_natDegree_lt`, `natDegree_one`, `Polynomial.natDegree_C_mul_X_pow` with `(3 : ℚ_[3]) ^ (2j+1) ≠ 0`); coefficients `1`, `0`, `3 ^ (2j+1)` (`Polynomial.coeff_add`, `coeff_one`, `coeff_C_mul_X_pow`). Bounds with `c := (3 : ℝ) ^ m` (`Padic.normedAddValuation_base`): `k = 0`: `1 ≤ 1`; `k = 1`: `0 ≤ 1`; `k = 2`: `‖3 ^ (2j+1)‖ * c ^ 2 = 3 ^ (-(2j+1 : ℤ)) * 3 ^ (2 m) = 1` (`Padic.norm_p_pow`, `← Real.rpow_natCast`, `← Real.rpow_mul`, `← Real.rpow_intCast`, `← Real.rpow_add`, `(2 * j + 1 : ℝ) = m * 2` by `ring`, `Real.rpow_zero`); `k ≥ 3`: `0 ≤ 1`. `heq` is the `k = 2` computation.
2. `newtonSlopes_one_add_three_pow_mul_X_sq`: `NewtonPolygon.isPure_iff_slopeMultiset` with 1 and `card_newtonSlopes = 2 - 0` (`natTrailingDegree = 0` from `coeff 0 = 1`).
3. `isPure_C_inv_mul_cyclotomic_comp_X_add_one`: `g := C (p⁻¹) * Φ_p.comp (X + 1)`, `coeff g i = p⁻¹ * p.choose (i + 1)` (`Polynomial.coeff_C_mul`, T067). `isPure_of_bounds 𝓥` at `m := -1 / ((p : ℝ) - 1)`, `c := (p : ℝ) ^ m`: `coeff g 0 = p⁻¹ * p = 1 ≠ 0` (`Nat.choose_one_right`, `inv_mul_cancel₀`); `natDegree g = p - 1` (`Polynomial.natDegree_C_mul (inv_ne_zero …)`, `Polynomial.natDegree_comp`, `natDegree_cyclotomic`, `Nat.totient_prime`, `natDegree_X_add_C`, `mul_one`), `0 < p - 1` (`Nat.Prime.one_lt`, `Nat.sub_pos_of_lt`). Bounds: for `i + 1 < p`, `i ≥ 1`: `p ∣ p.choose (i + 1)` (`Nat.Prime.dvd_choose_self (Fact.out) (Nat.succ_ne_zero i) hlt`), so `‖(p.choose (i+1) : ℚ_[p])‖ ≤ (p : ℝ) ^ (-(1 : ℤ))` (`Padic.norm_int_le_pow_iff_dvd` with `Int.natCast_dvd_natCast`, `pow_one`, `Nat.cast_pow`), hence `‖coeff g i‖ = p * ‖choose‖ ≤ 1` (`norm_mul`, `norm_inv`, `Padic.norm_p`, `inv_inv`, `zpow_neg_one`) and `c ^ i = p ^ (m i) ≤ 1` (`Real.rpow_le_one_of_one_le_of_nonpos`, `m ≤ 0`); `i = p - 1`: `‖coeff g (p-1)‖ = p` (`Nat.choose_self`, `norm_one`) and `c ^ (p-1) = p ^ (m (p - 1)) = p ^ (-1 : ℝ) = p⁻¹` (`← Real.rpow_natCast`, `← Real.rpow_mul`, `div_mul_cancel₀` with `(p : ℝ) - 1 ≠ 0`, `Real.rpow_neg_one`), product `1` (`mul_inv_cancel₀`); `i ≥ p`: `coeff g i = 0` (`Nat.choose_eq_zero_of_lt`), term `0 ≤ 1`.
""" + DEC + "L12.9–L12.10, L12.14 (plan D10).",
  mathlib="`Nat.fact_prime_three`, `Polynomial.natDegree_add_eq_right_of_natDegree_lt`, `Polynomial.natDegree_one`, `Polynomial.natDegree_C_mul_X_pow`, `Polynomial.coeff_add`, `Polynomial.coeff_one`, `Polynomial.coeff_C_mul_X_pow`, `Padic.norm_p_pow`, `Real.rpow_natCast`, `Real.rpow_mul`, `Real.rpow_intCast`, `Real.rpow_add`, `Real.rpow_zero`, `NewtonPolygon.isPure_iff_slopeMultiset`, `Polynomial.coeff_C_mul`, `Nat.choose_one_right`, `Nat.choose_self`, `Nat.choose_eq_zero_of_lt`, `inv_mul_cancel₀`, `mul_inv_cancel₀`, `Polynomial.natDegree_C_mul`, `Polynomial.natDegree_comp`, `Polynomial.natDegree_cyclotomic`, `Nat.totient_prime`, `Polynomial.natDegree_X_add_C`, `Nat.Prime.one_lt`, `Nat.sub_pos_of_lt`, `Nat.Prime.dvd_choose_self`, `Nat.succ_ne_zero`, `Padic.norm_int_le_pow_iff_dvd`, `Int.natCast_dvd_natCast`, `norm_mul`, `norm_inv`, `Padic.norm_p`, `inv_inv`, `zpow_neg_one`, `Real.rpow_le_one_of_one_le_of_nonpos`, `div_mul_cancel₀`, `Real.rpow_neg_one`, `norm_one`, `Nat.cast_pow`.",
  sources="[RM] Acceptance (\"1 + 3^{2j+1} X² over ℚ_3 is pure of slope j + ½, as an equality of rational numbers … This is the shape of statement the additive normalisation exists for\"; \"Φ_p(X + 1) / p is pure of slope -1/(p-1)\").",
  gen="The slope is the real `j + 1/2` (resp. `-1/(p-1)`); rationality in general is T033 (plan D10). Only divisibility of the interior binomials is needed.")

t(id='T072', title='Chain-root gate and the roadmap status paragraph', file='PhD/TauCeti.lean', deps='CLEANUP-3, CLEANUP-5, CLEANUP-7, CLEANUP-10, CLEANUP-13, CLEANUP-14, CLEANUP-17, CLEANUP-20, CLEANUP-23, CLEANUP-24, CLEANUP-25, CLEANUP-28',
  par='no', typ='gate', leaves='all',
  statement_override="""-- PhD/TauCeti.lean already imports PhD.TauCeti.Code.NewtonPolygons.Coeff.Examples (added 2026-10-06).
-- Gate: `lake build PhD.TauCeti` succeeds with no `sorry` warning from PhD/TauCeti/Code/NewtonPolygons/Coeff/;
-- `#print axioms` on the five milestone declarations and on every declaration of the layer reports only
-- `propext`, `Classical.choice`, `Quot.sound`; `lake exe runLinter` is clean on the twelve modules.""",
  decls=[],
  sketch="""1. `lake build PhD.TauCeti` (the chain root, both chains in one environment) — must succeed with no `sorry` warnings from `Coeff/`.
2. `#print axioms` on every declaration of the twelve modules (generate the list from `scratch/fullnames.json` as Layer 1's `axioms.py` did); only `propext`, `Classical.choice`, `Quot.sound`.
3. `lake exe runLinter PhD.TauCeti.Code.NewtonPolygons.Coeff.<Module>` for the twelve modules.
4. Append the Layer 2 "Status (date)" paragraph to `PhD/TauCeti/Roadmaps/NewtonPolygons/README.md` after the Layer 2 introduction, in the style of Layer 1's: implementation path, the five milestones with their axiom report, and the deviations/errata D1–D10 of `plan.md` (in particular that §2.4.4 is deferred to Layer 3/4, that §2.2.4's direction is corrected, and that restrictedness/distinguishedness come from the rigid-analytic chain's `Restricted/PowerSeries/` files). Do not edit the roadmap's own sentences.
""",
  mathlib="(none)",
  sources="[RM] (the roadmap README).",
  gen="(n/a)")

# ---------------------------------------------------------------- cleanups and order
CLEAN = {
    'CLEANUP-1': ('NormedAddValuation.lean', 'T003', 'mid'),
    'CLEANUP-2': ('NormedAddValuation.lean', 'T006', 'mid'),
    'CLEANUP-3': ('NormedAddValuation.lean', 'T009', 'final'),
    'CLEANUP-4': ('Generic.lean', 'T012', 'mid'),
    'CLEANUP-5': ('Generic.lean', 'T015', 'final'),
    'CLEANUP-6': ('CoeffVal.lean', 'T018', 'mid'),
    'CLEANUP-7': ('CoeffVal.lean', 'T020', 'final'),
    'CLEANUP-8': ('PowerSeries.lean', 'T023', 'mid'),
    'CLEANUP-9': ('PowerSeries.lean', 'T026', 'mid'),
    'CLEANUP-10': ('PowerSeries.lean', 'T027', 'final'),
    'CLEANUP-11': ('Polynomial.lean', 'T030', 'mid'),
    'CLEANUP-12': ('Polynomial.lean', 'T033', 'mid'),
    'CLEANUP-13': ('Polynomial.lean', 'T036', 'final'),
    'CLEANUP-14': ('Extension.lean', 'T038', 'final'),
    'CLEANUP-15': ('SupportValue.lean', 'T041', 'mid'),
    'CLEANUP-16': ('SupportValue.lean', 'T044', 'mid'),
    'CLEANUP-17': ('SupportValue.lean', 'T046', 'final'),
    'CLEANUP-18': ('GaussNorm.lean', 'T049', 'mid'),
    'CLEANUP-19': ('GaussNorm.lean', 'T052', 'mid'),
    'CLEANUP-20': ('GaussNorm.lean', 'T053', 'final'),
    'CLEANUP-21': ('Pure.lean', 'T056', 'mid'),
    'CLEANUP-22': ('Pure.lean', 'T059', 'mid'),
    'CLEANUP-23': ('Pure.lean', 'T060', 'final'),
    'CLEANUP-24': ('Distinguished.lean', 'T062', 'final'),
    'CLEANUP-25': ('Padic.lean', 'T063', 'final'),
    'CLEANUP-26': ('Examples.lean', 'T066', 'mid'),
    'CLEANUP-27': ('Examples.lean', 'T069', 'mid'),
    'CLEANUP-28': ('Examples.lean', 'T071', 'final'),
}

ALL = {
    'CLEANUP-ALL-1': ('CLEANUP-6, CLEANUP-3, CLEANUP-5', 'M1 (T019)', '`NormedAddValuation.lean`, `Generic.lean`, `CoeffVal.lean` so far.'),
    'CLEANUP-ALL-2': ('CLEANUP-12, CLEANUP-10', 'M2 (T034)', '`PowerSeries.lean`, `Polynomial.lean` so far.'),
    'CLEANUP-ALL-3': ('T048, CLEANUP-13, CLEANUP-17', 'M3 (T049)', '`Polynomial.lean`, `SupportValue.lean`, `GaussNorm.lean` so far.'),
    'CLEANUP-ALL-4': ('T061, CLEANUP-23', 'M4 (T062)', '`Pure.lean`, `Distinguished.lean` so far.'),
    'CLEANUP-ALL-5': ('T070, CLEANUP-14, CLEANUP-24, CLEANUP-25', 'M5 (T071)', '`Extension.lean`, `Padic.lean`, `Examples.lean` so far.'),
}

ORDER = [
    'T001', 'T002', 'T003', 'CLEANUP-1', 'T004', 'T005', 'T006', 'CLEANUP-2', 'T007', 'T008', 'T009', 'CLEANUP-3',
    'T010', 'T011', 'T012', 'CLEANUP-4', 'T013', 'T014', 'T015', 'CLEANUP-5',
    'T016', 'T017', 'T018', 'CLEANUP-6', 'CLEANUP-ALL-1', 'T019', 'T020', 'CLEANUP-7',
    'T021', 'T022', 'T023', 'CLEANUP-8', 'T024', 'T025', 'T026', 'CLEANUP-9', 'T027', 'CLEANUP-10',
    'T028', 'T029', 'T030', 'CLEANUP-11', 'T031', 'T032', 'T033', 'CLEANUP-12', 'CLEANUP-ALL-2', 'T034', 'T035', 'T036', 'CLEANUP-13',
    'T037', 'T038', 'CLEANUP-14',
    'T039', 'T040', 'T041', 'CLEANUP-15', 'T042', 'T043', 'T044', 'CLEANUP-16', 'T045', 'T046', 'CLEANUP-17',
    'T047', 'T048', 'CLEANUP-ALL-3', 'T049', 'CLEANUP-18', 'T050', 'T051', 'T052', 'CLEANUP-19', 'T053', 'CLEANUP-20',
    'T054', 'T055', 'T056', 'CLEANUP-21', 'T057', 'T058', 'T059', 'CLEANUP-22', 'T060', 'CLEANUP-23',
    'T061', 'CLEANUP-ALL-4', 'T062', 'CLEANUP-24',
    'T063', 'CLEANUP-25',
    'T064', 'T065', 'T066', 'CLEANUP-26', 'T067', 'T068', 'T069', 'CLEANUP-27', 'T070', 'CLEANUP-ALL-5', 'T071', 'CLEANUP-28',
    'T072', 'CLEANUP-FINAL',
]

FINAL = {
    'deps': 'T072',
    'text': ("Run /cleanup-all on the twelve modules of `PhD/TauCeti/Code/NewtonPolygons/Coeff/` inline as the main agent: "
             "`lake exe runLinter` on each, `lake build PhD.TauCeti` with no warnings from the layer, docstrings naming "
             "the final declarations, imports pruned by hand (the build confirms each removal), `#print axioms` standard "
             "throughout. Then update the memory file `tauceti-np-layer2-board.md` to COMPLETE and the "
             "`parallel-ticket-boards` pointer."),
}
