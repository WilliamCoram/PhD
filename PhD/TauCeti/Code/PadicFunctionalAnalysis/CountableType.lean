/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.FiniteDimension
import PhD.TauCeti.Code.PadicFunctionalAnalysis.Serre

/-!
# Banach spaces of countable type

A Banach space over a complete nonarchimedean nontrivially normed field `K` — not assumed
discretely valued — is *of countable type* when it has a countable subset with dense span. Such a
space has, for every `0 < t < 1`, a `t`-orthogonal sequence spanning a dense subspace (Schneider's
inductive distance argument in the proof of Proposition 10.4), so an infinite-dimensional one is
topologically isomorphic to `C₀(ℕ, K)` and every such space is potentially orthonormalisable over
any `K`. Quotients and closed subspaces of spaces of countable type are of countable type, and
every closed subspace is complemented (Schneider, Proposition 10.5), which also holds over a
discretely valued field without countability.

⚠ Over a non-discretely-valued `K` a `1`-orthogonal basis need not exist (roadmap §2.4.2, recorded
only); the orthogonal basis over a discretely valued `K` (van Rooij; Perez-Garcia–Schikhof) is not
on this board — see the plan's errata.

Roadmap: `PhD/TauCeti/Roadmaps/PadicFunctionalAnalysis/README.md`, §2.4.
Tau Ceti home: `TauCeti/Analysis/Normed/Module/Ultra/CountableType.lean`.

## Main declarations

* `Module.IsCountableType`.
* `Module.IsCountableType.exists_isTOrthogonalFamily_nat` — the `t`-orthogonal sequence
  (Schneider, Prop 10.4 (a)–(d)).
* `Module.IsCountableType.exists_continuousLinearEquiv_nat` — Schneider, Proposition 10.4.
* `Module.IsCountableType.isPotentiallyONable`.
* `Submodule.closedComplemented_of_isCountableType`,
  `Submodule.closedComplemented_of_isRankOneDiscrete` — Schneider, Proposition 10.5.
* `Module.IsCountableType.submodule`, `Module.IsCountableType.quotient`.
-/

universe u v

open Filter Topology Function Module
open scoped ZeroAtInfty
open ZeroAtInftyContinuousMap

namespace Module

/-- A normed space is **of countable type** when it has a countable subset with dense span. Source:
roadmap §2.4 ("A `K`-Banach space with a dense subspace of countably infinite dimension");
Schneider, Prop 10.4 ("contains a dense vector subspace of countably infinite dimension"). -/
def IsCountableType (K : Type u) (V : Type v) [NormedField K] [NormedAddCommGroup V]
    [NormedSpace K V] : Prop :=
  ∃ s : Set V, s.Countable ∧ Dense (Submodule.span K s : Set V)

end Module

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {V : Type v} [NormedAddCommGroup V] [NormedSpace K V] [IsUltrametricDist V] [CompleteSpace V]

/-! ### The inductive construction of a `t`-orthogonal sequence -/

/-- **The distance step**: for a closed subspace `U`, a vector `w ∉ U` and `0 < r < 1`, there is
`v ∈ w + U` with `r ‖v‖ ≤ ‖v + u‖` for all `u ∈ U`. Source: Schneider, Prop 10.4 ("Fixing some
`v ∈ Vₙ ∖ Vₙ₋₁` we therefore have `inf {‖v + w‖ : w ∈ Vₙ₋₁} > 0`. There consequently exists a
vector `w' ∈ Vₙ₋₁` such that `rₙ/rₙ₊₁ ≤ inf{‖v + w‖ : w ∈ Vₙ₋₁} / ‖v + w'‖ ≤ 1`"). -/
theorem Submodule.exists_add_mem_forall_mul_norm_le (U : Submodule K V) (hU : IsClosed (U : Set V))
    {w : V} (hw : w ∉ U) {r : ℝ} (hr : r < 1) :
    ∃ u₀ ∈ U, ∀ u ∈ U, r * ‖w + u₀‖ ≤ ‖w + u₀ + u‖ := by
  sorry

/-- The step inequality in its two-term form: `‖a v + u‖ ≥ r max(‖a v‖, ‖u‖)` for `u ∈ U`. Source:
Schneider, Prop 10.4 ("In fact, we have `‖a vₙ + w‖ ≥ (rₙ/rₙ₊₁) max(‖a vₙ‖, ‖w‖)` … If
`‖a vₙ‖ = ‖w‖` this is a consequence of the previous inequality; if `‖a vₙ‖ ≠ ‖w‖` this follows from
`‖a vₙ + w‖ = max(‖a vₙ‖, ‖w‖)`"). -/
theorem norm_smul_add_ge_mul_max (U : Submodule K V) {v : V} {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1)
    (hv : ∀ u ∈ U, r * ‖v‖ ≤ ‖v + u‖) (a : K) {u : V} (hu : u ∈ U) :
    r * max ‖a • v‖ ‖u‖ ≤ ‖a • v + u‖ := by
  sorry

/-- **The `t`-orthogonal sequence** of an infinite-dimensional space of countable type: a sequence
of norm at most `1`, bounded below, `t`-orthogonal, with dense span. Source: Schneider, Prop 10.4,
properties (a)–(d) ("`‖∑ aᵢ vᵢ‖ ≥ r · max(‖a₁v₁‖, …, ‖aₙvₙ‖)` … We therefore may assume that
`ε ≤ ‖vₙ‖ ≤ 1` … `‖∑ aᵢ vᵢ‖ ≥ r · max(|a₁|, …, |aₙ|)`"); roadmap §2.4.1–2.4.2. -/
theorem Module.IsCountableType.exists_isTOrthogonalFamily_nat (hV : IsCountableType K V)
    (hfin : ¬ FiniteDimensional K V) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ v : ℕ → V, (∀ n, ‖v n‖ ≤ 1) ∧ (∃ δ : ℝ, 0 < δ ∧ ∀ n, δ ≤ ‖v n‖) ∧
      IsTOrthogonalFamily K t v ∧ Dense (Submodule.span K (Set.range v) : Set V) := by
  sorry

/-- The finite-dimensional case of the construction: a `t`-orthogonal basis. Source: Schneider,
Prop 10.4 (a)–(c) for a finite chain `V₀ ⊆ … ⊆ Vₙ = V`; roadmap §2.4.2 ("A `K`-Banach space of
countable type has a `t`-orthogonal basis for every `0 < t < 1`"). -/
theorem Module.exists_isTOrthogonalFamily_fin_of_finiteDimensional [FiniteDimensional K V] {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ (n : ℕ) (v : Fin n → V), IsTOrthogonalFamily K t v ∧
      Submodule.span K (Set.range v) = ⊤ := by
  sorry

/-! ### Schneider's Proposition 10.4 and its consequences -/

/-- **Schneider, Proposition 10.4**: an infinite-dimensional Banach space of countable type is
topologically isomorphic to `C₀(ℕ, K)`. Source: Schneider, Prop 10.4 ("Suppose that the
`K`-Banach space `V` contains a dense vector subspace of countably infinite dimension; then `V` is
topologically isomorphic to `c₀(ℕ)`"); roadmap §2.4.1. -/
theorem Module.IsCountableType.exists_continuousLinearEquiv_nat (hV : IsCountableType K V)
    (hfin : ¬ FiniteDimensional K V) : Nonempty (V ≃L[K] C₀(ℕ, K)) := by
  sorry

/-- A Banach space of countable type is potentially orthonormalisable over any `K`. Source:
roadmap §2.4.1 ("Hence such a space is potentially orthonormalisable over any `K`"). -/
theorem Module.IsCountableType.isPotentiallyONable (hV : IsCountableType K V) :
    IsPotentiallyONable K V := by
  sorry

/-- A quotient of a space of countable type is of countable type. Source: roadmap §2.4.3 ("a
quotient of a space of countable type is of countable type"); Schneider, Prop 10.5 ("the quotient
`V/U` again is a Banach space which in case (b) contains a vector subspace of countable
dimension"). -/
theorem Module.IsCountableType.quotient (hV : IsCountableType K V) (U : Submodule K V)
    [IsClosed (U : Set V)] : IsCountableType K (V ⧸ U) := by
  sorry

/-- A closed subspace whose quotient has (Pr) is complemented: lift the identity of `V ⧸ U` along
the projection, and `id - s ∘ pr` is a continuous projector onto `U`. Source: Schneider, Prop 10.5
("The continuous linear map `f ∘ g : V/U → V` then is a section of the projection map
`V → V/U`, and `P := (id_V − f ∘ g ∘ pr)` is a continuous projector onto `U`"). -/
theorem Submodule.closedComplemented_of_hasPr_quotient (U : Submodule K V) [IsClosed (U : Set V)]
    (h : HasPr K (V ⧸ U)) : U.ClosedComplemented := by
  sorry

/-- **Schneider, Proposition 10.5 (a)**: over a discretely valued field every closed subspace of a
Banach space is complemented. Source: Schneider, Prop 10.5 ("Let `V` be a `K`-Banach space and
suppose that (a) `K` is discretely valued … then every closed vector subspace `U ⊆ V` is
complemented"). -/
theorem Submodule.closedComplemented_of_isRankOneDiscrete
    [Valuation.IsRankOneDiscrete (NormedField.valuation (K := K))] (U : Submodule K V)
    [IsClosed (U : Set V)] : U.ClosedComplemented := by
  sorry

/-- **Schneider, Proposition 10.5 (b)**: every closed subspace of a Banach space of countable type
is complemented. Source: Schneider, Prop 10.5 ("(b) `V` contains a dense vector subspace of
countable dimension; then every closed vector subspace `U ⊆ V` is complemented"); roadmap §2.4.3
("is complemented by a closed subspace"). -/
theorem Submodule.closedComplemented_of_isCountableType (hV : IsCountableType K V)
    (U : Submodule K V) [IsClosed (U : Set V)] : U.ClosedComplemented := by
  sorry

/-- A closed subspace of a space of countable type is of countable type: it is complemented, hence
isomorphic to the quotient by its complement. Source: roadmap §2.4.3 ("A closed subspace of a
space of countable type is of countable type"); Schneider, Prop 10.5 with Prop 8.3. -/
theorem Module.IsCountableType.submodule (hV : IsCountableType K V) (U : Submodule K V)
    [IsClosed (U : Set V)] : IsCountableType K U := by
  sorry
