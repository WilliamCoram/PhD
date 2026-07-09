import PhD.TateFredholm.Pr

/-!
# Residue machinery for Serre's theorem

Sub-development for `isPotentiallyONable_of_uniformizer` (see `BaseChange.lean`),
produced by the `/develop --decompose` pass.  Source: [Bel] §II.1.4 (Hypothesis II.1.11,
Lemma II.1.12, Theorem II.1.13, p. 58); ultimately [Serre] Prop. 1.  The tree:
discreteness of the value group (`R1`), the unit ball and its residue field (`R2`–`R4`),
a quotient-free "residue basis" interface (`R5`), successive approximation
(`R6a`–`R6b`, the analytic heart), assembly over discrete norms (`R6`), and the
norm-rescaling step (`R7`) feeding the final theorem.
See `.mathlib-quality/decomposition.md` for source quotes and per-leaf verification. -/

open Filter Topology

set_option linter.unusedSectionVars false

noncomputable section

namespace TateFredholm

section SerreResidue

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- **R1.**  Discreteness: under the largest-norm-`< 1` hypothesis the value group is
`‖π‖^ℤ`.  [Bel] p. 58: "the set of non-zero norms `|R∗|` is the discrete subgroup
`|π|^ℤ`". -/
theorem exists_norm_eq_zpow (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖) {x : K} (hx : x ≠ 0) :
    ∃ n : ℤ, ‖x‖ = ‖π‖ ^ n := by
  sorry

/-- **R2.**  The unit ball `K⁰ = {x : ‖x‖ ≤ 1}` is a subring ([Bel] p. 58: "`R⁰` the set
of elements of `R` such that `|r| ≤ 1`, which is a subring of `R`"). -/
def unitBall (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K] : Subring K where
  carrier := {x : K | ‖x‖ ≤ 1}
  mul_mem' := by sorry
  one_mem' := by sorry
  add_mem' := by sorry
  zero_mem' := by sorry
  neg_mem' := by sorry

/-- **R3.**  Units of the unit ball are the norm-one elements. -/
theorem unitBall_isUnit_iff (x : unitBall K) : IsUnit x ↔ ‖(x : K)‖ = 1 := by
  sorry

/-- **R4.**  `(π)` is a maximal ideal of `K⁰` (so `K⁰/(π)` is the residue *field*, via
`Ideal.Quotient.field`) — the general-`K` form of [Bel]'s "`M̃` has a basis over `𝔽_p`". -/
theorem isMaximal_span_pi (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖) :
    (Ideal.span {(⟨π, hπ1.le⟩ : unitBall K)}).IsMaximal := by
  sorry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace K E] [IsUltrametricDist E]
  [CompleteSpace E]

/-- **R5.**  Residue-basis interface (quotient-free phrasing): there is a family of
norm-one vectors whose residues mod `π` form a basis — spanning = one-step approximation,
independence = norms detect residues.  The proof route builds `Ẽ = E⁰/πE⁰` over the
residue field of `R4` and applies `Basis.ofVectorSpace`; the statement deliberately
avoids the quotient so downstream leaves consume only norms. -/
theorem exists_residue_approx (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    (hE : ∀ m : E, m ≠ 0 → ∃ n : ℤ, ‖m‖ = ‖π‖ ^ n) :
    ∃ (ι : Type _) (e : ι → E), (∀ i, ‖e i‖ = 1) ∧
      (∀ m : E, ‖m‖ ≤ 1 → ∃ a : ι →₀ K, (∀ i, ‖a i‖ ≤ 1) ∧
        ‖m - a.sum fun i c => c • e i‖ ≤ ‖π‖) ∧
      (∀ a : ι →₀ K, (∀ i, ‖a i‖ ≤ 1) →
        ‖a.sum fun i c => c • e i‖ ≤ ‖π‖ → ∀ i, ‖a i‖ ≤ ‖π‖) := by
  sorry

/-- **R6a.**  Successive approximation (the analytic heart, [Bel] Lemma II.1.12 proof):
given a residue-approximating family, every vector has a `c(ι, K)`-expansion realising
its norm. -/
theorem exists_expansion_of_residue_approx (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hE : ∀ m : E, m ≠ 0 → ∃ n : ℤ, ‖m‖ = ‖π‖ ^ n)
    {ι : Type*} (e : ι → E) (he : ∀ i, ‖e i‖ = 1)
    (happrox : ∀ m : E, ‖m‖ ≤ 1 → ∃ a : ι →₀ K, (∀ i, ‖a i‖ ≤ 1) ∧
      ‖m - a.sum fun i c => c • e i‖ ≤ ‖π‖) (m : E) :
    ∃ a : c(ι, K), HasSum (fun i => a i • e i) m ∧ (⨆ i, ‖a i‖) = ‖m‖ := by
  sorry

/-- **R6b.**  Coefficient uniqueness from residue independence ([Bel] Lemma II.1.12,
converse direction of the expansion). -/
theorem expansion_unique_of_residue_indep (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    {ι : Type*} (e : ι → E)
    (hindep : ∀ a : ι →₀ K, (∀ i, ‖a i‖ ≤ 1) →
      ‖a.sum fun i c => c • e i‖ ≤ ‖π‖ → ∀ i, ‖a i‖ ≤ ‖π‖)
    {a b : c(ι, K)} {m : E}
    (ha : HasSum (fun i => a i • e i) m) (hb : HasSum (fun i => b i • e i) m) :
    a = b := by
  sorry

/-- **R6.**  Assembly: a Banach space whose norms lie in `‖π‖^ℤ ∪ {0}` is ONable
([Bel] Lemma II.1.12, packaged for our iso-based `IsONable`). -/
theorem isONable_of_discrete_norms (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖)
    (hE : ∀ m : E, m ≠ 0 → ∃ n : ℤ, ‖m‖ = ‖π‖ ^ n) :
    IsONable K E := by
  sorry

open Classical in
/-- **R7 data.**  The rescaled norm of [Bel] Theorem II.1.13's proof:
`‖m‖′ = inf {‖π‖^n : n ∈ ℤ, ‖m‖ ≤ ‖π‖^n}`, in closed form via the floor of a log
ratio (`0` at `m = 0`). -/
noncomputable def rescale (π : K) (m : E) : ℝ :=
  if m = 0 then 0 else ‖π‖ ^ (⌊Real.log ‖m‖ / Real.log ‖π‖⌋ : ℤ)

/-- **R7a.**  Sandwich: `‖m‖ ≤ ‖m‖′ < ‖π‖⁻¹ ‖m‖` — the rescaled norm is equivalent to
the original ("a norm ... equivalent to `|·|`", [Bel] p. 58). -/
theorem le_rescale_and_rescale_lt (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1) (m : E)
    (hm : m ≠ 0) :
    ‖m‖ ≤ rescale π m ∧ rescale π m < ‖π‖⁻¹ * ‖m‖ := by
  sorry

/-- **R7b.**  The rescaled norm is ultrametric. -/
theorem rescale_add_le (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1) (m n : E) :
    rescale π (m + n) ≤ max (rescale π m) (rescale π n) := by
  sorry

/-- **R7c.**  The rescaled norm is exactly `K`-homogeneous (uses discreteness `R1`: every
scalar norm is a `‖π‖`-power). -/
theorem rescale_smul (π : K) (hπ0 : 0 < ‖π‖) (hπ1 : ‖π‖ < 1)
    (hπmax : ∀ x : K, ‖x‖ < 1 → ‖x‖ ≤ ‖π‖) (c : K) (m : E) :
    rescale π (c • m) = ‖c‖ * rescale π m := by
  sorry

end SerreResidue

end TateFredholm

end
