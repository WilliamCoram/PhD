/-
Copyright (c) 2026 William Coram. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Coram
-/
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# The `v`-adic completion of a number field is a nontrivially normed field

Mathlib makes `v.adicCompletion K` a `NormedField` (`Valued.toNormedField`, via the rank-one
valuation `instRankOneAdicCompletion`); the nontriviality of the norm (a uniformizer has norm
`< 1`) is `Valued.toNontriviallyNormedField`, which mathlib keeps as a *scoped* instance
(`open scoped Valued`) because of the `ℚ_p` diamond.  On adic completions there is no
competing instance, so we register it globally: this is the typeclass pack the
overconvergent-forms layer (`PhD/QMF/Weight/`) needs at `K = v.adicCompletion F`.

## Main declarations

* `NumberField.HeightOneSpectrum.instNontriviallyNormedFieldAdicCompletion` — the
  global `NontriviallyNormedField (v.adicCompletion K)` instance, definitionally
  `Valued.toNontriviallyNormedField` on top of mathlib's `NormedField` instance.
-/

namespace NumberField.HeightOneSpectrum

open IsDedekindDomain
open scoped WithZero

variable {K : Type*} [Field K] [NumberField K] (v : HeightOneSpectrum (RingOfIntegers K))

/-- The `v`-adic completion of a number field is a nontrivially normed field
(`Valued.toNontriviallyNormedField`, on top of mathlib's `NormedField` instance). -/
noncomputable instance instNontriviallyNormedFieldAdicCompletion :
    NontriviallyNormedField (v.adicCompletion K) :=
  Valued.toNontriviallyNormedField (v.adicCompletion K) ℤᵐ⁰

end NumberField.HeightOneSpectrum

-- The new instance sits on top of mathlib's `NormedField` instance: same norm, no diamond.
example {K : Type*} [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum
    (NumberField.RingOfIntegers K)) :
    (NumberField.HeightOneSpectrum.instNontriviallyNormedFieldAdicCompletion v).toNormedField
      = NumberField.HeightOneSpectrum.instNormedFieldValuedAdicCompletion K v := rfl
