/-
Copyright (c) 2025 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Salvatore Mercuri
-/
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Adic Valuation

Material destined for Mathlib.
-/

namespace IsDedekindDomain.HeightOneSpectrum

-- TODO upstream
open IsDedekindDomain

instance {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Countable K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) :
    TopologicalSpace.SeparableSpace (v.adicCompletion K) where
  exists_countable_dense :=
    -- `adicCompletion` is now a one-field structure (not defeq to `Completion`), so use the
    -- mathlib-provided dense range of `algebraMap K → adicCompletion` and `K`'s countability.
    ⟨Set.range (algebraMap K (v.adicCompletion K)),
      Set.countable_range _, denseRange_algebraMap K v⟩

-- PORT: the FLT lemma `intValuation_eq_coe_neg_multiplicity` is skipped: it landed in mathlib
-- as `IsDedekindDomain.HeightOneSpectrum.intValuation_eq_exp_neg_multiplicity`
-- (Mathlib.RingTheory.DedekindDomain.AdicValuation) with an identical statement.

/-- `adicCompletion.equiv` as a `K`-algebra isomorphism onto the underlying completion. -/
noncomputable def adicCompletion.algEquiv
    {A : Type*} [CommRing A] [IsDedekindDomain A] (K : Type*) [Field K] [Algebra A K]
    [IsFractionRing A K] (v : HeightOneSpectrum A) :
    v.adicCompletion K ≃ₐ[K] (v.valuation K).Completion :=
  AlgEquiv.ofRingEquiv (f := adicCompletion.equiv K v)
    fun x => algebraMap_adicCompletion_toCompletion A K v x

end IsDedekindDomain.HeightOneSpectrum
