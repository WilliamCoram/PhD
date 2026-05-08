import Mathlib.RingTheory.MvPowerSeries.Basic

open Finset (antidiagonal mem_antidiagonal)

namespace MvPowerSeries

open Finsupp

variable {σ R : Type*}

variable [Semiring R]

variable (m n : σ →₀ ℕ) (φ ψ : MvPowerSeries σ R)

variable {S T : Type*}  [Semiring S] [Semiring T]
variable (f : R →+* S) (g : S →+* T)

open Function

variable {f}

theorem map_injective (hf : Injective f) :
    Injective (map f : MvPowerSeries σ R → MvPowerSeries σ S) := by
  simp [Injective, MvPowerSeries.ext_iff]
  grind

theorem map_injective_iff : Injective (map (σ := σ) f) ↔ Injective f := by
  refine ⟨fun h r r' eq ↦ ?_, map_injective⟩
  specialize h (a₁ := C r) (a₂ := C r')
  simp only [map_C, eq, forall_const] at h
  rw [← constantCoeff_C r, ← constantCoeff_C r', h]

theorem map_surjective (hf : Surjective f) :
    Surjective (map f : MvPowerSeries σ R → MvPowerSeries σ S) := by
  intro p; choose q _ using fun _ ↦ hf (coeff _ p)
  use q; simpa [MvPowerSeries.ext_iff]

theorem map_surjective_iff : Surjective (map (σ := σ) f) ↔ Surjective f := by
  refine ⟨fun h ↦ ?_, map_surjective⟩
  intro s; obtain ⟨p, hp⟩ := h (C s)
  rw [MvPowerSeries.ext_iff] at hp
  use constantCoeff p; simpa using hp 0

/-- If `f` is a left-inverse of `g` then `map f` is a left-inverse of `map g`. -/
theorem map_leftInverse {g : S →+* R} (hf : LeftInverse f g) :
    LeftInverse (map f : MvPowerSeries σ R → MvPowerSeries σ S) (map g) := fun p => by
  simp [← RingHom.comp_apply, ← map_comp, (RingHom.ext hf : f.comp g = RingHom.id _)]

/-- If `f` is a right-inverse of `g` then `map f` is a right-inverse of `map g`. -/
theorem map_rightInverse {g : S →+* R} (hf : RightInverse f g) :
    RightInverse (map f : MvPowerSeries σ R →  MvPowerSeries σ S) (map g) :=
  (map_leftInverse hf.leftInverse).rightInverse
