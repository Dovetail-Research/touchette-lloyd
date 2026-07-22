-- VENDORED from teorth/pfr @ a177b2e4abe4b31c8024b9afebe646bf6bb8f91b
-- Upstream path: PFR/Mathlib/MeasureTheory/Measure/Dirac.lean
-- Do not edit by hand; see VENDORED.md. Re-sync with scripts/vendor.sh.
module

public import Mathlib.MeasureTheory.Measure.Dirac

public section

namespace MeasureTheory.Measure
variable {α : Type*} [MeasurableSpace α] {s : Set α} {a : α}

@[simp]
lemma dirac_real_apply' (a : α) (hs : MeasurableSet s) : (dirac a).real s = s.indicator 1 a := by
  by_cases ha : a ∈ s <;> simp [Measure.real, *]

end MeasureTheory.Measure
