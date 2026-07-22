-- VENDORED from teorth/pfr @ a177b2e4abe4b31c8024b9afebe646bf6bb8f91b
-- Upstream path: PFR/Mathlib/Data/Set/Card.lean
-- Do not edit by hand; see VENDORED.md. Re-sync with scripts/vendor.sh.
module

public import Mathlib.Data.Set.Card
public import InfoTheory.PFR.Mathlib.Data.Set.Basic
public import InfoTheory.PFR.Mathlib.Data.Set.Insert

public section

namespace Set
variable {α : Type*}

-- TODO: Rename `ncard_singleton_inter` to `ncard_singleton_inter_le_one`

lemma ncard_singleton_inter' (a : α) (s : Set α) [Decidable (a ∈ s)] :
    ({a} ∩ s).ncard = if a ∈ s then 1 else 0 := by
  split_ifs <;> simp [*]

lemma ncard_inter_singleton (a : α) (s : Set α) [Decidable (a ∈ s)] :
    (s ∩ {a}).ncard = if a ∈ s then 1 else 0 := by
  split_ifs <;> simp [*]

end Set
