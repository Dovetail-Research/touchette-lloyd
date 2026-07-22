-- VENDORED from teorth/pfr @ a177b2e4abe4b31c8024b9afebe646bf6bb8f91b
-- Upstream path: PFR/Mathlib/Data/Set/Insert.lean
-- Do not edit by hand; see VENDORED.md. Re-sync with scripts/vendor.sh.
module

public import Mathlib.Data.Set.Insert

public section

namespace Set
variable {α : Type*} {s t : Set α}

-- TODO: Rename `inter_singleton_eq_empty` to `inter_singleton_eq_empty_iff`
@[simp] alias ⟨_, inter_singleton_eq_empty'⟩ := inter_singleton_eq_empty

-- TODO: Rename `singleton_inter_eq_empty` to `singleton_inter_eq_empty_iff`
@[simp] alias ⟨_, singleton_inter_eq_empty'⟩ := singleton_inter_eq_empty

end Set
