-- VENDORED from teorth/pfr @ a177b2e4abe4b31c8024b9afebe646bf6bb8f91b
-- Upstream path: PFR/ForMathlib/Pair.lean
-- Do not edit by hand; see VENDORED.md. Re-sync with scripts/vendor.sh.
module

public import Mathlib.Util.Notation3
public import Mathlib.Tactic.Basic

public section

/-- The pair of two random variables -/
abbrev prod {Ω S T : Type*} (X : Ω → S) (Y : Ω → T) (ω : Ω) : S × T := (X ω, Y ω)

@[inherit_doc prod] notation3:100 "⟨" X ", " Y "⟩" => prod X Y

@[simp]
lemma prod_eq {Ω S T : Type*} {X : Ω → S} {Y : Ω → T} {ω : Ω} :
    (⟨ X, Y ⟩ : Ω → S × T) ω = (X ω, Y ω) := rfl
