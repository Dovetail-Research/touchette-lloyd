-- VENDORED from teorth/pfr @ 0811856fd51caca800c7786d85b79541e8704f54
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
