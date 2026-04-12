import TouchetteLloyd.InfoTheory
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Probability.Independence.Basic

/-!
# The Touchette-Lloyd Theorem

## Background

Touchette and Lloyd (2000) proved a fundamental bound relating "optimization"
(entropy reduction in a controlled system) to "modeling" (mutual information
between a controller's actions and the environment's state).

Informally: each bit of mutual information between a controller and the
environment it acts on can buy at most one additional bit of entropy
reduction beyond what is achievable without any feedback.

## Setup

A **control system** is a probability space `Ω` equipped with three
random variables:
- `X : Ω → S`   — the initial environment state
- `A : Ω → Act`  — the action chosen by the policy
- `Y : Ω → S`   �� the final environment state

The dynamics are encoded in the joint distribution: the law of `(X, A, Y)`
on `Ω` captures the prior `P(X)`, the policy `P(A|X)`, and the dynamics
`P(Y|X,A)` simultaneously.

A policy is **blind** if `X` and `A` are independent (`IndepFun X A μ`),
meaning the action does not depend on the state.

## Theorem

For any policy:

    `H[X] - H[Y] ≤ sup_{blind} [H[X] - H[Y_blind]] + I[X : A]`

## Reference

H. Touchette and S. Lloyd, "Information-theoretic approach to the study
of control systems," Physica A, vol. 331, pp. 140–172, 2004.
arXiv: physics/0104007
-/

noncomputable section

open MeasureTheory Real Finset
open scoped BigOperators ENNReal

namespace TouchetteLloyd

variable {Ω : Type*} [MeasurableSpace Ω]
variable {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
variable {Act : Type*} [MeasurableSpace Act] [MeasurableSingletonClass Act] [Fintype Act]

/-! ### Control system definitions -/

/-- A **control system** bundles a probability space with the three random
    variables (initial state, action, final state) and measurability proofs. -/
structure ControlSystem (Ω S Act : Type*)
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace Act] where
  /-- Probability measure on the sample space. -/
  μ : Measure Ω
  /-- The measure is a probability measure. -/
  prob : IsProbabilityMeasure μ
  /-- Initial environment state. -/
  X : Ω → S
  /-- Action chosen by the policy. -/
  A : Ω → Act
  /-- Final environment state. -/
  Y : Ω → S
  /-- Measurability of X. -/
  hX : Measurable X
  /-- Measurability of A. -/
  hA : Measurable A
  /-- Measurability of Y. -/
  hY : Measurable Y

variable (sys : ControlSystem Ω S Act)

instance : IsProbabilityMeasure sys.μ := sys.prob

/-! ### Entropy reduction and mutual information -/

/-- **Entropy reduction**: `ΔH = H[X] - H[Y]`.

    Measures how much the policy reduces uncertainty about the
    environment state. -/
def entropyReduction (sys : ControlSystem Ω S Act) : ℝ :=
  H[sys.X ; sys.μ] - H[sys.Y ; sys.μ]

/-- **Policy mutual information**: `I[X : A]`.

    Measures how much the policy's actions depend on (or "model")
    the environment state. For a blind policy, this is zero. -/
def policyMI (sys : ControlSystem Ω S Act) : ℝ :=
  I[sys.X : sys.A ; sys.μ]

/-! ### Blind systems -/

/-- A control system is **blind** if the action is independent of the
    initial state: `IndepFun X A μ`.

    Equivalently, `P(X, A) = P(X) · P(A)`, so the agent chooses its
    action without observing the environment. -/
def ControlSystem.IsBlind (sys : ControlSystem Ω S Act) : Prop :=
  ProbabilityTheory.IndepFun sys.X sys.A sys.μ

/-! ### The theorem and its supporting lemmas -/

/-- The set of entropy reductions achievable by blind control systems
    (over all possible probability spaces, priors, dynamics, and blind policies). -/
def blindReductions : Set ℝ :=
  { r : ℝ | ∃ (Ω' : Type) (_ : MeasurableSpace Ω')
      (sys' : ControlSystem Ω' S Act), sys'.IsBlind ∧ entropyReduction sys' = r }

/-! #### Information-theoretic foundations -/

/-- **Gibbs' inequality**: mutual information is nonneg. -/
lemma policyMI_nonneg (sys : ControlSystem Ω S Act) :
    0 ≤ policyMI sys :=
  mutualInfo_nonneg sys.X sys.A sys.μ sys.hX sys.hA

/-- **I(Y ; A) ≥ 0**: mutual information between outcome and action. -/
lemma mutualInfo_YA_nonneg (sys : ControlSystem Ω S Act) :
    0 ≤ I[sys.Y : sys.A ; sys.μ] :=
  mutualInfo_nonneg sys.Y sys.A sys.μ sys.hY sys.hA

/-! #### Proof Step 1 — Entropy reduction decomposes via conditional entropies

    `H[X] - H[Y] = [H[X|A] - H[Y|A]] + [I[X:A] - I[Y:A]]`

This follows from `I[Z:A] = H[Z] - H[Z|A]` applied to both X and Y. -/

lemma entropyReduction_decomp (sys : ControlSystem Ω S Act) :
    entropyReduction sys =
      (H[sys.X | sys.A ; sys.μ] - H[sys.Y | sys.A ; sys.μ])
      + (policyMI sys - I[sys.Y : sys.A ; sys.μ]) := by
  simp only [entropyReduction, policyMI, mutualInfo, condEntropy, entropy]
  ring

/-! #### Proof Step 2 — Each action's conditional system is a blind policy

    `H[X|A] - H[Y|A] ≤ ΔH_blind^max`

For each action value `a`, the conditional distribution `P(·|A=a)` with
fixed action `a` constitutes a blind policy. Averaging over `a` gives
the bound. -/

lemma condEntropy_reduction_le_blind_sup
    (sys : ControlSystem Ω S Act)
    (hne : Set.Nonempty (blindReductions (S := S) (Act := Act)))
    (hbd : BddAbove (blindReductions (S := S) (Act := Act))) :
    H[sys.X | sys.A ; sys.μ] - H[sys.Y | sys.A ; sys.μ] ≤
      sSup (blindReductions (S := S) (Act := Act)) := by
  sorry

/-! #### Proof Step 3 — Assemble the main inequality

From the decomposition (Step 1):
    `ΔH = [H[X|A] - H[Y|A]] + [I[X:A] - I[Y:A]]`

From the conditional bound (Step 2):
    `H[X|A] - H[Y|A] ≤ ΔH_blind^max`

From non-negativity of mutual information:
    `I[Y:A] ≥ 0`

Therefore:
    `ΔH ≤ ΔH_blind^max + I[X:A] - I[Y:A] ≤ ΔH_blind^max + I[X:A]`  ∎ -/

/-- **The Touchette-Lloyd Theorem.**

For any control system, the entropy reduction is bounded by the best
entropy reduction achievable by any blind policy, plus the mutual
information `I[X : A]`:

    `H[X] - H[Y] ≤ sup_{blind} ΔH_blind + I[X : A]`

Each bit of "modeling" (mutual information with the environment) buys
at most one additional bit of "optimization" (entropy reduction) beyond
what is achievable without feedback. -/
theorem touchette_lloyd
    (sys : ControlSystem Ω S Act)
    (hne : Set.Nonempty (blindReductions (S := S) (Act := Act)))
    (hbd : BddAbove (blindReductions (S := S) (Act := Act))) :
    entropyReduction sys ≤ sSup (blindReductions (S := S) (Act := Act)) + policyMI sys := by
  -- Step 1: Decompose ΔH into conditional entropies and mutual informations
  rw [entropyReduction_decomp]
  -- Step 2: The conditional entropy reduction is bounded by the blind maximum
  have hcond := condEntropy_reduction_le_blind_sup sys hne hbd
  -- Step 3: I[Y : A] ≥ 0 by Gibbs' inequality
  have hmi := mutualInfo_YA_nonneg sys
  -- Conclude
  linarith

/-! ### Corollary and supporting results -/

/-- A blind system has zero policy mutual information. -/
theorem blind_policyMI_eq_zero (sys : ControlSystem Ω S Act) (hblind : sys.IsBlind) :
    policyMI sys = 0 := by
  sorry

end TouchetteLloyd

end
