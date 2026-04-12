import TouchetteLloyd.InfoTheory
import Mathlib.Order.ConditionallyCompleteLattice.Basic

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

A **control system** consists of:
- A finite state space `S` and finite action space `Act`
- A prior distribution `μ : S → ℝ` over initial environment states
- Dynamics `κ : S × Act → S → ℝ`, a Markov kernel giving `P(Y | X, A)`

A **policy** is a Markov kernel `π : S → Act → ℝ` giving `P(A | X)`.

Together these induce a joint distribution over `(X, A, Y)`:

    `P(x, a, y) = μ(x) · π(x, a) · κ((x, a), y)`

A policy is **blind** if the action distribution is independent of the
state: `π(x, a) = π(x', a)` for all `x, x', a`. Equivalently, a blind
policy is just a fixed distribution over `Act`.

## Theorem

For any policy `π`:

    `H(X) - H(Y | A) ≤ sup_{q blind} [H(X) - H(Y_q | A_q)] + I(X ; A)`

where `I(X ; A)` is the mutual information between state and action
under policy `π`.

## Reference

H. Touchette and S. Lloyd, "Information-theoretic approach to the study
of control systems," Physica A, vol. 331, pp. 140–172, 2004.
arXiv: physics/0104007
-/

noncomputable section

open Finset Real
open scoped BigOperators

namespace TouchetteLloyd

variable {S Act : Type*} [Fintype S] [Fintype Act]

/-! ### Control system definitions -/

/-- A discrete control system with finite state space `S` and action space `Act`. -/
structure ControlSystem (S : Type*) (Act : Type*) [Fintype S] [Fintype Act] where
  /-- Prior distribution over initial states `P(X)`. -/
  prior : S → ℝ
  prior_isPMF : IsPMF prior
  /-- Dynamics kernel `P(Y | X, A)`. -/
  dynamics : S × Act → S → ℝ
  dynamics_isKernel : IsMarkovKernel dynamics

/-- A policy `P(A | X)`, represented as a Markov kernel from states to actions. -/
structure Policy (S : Type*) (Act : Type*) [Fintype S] [Fintype Act] where
  /-- The policy kernel `π(a | x)`. -/
  val : S → Act → ℝ
  isKernel : IsMarkovKernel val

/-! ### Induced distributions -/

/-- The joint distribution on `S × Act × S` induced by a control system
    and a policy:
    `P(x, a, y) = μ(x) · π(a | x) · κ(y | x, a)` -/
def inducedJoint (sys : ControlSystem S Act) (π : Policy S Act) :
    S × Act × S → ℝ :=
  fun ⟨x, a, y⟩ => sys.prior x * π.val x a * sys.dynamics (x, a) y

/-- Marginal joint distribution on `(X, A)`:
    `P(x, a) = μ(x) · π(a | x)` -/
def jointXA (sys : ControlSystem S Act) (π : Policy S Act) :
    S × Act → ℝ :=
  fun ⟨x, a⟩ => sys.prior x * π.val x a

/-- Marginal joint distribution on `(A, Y)`:
    `P(a, y) = ∑_x μ(x) · π(a | x) · κ(y | x, a)` -/
def jointAY (sys : ControlSystem S Act) (π : Policy S Act) :
    Act × S → ℝ :=
  fun ⟨a, y⟩ => ∑ x : S, sys.prior x * π.val x a * sys.dynamics (x, a) y

/-! ### Blind policies -/

/-- A policy is **blind** (or "open-loop") if the action distribution does not
    depend on the state. This means `P(A | X) = P(A)`, i.e., the agent chooses
    its action without observing the environment. -/
def Policy.IsBlind (π : Policy S Act) : Prop :=
  ∀ (x₁ x₂ : S) (a : Act), π.val x₁ a = π.val x₂ a

/-- Construct a blind policy from a fixed action distribution `q`. -/
def blindPolicyOf [Nonempty S] (q : Act → ℝ) (hq : IsPMF q) : Policy S Act where
  val := fun _ a => q a
  isKernel :=
    { nonneg := fun _ a => hq.nonneg a
      sum_one := fun _ => hq.sum_one }

theorem blindPolicyOf_isBlind [Nonempty S] (q : Act → ℝ) (hq : IsPMF q) :
    (blindPolicyOf (S := S) q hq).IsBlind :=
  fun _ _ _ => rfl

/-! ### Entropy reduction and mutual information -/

/-- **Entropy reduction** achieved by policy `π`:

    `ΔH(π) = H(X) - H(Y | A)`

    where `H(Y | A)` is the conditional entropy of the outcome given
    the action, computed from the marginal joint `P(A, Y)`.

    This measures how much the policy reduces our uncertainty about
    the environment state. -/
def entropyReduction (sys : ControlSystem S Act) (π : Policy S Act) : ℝ :=
  shannonEntropy sys.prior - condEntropy (jointAY sys π)

/-- **Policy mutual information** `I(X ; A)`:

    The mutual information between the environment state and the action
    under policy `π`, computed from the marginal joint `P(X, A)`.

    This quantifies how much the policy's actions "model" or depend on
    the environment. For a blind policy, `I(X ; A) = 0`. -/
def policyMI (sys : ControlSystem S Act) (π : Policy S Act) : ℝ :=
  mutualInfo (jointXA sys π)

/-! ### The theorem -/

/-- The set of entropy reductions achievable by blind policies. -/
def blindReductions (sys : ControlSystem S Act) : Set ℝ :=
  { r : ℝ | ∃ π : Policy S Act, π.IsBlind ∧ entropyReduction sys π = r }

/-- **The Touchette-Lloyd Theorem.**

For any control system and any policy `π`, the entropy reduction achieved
by `π` is bounded by the best entropy reduction achievable by any blind
policy, plus the mutual information `I(X ; A)` under `π`:

    `H(X) - H(Y | A) ≤ sup_{q blind} [H(X) - H(Y_q | A_q)] + I(X ; A)`

Equivalently: each bit of "modeling" (mutual information with the
environment) can buy at most one additional bit of "optimization"
(entropy reduction) beyond what is achievable without feedback.

**Note:** The `BddAbove` and `Set.Nonempty` hypotheses ensure the
supremum is well-defined. Both hold automatically for finite state
and action spaces (the set of blind policies is compact and nonempty),
but we leave them as explicit hypotheses for now. -/
theorem touchette_lloyd
    (sys : ControlSystem S Act) (π : Policy S Act)
    (hne : Set.Nonempty (blindReductions sys))
    (hbd : BddAbove (blindReductions sys)) :
    entropyReduction sys π ≤ sSup (blindReductions sys) + policyMI sys π := by
  sorry

/-- A corollary in universally-quantified form: the entropy reduction of any
    sighted policy exceeds that of any *specific* blind policy by at most
    `I(X ; A)`. This form avoids the `sSup` and is often easier to work with.

    Note this is slightly weaker than `touchette_lloyd` (which compares
    against the *best* blind policy). -/
theorem touchette_lloyd' (sys : ControlSystem S Act)
    (π : Policy S Act) (q : Policy S Act) (hq : q.IsBlind) :
    entropyReduction sys π - entropyReduction sys q ≤ policyMI sys π := by
  sorry

/-! ### Key lemma: blind policies have zero mutual information -/

/-- A blind policy has zero mutual information with the environment state.
    This is because `P(X, A) = P(X) · P(A)` when `π` is blind, so
    `I(X ; A) = 0`. -/
theorem blind_policyMI_eq_zero (sys : ControlSystem S Act)
    (π : Policy S Act) (hπ : π.IsBlind) :
    policyMI sys π = 0 := by
  sorry

end TouchetteLloyd

end
