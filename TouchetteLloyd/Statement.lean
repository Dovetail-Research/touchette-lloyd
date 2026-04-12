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

    `H(X) - H(Y) ≤ sup_{q blind} [H(X) - H(Y_q)] + I(X ; A)`

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

/-- Marginal distribution on `Y` (the final state):
    `P(y) = ∑_x ∑_a μ(x) · π(a | x) · κ(y | x, a)` -/
def marginalY (sys : ControlSystem S Act) (π : Policy S Act) :
    S → ℝ :=
  fun y => ∑ x : S, ∑ a : Act, sys.prior x * π.val x a * sys.dynamics (x, a) y

/-- Joint distribution on `(A, X)` (action first, state second):
    `P(a, x) = μ(x) · π(a | x)`

    This is the same data as `jointXA` but with the components swapped,
    so that `condEntropy jointAX = H(X | A)` and
    `marginalFst jointAX = P(A)`. -/
def jointAX (sys : ControlSystem S Act) (π : Policy S Act) :
    Act × S → ℝ :=
  fun ⟨a, x⟩ => sys.prior x * π.val x a

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

    `ΔH(π) = H(X) - H(Y)`

    where `H(Y)` is the (unconditional) entropy of the final state
    distribution. This measures how much the policy reduces uncertainty
    about the environment state. -/
def entropyReduction (sys : ControlSystem S Act) (π : Policy S Act) : ℝ :=
  shannonEntropy sys.prior - shannonEntropy (marginalY sys π)

/-- **Policy mutual information** `I(X ; A)`:

    The mutual information between the environment state and the action
    under policy `π`, computed from the marginal joint `P(X, A)`.

    This quantifies how much the policy's actions "model" or depend on
    the environment. For a blind policy, `I(X ; A) = 0`. -/
def policyMI (sys : ControlSystem S Act) (π : Policy S Act) : ℝ :=
  mutualInfo (jointXA sys π)

/-! ### Auxiliary lemmas on induced distributions -/

/-- The first marginal of `jointXA` recovers the prior: `∑_a P(x,a) = P(x)`.

    This holds because `π` is a Markov kernel: `∑_a π(a|x) = 1`. -/
lemma marginalFst_jointXA (sys : ControlSystem S Act) (π : Policy S Act) :
    marginalFst (jointXA sys π) = sys.prior := by
  ext x
  simp only [marginalFst, jointXA]
  rw [← Finset.mul_sum]
  simp [π.isKernel.sum_one x]

/-- The second marginal of `jointAY` recovers `marginalY`:
    `∑_a P(a,y) = P(y)`. -/
lemma marginalSnd_jointAY (sys : ControlSystem S Act) (π : Policy S Act) :
    marginalSnd (jointAY sys π) = marginalY sys π := by
  ext y
  simp only [marginalSnd, jointAY, marginalY]
  rw [Finset.sum_comm]

/-- The first marginal of `jointAX` equals the first marginal of `jointAY`.

    Both give the marginal action distribution
    `P(a) = ∑_x μ(x) · π(a|x)`. -/
lemma marginalFst_jointAX (sys : ControlSystem S Act) (π : Policy S Act) :
    marginalFst (jointAX sys π) = marginalFst (jointAY sys π) := by
  ext a
  simp only [marginalFst, jointAX, jointAY]
  rw [Finset.sum_comm]
  congr 1; ext x
  rw [← Finset.mul_sum]
  simp [sys.dynamics_isKernel.sum_one (x, a)]

/-- `jointAX` and `jointAY` have the same first-marginal entropy `H(A)`. -/
lemma shannonEntropy_marginalFst_AX_eq_AY
    (sys : ControlSystem S Act) (π : Policy S Act) :
    shannonEntropy (marginalFst (jointAX sys π)) =
      shannonEntropy (marginalFst (jointAY sys π)) := by
  rw [marginalFst_jointAX]

/-- The second marginal of `jointXA` equals the first marginal of `jointAX`.

    Both give the marginal action distribution `P(a) = ∑_x μ(x) · π(a|x)`. -/
lemma marginalSnd_jointXA_eq_marginalFst_jointAX
    (sys : ControlSystem S Act) (π : Policy S Act) :
    marginalSnd (jointXA sys π) = marginalFst (jointAX sys π) := by
  ext a
  simp [marginalSnd, marginalFst, jointXA, jointAX]

/-- Shannon entropy is invariant under swapping coordinates:
    `H(jointAX) = H(jointXA)`.

    This holds because summing `f(a,x) log f(a,x)` over all `(a,x)`
    gives the same result as summing `f(x,a) log f(x,a)` over all `(x,a)`,
    since `jointAX(a,x) = jointXA(x,a)` by definition. -/
lemma shannonEntropy_jointAX_eq_jointXA
    (sys : ControlSystem S Act) (π : Policy S Act) :
    shannonEntropy (jointAX sys π) = shannonEntropy (jointXA sys π) := by
  simp only [shannonEntropy, jointAX, jointXA]
  congr 1
  exact Fintype.sum_equiv (Equiv.prodComm Act S) _ _ (fun ⟨_, _⟩ => rfl)

/-! ### The theorem and its supporting lemmas -/

/-- The set of entropy reductions achievable by blind policies. -/
def blindReductions (sys : ControlSystem S Act) : Set ℝ :=
  { r : ℝ | ∃ π : Policy S Act, π.IsBlind ∧ entropyReduction sys π = r }

/-! #### Information-theoretic foundations -/

/-- **Gibbs' inequality / non-negativity of mutual information.**

    For any valid joint PMF, `I(X ; Y) ≥ 0`. This is equivalent to
    the Gibbs inequality `D_KL(p ∥ q) ≥ 0` applied to the joint vs.
    the product of marginals. -/
lemma mutualInfo_nonneg {X Y : Type*} [Fintype X] [Fintype Y]
    (joint : X × Y → ℝ) (hj : IsPMF joint) :
    0 ≤ mutualInfo joint := by
  sorry

/-- The joint distribution on `(A, Y)` is a valid PMF. -/
lemma jointAY_isPMF (sys : ControlSystem S Act) (π : Policy S Act) :
    IsPMF (jointAY sys π) := by
  sorry

/-! #### Proof Step 1 — Entropy reduction decomposes via conditional entropies

Following the proof in the companion post, we decompose:

    `H(X) - H(Y) = [H(X|A) - H(Y|A)] + [I(X;A) - I(Y;A)]`

In our definitions:
- `H(X|A) = condEntropy (jointAX sys π)`  (since jointAX is on Act × S)
- `H(Y|A) = condEntropy (jointAY sys π)`  (since jointAY is on Act × S)
- `I(X;A) = policyMI sys π = mutualInfo (jointXA sys π)`
- `I(Y;A) = mutualInfo (jointAY sys π)`

The identity follows from `H(Z) = H(Z|A) + I(Z;A)` applied to both X and Y.
-/

/-- **Entropy reduction decomposition.**

    `H(X) - H(Y) = [H(X|A) - H(Y|A)] + [I(X;A) - I(Y;A)]`

    This is an algebraic identity following from the chain rule
    `H(Z) = H(Z|A) + I(Z;A)` applied to both X and Y. In our
    definitions, the `I(X;A)` term equals `policyMI` and uses the
    fact that `marginalFst jointXA = sys.prior` and
    `marginalSnd jointAY = marginalY`. -/
lemma entropyReduction_decomp (sys : ControlSystem S Act) (π : Policy S Act) :
    entropyReduction sys π =
      (condEntropy (jointAX sys π) - condEntropy (jointAY sys π))
      + (policyMI sys π - mutualInfo (jointAY sys π)) := by
  simp only [entropyReduction, condEntropy, policyMI, mutualInfo]
  rw [marginalFst_jointXA, marginalSnd_jointAY, shannonEntropy_marginalFst_AX_eq_AY,
      shannonEntropy_jointAX_eq_jointXA,
      show shannonEntropy (marginalSnd (jointXA sys π)) =
           shannonEntropy (marginalFst (jointAY sys π)) from by
        rw [marginalSnd_jointXA_eq_marginalFst_jointAX, marginalFst_jointAX]]
  ring

/-! #### Proof Step 2 — Each action's conditional system is a blind policy

For each action value `a`, the conditional distribution `P(X | A = a)`
together with the fixed action `a` constitutes a blind policy. Its entropy
reduction `H(X | A=a) - H(Y | A=a)` therefore cannot exceed `ΔH_blind^max`.

Taking the expectation over `A` yields:
    `H(X|A) - H(Y|A) ≤ ΔH_blind^max = sSup (blindReductions sys)`
-/

/-- **Conditional entropy reduction is bounded by the blind supremum.**

    `H(X|A) - H(Y|A) ≤ sup_{q blind} ΔH(q)`

    This is the core semantic step: for each action value `a`, the
    conditional distribution `P(·|A=a)` with fixed action `a` acts as
    a blind policy, so its entropy reduction cannot exceed the blind
    maximum. Averaging over `a` preserves the bound. -/
lemma condEntropy_reduction_le_blind_sup
    (sys : ControlSystem S Act) (π : Policy S Act)
    (hne : Set.Nonempty (blindReductions sys))
    (hbd : BddAbove (blindReductions sys)) :
    condEntropy (jointAX sys π) - condEntropy (jointAY sys π) ≤
      sSup (blindReductions sys) := by
  sorry

/-! #### Proof Step 3 — Assemble the main inequality

From the decomposition (Step 1):
    `ΔH(π) = [H(X|A) - H(Y|A)] + [I(X;A) - I(Y;A)]`

From the conditional bound (Step 2):
    `H(X|A) - H(Y|A) ≤ ΔH_blind^max`

From non-negativity of mutual information:
    `I(Y;A) ≥ 0`

Therefore:
    `ΔH(π) ≤ ΔH_blind^max + I(X;A) - I(Y;A) ≤ ΔH_blind^max + I(X;A)`  ∎
-/

/-- **The Touchette-Lloyd Theorem.**

For any control system and any policy `π`, the entropy reduction achieved
by `π` is bounded by the best entropy reduction achievable by any blind
policy, plus the mutual information `I(X ; A)` under `π`:

    `H(X) - H(Y) ≤ sup_{q blind} [H(X) - H(Y_q)] + I(X ; A)`

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
  -- Step 1: Decompose ΔH into conditional entropies and mutual informations
  rw [entropyReduction_decomp]
  -- Step 2: The conditional entropy reduction is bounded by the blind maximum
  have hcond := condEntropy_reduction_le_blind_sup sys π hne hbd
  -- Step 3: I(Y ; A) ≥ 0 by Gibbs' inequality
  have hmi := mutualInfo_nonneg (jointAY sys π) (jointAY_isPMF sys π)
  -- Conclude: (cond gap) + (I(X;A) - I(Y;A)) ≤ sup + I(X;A)
  linarith

/-! ### Corollary and supporting results -/

/-- A corollary in universally-quantified form: the entropy reduction of any
    sighted policy exceeds that of any *specific* blind policy by at most
    `I(X ; A)`. This form avoids the `sSup` and is often easier to work with.

    Note this is slightly weaker than `touchette_lloyd` (which compares
    against the *best* blind policy). -/
theorem touchette_lloyd' (sys : ControlSystem S Act)
    (π : Policy S Act) (q : Policy S Act) (hq : q.IsBlind) :
    entropyReduction sys π - entropyReduction sys q ≤ policyMI sys π := by
  sorry

/-- A blind policy has zero mutual information with the environment state.
    This is because `P(X, A) = P(X) · P(A)` when `π` is blind, so
    `I(X ; A) = 0`. -/
theorem blind_policyMI_eq_zero (sys : ControlSystem S Act)
    (π : Policy S Act) (hπ : π.IsBlind) :
    policyMI sys π = 0 := by
  sorry

end TouchetteLloyd

end
