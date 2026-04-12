import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Shannon Information Theory (Discrete Finite Case)

Definitions of Shannon entropy, conditional entropy, and mutual information
for probability distributions over finite types.

We work with natural logarithm throughout (Mathlib's `Real.log`). To convert
to bits, divide by `Real.log 2`.

## Convention

We use the convention `0 · log 0 = 0`, which is automatic because
Mathlib defines `Real.log 0 = 0`.
-/

noncomputable section

open Finset Real
open scoped BigOperators

namespace TouchetteLloyd

/-! ### Valid probability distributions -/

/-- A function `p : Ω → ℝ` is a valid probability mass function if it is
    nonnegative and sums to 1. -/
structure IsPMF {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ p x
  sum_one : ∑ x : Ω, p x = 1

/-- A function `κ : X → Y → ℝ` is a valid Markov kernel if for each `x`,
    `κ x` is a PMF over `Y`. -/
structure IsMarkovKernel {X Y : Type*} [Fintype X] [Fintype Y]
    (κ : X → Y → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ κ x y
  sum_one : ∀ x, ∑ y : Y, κ x y = 1

/-! ### Shannon entropy -/

/-- Shannon entropy of a distribution `p` over a finite type `Ω`.

    `H(p) = - ∑_x p(x) · log(p(x))`

    This is always nonneg for valid PMFs (proof omitted here). -/
def shannonEntropy {Ω : Type*} [Fintype Ω] (p : Ω → ℝ) : ℝ :=
  - ∑ x : Ω, p x * Real.log (p x)

/-! ### Marginal distributions -/

/-- First marginal of a joint distribution on `X × Y`:
    `p₁(x) = ∑_y p(x, y)`. -/
def marginalFst {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X × Y → ℝ) : X → ℝ :=
  fun x => ∑ y : Y, p (x, y)

/-- Second marginal of a joint distribution on `X × Y`:
    `p₂(y) = ∑_x p(x, y)`. -/
def marginalSnd {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X × Y → ℝ) : Y → ℝ :=
  fun y => ∑ x : X, p (x, y)

/-! ### Conditional entropy and mutual information -/

/-- Conditional entropy `H(Y | X) = H(X, Y) - H(X)`.

    This equals `-∑_{x,y} p(x,y) log p(y|x)` when the marginal `p(x) > 0`
    for all `x` in the support. -/
def condEntropy {X Y : Type*} [Fintype X] [Fintype Y]
    (joint : X × Y → ℝ) : ℝ :=
  shannonEntropy joint - shannonEntropy (marginalFst joint)

/-- Mutual information `I(X ; Y) = H(X) + H(Y) - H(X, Y)`.

    Equivalent to `H(X) - H(X|Y)` or `H(Y) - H(Y|X)`. -/
def mutualInfo {X Y : Type*} [Fintype X] [Fintype Y]
    (joint : X × Y → ℝ) : ℝ :=
  shannonEntropy (marginalFst joint) + shannonEntropy (marginalSnd joint) -
    shannonEntropy joint

end TouchetteLloyd

end
