import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Real

/-!
# Shannon Information Theory (Discrete Finite Case)

Definitions of Shannon entropy, conditional entropy, and mutual information
for random variables on a probability space with finite codomains.

## Design

Following the design of `teorth/pfr`, random variables are modeled as
plain functions `X : Ω → S` from a probability space `Ω`. Entropy is
defined via Mathlib's `negMulLog` (`x ↦ -x * log x`) applied to the
pushed-forward measure.

We restrict to `Fintype` codomains (rather than pfr's more general
`FiniteRange` typeclass) since our state and action spaces are finite.

## Main definitions

* `measureEntropy μ` : entropy of a measure, `Hm[μ]`
* `entropy X μ` : Shannon entropy of a random variable, `H[X ; μ]`
* `mutualInfo X Y μ` : mutual information, `I[X : Y ; μ]`

## Main results

* `mutualInfo_nonneg` : `0 ≤ I[X : Y ; μ]` (via Jensen / Gibbs)
* `chain_rule` : `H[⟨X, Y⟩ ; μ] = H[Y ; μ] + H[X | Y ; μ]`

## References

* H. Touchette, S. Lloyd, "Information-theoretic approach to the study of
  control systems," Physica A, 2004.
* T. Tao et al., teorth/pfr (Lean 4 formalization of PFR conjecture)
-/

noncomputable section

open MeasureTheory Real Finset
open scoped BigOperators ENNReal

namespace TouchetteLloyd

/-! ### Measure entropy -/

/-- Entropy of a probability measure on a finite measurable type.

    `Hm[μ] = ∑ s, negMulLog (μ.real {s})`

    where `negMulLog x = -x * log x` (with the convention `0 log 0 = 0`). -/
def measureEntropy {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype S] (μ : Measure S) : ℝ :=
  ∑ s : S, negMulLog (μ.real {s})

notation:100 "Hm[" μ "]" => measureEntropy μ

lemma measureEntropy_nonneg {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype S] (μ : Measure S) [IsProbabilityMeasure μ] :
    0 ≤ Hm[μ] := by
  apply Finset.sum_nonneg
  intro s _
  apply negMulLog_nonneg measureReal_nonneg
  calc μ.real {s} = (μ {s}).toReal := rfl
    _ ≤ (μ Set.univ).toReal := by
        apply ENNReal.toReal_mono (measure_ne_top μ _)
        exact measure_mono (Set.subset_univ _)
    _ = 1 := by simp [measure_univ]

/-! ### Random variable entropy -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Shannon entropy of a random variable `X : Ω → S`, defined as the
    measure entropy of its law (pushforward measure `μ.map X`).

    `H[X ; μ] = ∑ s, negMulLog (P(X = s))` -/
def entropy {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    (X : Ω → S) (μ : Measure Ω) : ℝ :=
  Hm[μ.map X]

notation:100 "H[" X " ; " μ "]" => entropy X μ

/-! ### Mutual information -/

/-- Mutual information of two random variables.

    `I[X : Y ; μ] = H[X ; μ] + H[Y ; μ] - H[⟨X, Y⟩ ; μ]`

    This measures the statistical dependence between X and Y.
    Equivalently, `I[X : Y] = H[X] - H[X | Y] = H[Y] - H[Y | X]`. -/
def mutualInfo {S T : Type*}
    [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : ℝ :=
  H[X ; μ] + H[Y ; μ] - H[fun ω => (X ω, Y ω) ; μ]

notation:100 "I[" X " : " Y " ; " μ "]" => mutualInfo X Y μ

/-! ### Conditional entropy -/

/-- Conditional entropy of X given Y, defined via the chain rule.

    `H[X | Y ; μ] = H[⟨X, Y⟩ ; μ] - H[Y ; μ]`

    This equals `∑_y P(Y=y) · H[X | Y=y]`, the expected entropy of X
    conditioned on the value of Y. -/
def condEntropy {S T : Type*}
    [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) : ℝ :=
  H[fun ω => (X ω, Y ω) ; μ] - H[Y ; μ]

notation:100 "H[" X " | " Y " ; " μ "]" => condEntropy X Y μ

/-! ### Basic identities -/

/-- The chain rule: `H[⟨X, Y⟩] = H[Y] + H[X | Y]`. -/
lemma chain_rule {S T : Type*}
    [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    H[fun ω => (X ω, Y ω) ; μ] = H[Y ; μ] + H[X | Y ; μ] := by
  simp [condEntropy]

/-- Mutual information equals entropy minus conditional entropy. -/
lemma mutualInfo_eq_entropy_sub_condEntropy {S T : Type*}
    [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) :
    I[X : Y ; μ] = H[X ; μ] - H[X | Y ; μ] := by
  simp [mutualInfo, condEntropy]
  ring

/-! ### Non-negativity of mutual information (Gibbs' inequality)

This is the key information-theoretic inequality: `I[X : Y ; μ] ≥ 0`.

The proof follows from Jensen's inequality applied to the concave function
`negMulLog`. Specifically, we express `I[X : Y]` as a KL-like sum
`∑_{s,t} P(s,t) log(P(s,t) / (P(s) P(t)))` and apply the log-sum inequality.

For a self-contained proof in the discrete finite case, see
`teorth/pfr` (`PFR.ForMathlib.Entropy.Measure`, `measureMutualInfo_nonneg`),
which uses `concaveOn_negMulLog.le_map_sum` from Mathlib. -/

lemma mutualInfo_nonneg {S T : Type*}
    [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) :
    0 ≤ I[X : Y ; μ] := by
  sorry

end TouchetteLloyd

end
