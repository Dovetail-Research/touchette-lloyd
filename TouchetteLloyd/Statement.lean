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
- `A : Ω → Act` — the action chosen by the policy
- `Y : Ω → S`   — the final environment state

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
variable {S : Type} [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
variable {Act : Type} [MeasurableSpace Act] [MeasurableSingletonClass Act] [Fintype Act]

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

/-! #### Entropy bounds -/

omit [MeasurableSingletonClass Act] [Fintype Act] in
/-- Entropy reduction is bounded above by the cardinality of the state space. -/
lemma entropyReduction_le_card (sys : ControlSystem Ω S Act) :
    entropyReduction sys ≤ Fintype.card S := by
  haveI : IsProbabilityMeasure (sys.μ.map sys.X) :=
    Measure.isProbabilityMeasure_map sys.hX.aemeasurable
  haveI : IsProbabilityMeasure (sys.μ.map sys.Y) :=
    Measure.isProbabilityMeasure_map sys.hY.aemeasurable
  simp only [entropyReduction, entropy]
  linarith [measureEntropy_le_card (sys.μ.map sys.X),
            measureEntropy_nonneg (sys.μ.map sys.Y)]

omit [MeasurableSingletonClass Act] [Fintype Act] in
/-- The set of blind entropy reductions is bounded above.

    Since `S` is finite, entropy is bounded by `|S|`, so every entropy
    reduction `H[X] - H[Y] ≤ H[X] ≤ |S|`. -/
lemma blindReductions_bddAbove : BddAbove (blindReductions (S := S) (Act := Act)) := by
  use Fintype.card S
  intro r ⟨Ω', mΩ', sys', _, hr⟩
  rw [← hr]
  exact entropyReduction_le_card sys'

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
fixed action `a` constitutes a blind policy. Its entropy reduction
`H[X|A=a] - H[Y|A=a]` is therefore in `blindReductions`. Since
`H[X|A] - H[Y|A] = Σ_a P(A=a) · (H[X|A=a] - H[Y|A=a])` is a convex
combination of values each ≤ `sSup(blindReductions)`, the bound follows.

We decompose this into three sub-lemmas. -/

/-- **Sub-lemma 2a: Conditional entropy representation.**

    `H[X|A] - H[Y|A]` can be expressed as a weighted average of per-action
    entropy reductions, with weights `P(A = a)` summing to 1.

    `H[X|A] - H[Y|A] = Σ_a P(A=a) · (H[X|A=a] - H[Y|A=a])`

    This follows from the standard representation of conditional entropy
    as `H[X|A] = Σ_a P(A=a) · H[X|A=a]`. -/
lemma condEntropy_diff_eq_weighted_sum
    (sys : ControlSystem Ω S Act) :
    ∃ (w : Act → ℝ) (r : Act → ℝ),
      (∀ a, 0 ≤ w a) ∧
      (∑ a : Act, w a = 1) ∧
      (H[sys.X | sys.A ; sys.μ] - H[sys.Y | sys.A ; sys.μ] = ∑ a, w a * r a) ∧
      (∀ a, w a > 0 →
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (sys' : ControlSystem Ω' S Act),
          sys'.IsBlind ∧ entropyReduction sys' = r a) := by
  -- Joint distributions on S × Act
  set νXA := sys.μ.map (fun ω => (sys.X ω, sys.A ω)) with νXA_def
  set νYA := sys.μ.map (fun ω => (sys.Y ω, sys.A ω)) with νYA_def
  -- Probability measure instances for the joints
  haveI hpXA : IsProbabilityMeasure νXA :=
    Measure.isProbabilityMeasure_map (sys.hX.prodMk sys.hA).aemeasurable
  haveI hpYA : IsProbabilityMeasure νYA :=
    Measure.isProbabilityMeasure_map (sys.hY.prodMk sys.hA).aemeasurable
  haveI hpA : IsProbabilityMeasure (sys.μ.map sys.A) :=
    Measure.isProbabilityMeasure_map sys.hA.aemeasurable
  -- Both joints have the same action marginal: νXA.map snd = μ.map A = νYA.map snd
  have hXA_snd : νXA.map Prod.snd = sys.μ.map sys.A :=
    Measure.map_map measurable_snd (sys.hX.prodMk sys.hA)
  have hYA_snd : νYA.map Prod.snd = sys.μ.map sys.A :=
    Measure.map_map measurable_snd (sys.hY.prodMk sys.hA)
  -- Apply chain rule (decomposing along Act) to both joints
  have hXA_chain := measureEntropy_chain_snd νXA
  have hYA_chain := measureEntropy_chain_snd νYA
  rw [hXA_snd] at hXA_chain
  rw [hYA_snd] at hYA_chain
  -- Define witnesses
  set w : Act → ℝ := fun a => (sys.μ.map sys.A).real {a}
  set r : Act → ℝ := fun a =>
    (∑ s, negMulLog (νXA.real {(s, a)} / w a)) -
    (∑ s, negMulLog (νYA.real {(s, a)} / w a))
  refine ⟨w, r, fun a => measureReal_nonneg, ?_, ?_, ?_⟩
  -- (1) Weights sum to 1
  · exact sum_measureReal_singleton _
  -- (2) Algebraic identity: H[X|A] - H[Y|A] = ∑ a, w a * r a
  · -- Unfold condEntropy: H[X|A] - H[Y|A] = Hm[νXA] - Hm[νYA]
    have hcond : H[sys.X | sys.A ; sys.μ] - H[sys.Y | sys.A ; sys.μ] =
        Hm[νXA] - Hm[νYA] := by
      simp only [condEntropy, entropy, νXA_def, νYA_def]; ring
    rw [hcond]
    -- Expand RHS: ∑ a, w a * r a = CX - CY where CX, CY are from chain rule
    have hRHS : ∑ a : Act, w a * r a =
        (∑ a, w a * ∑ s, negMulLog (νXA.real {(s, a)} / w a)) -
        (∑ a, w a * ∑ s, negMulLog (νYA.real {(s, a)} / w a)) := by
      simp_rw [r, mul_sub, ← Finset.sum_sub_distrib]
    rw [hRHS]
    -- Both sides equal CX - CY by the chain rule
    linarith [hXA_chain, hYA_chain]
  -- (3) For each a with w a > 0, construct a blind system with entropyReduction = r a
  · intro a ha
    -- Step 1: Obtain ℝ≥0∞ non-vanishing of action probability
    have ha_ennreal : (sys.μ.map sys.A) {a} ≠ 0 := by
      intro h
      simp [w, Measure.real, h] at ha
    have ha_ne_top : (sys.μ.map sys.A) {a} ≠ ⊤ := measure_ne_top _ _
    -- Step 2: Define conditional mass functions (in ℝ≥0∞)
    set wA := (sys.μ.map sys.A) {a}
    set fX : S → ℝ≥0∞ := fun s => νXA {(s, a)} / wA
    set fY : S → ℝ≥0∞ := fun s => νYA {(s, a)} / wA
    -- Step 3: Show conditional mass functions sum to 1
    have hfX_sum : ∑ s : S, fX s = 1 := by
      simp only [fX, div_eq_mul_inv]
      rw [← Finset.sum_mul, ← marginalize_snd_ennreal νXA a, hXA_snd,
        ENNReal.mul_inv_cancel ha_ennreal ha_ne_top]
    have hfY_sum : ∑ s : S, fY s = 1 := by
      simp only [fY, div_eq_mul_inv]
      rw [← Finset.sum_mul, ← marginalize_snd_ennreal νYA a, hYA_snd,
        ENNReal.mul_inv_cancel ha_ennreal ha_ne_top]
    -- Step 4: Build probability measures on S from conditional distributions
    set μ_X := measureOfMass fX
    set μ_Y := measureOfMass fY
    haveI : IsProbabilityMeasure μ_X := measureOfMass_isProbabilityMeasure fX hfX_sum
    haveI : IsProbabilityMeasure μ_Y := measureOfMass_isProbabilityMeasure fY hfY_sum
    -- Step 5: Build the control system on S × S
    set μ' := μ_X.prod μ_Y
    haveI : IsProbabilityMeasure μ' := inferInstance
    set sys' : ControlSystem (S × S) S Act :=
      { μ := μ'
        prob := inferInstance
        X := Prod.fst
        A := fun _ => a
        Y := Prod.snd
        hX := measurable_fst
        hA := measurable_const
        hY := measurable_snd }
    refine ⟨S × S, inferInstance, sys', ?_, ?_⟩
    -- Step 6: Prove blindness (constant action is independent of everything)
    · exact ProbabilityTheory.indepFun_const_right Prod.fst a
    -- Step 7: Prove entropy reduction matches r a
    · -- entropyReduction = H[fst ; μ'] - H[snd ; μ']
      show Hm[μ'.map Prod.fst] - Hm[μ'.map Prod.snd] = r a
      -- Compute marginal entropies via measureOfMass
      -- First, show that the marginals of μ' = μ_X.prod μ_Y have the right entropy
      -- (μ_X.prod μ_Y).map fst has singleton values μ_X{s}
      -- Helper: singleton product set decomposition
      have hsing : ∀ (s t : S), ({(s, t)} : Set (S × S)) = {s} ×ˢ {t} := by
        intro s t; ext ⟨a, b⟩; simp
      -- Marginal of product measure on fst equals μ_X
      have hfst_real : ∀ s, (μ'.map Prod.fst).real {s} = μ_X.real {s} := by
        intro s; rw [marginalize_fst μ' s]
        simp only [Measure.real, μ', hsing, Measure.prod_prod, ENNReal.toReal_mul]
        rw [← Finset.mul_sum,
          show ∑ i : S, (μ_Y {i}).toReal = 1 from sum_measureReal_singleton μ_Y, mul_one]
      -- Marginal of product measure on snd equals μ_Y
      have hsnd_real : ∀ s, (μ'.map Prod.snd).real {s} = μ_Y.real {s} := by
        intro s; rw [marginalize_snd μ' s]
        simp only [Measure.real, μ', hsing, Measure.prod_prod, ENNReal.toReal_mul]
        rw [← Finset.sum_mul,
          show ∑ i : S, (μ_X {i}).toReal = 1 from sum_measureReal_singleton μ_X, one_mul]
      -- Connect measureOfMass to the conditional probability
      have hfX_real : ∀ s, (measureOfMass fX).real {s} = νXA.real {(s, a)} / w a := by
        intro s; rw [measureOfMass_real_singleton, ENNReal.toReal_div]; rfl
      have hfY_real : ∀ s, (measureOfMass fY).real {s} = νYA.real {(s, a)} / w a := by
        intro s; rw [measureOfMass_real_singleton, ENNReal.toReal_div]; rfl
      -- Assemble the entropy equalities
      have hfst_entropy : Hm[μ'.map Prod.fst] = ∑ s, negMulLog (νXA.real {(s, a)} / w a) := by
        simp only [measureEntropy, hfst_real, show μ_X = measureOfMass fX from rfl, hfX_real]
      have hsnd_entropy : Hm[μ'.map Prod.snd] = ∑ s, negMulLog (νYA.real {(s, a)} / w a) := by
        simp only [measureEntropy, hsnd_real, show μ_Y = measureOfMass fY from rfl, hfY_real]
      rw [hfst_entropy, hsnd_entropy]

/-- **Sub-lemma 2b: Weighted average bound.**

    If `f = Σ_i w_i r_i` where `w_i ≥ 0`, `Σ w_i = 1`, and every `r_i`
    with `w_i > 0` is `≤ C`, then `f ≤ C`.

    This is a standard property of convex combinations. -/
lemma weighted_sum_le_sup {ι : Type*} [Fintype ι]
    (w r : ι → ℝ) (C : ℝ)
    (hw_nonneg : ∀ i, 0 ≤ w i)
    (hw_sum : ∑ i, w i = 1)
    (hr_bound : ∀ i, w i > 0 → r i ≤ C) :
    ∑ i, w i * r i ≤ C := by
  calc ∑ i, w i * r i
      ≤ ∑ i, w i * C := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : w i > 0
        · exact mul_le_mul_of_nonneg_left (hr_bound i hi) (le_of_lt hi)
        · push Not at hi
          have : w i = 0 := le_antisymm hi (hw_nonneg i)
          simp [this]
    _ = C := by rw [← Finset.sum_mul, hw_sum, one_mul]

omit [MeasurableSingletonClass Act] [Fintype Act] in
/-- **Sub-lemma 2c: Blind systems contribute to blindReductions.**

    If `r` is the entropy reduction of some blind system, then `r ≤ sSup(blindReductions)`. -/
lemma blind_entropyReduction_le_sSup
    {Ω' : Type} [MeasurableSpace Ω'] (sys' : ControlSystem Ω' S Act)
    (hblind : sys'.IsBlind) :
    entropyReduction sys' ≤ sSup (blindReductions (S := S) (Act := Act)) := by
  apply le_csSup blindReductions_bddAbove
  exact ⟨Ω', inferInstance, sys', hblind, rfl⟩

/-- **Conditional entropy reduction is bounded by the blind supremum.** -/
lemma condEntropy_reduction_le_blind_sup
    (sys : ControlSystem Ω S Act) :
    H[sys.X | sys.A ; sys.μ] - H[sys.Y | sys.A ; sys.μ] ≤
      sSup (blindReductions (S := S) (Act := Act)) := by
  -- Obtain the weighted-sum representation
  obtain ⟨w, r, hw_nonneg, hw_sum, h_eq, h_blind⟩ := condEntropy_diff_eq_weighted_sum sys
  -- Rewrite the LHS as the weighted sum
  rw [h_eq]
  -- Apply the convex combination bound
  apply weighted_sum_le_sup w r _ hw_nonneg hw_sum
  -- For each a with w a > 0, the corresponding r a is ≤ sSup
  intro a ha
  obtain ⟨Ω', mΩ', sys', hblind, hr⟩ := h_blind a ha
  rw [← hr]
  exact blind_entropyReduction_le_sSup sys' hblind

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
    (sys : ControlSystem Ω S Act) :
    entropyReduction sys ≤ sSup (blindReductions (S := S) (Act := Act)) + policyMI sys := by
  -- Step 1: Decompose ΔH into conditional entropies and mutual informations
  rw [entropyReduction_decomp]
  -- Step 2: The conditional entropy reduction is bounded by the blind maximum
  have hcond := condEntropy_reduction_le_blind_sup sys
  -- Step 3: I[Y : A] ≥ 0 by Gibbs' inequality
  have hmi := mutualInfo_YA_nonneg sys
  -- Conclude
  linarith

/-! ### Corollary and supporting results -/

/-- A blind system has zero policy mutual information. -/
theorem blind_policyMI_eq_zero (sys : ControlSystem Ω S Act) (hblind : sys.IsBlind) :
    policyMI sys = 0 := by
  -- policyMI = I[X : A] = H[X] + H[A] - H[(X,A)]
  -- Independence ⟹ joint law = product of marginals ⟹ H[(X,A)] = H[X] + H[A]
  simp only [policyMI, mutualInfo]
  suffices h : H[fun ω => (sys.X ω, sys.A ω) ; sys.μ] = H[sys.X ; sys.μ] + H[sys.A ; sys.μ] by
    linarith
  -- From independence: μ.map (X,A) = (μ.map X).prod (μ.map A)
  have h_prod : sys.μ.map (fun ω => (sys.X ω, sys.A ω)) =
      (sys.μ.map sys.X).prod (sys.μ.map sys.A) :=
    (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      sys.hX.aemeasurable sys.hA.aemeasurable).mp hblind
  -- Rewrite entropy using the product decomposition
  simp only [entropy, h_prod]
  -- Entropy of product measure = sum of entropies
  have : IsProbabilityMeasure (sys.μ.map sys.X) :=
    Measure.isProbabilityMeasure_map sys.hX.aemeasurable
  have : IsProbabilityMeasure (sys.μ.map sys.A) :=
    Measure.isProbabilityMeasure_map sys.hA.aemeasurable
  exact measureEntropy_prod (sys.μ.map sys.X) (sys.μ.map sys.A)

end TouchetteLloyd

end
