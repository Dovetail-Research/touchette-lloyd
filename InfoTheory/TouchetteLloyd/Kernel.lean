module

public import InfoTheory.Entropy

/-!
# The Touchette-Lloyd theorem, kernel formulation

Here the control system is specified distributionally: a prior `ν : Measure S` on the state
space, a policy kernel `policy : Kernel S A`, and an environment kernel
`env : Kernel (S × A) T`. The theorem bounds the closed-loop entropy reduction by the best
*blind* reduction (same environment, action independent of state) plus the mutual information
between state and action.

The headline statement `touchetteLloyd` takes the initial state as a random variable
`X : Ω → S` and derives itself from the purely measure-level `touchetteLloyd_measure` via
`ν = μ.map X`. For the formulation where actions and final states are also random variables
on a shared sample space, see `InfoTheory.TouchetteLloyd.RandomVariable`; the two are linked
by conditional disintegration (`condDistrib`).
-/

public section

open MeasureTheory ProbabilityTheory Real

namespace TouchetteLloyd

variable {S A T : Type*}
  [MeasurableSpace S] [Finite S] [MeasurableSingletonClass S]
  [MeasurableSpace A] [Finite A] [MeasurableSingletonClass A]
  [MeasurableSpace T] [Finite T] [MeasurableSingletonClass T]

/-- A policy is **blind** for the prior `ν` if the joint law of state and action is the product
of its marginals: the action carries no information about the state. -/
def IsBlind (ν : Measure S) (policy : Kernel S A) : Prop :=
  ν ⊗ₘ policy = ν.prod (policy ∘ₘ ν)

/-- Closed-loop entropy reduction `H[X] - H[Y]` of the control system
`(ν, policy, env)`. -/
noncomputable def entropyReduction (ν : Measure S) (policy : Kernel S A)
    (env : Kernel (S × A) T) : ℝ :=
  Hm[ν] - Hm[env ∘ₘ (ν ⊗ₘ policy)]

/-- The entropy reductions achievable with environment `env` by *blind* control, ranging over
all priors and all blind policies. -/
noncomputable def blindReductions (env : Kernel (S × A) T) : Set ℝ :=
  { r : ℝ | ∃ (ν : Measure S) (_ : IsProbabilityMeasure ν)
      (policy : Kernel S A) (_ : IsMarkovKernel policy),
      IsBlind ν policy ∧ entropyReduction ν policy env = r }

/-- Pure actions suffice: the supremum of blind reductions is already attained by
deterministic, state-independent actions (by concavity of entropy, a mixture of actions never
beats the best pure action). -/
lemma sSup_blindReductions_eq_sSup_pure (env : Kernel (S × A) T) :
    sSup (blindReductions env) =
      sSup { r : ℝ | ∃ (ν : Measure S) (_ : IsProbabilityMeasure ν) (a : A),
        Hm[ν] - Hm[env ∘ₘ (ν.map (fun x ↦ (x, a)))] = r } := by
  sorry

/-- The Touchette-Lloyd theorem, measure-level form: the closed-loop entropy reduction of the
system `(ν, policy, env)` is at most the best blind reduction plus the state-action mutual
information. -/
theorem touchetteLloyd_measure [Nonempty A] (ν : Measure S) [IsProbabilityMeasure ν]
    (policy : Kernel S A) [IsMarkovKernel policy]
    (env : Kernel (S × A) T) [IsMarkovKernel env] :
    entropyReduction ν policy env ≤ sSup (blindReductions env) + Im[ν ⊗ₘ policy] := by
  sorry

/-- The Touchette-Lloyd theorem, with the initial state given as a random variable `X` on a
sample space `Ω` and the policy and environment given as Markov kernels. -/
theorem touchetteLloyd [Nonempty A] {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → S} (hX : Measurable X)
    (policy : Kernel S A) [IsMarkovKernel policy]
    (env : Kernel (S × A) T) [IsMarkovKernel env] :
    H[X ; μ] - Hm[env ∘ₘ (μ.map X ⊗ₘ policy)]
      ≤ sSup (blindReductions env) + Im[μ.map X ⊗ₘ policy] := by
  haveI : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
  simpa only [entropyReduction, entropy_def] using touchetteLloyd_measure (μ.map X) policy env

end TouchetteLloyd
