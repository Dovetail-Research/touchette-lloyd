module

public import InfoTheory.Entropy

/-!
# Smoke test for the entropy API

Restates, as `example`s, the main facts our earlier Touchette-Lloyd prototype
proved by hand (in its `Fintype`-restricted setting), now as immediate
consequences of the vendored entropy library. This file's purpose is to pin
down the API our own developments build on; it proves nothing new.

Original material goes in sibling files under `InfoTheory/TouchetteLloyd/`, importing
`InfoTheory.Entropy` (never `InfoTheory.PFR.*` directly).
-/

public section

open MeasureTheory ProbabilityTheory Real

/-!
### Towards the Touchette-Lloyd theorem, kernel formulation

A control system over state space `S`, action space `A`, and final-state space `T` is a prior
`ν : Measure S` together with a policy kernel `policy : Kernel S A` and an environment kernel
`env : Kernel (S × A) T`. The Touchette-Lloyd theorem bounds the closed-loop entropy reduction
by the best *blind* reduction (same environment, action independent of state) plus the mutual
information between state and action.
-/

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

theorem touchetteLloyd [Nonempty A] (μ : Measure S) [IsProbabilityMeasure μ]
    (policy : Kernel S A) [IsMarkovKernel policy]
    (env : Kernel (S × A) T) [IsMarkovKernel env] :
    entropyReduction μ policy env ≤ sSup (blindReductions env) + Im[μ ⊗ₘ policy] := by
  sorry

end TouchetteLloyd
