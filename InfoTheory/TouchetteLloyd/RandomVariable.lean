module

public import InfoTheory.Entropy

/-!
# The Touchette-Lloyd theorem, random-variable formulation

Here a control system is three random variables on a shared probability space: the initial
state `X`, the action `A`, and the final state `Y`, bundled in a `ControlSystem` structure
together with the environment kernel `env` that generates `Y` from `(X, A)`. Blindness is
independence of `X` and `A`, and the set of blind reductions ranges over control systems
*with the same environment* on arbitrary sample spaces — matching Touchette-Lloyd, where
the dynamics `p(y|x,a)` is held fixed and only the prior and the (blind) policy vary.
(Our earlier prototype omitted the environment from the structure, which made its version
of the theorem substantially weaker than the paper's.)

For the formulation where the policy and the environment are Markov kernels and only the
initial state is a random variable, see `InfoTheory.TouchetteLloyd.Kernel`; a control system
in the present sense determines kernels via conditional disintegration (`condDistrib`).
-/

public section

open MeasureTheory ProbabilityTheory Real

namespace TouchetteLloyd

variable {S Act T : Type*}
  [MeasurableSpace S] [Finite S] [MeasurableSingletonClass S]
  [MeasurableSpace Act] [Finite Act] [MeasurableSingletonClass Act]
  [MeasurableSpace T] [Finite T] [MeasurableSingletonClass T]
  {Ω : Type*} [MeasurableSpace Ω]

/-- A **control system**: a probability space carrying the initial state, the action, and the
final state as random variables, together with the environment (dynamics) kernel through
which the final state is generated from the state-action pair. -/
structure ControlSystem (Ω S Act T : Type*)
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace Act] [MeasurableSpace T] where
  /-- Probability measure on the sample space. -/
  μ : Measure Ω
  /-- The measure is a probability measure. -/
  prob : IsProbabilityMeasure μ
  /-- Initial environment state. -/
  X : Ω → S
  /-- Action chosen by the policy. -/
  A : Ω → Act
  /-- Final environment state. -/
  Y : Ω → T
  /-- Measurability of `X`. -/
  hX : Measurable X
  /-- Measurability of `A`. -/
  hA : Measurable A
  /-- Measurability of `Y`. -/
  hY : Measurable Y
  /-- Environment (dynamics) kernel. -/
  env : Kernel (S × Act) T
  /-- The environment kernel is Markov. -/
  mkv : IsMarkovKernel env
  /-- `Y` is generated from `(X, A)` by `env`: the joint law of `((X, A), Y)` is the
  disintegration of the state-action law through `env`. -/
  hEnv : μ.map (fun ω ↦ ((X ω, A ω), Y ω)) = (μ.map fun ω ↦ (X ω, A ω)) ⊗ₘ env

instance (sys : ControlSystem Ω S Act T) : IsProbabilityMeasure sys.μ := sys.prob

instance (sys : ControlSystem Ω S Act T) : IsMarkovKernel sys.env := sys.mkv

namespace ControlSystem

variable (sys : ControlSystem Ω S Act T)

/-- **Entropy reduction** `H[X] - H[Y]`: how much the system reduces uncertainty about the
environment state. -/
noncomputable def entropyReduction : ℝ :=
  H[sys.X ; sys.μ] - H[sys.Y ; sys.μ]

/-- **Policy mutual information** `I[X : A]`: how much the action depends on (or "models")
the initial state. -/
noncomputable def policyMI : ℝ :=
  I[sys.X : sys.A ; sys.μ]

/-- A control system is **blind** if the action is independent of the initial state: the
agent acts without observing the environment. -/
def IsBlind : Prop :=
  IndepFun sys.X sys.A sys.μ

/-- The entropy reductions achievable by blind control systems with environment `env`, over
all sample spaces and priors. -/
noncomputable def blindReductions (env : Kernel (S × Act) T) : Set ℝ :=
  { r : ℝ | ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (sys' : ControlSystem Ω' S Act T),
      sys'.env = env ∧ sys'.IsBlind ∧ sys'.entropyReduction = r }

/-- The Touchette-Lloyd theorem, random-variable form: the entropy reduction of a control
system exceeds the best blind reduction *achievable with the same environment* by at most
the policy mutual information. -/
theorem touchetteLloyd :
    sys.entropyReduction ≤ sSup (blindReductions sys.env) + sys.policyMI := by
  sorry

end ControlSystem

end TouchetteLloyd
