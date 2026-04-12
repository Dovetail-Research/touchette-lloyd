import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Prod

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

/-- Sum of singleton real measures equals 1 for a probability measure. -/
lemma sum_measureReal_singleton {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype S] (μ : Measure S) [IsProbabilityMeasure μ] :
    ∑ s : S, μ.real {s} = 1 := by
  have h_ennreal : ∑ s : S, μ {s} = 1 := by
    rw [← measure_biUnion_finset
      (fun x _ y _ hxy => Set.disjoint_singleton.mpr hxy)
      (fun s _ => measurableSet_singleton s)]
    have : (⋃ s ∈ Finset.univ, ({s} : Set S)) = Set.univ := by ext; simp
    rw [this, measure_univ]
  rw [show (1 : ℝ) = (1 : ℝ≥0∞).toReal from by simp, ← h_ennreal,
    ENNReal.toReal_sum (fun s _ => measure_ne_top μ {s})]
  simp [Measure.real]

/-- Entropy of a product measure equals the sum of the entropies.

    `Hm[μ × ν] = Hm[μ] + Hm[ν]`

    This follows from `negMulLog(p·q) = q·negMulLog(p) + p·negMulLog(q)` and
    the fact that the marginal weights sum to 1. -/
lemma measureEntropy_prod {S T : Type*}
    [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (μ : Measure S) (ν : Measure T) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    Hm[μ.prod ν] = Hm[μ] + Hm[ν] := by
  simp only [measureEntropy, Fintype.sum_prod_type]
  -- Rewrite {(s,t)} as {s} ×ˢ {t}, apply product measure formula, then negMulLog product rule
  have hsing : ∀ (s : S) (t : T), ({(s, t)} : Set (S × T)) = {s} ×ˢ {t} :=
    fun s t => by ext ⟨a, b⟩; simp
  simp_rw [hsing, measureReal_prod_prod, negMulLog_mul, Finset.sum_add_distrib]
  -- LHS = (∑ s, ∑ t, ν.real{t} · negMulLog(μ.real{s}))
  --      + (∑ s, ∑ t, μ.real{s} · negMulLog(ν.real{t}))
  -- First sum: factor out negMulLog(μ.real{s}), use ∑ ν.real = 1
  -- Second sum: factor out negMulLog(ν.real{t}), use ∑ μ.real = 1
  congr 1
  · congr 1; ext s
    rw [← Finset.sum_mul, sum_measureReal_singleton ν, one_mul]
  · simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, sum_measureReal_singleton μ, one_mul]

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

/-! ### Marginalization lemmas -/

/-- Marginalization: `(ν.map fst).real {s} = ∑ t, ν.real {(s,t)}`. -/
lemma marginalize_fst {S T : Type*}
    [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (ν : Measure (S × T)) [IsFiniteMeasure ν] (s : S) :
    (ν.map Prod.fst).real {s} = ∑ t, ν.real {(s, t)} := by
  -- Decompose the preimage Prod.fst���¹'{s} into disjoint singletons {(s,t)}
  suffices h : (ν.map Prod.fst) {s} = ∑ t : T, ν {(s, t)} by
    simp only [Measure.real, h, ENNReal.toReal_sum (fun t _ => measure_ne_top ν _)]
  rw [Measure.map_apply measurable_fst (measurableSet_singleton s)]
  have h_set : (Prod.fst ⁻¹' {s} : Set (S × T)) =
      ⋃ t ∈ (Finset.univ : Finset T), ({(s, t)} : Set (S × T)) := by
    ext ⟨a, b⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_univ, Set.iUnion_true,
      Set.mem_iUnion, Prod.mk.injEq]
    exact ⟨fun h => ⟨b, h, rfl⟩, fun ⟨_, h, _⟩ => h⟩
  rw [h_set, measure_biUnion_finset
    (fun i _ j _ hij => Set.disjoint_singleton.mpr (fun h => hij (Prod.mk.inj h).2))
    (fun t _ => measurableSet_singleton _)]

/-- Marginalization (ℝ≥0∞): `(ν.map snd) {t} = ∑ s, ν {(s,t)}`. -/
lemma marginalize_snd_ennreal {S T : Type*}
    [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (ν : Measure (S × T)) (t : T) :
    (ν.map Prod.snd) {t} = ∑ s, ν {(s, t)} := by
  rw [Measure.map_apply measurable_snd (measurableSet_singleton t)]
  have h_set : (Prod.snd ⁻¹' {t} : Set (S × T)) =
      ⋃ s ∈ (Finset.univ : Finset S), ({(s, t)} : Set (S × T)) := by
    ext ⟨a, b⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_univ, Set.iUnion_true,
      Set.mem_iUnion, Prod.mk.injEq]
    exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  rw [h_set, measure_biUnion_finset
    (fun i _ j _ hij => Set.disjoint_singleton.mpr (fun h => hij (Prod.mk.inj h).1))
    (fun s _ => measurableSet_singleton _)]

/-- Marginalization: `(ν.map snd).real {t} = ∑ s, ν.real {(s,t)}`. -/
lemma marginalize_snd {S T : Type*}
    [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (ν : Measure (S × T)) [IsFiniteMeasure ν] (t : T) :
    (ν.map Prod.snd).real {t} = ∑ s, ν.real {(s, t)} := by
  suffices h : (ν.map Prod.snd) {t} = ∑ s : S, ν {(s, t)} by
    simp only [Measure.real, h, ENNReal.toReal_sum (fun s _ => measure_ne_top ν _)]
  rw [Measure.map_apply measurable_snd (measurableSet_singleton t)]
  have h_set : (Prod.snd ⁻¹' {t} : Set (S × T)) =
      ⋃ s ∈ (Finset.univ : Finset S), ({(s, t)} : Set (S × T)) := by
    ext ⟨a, b⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_univ, Set.iUnion_true,
      Set.mem_iUnion, Prod.mk.injEq]
    exact ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, _, h⟩ => h⟩
  rw [h_set, measure_biUnion_finset
    (fun i _ j _ hij => Set.disjoint_singleton.mpr (fun h => hij (Prod.mk.inj h).1))
    (fun s _ => measurableSet_singleton _)]

/-- When the marginal `(ν.map fst).real {s} = 0`, the joint `ν.real {(s,t)} = 0`. -/
private lemma joint_zero_of_marginal_fst_zero {S T : Type*}
    [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (ν : Measure (S × T)) [IsFiniteMeasure ν]
    {s : S} (hs : (ν.map Prod.fst).real {s} = 0) (t : T) :
    ν.real {(s, t)} = 0 := by
  have hmarg := marginalize_fst ν s
  rw [hs] at hmarg
  -- hmarg : 0 = ∑ t', ν.real {(s, t')}; all terms ≥ 0, so each is 0
  have h_le : ν.real {(s, t)} ≤ ∑ t' : T, ν.real {(s, t')} :=
    Finset.single_le_sum (f := fun t' => ν.real {(s, t')})
      (fun _ _ => measureReal_nonneg) (Finset.mem_univ t)
  linarith [measureReal_nonneg (μ := ν) (s := {(s, t)})]

/-! ### Non-negativity of mutual information (Gibbs' inequality)

This is the key information-theoretic inequality: `I[X : Y ; μ] ≥ 0`.

The proof uses Jensen's inequality applied to the concave function `negMulLog`.

**Proof sketch** (sub-additivity of entropy):
1. Decompose `H(X,Y) = H(X) + H(Y|X)` using `negMulLog_mul` with conditional
   distributions `p(t|s) = p(s,t)/p_X(s)`.
2. Show `H(Y|X) ≤ H(Y)` by applying Jensen term-by-term:
   for each `t`, `∑_s p_X(s) · negMulLog(p(t|s)) ≤ negMulLog(p_Y(t))`,
   using `concaveOn_negMulLog.le_map_sum`.
3. Combine: `H(X,Y) = H(X) + H(Y|X) ≤ H(X) + H(Y)`. -/

/-- **Sub-additivity of entropy**: `Hm[ν] ≤ Hm[ν.map fst] + Hm[ν.map snd]`.

    The entropy of a joint distribution is at most the sum of the marginal
    entropies. Equality holds iff the coordinates are independent.

    Proved via Jensen's inequality on `concaveOn_negMulLog`. -/
lemma measureEntropy_subadditive {S T : Type*}
    [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (ν : Measure (S × T)) [IsProbabilityMeasure ν] :
    Hm[ν] ≤ Hm[ν.map Prod.fst] + Hm[ν.map Prod.snd] := by
  -- Abbreviations for the distributions
  set p := fun st : S × T => ν.real {st}
  set pX := fun s : S => (ν.map Prod.fst).real {s}
  set pY := fun t : T => (ν.map Prod.snd).real {t}
  -- Conditional distribution: c(s,t) = p(s,t) / pX(s)
  set c := fun s : S => fun t : T => p (s, t) / pX s
  -- Basic properties
  have hpX_nn : ∀ s, 0 ≤ pX s := fun _ => measureReal_nonneg
  have hc_nn : ∀ s t, 0 ≤ c s t := fun s t => div_nonneg measureReal_nonneg (hpX_nn _)
  -- Marginalization: pX(s) = ∑_t p(s,t)
  have hpX_eq : ∀ s, pX s = ∑ t, p (s, t) := fun s => marginalize_fst ν s
  -- Key identity: pX(s) * c(s,t) = p(s,t)
  have hpc : ∀ s t, pX s * c s t = p (s, t) := by
    intro s t
    simp only [c]
    by_cases hs : pX s = 0
    · rw [hs, zero_mul]; exact (joint_zero_of_marginal_fst_zero ν hs t).symm
    · exact mul_div_cancel₀ (p (s, t)) hs
  -- Convex combination identity: pY(t) = ∑_s pX(s) * c(s,t)
  have hpY_comb : ∀ t, pY t = ∑ s, pX s * c s t := by
    intro t; show (ν.map Prod.snd).real {t} = _
    rw [marginalize_snd ν t]; congr 1; ext s; exact (hpc s t).symm
  -- Weights sum to 1
  haveI : IsProbabilityMeasure (ν.map Prod.fst) :=
    Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hpX_sum : ∑ s, pX s = 1 := sum_measureReal_singleton _
  -- Step 1: Chain rule decomposition via negMulLog_mul
  --   negMulLog(p(s,t)) = c(s,t) * negMulLog(pX(s)) + pX(s) * negMulLog(c(s,t))
  have hchain : ∀ s t,
      negMulLog (p (s, t)) = c s t * negMulLog (pX s) + pX s * negMulLog (c s t) := by
    intro s t; rw [← hpc s t]; exact negMulLog_mul (pX s) (c s t)
  -- Step 2: Jensen's inequality for each t
  --   ∑_s pX(s) * negMulLog(c(s,t)) ≤ negMulLog(pY(t))
  have jensen : ∀ t, ∑ s, pX s * negMulLog (c s t) ≤ negMulLog (pY t) := by
    intro t
    rw [hpY_comb t]
    have hj := concaveOn_negMulLog.le_map_sum
      (t := Finset.univ)
      (fun s _ => hpX_nn s)
      hpX_sum
      (fun s _ => Set.mem_Ici.mpr (hc_nn s t))
    simp only [smul_eq_mul] at hj
    exact hj
  -- Step 3: Combine
  show ∑ st : S × T, negMulLog (p st) ≤
    ∑ s, negMulLog (pX s) + ∑ t, negMulLog (pY t)
  rw [Fintype.sum_prod_type]
  simp_rw [hchain, Finset.sum_add_distrib]
  -- The first sum simplifies to Hm[ν.map fst]
  have hfirst : ∑ s, ∑ t, c s t * negMulLog (pX s) = ∑ s, negMulLog (pX s) := by
    congr 1; ext s
    rw [← Finset.sum_mul]
    by_cases hs : pX s = 0
    · have h0 : negMulLog (pX s) = 0 := by rw [hs]; exact negMulLog_zero
      rw [h0, mul_zero]
    · have hc_sum : ∑ t : T, c s t = 1 := by
        show ∑ t : T, p (s, t) / pX s = 1
        rw [← Finset.sum_div, ← hpX_eq s, div_self hs]
      rw [hc_sum, one_mul]
  rw [hfirst]
  -- Suffices: H(Y|X) ≤ H(Y), i.e., the conditional part is bounded
  have hsecond : ∑ s, ∑ t, pX s * negMulLog (c s t) ≤ ∑ t, negMulLog (pY t) := by
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum (fun t _ => jensen t)
  linarith

/-- **Non-negativity of mutual information** (Gibbs' inequality).

    `0 ≤ I[X : Y ; μ]`

    Follows immediately from sub-additivity of entropy:
    `H[(X,Y)] ≤ H[X] + H[Y]`, so `I[X:Y] = H[X] + H[Y] - H[(X,Y)] ≥ 0`. -/
lemma mutualInfo_nonneg {S T : Type*}
    [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) :
    0 ≤ I[X : Y ; μ] := by
  simp only [mutualInfo, entropy]
  -- Reduce to sub-additivity of measure entropy
  set ν := μ.map (fun ω => (X ω, Y ω))
  have hXY : Measurable (fun ω => (X ω, Y ω)) := hX.prodMk hY
  have hprob : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hXY.aemeasurable
  have hfst : ν.map Prod.fst = μ.map X :=
    Measure.map_map measurable_fst hXY
  have hsnd : ν.map Prod.snd = μ.map Y :=
    Measure.map_map measurable_snd hXY
  rw [← hfst, ← hsnd]
  linarith [measureEntropy_subadditive ν]

/-- When the marginal `(ν.map snd).real {t} = 0`, the joint `ν.real {(s,t)} = 0`. -/
private lemma joint_zero_of_marginal_snd_zero {S T : Type*}
    [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (ν : Measure (S × T)) [IsFiniteMeasure ν]
    {t : T} (ht : (ν.map Prod.snd).real {t} = 0) (s : S) :
    ν.real {(s, t)} = 0 := by
  have hmarg := marginalize_snd ν t
  rw [ht] at hmarg
  have h_le : ν.real {(s, t)} ≤ ∑ s' : S, ν.real {(s', t)} :=
    Finset.single_le_sum (f := fun s' => ν.real {(s', t)})
      (fun _ _ => measureReal_nonneg) (Finset.mem_univ s)
  linarith [measureReal_nonneg (μ := ν) (s := {(s, t)})]

/-! ### Chain rule for measure entropy (decomposition along second component)

    `Hm[ν] = Hm[ν.map snd] + ∑_t w(t) * ∑_s negMulLog(ν.real{(s,t)} / w(t))`

    This is the measure-level chain rule `H[X,Y] = H[Y] + H[X|Y]`, where
    the conditional entropy `H[X|Y]` is written explicitly as a weighted
    sum of per-value entropies. -/

/-- **Measure entropy chain rule** (decomposing along the second component):
    `Hm[ν] = Hm[ν.map snd] + ∑ t, w(t) * ∑ s, negMulLog(ν.real{(s,t)} / w(t))`. -/
lemma measureEntropy_chain_snd {S T : Type*}
    [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
    [MeasurableSpace T] [MeasurableSingletonClass T] [Fintype T]
    (ν : Measure (S × T)) [IsProbabilityMeasure ν] :
    Hm[ν] = Hm[ν.map Prod.snd] +
      ∑ t, (ν.map Prod.snd).real {t} *
        ∑ s, negMulLog (ν.real {(s, t)} / (ν.map Prod.snd).real {t}) := by
  set p := fun st : S × T => ν.real {st}
  set w := fun t : T => (ν.map Prod.snd).real {t}
  set c := fun s : S => fun t : T => p (s, t) / w t
  have hw_nn : ∀ t, 0 ≤ w t := fun _ => measureReal_nonneg
  have hw_eq : ∀ t, w t = ∑ s, p (s, t) := fun t => marginalize_snd ν t
  have hpc : ∀ s t, w t * c s t = p (s, t) := by
    intro s t; simp only [c]
    by_cases ht : w t = 0
    · rw [ht, zero_mul]; exact (joint_zero_of_marginal_snd_zero ν ht s).symm
    · exact mul_div_cancel₀ (p (s, t)) ht
  haveI : IsProbabilityMeasure (ν.map Prod.snd) :=
    Measure.isProbabilityMeasure_map measurable_snd.aemeasurable
  -- Chain rule: negMulLog(p(s,t)) = c(s,t) * negMulLog(w(t)) + w(t) * negMulLog(c(s,t))
  have hchain : ∀ s t,
      negMulLog (p (s, t)) = c s t * negMulLog (w t) + w t * negMulLog (c s t) := by
    intro s t; rw [← hpc s t]; exact negMulLog_mul (w t) (c s t)
  -- Expand the LHS and apply the chain rule decomposition
  show ∑ st : S × T, negMulLog (p st) =
    ∑ t, negMulLog (w t) + ∑ t, w t * ∑ s, negMulLog (c s t)
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  simp_rw [hchain, Finset.sum_add_distrib]
  congr 1
  · -- First sum: ∑_t [∑_s c(s,t)] * negMulLog(w(t)) = ∑_t negMulLog(w(t))
    congr 1; ext t
    rw [← Finset.sum_mul]
    by_cases ht : w t = 0
    · have h0 : negMulLog (w t) = 0 := by rw [ht]; exact negMulLog_zero
      rw [h0, mul_zero]
    · have hc_sum : ∑ s : S, c s t = 1 := by
        show ∑ s : S, p (s, t) / w t = 1
        rw [← Finset.sum_div, ← hw_eq t, div_self ht]
      rw [hc_sum, one_mul]
  · -- Second sum: extract w(t) from inner sum
    congr 1; ext t; exact (Finset.mul_sum ..).symm

/-! ### Measure construction from mass functions -/

/-- Construct a measure on a finite type from a mass function `f : S → ℝ≥0∞`.

    The resulting measure satisfies `(measureOfMass f) {s} = f s`. -/
def measureOfMass {S : Type*} [MeasurableSpace S] [Fintype S]
    (f : S → ℝ≥0∞) : Measure S :=
  Finset.sum Finset.univ (fun s => f s • Measure.dirac s)

/-- Singleton evaluation of `measureOfMass`. -/
lemma measureOfMass_singleton {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    [Fintype S] (f : S → ℝ≥0∞) (s : S) :
    measureOfMass f {s} = f s := by
  simp only [measureOfMass, Measure.finset_sum_apply, Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single s]
  · rw [Measure.dirac_apply_of_mem (Set.mem_singleton s), mul_one]
  · intro b _ hbs
    rw [Measure.dirac_apply' b (measurableSet_singleton s),
      Set.indicator_of_notMem (fun h => hbs (Set.mem_singleton_iff.mp h)), mul_zero]
  · exact fun h => absurd (Finset.mem_univ s) h

/-- `measureOfMass f` is a probability measure when the masses sum to 1. -/
lemma measureOfMass_isProbabilityMeasure {S : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S] [Fintype S]
    (f : S → ℝ≥0∞) (hf : ∑ s, f s = 1) :
    IsProbabilityMeasure (measureOfMass f) := by
  constructor
  have h_univ : (Set.univ : Set S) = ⋃ s ∈ Finset.univ, {s} := by ext; simp
  rw [h_univ, measure_biUnion_finset
    (fun x _ y _ hxy => Set.disjoint_singleton.mpr hxy)
    (fun s _ => measurableSet_singleton s)]
  simp [measureOfMass_singleton, hf]

/-- `measureReal` of `measureOfMass` on singletons. -/
lemma measureOfMass_real_singleton {S : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S] [Fintype S]
    (f : S → ℝ≥0∞) (s : S) :
    (measureOfMass f).real {s} = (f s).toReal := by
  simp [Measure.real, measureOfMass_singleton]

/-- Entropy of `measureOfMass f` equals `∑ s, negMulLog (f s).toReal`. -/
lemma measureEntropy_measureOfMass {S : Type*} [MeasurableSpace S]
    [MeasurableSingletonClass S] [Fintype S]
    (f : S → ℝ≥0∞) :
    Hm[measureOfMass f] = ∑ s, negMulLog (f s).toReal := by
  simp only [measureEntropy, measureOfMass_real_singleton]

end TouchetteLloyd

end
