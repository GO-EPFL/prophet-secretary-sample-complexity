import ProphetSecretary.Limiting.HybridOutcomes
import ProphetSecretary.Model.ScalarObjectiveBounds

/-!
# Scalar objectives of bounded finite-intensity hybrid instances

The data describe a truncated limiting state: finitely many retained distributions,
finite positive-mark intensity, a fixed terminal reward, and a common cap. Bounds and
integrability are proved from these input assumptions. Scalar value is the supremum
over general measurable hybrid rules sharing one code across all Poisson counts.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal NNReal

namespace ProphetSecretary.Limiting

/-- Bounded input data for the finite-intensity part of a limiting instance. -/
structure FiniteIntensityHybridInstance (n : ℕ) where
  cap : ℝ≥0
  terminal : ℝ≥0
  terminal_le_cap : terminal ≤ cap
  individuals : ProphetSecretary.Model.Instance n
  individual_bounded : ∀ i, ∀ᵐ x : ℝ ∂individuals.law i, x ≤ (cap : ℝ)
  intensity : FiniteMeasure ℝ
  intensity_supported : ∀ᵐ x : ℝ ∂(intensity : Measure ℝ), x ∈ Ioc (0 : ℝ) (cap : ℝ)

namespace FiniteIntensityHybridInstance

variable {n : ℕ} (B : FiniteIntensityHybridInstance n)

noncomputable def law {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) : Measure (HybridWorld n Seed) :=
  hybridWorldLaw B.individuals B.intensity ν

instance law_isProbability {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (B.law ν) := by unfold law; infer_instance

noncomputable def expectedMaximum : ℝ := hybridExpectedMaximum B.individuals B.intensity B.terminal

lemma terminal_le_cap_real : (B.terminal : ℝ) ≤ (B.cap : ℝ) := by exact_mod_cast B.terminal_le_cap

lemma integrable_maximum : Integrable (hybridMaximum B.terminal) (hybridValueLaw B.individuals B.intensity) :=
  integrable_hybridMaximum _ _ B.cap.property B.terminal_le_cap_real B.individual_bounded B.intensity_supported

lemma expectedMaximum_nonnegative : 0 ≤ B.expectedMaximum := hybridExpectedMaximum_nonnegative _ _ _

lemma expectedMaximum_le_cap : B.expectedMaximum ≤ (B.cap : ℝ) :=
  hybridExpectedMaximum_le _ _ B.cap.property B.terminal_le_cap_real B.individual_bounded B.intensity_supported

lemma terminal_le_expectedMaximum : (B.terminal : ℝ) ≤ B.expectedMaximum :=
  hybridExpectedMaximum_ge_terminal _ _ B.cap.property B.terminal_le_cap_real B.individual_bounded B.intensity_supported

end FiniteIntensityHybridInstance

/-- Independent auxiliary randomness and one count-independent hybrid rule. -/
structure RandomizedHybridPolicy (n : ℕ) where
  Seed : Type
  [seedSpace : MeasurableSpace Seed]
  seedLaw : Measure Seed
  [probability : IsProbabilityMeasure seedLaw]
  rule : HybridRule n Seed
  measurable_rule : rule.IsMeasurable

attribute [instance] RandomizedHybridPolicy.seedSpace RandomizedHybridPolicy.probability

namespace RandomizedHybridPolicy

variable {n : ℕ} (π : RandomizedHybridPolicy n) (B : FiniteIntensityHybridInstance n)

noncomputable def expectedReward : ℝ := π.rule.expectedReward B.individuals B.intensity B.terminal π.seedLaw
noncomputable def expectedDuration : ℝ := π.rule.meanDuration B.individuals B.intensity π.seedLaw

lemma integrable_reward : Integrable (π.rule.realizedReward B.terminal) (B.law π.seedLaw) :=
  π.rule.integrable_realizedReward π.measurable_rule _ _ _ B.terminal.property B.cap.property B.terminal_le_cap_real
    B.individual_bounded B.intensity_supported

lemma integrable_duration : Integrable π.rule.realizedDuration (B.law π.seedLaw) :=
  π.rule.integrable_realizedDuration π.measurable_rule _ _ _

lemma expectedReward_nonnegative : 0 ≤ π.expectedReward B :=
  π.rule.expectedReward_nonnegative _ _ _ B.terminal.property B.individual_bounded B.intensity_supported

lemma expectedReward_le_maximum : π.expectedReward B ≤ B.expectedMaximum :=
  π.rule.expectedReward_le_maximum π.measurable_rule _ _ _ B.terminal.property B.cap.property B.terminal_le_cap_real
    B.individual_bounded B.intensity_supported

lemma expectedReward_le_cap : π.expectedReward B ≤ (B.cap : ℝ) :=
  (π.expectedReward_le_maximum B).trans B.expectedMaximum_le_cap

lemma expectedDuration_nonnegative : 0 ≤ π.expectedDuration B := π.rule.meanDuration_nonnegative _ _ _
lemma expectedDuration_le_one : π.expectedDuration B ≤ 1 := π.rule.meanDuration_le_one π.measurable_rule _ _ _

noncomputable def scalarObjective (w c : ℝ) : ℝ :=
  ∫ v, w * π.rule.realizedReward B.terminal v + c * π.rule.realizedDuration v ∂B.law π.seedLaw

lemma scalarObjective_eq (w c : ℝ) : π.scalarObjective B w c = w * π.expectedReward B + c * π.expectedDuration B := by
  unfold scalarObjective expectedReward expectedDuration HybridRule.expectedReward HybridRule.meanDuration
  rw [integral_add ((π.integrable_reward B).const_mul w) ((π.integrable_duration B).const_mul c),
    integral_const_mul, integral_const_mul]
  rfl

lemma scalarObjective_nonnegative {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) : 0 ≤ π.scalarObjective B w c := by
  rw [π.scalarObjective_eq B w c]
  exact add_nonneg (mul_nonneg hw (π.expectedReward_nonnegative B)) (mul_nonneg hc (π.expectedDuration_nonnegative B))

lemma scalarObjective_le {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    π.scalarObjective B w c ≤ w * B.expectedMaximum + c := by
  rw [π.scalarObjective_eq B w c]
  exact add_le_add (mul_le_mul_of_nonneg_left (π.expectedReward_le_maximum B) hw)
    ((mul_le_mul_of_nonneg_left (π.expectedDuration_le_one B) hc).trans_eq (mul_one c))

lemma scalarObjective_le_abs (w c : ℝ) : π.scalarObjective B w c ≤ |w| * (B.cap : ℝ) + |c| := by
  rw [π.scalarObjective_eq B w c]
  have hr : w * π.expectedReward B ≤ |w| * (B.cap : ℝ) :=
    (mul_le_mul_of_nonneg_right (le_abs_self w) (π.expectedReward_nonnegative B)).trans
      (mul_le_mul_of_nonneg_left (π.expectedReward_le_cap B) (abs_nonneg w))
  have ht : c * π.expectedDuration B ≤ |c| :=
    (mul_le_mul_of_nonneg_right (le_abs_self c) (π.expectedDuration_nonnegative B)).trans
      ((mul_le_mul_of_nonneg_left (π.expectedDuration_le_one B) (abs_nonneg c)).trans_eq (mul_one _))
  exact add_le_add hr ht

/-- Waiting receives the fixed terminal reward at normalized duration one. -/
noncomputable def waiting (n : ℕ) : RandomizedHybridPolicy n where
  Seed := Unit
  seedLaw := Measure.dirac ()
  rule := ⟨fun _ _ _ _ _ _ => false, fun _ _ _ _ _ => false⟩
  measurable_rule := ⟨measurable_const, measurable_const⟩

lemma waiting_adapter (N : ℕ) :
    (waiting n).rule.asFinitePolicy N = (Model.RandomizedPolicy.waiting (n + N)).rule := by
  change Model.Policy.mk _ = Model.Policy.mk _
  congr 1
  funext r t j x H
  induction j using Fin.addCases <;> simp [waiting]

@[simp] lemma waiting_realizedDuration (v : HybridWorld n Unit) :
    (waiting n).rule.realizedDuration v = 1 := by
  change ((waiting n).rule.asFinitePolicy v.1.1).stoppingTime v.2.2.2 Finset.univ
    (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) = 1
  rw [waiting_adapter]
  simp [Model.RandomizedPolicy.waiting, Model.Policy.stoppingTime, Model.Policy.stopTimes,
    Model.Policy.accepted, Model.Policy.action]

@[simp] lemma waiting_realizedReward (a : ℝ) (v : HybridWorld n Unit) :
    (waiting n).rule.realizedReward a v = a := by
  simp [HybridRule.realizedReward, HybridRule.reward, HybridRule.HasSelection, waiting_adapter,
    Model.RandomizedPolicy.waiting, Model.Policy.ActualSelects, Model.Policy.Selects,
    Model.Policy.accepted, Model.Policy.action]

@[simp] lemma waiting_expectedReward : (waiting n).expectedReward B = (B.terminal : ℝ) := by
  simp [expectedReward, HybridRule.expectedReward]

@[simp] lemma waiting_expectedDuration : (waiting n).expectedDuration B = 1 := by
  simp [expectedDuration, HybridRule.meanDuration]

@[simp] lemma waiting_scalarObjective (w c : ℝ) :
    (waiting n).scalarObjective B w c = w * (B.terminal : ℝ) + c := by
  rw [scalarObjective_eq, waiting_expectedReward, waiting_expectedDuration, mul_one]

end RandomizedHybridPolicy

namespace FiniteIntensityHybridInstance

variable {n : ℕ} (B : FiniteIntensityHybridInstance n)

noncomputable def scalarPayoffs (w c : ℝ) : Set ℝ := Set.range (fun π : RandomizedHybridPolicy n => π.scalarObjective B w c)
noncomputable def optimalScalarValue (w c : ℝ) : ℝ := sSup (B.scalarPayoffs w c)

lemma scalarPayoffs_nonempty (w c : ℝ) : (B.scalarPayoffs w c).Nonempty :=
  ⟨(RandomizedHybridPolicy.waiting n).scalarObjective B w c, ⟨RandomizedHybridPolicy.waiting n, rfl⟩⟩

lemma scalarPayoffs_bddAbove (w c : ℝ) : BddAbove (B.scalarPayoffs w c) := by
  refine ⟨|w| * (B.cap : ℝ) + |c|, ?_⟩
  rintro _ ⟨π, rfl⟩
  exact π.scalarObjective_le_abs B w c

lemma scalarObjective_le_value (π : RandomizedHybridPolicy n) (w c : ℝ) : π.scalarObjective B w c ≤ B.optimalScalarValue w c :=
  le_csSup (B.scalarPayoffs_bddAbove w c) ⟨π, rfl⟩

lemma optimalScalarValue_le {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    B.optimalScalarValue w c ≤ w * B.expectedMaximum + c := by
  apply csSup_le (B.scalarPayoffs_nonempty w c)
  rintro _ ⟨π, rfl⟩
  exact π.scalarObjective_le B hw hc

lemma optimalScalarValue_nonnegative {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    0 ≤ B.optimalScalarValue w c :=
  ((RandomizedHybridPolicy.waiting n).scalarObjective_nonnegative B hw hc).trans (B.scalarObjective_le_value _ w c)

lemma terminalScalar_le_optimalScalarValue (w c : ℝ) :
    w * (B.terminal : ℝ) + c ≤ B.optimalScalarValue w c := by
  simpa using B.scalarObjective_le_value (RandomizedHybridPolicy.waiting n) w c

lemma durationReward_le_optimalScalarValue {w c : ℝ} (hw : 0 ≤ w) :
    c ≤ B.optimalScalarValue w c := by
  exact (le_add_of_nonneg_left (mul_nonneg hw B.terminal.property)).trans
    (B.terminalScalar_le_optimalScalarValue w c)

end FiniteIntensityHybridInstance
end ProphetSecretary.Limiting
