import ProphetSecretary.Limiting.CountablePolicyBounds

/-!
# Scalar objectives of the full countable policy class

The supremum ranges over all measurable observable randomized callbacks with
an attained first acceptance almost surely. It is not defined as a limit of
truncated optimal values; equality with that limit requires a separate causal
simulation theorem.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting
open CountableInstance

structure RandomizedCountablePolicy (B : CountableInstance) where
  Seed : Type
  [seedSpace : MeasurableSpace Seed]
  seedLaw : Measure Seed
  [probability : IsProbabilityMeasure seedLaw]
  rule : CountableRule Seed
  measurable_rule : rule.IsMeasurable
  admissible : rule.Admissible B seedLaw

attribute [instance] RandomizedCountablePolicy.seedSpace RandomizedCountablePolicy.probability

namespace RandomizedCountablePolicy

variable {B : CountableInstance} (π : RandomizedCountablePolicy B)

noncomputable def expectedReward : ℝ :=
  ∫ v, π.rule.realizedReward B.terminal v ∂B.completeWorldLaw π.seedLaw

noncomputable def expectedDuration : ℝ :=
  ∫ v, π.rule.realizedDuration v ∂B.completeWorldLaw π.seedLaw

noncomputable def scalarObjective (w c : ℝ) : ℝ := w * π.expectedReward + c * π.expectedDuration

lemma integrable_reward : Integrable (π.rule.realizedReward B.terminal) (B.completeWorldLaw π.seedLaw) :=
  π.rule.integrable_reward B π.seedLaw π.measurable_rule

lemma integrable_duration : Integrable π.rule.realizedDuration (B.completeWorldLaw π.seedLaw) :=
  π.rule.integrable_duration B π.seedLaw π.measurable_rule

lemma expectedReward_nonnegative : 0 ≤ π.expectedReward :=
  integral_nonneg_of_ae ((π.rule.reward_bounded B π.seedLaw).mono (fun _ hv => hv.1))

lemma expectedReward_le_cap : π.expectedReward ≤ (B.cap : ℝ) := by
  change (∫ v, π.rule.realizedReward B.terminal v ∂B.completeWorldLaw π.seedLaw) ≤ (B.cap : ℝ)
  have hi := integral_mono_ae π.integrable_reward (integrable_const (B.cap : ℝ))
    ((π.rule.reward_bounded B π.seedLaw).mono (fun _ hv => hv.2))
  simpa only [integral_const,probReal_univ,one_smul] using hi

lemma expectedDuration_nonnegative : 0 ≤ π.expectedDuration :=
  integral_nonneg (fun v => (π.rule.duration_bounds v).1)

lemma expectedDuration_le_one : π.expectedDuration ≤ 1 := by
  change (∫ v, π.rule.realizedDuration v ∂B.completeWorldLaw π.seedLaw) ≤ 1
  have hi := integral_mono π.integrable_duration (integrable_const (1 : ℝ))
    (fun v => (π.rule.duration_bounds v).2)
  simpa only [integral_const,probReal_univ,one_smul] using hi

lemma expectedReward_le_maximum : π.expectedReward ≤ B.expectedMaximum := by
  let f : CompleteWorld π.Seed → ValueWorld := fun v => (v.1,v.2.1)
  have hmp := B.value_projection_measurePreserving π.seedLaw
  have hInt : Integrable (fun v : CompleteWorld π.Seed => B.maximum (f v)) (B.completeWorldLaw π.seedLaw) :=
    hmp.integrable_comp_of_integrable B.integrable_maximum
  have hR := integral_mono_ae π.integrable_reward hInt (π.rule.reward_le_maximum B π.seedLaw)
  have he := integral_map (μ := B.completeWorldLaw π.seedLaw) hmp.measurable.aemeasurable B.measurable_maximum.aestronglyMeasurable
  rw [hmp.map_eq] at he
  exact hR.trans_eq he.symm

lemma scalarObjective_le_bound (w c : ℝ) :
    π.scalarObjective w c ≤ |w| * (B.cap : ℝ) + |c| := by
  have hR : w * π.expectedReward ≤ |w| * (B.cap : ℝ) :=
    (mul_le_mul_of_nonneg_right (le_abs_self w) π.expectedReward_nonnegative).trans
      (mul_le_mul_of_nonneg_left π.expectedReward_le_cap (abs_nonneg w))
  have hT : c * π.expectedDuration ≤ |c| := by
    calc
      c * π.expectedDuration ≤ |c| * π.expectedDuration :=
        mul_le_mul_of_nonneg_right (le_abs_self c) π.expectedDuration_nonnegative
      _ ≤ |c| * 1 := mul_le_mul_of_nonneg_left π.expectedDuration_le_one (abs_nonneg c)
      _ = |c| := mul_one _
  exact add_le_add hR hT

noncomputable def waiting (B : CountableInstance) : RandomizedCountablePolicy B where
  Seed := Unit
  seedLaw := Measure.dirac ()
  rule := ⟨fun _ _ _ _ _ _ => false,fun _ _ _ _ _ => false⟩
  measurable_rule := ⟨measurable_const,measurable_const⟩
  admissible := by
    apply ae_of_all
    intro v h
    obtain ⟨i,hi⟩ := h
    have hf : (CountableRule.mk (fun _ _ _ _ _ _ => false) (fun _ _ _ _ _ => false)).codeAccepted v i = False := by
      unfold CountableRule.codeAccepted CountableRule.candidateAction
      cases candidateEnumeration.symm i <;> simp
    exact False.elim (hf.mp hi)

lemma waiting_no_first (B : CountableInstance) (v : CompleteWorld Unit) :
    ¬∃ i, FirstAcceptance.Earliest (waiting B).rule.codeAccepted codeTime v i := by
  rintro ⟨i,hi⟩
  have ha := hi.1.2.2
  unfold CountableRule.candidateAction at ha
  cases hc : candidateEnumeration.symm i <;> simp only [waiting,hc] at ha <;> cases ha

lemma waiting_realizedReward (B : CountableInstance) (v : CompleteWorld Unit) :
    (waiting B).rule.realizedReward B.terminal v = (B.terminal : ℝ) :=
  (waiting B).rule.no_first_reward _ _ (waiting_no_first B v)

lemma waiting_realizedDuration (B : CountableInstance) (v : CompleteWorld Unit) :
    (waiting B).rule.realizedDuration v = 1 :=
  FirstAcceptance.stoppingTime_of_no_first (waiting_no_first B v)

lemma waiting_scalarObjective (B : CountableInstance) (w c : ℝ) :
    (waiting B).scalarObjective w c = w * (B.terminal : ℝ) + c := by
  unfold scalarObjective expectedReward expectedDuration
  simp only [waiting_realizedReward,waiting_realizedDuration,integral_const,probReal_univ,one_smul,mul_one]

end RandomizedCountablePolicy

namespace CountableInstance

variable (B : CountableInstance)

noncomputable def scalarPayoffs (w c : ℝ) : Set ℝ :=
  Set.range (fun π : RandomizedCountablePolicy B => π.scalarObjective w c)

noncomputable def optimalScalarValue (w c : ℝ) : ℝ := sSup (B.scalarPayoffs w c)

lemma scalarPayoffs_nonempty (w c : ℝ) : (B.scalarPayoffs w c).Nonempty :=
  ⟨_,⟨RandomizedCountablePolicy.waiting B,rfl⟩⟩

lemma scalarPayoffs_bddAbove (w c : ℝ) : BddAbove (B.scalarPayoffs w c) := by
  refine ⟨|w| * (B.cap : ℝ) + |c|,?_⟩
  rintro _ ⟨π,rfl⟩
  exact π.scalarObjective_le_bound w c

lemma scalarObjective_le_value (π : RandomizedCountablePolicy B) (w c : ℝ) :
    π.scalarObjective w c ≤ B.optimalScalarValue w c :=
  le_csSup (B.scalarPayoffs_bddAbove w c) ⟨π,rfl⟩

lemma waiting_le_value (w c : ℝ) : w * (B.terminal : ℝ) + c ≤ B.optimalScalarValue w c := by
  rw [← RandomizedCountablePolicy.waiting_scalarObjective B w c]
  exact B.scalarObjective_le_value _ _ _

lemma optimalScalarValue_le {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    B.optimalScalarValue w c ≤ w * B.expectedMaximum + c := by
  apply csSup_le (B.scalarPayoffs_nonempty w c)
  rintro _ ⟨π,rfl⟩
  exact add_le_add (mul_le_mul_of_nonneg_left π.expectedReward_le_maximum hw)
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left π.expectedDuration_le_one hc)

lemma optimalScalarValue_zero {c : ℝ} (hc : 0 ≤ c) : B.optimalScalarValue 0 c = c := by
  apply le_antisymm
  · simpa only [zero_mul,zero_add] using B.optimalScalarValue_le (w := 0) (by positivity) hc
  · simpa only [zero_mul,zero_add] using B.waiting_le_value 0 c

end CountableInstance
end ProphetSecretary.Limiting
