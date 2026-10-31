import ProphetSecretary.Model.ThresholdVariation

/-!
# Positive reward normalization of the canonical policy

Dividing a positive reward coefficient from both payoffs preserves every
threshold decision, including ties. The policy's selected reward and normalized
duration therefore agree under either scalar parametrization.
-/

open MeasureTheory

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.valueThreshold_rewardNormalized (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (A : Finset (Fin n)) (t : ℝ) (i : Fin n) :
    P.valueThreshold w c A t i = P.valueThreshold 1 (c / w) A t i := by
  rw [P.valueThreshold_rewardNormalize hP hw hc,
    P.valueThreshold_rewardNormalize hP zero_lt_one (div_nonneg hc hw.le)]
  simp only [div_one]
  congr 1
  ring

lemma Instance.valuePolicy_rewardNormalize_rule (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (P.valuePolicy hP hw.le hc).rule =
      (P.valuePolicy hP (w := 1) (c := c / w) zero_le_one (div_nonneg hc hw.le)).rule := by
  change thresholdPolicy (fun (_ : Unit) A t i ↦ P.valueThreshold w c A t i) =
    thresholdPolicy (fun (_ : Unit) A t i ↦ P.valueThreshold 1 (c / w) A t i)
  unfold thresholdPolicy
  congr 1
  funext r t i x H
  change Decidable.decide (P.valueThreshold w c (unseen H) t i ≤ x) =
    Decidable.decide (P.valueThreshold 1 (c / w) (unseen H) t i ≤ x)
  rw [P.valueThreshold_rewardNormalized hP hw hc]

lemma Instance.valuePolicy_rewardNormalize_duration (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (P.valuePolicy hP hw.le hc).expectedDuration P =
      (P.valuePolicy hP (w := 1) (c := c / w) zero_le_one (div_nonneg hc hw.le)).expectedDuration P := by
  unfold RandomizedPolicy.expectedDuration RandomizedPolicy.realizedDuration
  change (∫ ω : World n Unit, (P.valuePolicy hP hw.le hc).rule.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1
    ∂P.worldLaw (Measure.dirac ())) =
      ∫ ω : World n Unit, (P.valuePolicy hP (w := 1) (c := c / w) zero_le_one (div_nonneg hc hw.le)).rule.stoppingTime
        ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw (Measure.dirac ())
  rw [P.valuePolicy_rewardNormalize_rule hP hw hc]
  rfl

lemma Instance.valuePolicy_rewardNormalize_reward (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (P.valuePolicy hP hw.le hc).expectedReward P =
      (P.valuePolicy hP (w := 1) (c := c / w) zero_le_one (div_nonneg hc hw.le)).expectedReward P := by
  unfold RandomizedPolicy.expectedReward RandomizedPolicy.realizedReward
  change (∫ ω : World n Unit, (P.valuePolicy hP hw.le hc).rule.reward ω.2.2 Finset.univ ω.1 ω.2.1
    ∂P.worldLaw (Measure.dirac ())) =
      ∫ ω : World n Unit, (P.valuePolicy hP (w := 1) (c := c / w) zero_le_one (div_nonneg hc hw.le)).rule.reward
        ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw (Measure.dirac ())
  rw [P.valuePolicy_rewardNormalize_rule hP hw hc]
  rfl

end ProphetSecretary.Model
