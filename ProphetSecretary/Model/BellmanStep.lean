import ProphetSecretary.Model.BellmanIntegration
import ProphetSecretary.Model.FirstDecision

/-!
# Expected payoff at one observed first offer

The prefix is held fixed when future variables are averaged. The first action
uses only seed, identity, time, and current value. The continuation competitor
is compared with the unrestricted child optimum.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

namespace Instance

noncomputable def firstFutureLaw (P : Instance (n + 1)) (i : Fin (n + 1)) :
    Measure (FirstFutureData i) :=
  (P.restrictTo (remainingSet i)).valuesLaw.prod (clocksLaw (remainingSet i).card)

instance firstFutureLaw_probability (P : Instance (n + 1)) (i : Fin (n + 1)) :
    IsProbabilityMeasure (P.firstFutureLaw i) := by
  unfold firstFutureLaw
  infer_instance

lemma firstFuture_clocks_positive (P : Instance (n + 1)) (i : Fin (n + 1)) :
    ∀ᵐ z : FirstFutureData i ∂P.firstFutureLaw i, ∀ j, 0 < z.2 j :=
  (P.restrictTo (remainingSet i)).addUnitSeed_measurePreserving.quasiMeasurePreserving.ae
    ((P.restrictTo (remainingSet i)).world_clocks_positive (Measure.dirac ()))

end Instance

/-- Child payoff after fixing the observed first prefix. -/
noncomputable def Policy.firstContinuationObjective (π : Policy Seed (n + 1))
    (P : Instance (n + 1)) (i : Fin (n + 1)) (w c : ℝ) (p : Instance.FirstPrefixData Seed) : ℝ :=
  ∫ z : Instance.FirstFutureData i,
    π.firstRemainingPayoff i w c (p.1, p.2.1, p.2.2, z) ∂P.firstFutureLaw i

/-- Expected payoff conditional on the complete observable first prefix. -/
noncomputable def Policy.firstStepObjective (π : Policy Seed (n + 1))
    (P : Instance (n + 1)) (i : Fin (n + 1)) (w c : ℝ) (p : Instance.FirstPrefixData Seed) : ℝ :=
  ∫ z : Instance.FirstFutureData i,
    π.firstChildPayoff i w c (p.1, p.2.1, p.2.2, z) ∂P.firstFutureLaw i

lemma Policy.firstContinuationObjective_eq (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (P : Instance (n + 1)) (i : Fin (n + 1)) (w c : ℝ) (p : Instance.FirstPrefixData Seed) :
    π.firstContinuationObjective P i w c p =
      (π.fixedContinuationPolicy hπ (remainingSet i) p.1 p.2.1 (firstPrefix i p.2.1 p.2.2)).scalarObjective
        (P.restrictTo (remainingSet i)) w (c * (1 - p.2.1)) := by
  symm
  exact Instance.integral_unitPolicy_payoff (P.restrictTo (remainingSet i))
    (π.fixedContinuation (remainingSet i) p.1 p.2.1 (firstPrefix i p.2.1 p.2.2))
    (π.fixedContinuation_isMeasurable hπ _ _ _ _) w (c * (1 - p.2.1))

lemma Policy.integrable_firstRemaining (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (P : Instance (n + 1)) (hP : Integrable Instance.maximum P.valuesLaw)
    (i : Fin (n + 1)) (w c : ℝ) (p : Instance.FirstPrefixData Seed) :
    Integrable (fun z : Instance.FirstFutureData i ↦
      π.firstRemainingPayoff i w c (p.1, p.2.1, p.2.2, z)) (P.firstFutureLaw i) := by
  let Q := P.restrictTo (remainingSet i)
  let C := π.fixedContinuationPolicy hπ (remainingSet i) p.1 p.2.1 (firstPrefix i p.2.1 p.2.2)
  have hInt := ((C.integrable_realizedReward Q (P.restrictTo_integrable_maximum _ hP)).const_mul w).add
    ((C.integrable_realizedDuration Q).const_mul (c * (1 - p.2.1)))
  exact Q.addUnitSeed_measurePreserving.integrable_comp_of_integrable hInt

/-- All fixed-prefix first-step payoffs are integrable; expectations here are
not merely totalized Bochner integrals of potentially divergent functions. -/
lemma Policy.integrable_firstChild (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (P : Instance (n + 1)) (hP : Integrable Instance.maximum P.valuesLaw)
    (i : Fin (n + 1)) (w c : ℝ) (p : Instance.FirstPrefixData Seed) (ht : p.2.1 < 1) :
    Integrable (fun z : Instance.FirstFutureData i ↦
      π.firstChildPayoff i w c (p.1, p.2.1, p.2.2, z)) (P.firstFutureLaw i) := by
  have heq : (fun z : Instance.FirstFutureData i ↦ π.firstChildPayoff i w c (p.1, p.2.1, p.2.2, z)) =ᵐ[P.firstFutureLaw i]
      (fun z ↦ c * p.2.1 + if π.firstAction p.1 i p.2.1 p.2.2 = true then w * p.2.2 else
        π.firstRemainingPayoff i w c (p.1, p.2.1, p.2.2, z)) := by
    filter_upwards [P.firstFuture_clocks_positive i] with z hz
    exact π.firstDecision_scalarPayoff p.1 i ht p.2.2 z.1 z.2 hz w c
  apply Integrable.congr _ heq.symm
  by_cases ha : π.firstAction p.1 i p.2.1 p.2.2 = true
  · simp only [ha, if_true]
    exact integrable_const _
  · simp only [ha, Bool.false_eq_true, if_false]
    exact (integrable_const _).add (π.integrable_firstRemaining hπ P hP i w c p)

lemma Policy.measurable_firstContinuationObjective (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (P : Instance (n + 1)) (i : Fin (n + 1)) (w c : ℝ) :
    Measurable (π.firstContinuationObjective P i w c) := by
  have hmap : Measurable (fun z : Instance.FirstPrefixData Seed × Instance.FirstFutureData i ↦
      (z.1.1, z.1.2.1, z.1.2.2, z.2)) := by fun_prop
  exact ((π.measurable_firstRemainingPayoff hπ i w c).comp hmap).stronglyMeasurable.integral_prod_right'.measurable

lemma Policy.measurable_firstStepObjective (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (P : Instance (n + 1)) (i : Fin (n + 1)) (w c : ℝ) :
    Measurable (π.firstStepObjective P i w c) := by
  have hmap : Measurable (fun z : Instance.FirstPrefixData Seed × Instance.FirstFutureData i ↦
      (z.1.1, z.1.2.1, z.1.2.2, z.2)) := by fun_prop
  exact ((π.measurable_firstChildPayoff hπ i w c).comp hmap).stronglyMeasurable.integral_prod_right'.measurable

lemma Policy.firstDecision_expected (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (P : Instance (n + 1)) (hP : Integrable Instance.maximum P.valuesLaw)
    (i : Fin (n + 1)) (w c : ℝ) (p : Instance.FirstPrefixData Seed) (ht : p.2.1 < 1) :
    π.firstStepObjective P i w c p = c * p.2.1 +
      if π.firstAction p.1 i p.2.1 p.2.2 = true then w * p.2.2 else
        π.firstContinuationObjective P i w c p := by
  have heq : (fun z : Instance.FirstFutureData i ↦ π.firstChildPayoff i w c (p.1, p.2.1, p.2.2, z)) =ᵐ[P.firstFutureLaw i]
      (fun z ↦ c * p.2.1 + if π.firstAction p.1 i p.2.1 p.2.2 = true then w * p.2.2 else
        π.firstRemainingPayoff i w c (p.1, p.2.1, p.2.2, z)) := by
    filter_upwards [P.firstFuture_clocks_positive i] with z hz
    exact π.firstDecision_scalarPayoff p.1 i ht p.2.2 z.1 z.2 hz w c
  unfold Policy.firstStepObjective
  rw [integral_congr_ae heq]
  by_cases ha : π.firstAction p.1 i p.2.1 p.2.2 = true
  · simp only [ha, if_true]
    simp
  · simp only [ha, Bool.false_eq_true, if_false]
    rw [integral_add (integrable_const _) (π.integrable_firstRemaining hπ P hP i w c p)]
    simp only [integral_const, probReal_univ, one_smul]
    rfl

lemma Policy.firstContinuationObjective_le_optimal (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (P : Instance (n + 1)) (hP : Integrable Instance.maximum P.valuesLaw)
    (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (p : Instance.FirstPrefixData Seed) (ht : p.2.1 < 1) :
    π.firstContinuationObjective P i w c p ≤
      optimalScalarValue (P.restrictTo (remainingSet i)) w (c * (1 - p.2.1)) := by
  rw [π.firstContinuationObjective_eq hπ P i w c p]
  exact scalarObjective_le_optimal _ (P.restrictTo (remainingSet i))
    (P.restrictTo_integrable_maximum _ hP) hw (mul_nonneg hc (sub_nonneg.mpr ht.le))

/-- Averaging any continuation action is no better than choosing the larger
of acceptance payoff and optimal child continuation value. -/
lemma Policy.firstStepObjective_le_bellman (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (P : Instance (n + 1)) (hP : Integrable Instance.maximum P.valuesLaw)
    (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (p : Instance.FirstPrefixData Seed) (ht : p.2.1 < 1) :
    π.firstStepObjective P i w c p ≤ c * p.2.1 +
      max (w * p.2.2) (optimalScalarValue (P.restrictTo (remainingSet i)) w (c * (1 - p.2.1))) := by
  rw [π.firstDecision_expected hπ P hP i w c p ht]
  apply add_le_add le_rfl
  split_ifs
  · exact le_max_left _ _
  · exact (π.firstContinuationObjective_le_optimal hπ P hP i hw hc p ht).trans (le_max_right _ _)

end ProphetSecretary.Model
