import ProphetSecretary.Model.BellmanOptimal

/-!
# Bellman losses for general online competitors

The action loss compares acceptance with optimal additional child continuation.
It is distinct from the global competitive gap. The first-step identity retains
an explicit rejected-child regret; further recursion expands that regret into
later reached action losses.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def Policy.bellmanActionLoss (π : Policy Seed (n + 1)) (P : Instance (n + 1))
    (i : Fin (n + 1)) (w c : ℝ) (p : Instance.FirstPrefixData Seed) : ℝ :=
  max (w * p.2.2) (P.bellmanContinuation i w c p.2.1) -
    if π.firstAction p.1 i p.2.1 p.2.2 = true then w * p.2.2 else P.bellmanContinuation i w c p.2.1

noncomputable def Policy.bellmanChildRegret (π : Policy Seed (n + 1)) (P : Instance (n + 1))
    (i : Fin (n + 1)) (w c : ℝ) (p : Instance.FirstPrefixData Seed) : ℝ :=
  P.bellmanContinuation i w c p.2.1 - π.firstContinuationObjective P i w c p

omit [MeasurableSpace Seed] in
lemma Policy.bellmanActionLoss_nonnegative (π : Policy Seed (n + 1)) (P : Instance (n + 1))
    (i : Fin (n + 1)) (w c : ℝ) (p : Instance.FirstPrefixData Seed) :
    0 ≤ π.bellmanActionLoss P i w c p := by
  unfold Policy.bellmanActionLoss
  split_ifs
  · exact sub_nonneg.mpr (le_max_left _ _)
  · exact sub_nonneg.mpr (le_max_right _ _)

lemma Policy.firstContinuationObjective_nonnegative (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (P : Instance (n + 1)) (hP : Integrable Instance.maximum P.valuesLaw)
    (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (p : Instance.FirstPrefixData Seed) (ht : p.2.1 ≤ 1) :
    0 ≤ π.firstContinuationObjective P i w c p := by
  rw [π.firstContinuationObjective_eq hπ P i w c p]
  exact RandomizedPolicy.scalarObjective_nonnegative _ (P.restrictTo (remainingSet i))
    (P.restrictTo_integrable_maximum _ hP) hw (mul_nonneg hc (sub_nonneg.mpr ht))

lemma Policy.bellmanChildRegret_nonnegative (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (P : Instance (n + 1)) (hP : Integrable Instance.maximum P.valuesLaw)
    (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (p : Instance.FirstPrefixData Seed) (ht : p.2.1 < 1) :
    0 ≤ π.bellmanChildRegret P i w c p := by
  apply sub_nonneg.mpr
  have h := π.firstContinuationObjective_le_optimal hπ P hP i hw hc p ht
  simpa only [Instance.bellmanContinuation, max_eq_right (sub_nonneg.mpr ht.le)] using h

/-- The algebraic performance difference after averaging the residual future. -/
lemma Policy.bellman_firstGap (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (P : Instance (n + 1)) (hP : Integrable Instance.maximum P.valuesLaw)
    (i : Fin (n + 1)) (w c : ℝ) (p : Instance.FirstPrefixData Seed) (ht : p.2.1 < 1) :
    P.bellmanFirstPayoff i w c p.2 - π.firstStepObjective P i w c p =
      π.bellmanActionLoss P i w c p + if π.firstAction p.1 i p.2.1 p.2.2 = true then 0 else
        π.bellmanChildRegret P i w c p := by
  rw [π.firstDecision_expected hπ P hP i w c p ht]
  unfold Instance.bellmanFirstPayoff Policy.bellmanActionLoss Policy.bellmanChildRegret
  split_ifs <;> ring

lemma Policy.measurable_bellmanActionLoss (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (P : Instance (n + 1)) (hP : Integrable Instance.maximum P.valuesLaw)
    (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Measurable (π.bellmanActionLoss P i w c) := by
  have hx : Measurable (fun p : Instance.FirstPrefixData Seed ↦ w * p.2.2) :=
    measurable_const.mul (measurable_snd.comp measurable_snd)
  have hv : Measurable (fun p : Instance.FirstPrefixData Seed ↦ P.bellmanContinuation i w c p.2.1) :=
    (P.bellmanContinuation_continuous hP i hw hc).measurable.comp (measurable_fst.comp measurable_snd)
  have he : MeasurableSet {p : Instance.FirstPrefixData Seed | π.firstAction p.1 i p.2.1 p.2.2 = true} :=
    measurableSet_eq_fun (π.measurable_firstAction hπ i) measurable_const
  exact (hx.max hv).sub (Measurable.ite he hx hv)

lemma Policy.integrable_firstContinuationObjective (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (P : Instance (n + 1)) (hP : Integrable Instance.maximum P.valuesLaw)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Integrable (π.firstContinuationObjective P i w c)
      (ν.prod ((Instance.firstChildTimeLaw i).prod (P.law i))) := by
  let Q := P.restrictTo (remainingSet i)
  apply Integrable.of_bound (π.measurable_firstContinuationObjective hπ P i w c).aestronglyMeasurable
    (w * Q.expectedMaximum + c)
  filter_upwards [(P.firstPrefix_time_measurePreserving ν i).quasiMeasurePreserving.ae
    (Instance.firstChildTimeLaw_mem_unitInterval i)] with p hp
  have h0 := π.firstContinuationObjective_nonnegative hπ P hP i hw hc p hp.1.2
  have h1 := π.firstContinuationObjective_le_optimal hπ P hP i hw hc p hp.2
  have hcu0 : 0 ≤ c * (1 - p.2.1) := mul_nonneg hc (sub_nonneg.mpr hp.1.2)
  have hcu1 : c * (1 - p.2.1) ≤ c := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (sub_le_self 1 hp.1.1) hc
  have hV := optimalScalarValue_le_benchmark Q (P.restrictTo_integrable_maximum _ hP) hw hcu0
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact h1.trans (hV.trans (add_le_add le_rfl hcu1))

lemma Policy.integrable_bellmanChildRegret (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (P : Instance (n + 1)) (hP : Integrable Instance.maximum P.valuesLaw)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Integrable (π.bellmanChildRegret P i w c)
      (ν.prod ((Instance.firstChildTimeLaw i).prod (P.law i))) := by
  exact (((P.integrable_bellmanContinuation hP i hw hc).comp_fst (P.law i)).comp_snd ν).sub
    (π.integrable_firstContinuationObjective hπ P hP ν i hw hc)

lemma Policy.integrable_bellmanActionLoss (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (P : Instance (n + 1)) (hP : Integrable Instance.maximum P.valuesLaw)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Integrable (π.bellmanActionLoss P i w c)
      (ν.prod ((Instance.firstChildTimeLaw i).prod (P.law i))) := by
  have hx := (((P.integrable_maximum_iff.mp hP) i).const_mul w).comp_snd
    (Instance.firstChildTimeLaw i) |>.comp_snd ν
  have hv := (P.integrable_bellmanContinuation hP i hw hc).comp_fst (P.law i) |>.comp_snd ν
  have he : MeasurableSet {p : Instance.FirstPrefixData Seed | π.firstAction p.1 i p.2.1 p.2.2 = true} :=
    measurableSet_eq_fun (π.measurable_firstAction hπ i) measurable_const
  have hchoice0 := Integrable.piecewise he hx.restrict hv.restrict
  have hchoice : Integrable (fun p : Instance.FirstPrefixData Seed ↦
      if π.firstAction p.1 i p.2.1 p.2.2 = true then w * p.2.2 else P.bellmanContinuation i w c p.2.1)
      (ν.prod ((Instance.firstChildTimeLaw i).prod (P.law i))) := by
    apply hchoice0.congr
    filter_upwards [] with p
    by_cases ha : π.firstAction p.1 i p.2.1 p.2.2 = true <;> simp [Set.piecewise, ha]
  exact (hx.sup hv).sub hchoice

/-- The rejected child regret is integrable, including policies whose actions
use all identities, zero observations, past values and independent randomness. -/
lemma Policy.integrable_rejectedChildRegret (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (P : Instance (n + 1)) (hP : Integrable Instance.maximum P.valuesLaw)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Integrable (fun p : Instance.FirstPrefixData Seed ↦
      if π.firstAction p.1 i p.2.1 p.2.2 = true then 0 else π.bellmanChildRegret P i w c p)
      (ν.prod ((Instance.firstChildTimeLaw i).prod (P.law i))) := by
  have he : MeasurableSet {p : Instance.FirstPrefixData Seed | π.firstAction p.1 i p.2.1 p.2.2 = true} :=
    measurableSet_eq_fun (π.measurable_firstAction hπ i) measurable_const
  have hR := Integrable.piecewise he (integrable_const (0 : ℝ)).restrict
    (π.integrable_bellmanChildRegret hπ P hP ν i hw hc).restrict
  apply hR.congr
  filter_upwards [] with p
  by_cases ha : π.firstAction p.1 i p.2.1 p.2.2 = true <;> simp [Set.piecewise, ha]

/-- Exact first-step performance difference. Every rejected child term is a
regret against the same full policy class; no conditional optimizer is assumed. -/
theorem RandomizedPolicy.bellman_firstLossIdentity (π : RandomizedPolicy (n + 1))
    (P : Instance (n + 1)) (hP : Integrable Instance.maximum P.valuesLaw)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    optimalScalarValue P w c - π.scalarObjective P w c =
      ∑ i : Fin (n + 1), ∫ p : Instance.FirstPrefixData π.Seed,
        (π.rule.bellmanActionLoss P i w c p +
          if π.rule.firstAction p.1 i p.2.1 p.2.2 = true then 0 else π.rule.bellmanChildRegret P i w c p)
        ∂π.seedLaw.prod ((Instance.firstChildTimeLaw i).prod (P.law i)) := by
  rw [P.optimalScalarValue_eq_bellmanValue hP hw hc, π.scalarObjective_eq_firstStep P hP w c]
  unfold Instance.bellmanValue
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← P.integral_bellmanPrefix π.seedLaw hP i hw.le hc,
    ← integral_sub ((P.integrable_bellmanFirstPayoff hP i hw.le hc).comp_snd π.seedLaw)
      (π.integrable_firstStepObjective P hP i w c)]
  apply integral_congr_ae
  filter_upwards [(P.firstPrefix_time_measurePreserving π.seedLaw i).quasiMeasurePreserving.ae
    (Instance.firstChildTimeLaw_mem_unitInterval i)] with p hp
  exact π.rule.bellman_firstGap π.measurable_rule P hP i w c p hp.2

end ProphetSecretary.Model
