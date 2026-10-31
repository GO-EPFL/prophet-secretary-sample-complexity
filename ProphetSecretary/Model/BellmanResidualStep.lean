import ProphetSecretary.Model.BellmanResidualBasic

/-!
# One-step Bellman residual identity

Both transition laws have probability mass one. After subtracting their common child
continuation constant, the difference of acceptance-or-continuation expectations is the
positive-part residual. The rejected child gap is signed because its design and truth
laws may differ.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma Instance.abs_firstTransitionResidual_le (Q P : Instance (n + 1))
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (t : ℝ) :
    |Q.firstTransitionResidual P i w c t| ≤ w * ((∫ x, x ∂Q.law i) + ∫ x, x ∂P.law i) := by
  apply Q.abs_lawResidual_le P hQ hP i hw
  exact optimalScalarValue_nonnegative (Q.restrictTo (remainingSet i))
    (Q.restrictTo_integrable_maximum _ hQ) hw (mul_nonneg hc (le_max_left _ _))

lemma Instance.integrable_firstTransitionResidual (Q P : Instance (n + 1))
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Integrable (Q.firstTransitionResidual P i w c) (Instance.firstChildTimeLaw i) := by
  apply Integrable.of_bound (Q.firstTransitionResidual_continuous P hQ hP i hw hc).measurable.aestronglyMeasurable
    (w * ((∫ x, x ∂Q.law i) + ∫ x, x ∂P.law i))
  exact Eventually.of_forall fun t => by
    simpa only [Real.norm_eq_abs] using Q.abs_firstTransitionResidual_le P hQ hP i hw hc t

lemma Instance.integrable_bellmanFirstPayoff_under (Q P : Instance (n + 1))
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Integrable (Q.bellmanFirstPayoff i w c) ((Instance.firstChildTimeLaw i).prod (P.law i)) := by
  have ht : Integrable (id : ℝ → ℝ) (Instance.firstChildTimeLaw i) := by
    apply Integrable.of_bound aestronglyMeasurable_id 1
    filter_upwards [Instance.firstChildTimeLaw_mem_unitInterval i] with t ht
    simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg ht.1.1] using ht.1.2
  have hx := P.integrable_maximum_iff.mp hP i
  exact ((ht.const_mul c).comp_fst (P.law i)).add
    (((hx.const_mul w).comp_snd (Instance.firstChildTimeLaw i)).sup
      ((Q.integrable_bellmanContinuation hQ i hw hc).comp_fst (P.law i)))

lemma Policy.integrable_bellmanActionLoss_under (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (Q P : Instance (n + 1)) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Integrable (π.bellmanActionLoss Q i w c) (ν.prod ((Instance.firstChildTimeLaw i).prod (P.law i))) := by
  have hx := ((P.integrable_maximum_iff.mp hP i).const_mul w).comp_snd
    (Instance.firstChildTimeLaw i) |>.comp_snd ν
  have hv := (Q.integrable_bellmanContinuation hQ i hw hc).comp_fst (P.law i) |>.comp_snd ν
  have he : MeasurableSet {p : Instance.FirstPrefixData Seed | π.firstAction p.1 i p.2.1 p.2.2 = true} :=
    measurableSet_eq_fun (π.measurable_firstAction hπ i) measurable_const
  have hi := Integrable.piecewise he hx.restrict hv.restrict
  have hchoice : Integrable (fun p : Instance.FirstPrefixData Seed =>
      if π.firstAction p.1 i p.2.1 p.2.2 = true then w * p.2.2 else Q.bellmanContinuation i w c p.2.1)
      (ν.prod ((Instance.firstChildTimeLaw i).prod (P.law i))) := by
    apply hi.congr
    exact Eventually.of_forall fun p => by
      by_cases ha : π.firstAction p.1 i p.2.1 p.2.2 = true <;> simp [Set.piecewise, ha]
  exact (hx.sup hv).sub hchoice

/-- This is not a nonnegative regret: continuation is optimized under `Q`, but the
fixed continuation competitor's payoff is evaluated under `P`. -/
noncomputable def Policy.bellmanCrossGap (π : Policy Seed (n + 1)) (Q P : Instance (n + 1))
    (i : Fin (n + 1)) (w c : ℝ) (p : Instance.FirstPrefixData Seed) : ℝ :=
  Q.bellmanContinuation i w c p.2.1 - π.firstContinuationObjective P i w c p

lemma Policy.integrable_bellmanCrossGap (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (Q P : Instance (n + 1)) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Integrable (π.bellmanCrossGap Q P i w c) (ν.prod ((Instance.firstChildTimeLaw i).prod (P.law i))) :=
  (((Q.integrable_bellmanContinuation hQ i hw hc).comp_fst (P.law i)).comp_snd ν).sub
    (π.integrable_firstContinuationObjective hπ P hP ν i hw hc)

lemma Policy.integrable_rejectedCrossGap (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (Q P : Instance (n + 1)) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (i : Fin (n + 1)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Integrable (fun p : Instance.FirstPrefixData Seed =>
      if π.firstAction p.1 i p.2.1 p.2.2 = true then 0 else π.bellmanCrossGap Q P i w c p)
      (ν.prod ((Instance.firstChildTimeLaw i).prod (P.law i))) := by
  have he : MeasurableSet {p : Instance.FirstPrefixData Seed | π.firstAction p.1 i p.2.1 p.2.2 = true} :=
    measurableSet_eq_fun (π.measurable_firstAction hπ i) measurable_const
  have hi := Integrable.piecewise he (integrable_const (0 : ℝ)).restrict
    (π.integrable_bellmanCrossGap hπ Q P hQ hP ν i hw hc).restrict
  apply hi.congr
  exact Eventually.of_forall fun p => by
    by_cases ha : π.firstAction p.1 i p.2.1 p.2.2 = true <;> simp [Set.piecewise, ha]

lemma Policy.bellman_crossFirstGap (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (Q P : Instance (n + 1)) (hP : Integrable Instance.maximum P.valuesLaw)
    (i : Fin (n + 1)) (w c : ℝ) (p : Instance.FirstPrefixData Seed) (ht : p.2.1 < 1) :
    Q.bellmanFirstPayoff i w c p.2 - π.firstStepObjective P i w c p =
      π.bellmanActionLoss Q i w c p + if π.firstAction p.1 i p.2.1 p.2.2 = true then 0 else
        π.bellmanCrossGap Q P i w c p := by
  rw [π.firstDecision_expected hπ P hP i w c p ht]
  unfold Instance.bellmanFirstPayoff Policy.bellmanActionLoss Policy.bellmanCrossGap
  split_ifs <;> ring

/-- Changing only the first candidate's transition law produces the residual under
its true first-prefix measure. This uses both probability masses explicitly. -/
lemma Instance.integral_bellmanPrefix_with_residual (Q P : Instance (n + 1))
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin (n + 1))
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (∫ z, Q.bellmanFirstPayoff i w c z ∂(Instance.firstChildTimeLaw i).prod (Q.law i)) =
      ∫ p : Instance.FirstPrefixData Seed,
        Q.bellmanFirstPayoff i w c p.2 + Q.firstTransitionResidual P i w c p.2.1
        ∂ν.prod ((Instance.firstChildTimeLaw i).prod (P.law i)) := by
  let f : ℝ × ℝ → ℝ := fun z => Q.bellmanFirstPayoff i w c z + Q.firstTransitionResidual P i w c z.1
  have hfi : Integrable f ((Instance.firstChildTimeLaw i).prod (P.law i)) :=
    (Q.integrable_bellmanFirstPayoff_under P hQ hP i hw hc).add
      ((Q.integrable_firstTransitionResidual P hQ hP i hw hc).comp_fst (P.law i))
  have hfm : Measurable f := (Q.measurable_bellmanFirstPayoff hQ i hw hc).add
    ((Q.firstTransitionResidual_continuous P hQ hP i hw hc).measurable.comp measurable_fst)
  have hp := measurePreserving_snd (μ := ν) (ν := (Instance.firstChildTimeLaw i).prod (P.law i))
  have he := integral_map (μ := ν.prod ((Instance.firstChildTimeLaw i).prod (P.law i)))
    hp.measurable.aemeasurable hfm.aestronglyMeasurable
  rw [hp.map_eq] at he
  change _ = ∫ p : Instance.FirstPrefixData Seed, f p.2 ∂ν.prod ((Instance.firstChildTimeLaw i).prod (P.law i))
  rw [← he, integral_prod _ (Q.integrable_bellmanFirstPayoff hQ i hw hc), integral_prod _ hfi]
  apply integral_congr_ae
  exact Eventually.of_forall fun t => by
    let v := Q.bellmanContinuation i w c t
    have hQx := integrable_max_with (Q.law i) (Q.integrable_maximum_iff.mp hQ i) w v
    have hPx := integrable_max_with (P.law i) (P.integrable_maximum_iff.mp hP i) w v
    have hpayP : Integrable (fun x : ℝ => c * t + max (w * x) v) (P.law i) :=
      (integrable_const _).add hPx
    change (∫ x, c * t + max (w * x) v ∂Q.law i) =
      ∫ x, (c * t + max (w * x) v) + Q.firstTransitionResidual P i w c t ∂P.law i
    rw [integral_add (integrable_const _) hQx, integral_add hpayP (integrable_const _),
      integral_add (integrable_const _) hPx]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    change c * t + expectedMaxWith (Q.law i) w v =
      (c * t + expectedMaxWith (P.law i) w v) + Q.lawResidual P i w v
    rw [Q.lawResidual_eq_maxDifference P hQ hP i w v]
    ring

/-- The first-step residual identity against an arbitrary true-law policy. -/
theorem RandomizedPolicy.bellman_firstResidualIdentity (π : RandomizedPolicy (n + 1))
    (Q P : Instance (n + 1)) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    optimalScalarValue Q w c - π.scalarObjective P w c =
      ∑ i : Fin (n + 1), ∫ p : Instance.FirstPrefixData π.Seed,
        (Q.firstTransitionResidual P i w c p.2.1 + π.rule.bellmanActionLoss Q i w c p +
          if π.rule.firstAction p.1 i p.2.1 p.2.2 = true then 0 else π.rule.bellmanCrossGap Q P i w c p)
        ∂π.seedLaw.prod ((Instance.firstChildTimeLaw i).prod (P.law i)) := by
  rw [Q.optimalScalarValue_eq_bellmanValue hQ hw hc, π.scalarObjective_eq_firstStep P hP w c]
  unfold Instance.bellmanValue
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hInt : Integrable (fun p : Instance.FirstPrefixData π.Seed =>
      Q.bellmanFirstPayoff i w c p.2 + Q.firstTransitionResidual P i w c p.2.1)
      (π.seedLaw.prod ((Instance.firstChildTimeLaw i).prod (P.law i))) :=
    ((Q.integrable_bellmanFirstPayoff_under P hQ hP i hw.le hc).comp_snd π.seedLaw).add
    (((Q.integrable_firstTransitionResidual P hQ hP i hw.le hc).comp_fst (P.law i)).comp_snd π.seedLaw)
  rw [Q.integral_bellmanPrefix_with_residual P hQ hP π.seedLaw i hw.le hc,
    ← integral_sub hInt (π.integrable_firstStepObjective P hP i w c)]
  apply integral_congr_ae
  filter_upwards [(P.firstPrefix_time_measurePreserving π.seedLaw i).quasiMeasurePreserving.ae
    (Instance.firstChildTimeLaw_mem_unitInterval i)] with p hp
  have h := π.rule.bellman_crossFirstGap π.measurable_rule Q P hP i w c p hp.2
  linarith

end ProphetSecretary.Model
