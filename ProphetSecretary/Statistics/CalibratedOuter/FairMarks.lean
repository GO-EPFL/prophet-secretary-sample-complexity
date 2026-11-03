import ProphetSecretary.Statistics.CalibratedOuter.FairMarkExecution
import ProphetSecretary.Reach.CappedThresholdComparison

/-!
# Weighted loss from rounding the outer marks

The collision event depends only on the independent mark array. The loss
therefore scales with the expected maximum before bounded normalization.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m : ℕ}

private lemma outerMarkWorld_measurePreserving
    {X U T S V : Type} [MeasurableSpace X] [MeasurableSpace U] [MeasurableSpace T]
    [MeasurableSpace S] [MeasurableSpace V]
    (μX : Measure X) (μU : Measure U) (μT : Measure T) (μS : Measure S) (μV : Measure V)
    [IsProbabilityMeasure μX] [IsProbabilityMeasure μU] [IsProbabilityMeasure μT]
    [IsProbabilityMeasure μS] [IsProbabilityMeasure μV] :
    MeasurePreserving
      (fun q : (X × (U × (T × S))) × V => (q.1.1,q.1.2.1,q.1.2.2.1,q.2,q.1.2.2.2))
      ((μX.prod (μU.prod (μT.prod μS))).prod μV)
      (μX.prod (μU.prod (μT.prod (μV.prod μS)))) := by
  have h1 := measurePreserving_prodAssoc μX (μU.prod (μT.prod μS)) μV
  have h2 := (MeasurePreserving.id μX).prod (measurePreserving_prodAssoc μU (μT.prod μS) μV)
  have h3 := (MeasurePreserving.id μX).prod
    ((MeasurePreserving.id μU).prod (measurePreserving_prodAssoc μT μS μV))
  have h4 := (MeasurePreserving.id μX).prod
    ((MeasurePreserving.id μU).prod ((MeasurePreserving.id μT).prod
      (Measure.measurePreserving_swap (μ := μS) (ν := μV))))
  exact h4.comp (h3.comp (h2.comp h1))

set_option maxHeartbeats 180000 in
/-- The marked execution has a coupling with the continuous-mark execution
whose reward loss is proportional to the unbounded benchmark. -/
theorem outerFairMarkLearner_reward_loss (hn : 0<n) (hm : 1≤m) (L : Learner n (2*m))
    (b : ℕ) (hGrid : m^2*(n*(outerSampleBudget m+1))^2≤2^b)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) :
    (outerLearner m hm L).expectedReward P-(outerFairMarkLearner hm L b).expectedReward P ≤
      P.expectedMaximum/(2*(m : ℝ)^2) := by
  let N := 2^b
  have hN : 0<N := by positivity
  let M := outerMarkSlotCount n m
  let V := Instance.clocksLaw M
  letI : IsProbabilityMeasure V := Instance.clocksLaw_probability
  let T := P.reservoirLaw (outerSampleBudget m)
  let U := Instance.clocksLaw n
  let Q := L.seedLaw
  let Ω := World n (Reservoir n (outerSampleBudget m) × L.Seed)
  let μ : Measure Ω := P.worldLaw (T.prod Q)
  let mark := fun u : OuterMarkArray n m ℝ => fun i => uniformGridRound N hN (u i)
  have hmMark : Measurable mark :=
    measurable_pi_lambda _ (fun i => (measurable_uniformGridRound N hN).comp (measurable_pi_apply i))
  let π := (outerMarkedLearner V hm L id measurable_id).randomizedPolicy P
  let π' := (outerMarkedLearner V hm L mark hmMark).randomizedPolicy P
  let f : Ω × OuterMarkArray n m ℝ → π.World :=
    fun q => (q.1.1,q.1.2.1,q.1.2.2.1,q.2,q.1.2.2.2)
  have hLaw : MeasurePreserving f (μ.prod V) (P.worldLaw π.seedLaw) := by
    exact outerMarkWorld_measurePreserving P.valuesLaw U T Q V
  let f' : Ω × OuterMarkArray n m ℝ → π'.World :=
    fun q => (q.1.1,q.1.2.1,q.1.2.2.1,q.2,q.1.2.2.2)
  have hLaw' : MeasurePreserving f' (μ.prod V) (P.worldLaw π'.seedLaw) := by
    exact outerMarkWorld_measurePreserving P.valuesLaw U T Q V
  let X : Ω × OuterMarkArray n m ℝ → ℝ := fun q => π.realizedReward (f q)
  let X' : Ω × OuterMarkArray n m ℝ → ℝ := fun q => π'.realizedReward (f' q)
  have hX : Integrable X (μ.prod V) := by
    change Integrable (π.realizedReward ∘ f) _
    exact hLaw.integrable_comp_of_integrable (π.integrable_realizedReward P hP)
  have hX' : Integrable X' (μ.prod V) := by
    change Integrable (π'.realizedReward ∘ f') _
    exact hLaw'.integrable_comp_of_integrable (π'.integrable_realizedReward P hP)
  have hInt : (∫ q : Ω × OuterMarkArray n m ℝ, X q ∂μ.prod V) = (outerLearner m hm L).expectedReward P :=
    (hLaw.hasLaw.integral_comp π.measurable_realizedReward.aestronglyMeasurable).trans
      (outerMarkedLearner_uniform_reward hm L P)
  have hInt' : (∫ q : Ω × OuterMarkArray n m ℝ, X' q ∂μ.prod V) = (outerFairMarkLearner hm L b).expectedReward P :=
    (hLaw'.hasLaw.integral_comp π'.measurable_realizedReward.aestronglyMeasurable).trans
      (outerFairMarkLearner_reward_eq_rounded hm L b P).symm
  let E := outerMarkCollision M N hN
  let Y : Ω → ℝ := fun q => Instance.maximum q.1
  let G : Ω × OuterMarkArray n m ℝ → ℝ := fun q => Y q.1*E.indicator 1 q.2
  have hValues : MeasurePreserving (fun q : Ω => q.1) μ P.valuesLaw := measurePreserving_fst
  have hY : Integrable Y μ := by
    change Integrable (Instance.maximum ∘ fun q : Ω => q.1) μ
    exact hValues.integrable_comp_of_integrable hP
  have hG : Integrable G (μ.prod V) :=
    hY.smul_prod ((integrable_const (1 : ℝ)).indicator (measurableSet_outerMarkCollision M N hN))
  have hVals : ∀ᵐ q : Ω × OuterMarkArray n m ℝ ∂μ.prod V, ∀ i, 0≤q.1.1 i := by
    exact measurePreserving_fst.quasiMeasurePreserving.ae (hValues.quasiMeasurePreserving.ae P.ae_nonnegative)
  have hDom : ∀ᵐ q ∂μ.prod V, X q-X' q≤G q := by
    filter_upwards [hVals] with q hq
    by_cases he : q.2∈E
    · have h₁ := π.rule.reward_le_maximum (f q).2.2 Finset.univ q.1.1 q.1.2.1
      have h₂ := π'.rule.reward_nonnegative (f' q).2.2 Finset.univ q.1.1 q.1.2.1 hq
      have hx : X q≤Y q.1 := h₁
      have hx' : 0≤X' q := h₂
      simp only [G, Set.indicator_of_mem he, Pi.one_apply, mul_one]
      exact (sub_le_self _ hx').trans hx
    · have hu : Function.Injective (fun i => uniformGridIndex N hN (q.2 i)) := by
        exact not_not.mp he
      have hAct (i : Fin n) :
          π.rule.action (f q).2.2 Finset.univ q.1.1 q.1.2.1 i =
          π'.rule.action (f' q).2.2 Finset.univ q.1.1 q.1.2.1 i := by
        let y := q.1.2.2.1
        let s := q.1.2.2.2
        let x := q.1.1 i
        let t := q.1.2.1 i
        let H := history Finset.univ q.1.1 q.1.2.1 t
        change (outerMarkedLearner V hm L id measurable_id).policy.decide (y,(q.2,s)) t i x H =
          (outerMarkedLearner V hm L mark hmMark).policy.decide (y,(q.2,s)) t i x H
        rw [outerMarkedLearner_decide,outerMarkedLearner_decide]
        exact (outerPolicy_unpack_rounding hn hm hN L y s q.2 hu t i x H).symm
      have hEq : X q = X' q :=
        (π.rule.outcomes_eq_of_actions_eq π'.rule (f q).2.2 (f' q).2.2 Finset.univ q.1.1 q.1.2.1 hAct).1
      simp only [hEq, sub_self, G, Set.indicator_of_notMem he, mul_zero, le_rfl]
  have hBound := integral_mono_ae (hX.sub hX') hG hDom
  simp only [Pi.sub_apply] at hBound
  have hWeighted : (∫ q : Ω × OuterMarkArray n m ℝ, G q ∂μ.prod V) =
      (∫ q, Y q ∂μ)*V.real E := outerMarkCollision_weighted_expectation μ Y M N hN
  rw [integral_sub hX hX', hInt, hInt', hWeighted] at hBound
  have hBenchmark : (∫ q, Y q ∂μ) = P.expectedMaximum :=
    (measurePreserving_fst (μ := P.valuesLaw) (ν := U.prod (T.prod Q))).hasLaw.integral_comp
      Instance.measurable_maximum.aestronglyMeasurable
  rw [hBenchmark] at hBound
  calc
    _ ≤ P.expectedMaximum * V.real E := hBound
    _ ≤ P.expectedMaximum*(1/(2*(m : ℝ)^2)) :=
      mul_le_mul_of_nonneg_left (outerMarkCollision_probability M N m hN (by omega) hGrid)
        P.expectedMaximum_nonnegative
    _ = _ := by ring

end ProphetSecretary.Statistics.Calibration
