import ProphetSecretary.Limiting.CountableReachValue
import ProphetSecretary.Limiting.CountableCapExcess

/-!
# Expected excess on a reached individual

The actual pending-clock pair is independent of the candidate value by the
proved infinite-product erasure argument. Its event agrees almost surely with
actual reach for an admissible policy. Integrating the bounded cap excess
therefore gives q_i times that individual's expected excess.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

lemma CountableRule.reachedCapExcess_integrable_and_integral (π : CountableRule Seed) (hπ : π.IsMeasurable)
    (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν] (hAdm : π.Admissible B ν)
    (i : ℕ) (K : ℝ≥0) :
    Integrable (fun v : CompleteWorld Seed => if v.2.2.1 i≤π.realizedDuration v then Model.tailValue K (v.2.1 i) else 0) (B.completeWorldLaw ν) ∧
    (∫ v : CompleteWorld Seed, (if v.2.2.1 i≤π.realizedDuration v then Model.tailValue K (v.2.1 i) else 0) ∂B.completeWorldLaw ν)=
      π.individualReachProbability B ν i*B.individualCapExcess K i := by
  let μ := B.completeWorldLaw ν
  let A : CompleteWorld Seed → ℝ := fun v => if v.2.2.1 i≤π.pendingIndividualTime i v then 1 else 0
  have hAm : Measurable A := measurable_const.ite
    (measurableSet_le ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd)))
      (π.measurable_pendingIndividualTime hπ i)) measurable_const
  have hAI : Integrable A μ := Integrable.of_bound hAm.aestronglyMeasurable 1 (Eventually.of_forall fun v => by
    dsimp only [A]
    split_ifs <;> norm_num)
  have hXi : MeasurePreserving (fun v : CompleteWorld Seed => v.2.1 i) μ (B.individuals i : Measure ℝ) :=
    (B.individualValue_measurePreserving i).comp (measurePreserving_fst.comp measurePreserving_snd)
  have hTailI := hXi.integrable_comp_of_integrable (B.individualCapExcess_integrable K i)
  have hInd : IndepFun A (fun v : CompleteWorld Seed => Model.tailValue K (v.2.1 i)) μ := by
    have hF : Measurable (fun z : ℝ × ℝ => if z.2≤z.1 then (1:ℝ) else 0) :=
      measurable_const.ite (measurableSet_le measurable_snd measurable_fst) measurable_const
    have h := (π.pending_clock_value_independent hπ B ν i).comp hF (Model.measurable_tailValue K)
    simpa only [Function.comp_def,A] using h
  have hProdI := hInd.integrable_mul hAI hTailI
  have hE := π.reach_event_eq_pending_ae B ν hAdm i
  have hEq : (fun v : CompleteWorld Seed => if v.2.2.1 i≤π.realizedDuration v then Model.tailValue K (v.2.1 i) else 0)=ᵐ[μ]
      (fun v => A v*Model.tailValue K (v.2.1 i)) := by
    filter_upwards [hE] with v hv
    change (v.2.2.1 i≤π.realizedDuration v)=(v.2.2.1 i≤π.pendingIndividualTime i v) at hv
    by_cases h : v.2.2.1 i≤π.pendingIndividualTime i v
    · have hActual : v.2.2.1 i≤π.realizedDuration v := Eq.mpr hv h
      simp only [A,if_pos h,if_pos hActual,one_mul]
    · have hActual : ¬v.2.2.1 i≤π.realizedDuration v := fun hR => h (Eq.mp hv hR)
      simp only [A,if_neg h,if_neg hActual,zero_mul]
  have hMeanA : (∫ v, A v ∂μ)=π.individualReachProbability B ν i := by
    have hS : MeasurableSet {v : CompleteWorld Seed | v.2.2.1 i≤π.pendingIndividualTime i v} :=
      measurableSet_le ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd)))
        (π.measurable_pendingIndividualTime hπ i)
    have hI := integral_indicator_const (μ:=μ) (1:ℝ) hS
    have hMass : μ.real {v : CompleteWorld Seed | v.2.2.1 i≤π.pendingIndividualTime i v}=π.individualReachProbability B ν i :=
      (measureReal_congr hE).symm
    have hMean : (∫ v, A v ∂μ)=μ.real {v : CompleteWorld Seed | v.2.2.1 i≤π.pendingIndividualTime i v} := by
      simpa only [A,Set.indicator_apply,Set.mem_setOf_eq,smul_eq_mul,mul_one] using hI
    exact hMean.trans hMass
  have hMeanTail : (∫ v : CompleteWorld Seed, Model.tailValue K (v.2.1 i) ∂μ)=B.individualCapExcess K i := by
    have h := integral_map (μ:=μ) hXi.measurable.aemeasurable (Model.measurable_tailValue K).aestronglyMeasurable
    rw [hXi.map_eq] at h
    exact h.symm
  refine ⟨hProdI.congr hEq.symm,?_⟩
  rw [integral_congr_ae hEq,hInd.integral_fun_mul_eq_mul_integral hAI.aestronglyMeasurable hTailI.aestronglyMeasurable,hMeanA,hMeanTail]

end ProphetSecretary.Limiting.CountableInstance
