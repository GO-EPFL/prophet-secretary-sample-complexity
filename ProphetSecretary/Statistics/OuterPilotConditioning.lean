import ProphetSecretary.Statistics.OuterPilotSamples
import ProphetSecretary.Probability.ProductConditioning

/-!
# Conditional confidence of the actual independent cap-pilot block

The preceding cutoff may be any measurable function of independent outer data.
The q fresh raw samples and free tags have their constructed product law. Thus
the source confidence event has conditional probability at least 1−1/m given
the cutoff itself, with no conditional-independence interface assumed.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n : ℕ}

abbrev OuterPilotInputs (n m : ℕ) := Reservoir n (outerPilotRounds m) × (Fin (outerPilotRounds m) → Fin n → ℝ)

noncomputable def outerPilotInputsLaw (P : Instance n) (m : ℕ) : Measure (OuterPilotInputs n m) :=
  (P.reservoirLaw (outerPilotRounds m)).prod (outerTagRowsLaw n (outerPilotRounds m))

instance outerPilotInputsLaw_probability (P : Instance n) (m : ℕ) : IsProbabilityMeasure (outerPilotInputsLaw P m) := by
  unfold outerPilotInputsLaw
  infer_instance

noncomputable def outerPilotTaggedGood (P : Instance n) (m : ℕ) (hm : 1≤m) :
    Set ((ℝ × ℝ) × (Fin (outerPilotRounds m) → Fin n → ℝ × ℝ)) :=
  {p | retainedPilotSamples p.1 p.2∈numericalPilotSuccess (P.retainedMaximumLaw p.1)
    (outerPilotRank m) (outerPilotRank_pos hm)}

lemma measurableSet_outerPilotTaggedGood (P : Instance n) (m : ℕ) (hm : 1≤m) :
    MeasurableSet (outerPilotTaggedGood P m hm) := by
  let A := (ℝ × ℝ) × (Fin (outerPilotRounds m) → Fin n → ℝ × ℝ)
  have hB : Measurable (fun p : A => numericalPilotOrder (outerPilotRank m) (outerPilotRank_pos hm)
      (retainedPilotSamples p.1 p.2)) :=
    (measurable_numericalPilotOrder _ _).comp (measurable_retainedPilotSamples (n:=n) (q:=outerPilotRounds m))
  have hInput : Measurable (fun p : A => (p.1,numericalPilotOrder (outerPilotRank m) (outerPilotRank_pos hm)
      (retainedPilotSamples p.1 p.2))) := measurable_fst.prodMk hB
  have hStrict := P.measurable_retainedMaximumLaw_Ioi.comp hInput
  have hClosed := P.measurable_retainedMaximumLaw_Ici.comp hInput
  exact (measurableSet_le hStrict measurable_const).inter (measurableSet_le measurable_const hClosed)

noncomputable def outerPilotRawIndicator (P : Instance n) (m : ℕ) (hm : 1≤m)
    {D : Type*} (T : D → ℝ × ℝ) (p : D × OuterPilotInputs n m) : ℝ :=
  (outerPilotTaggedGood P m hm).indicator (fun _ => 1) (T p.1,taggedTrainingRows p.2.1 p.2.2)

lemma outerPilotRawIndicator_eq (P : Instance n) (m : ℕ) (hm : 1≤m)
    {D : Type*} (T : D → ℝ × ℝ) (p : D × OuterPilotInputs n m) :
    outerPilotRawIndicator P m hm T p=
      if (P.retainedMaximumLaw (T p.1)).real (Ioi (outerPilotValue m hm (T p.1) p.2))≤3/1000 ∧
        1/1000≤(P.retainedMaximumLaw (T p.1)).real (Ici (outerPilotValue m hm (T p.1) p.2)) then 1 else 0 := by
  have hEq : (T p.1,taggedTrainingRows p.2.1 p.2.2)∈outerPilotTaggedGood P m hm ↔
      ((P.retainedMaximumLaw (T p.1)).real (Ioi (outerPilotValue m hm (T p.1) p.2))≤3/1000 ∧
        1/1000≤(P.retainedMaximumLaw (T p.1)).real (Ici (outerPilotValue m hm (T p.1) p.2))) := Iff.rfl
  by_cases h : (T p.1,taggedTrainingRows p.2.1 p.2.2)∈outerPilotTaggedGood P m hm
  · simp only [outerPilotRawIndicator,Set.indicator_of_mem h,if_pos (hEq.mp h)]
  · simp only [outerPilotRawIndicator,Set.indicator_of_notMem h,if_neg (fun hR => h (hEq.mpr hR))]

/-- The probability estimate in `upouter:cap-pilot`, conditional on the actual
preceding cutoff. Fresh pilot samples are explicitly independent raw samples. -/
theorem outerPilot_conditional_success (P : Instance n) (m : ℕ) (hm : 1≤m)
    {D : Type*} [MeasurableSpace D] (μ : Measure D) [IsProbabilityMeasure μ]
    {T : D → ℝ × ℝ} (hT : Measurable T) :
    ∀ᵐ p ∂μ.prod (outerPilotInputsLaw P m),
      1-1/(m:ℝ)≤(μ.prod (outerPilotInputsLaw P m))[outerPilotRawIndicator P m hm T|
        MeasurableSpace.comap (fun p : D × OuterPilotInputs n m => T p.1) inferInstance] p := by
  let q := outerPilotRounds m
  let V := Fin q → Fin n → ℝ × ℝ
  let ν : Measure V := Measure.pi (fun _ : Fin q => P.taggedValuesLaw)
  let F : (ℝ × ℝ) × V → ℝ := (outerPilotTaggedGood P m hm).indicator (fun _ => 1)
  have hFm : Measurable F := measurable_const.indicator (measurableSet_outerPilotTaggedGood P m hm)
  haveI : IsProbabilityMeasure (μ.map T) := Measure.isProbabilityMeasure_map hT.aemeasurable
  have hFI : Integrable F ((μ.map T).prod ν) := by
    apply Integrable.of_bound hFm.aestronglyMeasurable 1
    exact Eventually.of_forall fun p => by
      by_cases h : p∈outerPilotTaggedGood P m hm
      · simp only [F,Set.indicator_of_mem h,norm_one,le_refl]
      · simp only [F,Set.indicator_of_notMem h,norm_zero,zero_le_one]
  have hTM : MeasurePreserving T μ (μ.map T) := ⟨hT,rfl⟩
  have hPair : MeasurePreserving (fun p : D × OuterPilotInputs n m => (T p.1,taggedTrainingRows p.2.1 p.2.2))
      (μ.prod (outerPilotInputsLaw P m)) ((μ.map T).prod ν) :=
    hTM.prod (taggedTrainingRows_measurePreserving P q)
  have hCE := ProphetSecretary.Probability.condExp_productPair (μ.map T) ν
    (μ.prod (outerPilotInputsLaw P m)) hPair hFm hFI
  have hIntegral (t : ℝ × ℝ) : 1-1/(m:ℝ)≤∫ a, F (t,a) ∂ν := by
    let S : Set (Fin q → ℝ) := {a |
      (P.retainedMaximumLaw t).real (Ioi (numericalPilotOrder (outerPilotRank m) (outerPilotRank_pos hm) a))≤3/1000 ∧
      1/1000≤(P.retainedMaximumLaw t).real (Ici (numericalPilotOrder (outerPilotRank m) (outerPilotRank_pos hm) a))}
    have hS : MeasurableSet S := measurableSet_numericalPilotSuccess (P.retainedMaximumLaw t) (outerPilotRank m) (outerPilotRank_pos hm)
    have hSamples := retainedPilotSamples_measurePreserving P q t
    have hTest : Measurable (S.indicator (fun _ => (1:ℝ))) := measurable_const.indicator hS
    have hMap := integral_map (μ:=ν) hSamples.measurable.aemeasurable hTest.aestronglyMeasurable
    rw [hSamples.map_eq] at hMap
    have hBound : 1-1/(m:ℝ)≤(Measure.pi (fun _ : Fin q => P.retainedMaximumLaw t)).real S :=
      outerPilot_success_probability (P.retainedMaximumLaw t) hm
    have hMass : (∫ a, S.indicator (fun _ => (1:ℝ)) a ∂Measure.pi (fun _ : Fin q => P.retainedMaximumLaw t))=
        (Measure.pi (fun _ : Fin q => P.retainedMaximumLaw t)).real S := by
      simpa only [smul_eq_mul,mul_one] using integral_indicator_const (μ:=Measure.pi (fun _ : Fin q => P.retainedMaximumLaw t)) (1:ℝ) hS
    rw [hMass] at hMap
    apply hBound.trans_eq
    apply hMap.trans
    apply integral_congr_ae
    exact Eventually.of_forall fun a => by
      have hGood : retainedPilotSamples t a∈S ↔ (t,a)∈outerPilotTaggedGood P m hm := Iff.rfl
      by_cases h : retainedPilotSamples t a∈S
      · simp only [Set.indicator_of_mem h,F,Set.indicator_of_mem (hGood.mp h)]
      · simp only [Set.indicator_of_notMem h,F,Set.indicator_of_notMem (fun hR => h (hGood.mpr hR))]
  have hFun : (fun p : D × OuterPilotInputs n m => F (T p.1,taggedTrainingRows p.2.1 p.2.2))=outerPilotRawIndicator P m hm T := rfl
  have hConv := condExp_congr_ae (μ:=μ.prod (outerPilotInputsLaw P m))
    (m:=MeasurableSpace.comap (fun p : D × OuterPilotInputs n m => T p.1) inferInstance)
    (Eventually.of_forall fun p => congrFun hFun.symm p)
  have hCE' := hConv.trans hCE
  filter_upwards [hCE'] with p hp
  rw [hp]
  exact hIntegral (T p.1)

end ProphetSecretary.Statistics
