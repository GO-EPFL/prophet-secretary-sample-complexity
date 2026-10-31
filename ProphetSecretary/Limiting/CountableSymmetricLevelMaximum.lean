import ProphetSecretary.Limiting.CountableSymmetricLevelPath
import ProphetSecretary.Limiting.CountableIndividualPayloadMaximum
import ProphetSecretary.Limiting.CountableAuxiliarySplit
import ProphetSecretary.Probability.FairSingleMaximumGain

/-!
# Actual prophet gain from a symmetric individual perturbation

The independent fair tag is integrated on the constructed full product law.
For every old world it gives nonnegative expected maximum gain; on an
individual/competing tie above the fixed positive level the gain is h/2.
The resulting lower bound retains the actual tie-event probability and the
explicit perturbation radius.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Probability

noncomputable def levelMaximumKernel (B : CountableInstance) (i : ℕ) (b h : ℝ)
    (z : CompleteWorld Unit × (Fin 1 → Bool)) : ℝ :=
  max (z.1.2.1 i+h*(variableSign z.2 0*positiveLevelIndicator b (z.1.2.1 i))) (B.competingMaximum i z.1)

lemma measurable_levelMaximumKernel (B : CountableInstance) (i : ℕ) (b h : ℝ) :
    Measurable (B.levelMaximumKernel i b h) := by
  have hXi : Measurable (fun v : CompleteWorld Unit => v.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hX := hXi.comp (measurable_fst : Measurable (Prod.fst : CompleteWorld Unit × (Fin 1 → Bool) → CompleteWorld Unit))
  have hSign := (measurable_of_countable (fun s : Fin 1 → Bool => variableSign s 0)).comp
    (measurable_snd : Measurable (Prod.snd : CompleteWorld Unit × (Fin 1 → Bool) → (Fin 1 → Bool)))
  exact (hX.add ((hSign.mul ((measurable_positiveLevelIndicator b).comp hX)).const_mul h)).max
    ((B.measurable_competingMaximum i).comp measurable_fst)

lemma integrable_levelMaximumKernel (B : CountableInstance) (i : ℕ) (b h : ℝ) (hh : 0≤h) :
    Integrable (B.levelMaximumKernel i b h) ((B.completeWorldLaw (Measure.dirac ())).prod (fairSigns 1)) := by
  have hXi : MeasurePreserving (fun v : CompleteWorld Unit => v.2.1 i)
      (B.completeWorldLaw (Measure.dirac ())) (B.individuals i : Measure ℝ) :=
    (B.individualValue_measurePreserving i).comp (measurePreserving_fst.comp measurePreserving_snd)
  have hGood : ∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()),
      ∀ s : Fin 1 → Bool, B.levelMaximumKernel i b h (v,s) ∈ Icc (0 : ℝ) ((B.cap : ℝ)+h) := by
    filter_upwards [hXi.quasiMeasurePreserving.ae (B.individual_supported i),B.competingMaximum_bounded_ae i (Measure.dirac ())]
      with v hx hy s
    have hAmp : variableSign s 0*positiveLevelIndicator b (v.2.1 i) ≤ 1 := by
      apply (le_abs_self _).trans
      rw [abs_mul,abs_variableSign,one_mul]
      exact positiveLevelIndicator_abs_le_one _ _
    have hPert : h*(variableSign s 0*positiveLevelIndicator b (v.2.1 i)) ≤ h := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hAmp hh
    exact ⟨hy.1.trans (le_max_right _ _),max_le (add_le_add hx.2 hPert)
      (hy.2.trans (le_add_of_nonneg_right hh))⟩
  apply Integrable.of_bound (B.measurable_levelMaximumKernel i b h).aestronglyMeasurable ((B.cap : ℝ)+h)
  filter_upwards [(Measure.quasiMeasurePreserving_fst
    (μ := B.completeWorldLaw (Measure.dirac ())) (ν := fairSigns 1)).ae hGood] with z hz
  rw [Real.norm_eq_abs,abs_of_nonneg (hz z.2).1]
  exact (hz z.2).2

theorem symmetricLevelIndividualPath_expectedMaximum_eq (B : CountableInstance) (i : ℕ)
    (b : ℝ) (hb : 0<b) (h : ℝ) (hh : 0≤h) (hSmall : h≤ individualValueRadius 1 b) :
    (B.symmetricLevelIndividualPath i b hb h).expectedMaximum=
      ∫ v : CompleteWorld Unit, (∫ s, B.levelMaximumKernel i b h (v,s) ∂fairSigns 1)
        ∂B.completeWorldLaw (Measure.dirac ()) := by
  have hNear : |h|≤ individualValueRadius 1 b := by simpa only [abs_of_nonneg hh] using hSmall
  have hPayload := B.individualPayloadValuePath_expectedMaximum_eq i (fairSigns 1)
    (symmetricIndividualAmplitude (positiveLevelIndicator b))
    (measurable_symmetricIndividualAmplitude (measurable_positiveLevelIndicator b))
    (by norm_num : (0 : ℝ)≤1) hb
    (symmetricIndividualAmplitude_bound (positiveLevelIndicator_abs_le_one b))
    (symmetricIndividualAmplitude_vanish (positiveLevelIndicator_vanish b)) h
  have hSplit := B.splitCompleteAuxiliary_measurePreserving (Measure.dirac ()) (fairSigns 1)
  have hSplitMean := hSplit.hasLaw.integral_comp (B.measurable_levelMaximumKernel i b h).aestronglyMeasurable
  calc
    _ = ∫ v : CompleteWorld (Unit × (Fin 1 → Bool)), B.levelMaximumKernel i b h (splitCompleteAuxiliary v)
        ∂B.completeWorldLaw ((Measure.dirac ()).prod (fairSigns 1)) := by
      refine hPayload.trans (integral_congr_ae (Eventually.of_forall (fun v => ?_)))
      change max (payloadValueDisplay (symmetricIndividualAmplitude (positiveLevelIndicator b)) 1 b h
        (v.2.1 i,v.2.2.2.2)) (B.competingMaximum i v)=
          B.levelMaximumKernel i b h (splitCompleteAuxiliary v)
      rw [payloadValueDisplay,if_pos hNear]
      rfl
    _ = ∫ z, B.levelMaximumKernel i b h z ∂(B.completeWorldLaw (Measure.dirac ())).prod (fairSigns 1) := hSplitMean
    _ = _ := integral_prod _ (B.integrable_levelMaximumKernel i b h hh)

noncomputable def individualCompetingTieAbove (B : CountableInstance) (i : ℕ) (b : ℝ) : Set (CompleteWorld Unit) :=
  {v | v.2.1 i=B.competingMaximum i v ∧ b≤v.2.1 i}

lemma measurableSet_individualCompetingTieAbove (B : CountableInstance) (i : ℕ) (b : ℝ) :
    MeasurableSet (B.individualCompetingTieAbove i b) := by
  have hXi : Measurable (fun v : CompleteWorld Unit => v.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  exact (measurableSet_eq_fun hXi (B.measurable_competingMaximum i)).inter (measurableSet_le measurable_const hXi)

theorem symmetricLevelIndividualPath_maximum_gain (B : CountableInstance) (i : ℕ)
    (b : ℝ) (hb : 0<b) (h : ℝ) (hh : 0≤h) (hSmall : h≤ individualValueRadius 1 b) :
    B.expectedMaximum+(B.completeWorldLaw (Measure.dirac ())).real (B.individualCompetingTieAbove i b)*(h/2) ≤
      (B.symmetricLevelIndividualPath i b hb h).expectedMaximum := by
  let μ := B.completeWorldLaw (Measure.dirac ())
  let E := B.individualCompetingTieAbove i b
  have hE : MeasurableSet E := B.measurableSet_individualCompetingTieAbove i b
  have hBaseInt : Integrable (fun v : CompleteWorld Unit => B.maximum (v.1,v.2.1)) μ :=
    (B.value_projection_measurePreserving (Measure.dirac ())).integrable_comp_of_integrable B.integrable_maximum
  have hIndicatorInt := (integrable_const (h/2) : Integrable (fun _ : CompleteWorld Unit => h/2) μ).indicator hE
  have hMeanInt := (B.integrable_levelMaximumKernel i b h hh).integral_prod_left
  have hPoint : (fun v : CompleteWorld Unit => B.maximum (v.1,v.2.1)+E.indicator (fun _ => h/2) v) ≤ᵐ[μ]
      (fun v => ∫ s, B.levelMaximumKernel i b h (v,s) ∂fairSigns 1) := by
    filter_upwards [B.maximum_eq_max_competing_ae (Measure.dirac ()) i] with v hv
    rw [hv]
    simpa only [E,individualCompetingTieAbove,Set.indicator_apply,Set.mem_setOf_eq,
      levelMaximumKernel,positiveLevelIndicator] using
      mean_single_signed_maximum_threshold_gain b (v.2.1 i) (B.competingMaximum i v) h hh
  have hBound := integral_mono_ae (hBaseInt.add hIndicatorInt) hMeanInt hPoint
  have hValue := (B.value_projection_measurePreserving (Measure.dirac ())).hasLaw.integral_comp B.measurable_maximum.aestronglyMeasurable
  change (∫ v : CompleteWorld Unit, B.maximum (v.1,v.2.1) ∂μ)=B.expectedMaximum at hValue
  change (∫ v : CompleteWorld Unit, B.maximum (v.1,v.2.1)+E.indicator (fun _ => h/2) v ∂μ) ≤ _ at hBound
  rw [integral_add hBaseInt hIndicatorInt,hValue,integral_indicator_const _ hE,smul_eq_mul] at hBound
  exact hBound.trans_eq (B.symmetricLevelIndividualPath_expectedMaximum_eq i b hb h hh hSmall).symm

end ProphetSecretary.Limiting.CountableInstance
