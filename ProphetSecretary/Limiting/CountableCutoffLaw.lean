import ProphetSecretary.Limiting.CutoffCountJointLaw
import ProphetSecretary.Probability.RandomMeasureLaw

/-!
# Actual anonymous configuration law above a strict cutoff

The entire restricted random counting measure has the finite-intensity Poisson
configuration law. Equality of finite evaluation vectors is upgraded using
the measurable structure on measures. No point labels or ordering are added
to an online observation.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal

namespace ProphetSecretary.Limiting

lemma measurable_cutoffCountingMeasure (b : ℝ) :
    Measurable (fun ω : CountableInstance.BandConfigurations =>
      (bandCountingMeasure ω).restrict (univ ×ˢ Ioi b)) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  have he : (fun ω : CountableInstance.BandConfigurations =>
      ((bandCountingMeasure ω).restrict (univ ×ˢ Ioi b)) S) =
      fun ω => bandCountingMeasure ω (S ∩ (univ ×ˢ Ioi b)) := by
    funext ω
    exact Measure.restrict_apply hS
  rw [he]
  exact (Measure.measurable_coe (hS.inter (MeasurableSet.univ.prod measurableSet_Ioi))).comp
    measurable_bandCountingMeasure

namespace CountableInstance

variable (B : CountableInstance)

/-- Actual cutoff-law transfer for all anonymous-history measurable
functionals, including policy execution functionals when separately proved
to depend only on these observations. -/
theorem cutoff_countingMeasure_law {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    B.bandConfigurationsLaw.map (fun ω => (bandCountingMeasure ω).restrict (univ ×ˢ Ioi b)) =
      (configurationLaw (B.intensityAbove b hb)).map countingMeasure := by
  let f := fun ω : BandConfigurations => (bandCountingMeasure ω).restrict (univ ×ˢ Ioi b)
  have hf : Measurable f := measurable_cutoffCountingMeasure b
  have hUpper : MeasurableSet (univ ×ˢ Ioi b : Set Point) := MeasurableSet.univ.prod measurableSet_Ioi
  have hFinite : MeasurableSet {m : Measure Point | m univ < ⊤} :=
    measurableSet_lt (Measure.measurable_coe MeasurableSet.univ) measurable_const
  have hSourceFinite : ∀ᵐ m ∂B.bandConfigurationsLaw.map f, m univ < ⊤ := by
    apply (ae_map_iff hf.aemeasurable hFinite).mpr
    filter_upwards [B.bandCountingMeasure_region_finite_ae hb hUpper (fun _ h => h)] with ω hω
    simpa only [f,Measure.restrict_apply_univ] using hω
  have hTargetFinite : ∀ᵐ m ∂(configurationLaw (B.intensityAbove b hb)).map countingMeasure, m univ < ⊤ := by
    apply (ae_map_iff measurable_countingMeasure.aemeasurable hFinite).mpr
    exact Filter.Eventually.of_forall (fun ω => by rw [countingMeasure_univ]; exact ENNReal.natCast_lt_top _)
  apply ProphetSecretary.Probability.randomMeasure_law_eq_of_finite_real_evaluations
    (B.bandConfigurationsLaw.map f) ((configurationLaw (B.intensityAbove b hb)).map countingMeasure)
    hSourceFinite hTargetFinite
  intro I
  have hEval : Measurable (fun m : Measure Point => fun S : I => m.real S.1.1) :=
    measurable_pi_lambda _ (fun S => (Measure.measurable_coe S.1.2).ennreal_toReal)
  rw [Measure.map_map hEval hf,Measure.map_map hEval measurable_countingMeasure]
  have hSource : (fun ω => fun S : I => (f ω).real S.1.1) =ᵐ[B.bandConfigurationsLaw]
      (fun ω => fun S : I => (bandPointCount (S.1.1 ∩ (univ ×ˢ Ioi b)) ω : ℝ)) := by
    filter_upwards [ae_all_iff.mpr (fun S : I => B.bandCountingMeasure_eq_natCount_ae hb
      (S.1.2.inter hUpper) (fun _ h => h.2))] with ω hω
    funext S
    change (((bandCountingMeasure ω).restrict (univ ×ˢ Ioi b)) S.1.1).toReal = _
    rw [Measure.restrict_apply S.1.2,hω S,ENNReal.toReal_natCast]
  have hTarget : (fun ω => fun S : I => (countingMeasure ω).real S.1.1) =
      (fun ω => fun S : I => (pointCount S.1.1 ω : ℝ)) := by
    funext ω S
    change (countingMeasure ω S.1.1).toReal = _
    rw [countingMeasure_eq_pointCount S.1.2,ENNReal.toReal_natCast]
  change B.bandConfigurationsLaw.map (fun ω => fun S : I => (f ω).real S.1.1) =
    (configurationLaw (B.intensityAbove b hb)).map (fun ω => fun S : I => (countingMeasure ω).real S.1.1)
  rw [hTarget]
  exact (Measure.map_congr hSource).trans
    (B.cutoff_counts_real_joint_law hb (fun S : I => S.1.1) (fun S => S.1.2))

end CountableInstance
end ProphetSecretary.Limiting
