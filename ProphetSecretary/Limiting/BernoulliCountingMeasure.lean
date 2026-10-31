import ProphetSecretary.Limiting.MarkedBernoulliPoissonCoupling
import ProphetSecretary.Limiting.Campbell

/-!
# The observable law of one rare marked point

The zero- and one-point configuration mixture is exactly a zero counting
measure together with its unnormalized point intensity. This identifies the
rare configuration representation with thresholded ordinary offers.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal ENNReal
namespace ProphetSecretary.Limiting

lemma fiberLaw_zero_countingMeasure (μ : FiniteMeasure ℝ) :
    (fiberLaw μ 0).map countingMeasure = Measure.dirac (0 : Measure Point) := by
  rw [fiberLaw,Measure.map_map measurable_countingMeasure (measurable_configuration_mk 0)]
  have h : countingMeasure ∘ configurationMk 0 = fun _ : Fin 0 → Point => (0 : Measure Point) := by
    funext v
    simp [countingMeasure,configurationMk ]
  rw [h,Measure.map_const,measure_univ,one_smul]

lemma fiberLaw_one_countingMeasure (μ : FiniteMeasure ℝ) :
    (fiberLaw μ 1).map countingMeasure = (pointLaw μ).map Measure.dirac := by
  rw [fiberLaw,Measure.map_map measurable_countingMeasure (measurable_configuration_mk 1)]
  have h : countingMeasure ∘ configurationMk 1 = Measure.dirac ∘ (fun v : Fin 1 → Point => v 0) := by
    funext v
    simp [countingMeasure,configurationMk]
  rw [h]
  have he : (arrayLaw μ 1).map (fun v : Fin 1 → Point => v 0) = pointLaw μ :=
    (measurePreserving_eval (fun _ : Fin 1 => pointLaw μ) 0).map_eq
  calc
    _ = ((arrayLaw μ 1).map (fun v : Fin 1 → Point => v 0)).map Measure.dirac :=
      (Measure.map_map (μ := arrayLaw μ 1) Measure.measurable_dirac (measurable_pi_apply (0 : Fin 1))).symm
    _ = _ := congrArg (fun ν : Measure Point => ν.map Measure.dirac) he

lemma bernoulliConfiguration_countingMeasure_law (μ : FiniteMeasure ℝ) (p : unitInterval)
    (hRate : μ.mass=unitInterval.toNNReal p) :
    (bernoulliConfigurationLaw μ p).map countingMeasure =
      ENNReal.ofReal (1-(p:ℝ)) • Measure.dirac (0 : Measure Point) + (intensity μ).map Measure.dirac := by
  rw [bernoulliConfigurationLaw_eq,Measure.map_add _ _ measurable_countingMeasure,
    Measure.map_smul,Measure.map_smul,fiberLaw_zero_countingMeasure,fiberLaw_one_countingMeasure,
    intensity_eq_mass_smul_pointLaw,Measure.map_smul,hRate,add_comm]
  rw [← unitInterval.coe_toNNReal p,ENNReal.ofReal_coe_nnreal]

noncomputable def observedSingleton (S : Set Point) (q : Point) : Measure Point :=
  if q∈S then Measure.dirac q else 0

lemma measurable_observedSingleton {S : Set Point} (hS : MeasurableSet S) :
    Measurable (observedSingleton S) := Measurable.ite hS Measure.measurable_dirac measurable_const

lemma observedSingleton_law (ν : Measure Point) [IsProbabilityMeasure ν]
    (S : Set Point) (hS : MeasurableSet S) :
    ν.map (observedSingleton S) =
      (ν.restrict S).map Measure.dirac + ν (Sᶜ) • Measure.dirac (0 : Measure Point) := by
  have hm := measurable_observedSingleton hS
  have hSplit := Measure.restrict_add_restrict_compl (μ := ν) hS
  calc
    _ = (ν.restrict S + ν.restrict Sᶜ).map (observedSingleton S) := by rw [hSplit]
    _ = (ν.restrict S).map (observedSingleton S) + (ν.restrict Sᶜ).map (observedSingleton S) :=
      Measure.map_add _ _ hm
    _ = _ := by
      congr 1
      · apply Measure.map_congr
        filter_upwards [ae_restrict_mem hS] with q hq
        exact if_pos hq
      · have he : observedSingleton S =ᵐ[ν.restrict Sᶜ] fun _ => (0 : Measure Point) := by
          filter_upwards [ae_restrict_mem hS.compl] with q hq
          exact if_neg hq
        rw [Measure.map_congr he,Measure.map_const,Measure.restrict_apply_univ]
end ProphetSecretary.Limiting
