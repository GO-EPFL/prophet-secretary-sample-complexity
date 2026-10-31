import ProphetSecretary.Statistics.OuterCutoffProgram
import ProphetSecretary.Model.OuterTaggedCDF
import ProphetSecretary.Probability.MinimumUniform

/-!
# The distribution of the actual cutoff score

Each independent tagged training round has a uniform population CDF score.
Monotonicity turns the minimum tagged maximum into the minimum of these scores.
Thus the Beta(1,m) calculation applies to the actual transcript-based cutoff.
Paper correspondence: `upouter:beta`.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability
variable {n : ℕ}

noncomputable def outerCutoffDataLaw (P : Instance n) (m : ℕ) :
    Measure (Reservoir n m × (Fin m → Fin n → ℝ)) :=
  (P.reservoirLaw m).prod (outerTagRowsLaw n m)

instance outerCutoffDataLaw_probability (P : Instance n) (m : ℕ) :
    IsProbabilityMeasure (outerCutoffDataLaw P m) := by
  unfold outerCutoffDataLaw
  infer_instance

noncomputable def outerCutoffRoundScores (P : Instance n) (hn : 0<n) (m : ℕ)
    (p : Reservoir n m × (Fin m → Fin n → ℝ)) : Fin m → ℝ :=
  fun r => P.taggedVoidProbability (ofLex (outerTaggedMaximum hn (taggedTrainingRows p.1 p.2 r)))

lemma outerCutoffRoundScores_measurePreserving (P : Instance n) (hn : 0<n) (m : ℕ) :
    MeasurePreserving (outerCutoffRoundScores P hn m) (outerCutoffDataLaw P m) (Instance.clocksLaw m) := by
  have hOne := P.outerTaggedMaximum_score_measurePreserving hn
  have hAll : MeasurePreserving
      (fun a : Fin m → Fin n → ℝ × ℝ => fun r => P.taggedVoidProbability (ofLex (outerTaggedMaximum hn (a r))))
      (Measure.pi (fun _ : Fin m => P.taggedValuesLaw)) (Instance.clocksLaw m) := by
    refine ⟨measurable_pi_lambda _ (fun r => hOne.measurable.comp (measurable_pi_apply r)),?_⟩
    rw [Measure.pi_map_pi (fun _ => hOne.measurable.aemeasurable)]
    simp only [hOne.map_eq,Instance.clocksLaw]
  exact hAll.comp (taggedTrainingRows_measurePreserving P m)

lemma outerCutoff_score_eq_minimum (P : Instance n) (hn : 0<n) (m : ℕ) (hm : 1≤m)
    (p : Reservoir n m × (Fin m → Fin n → ℝ)) :
    P.taggedVoidProbability (outerCutoff m hm p)=uniformMinimum m hm (outerCutoffRoundScores P hn m p) := by
  exact outerCutoff_score_eq_inf P hn m hm _

lemma measurable_outerCutoff_score (P : Instance n) (hn : 0<n) (m : ℕ) (hm : 1≤m) :
    Measurable (fun p : Reservoir n m × (Fin m → Fin n → ℝ) => P.taggedVoidProbability (outerCutoff m hm p)) := by
  have hEq : (fun p => P.taggedVoidProbability (outerCutoff m hm p))=
      (fun p => uniformMinimum m hm (outerCutoffRoundScores P hn m p)) :=
    funext (outerCutoff_score_eq_minimum P hn m hm)
  rw [hEq]
  exact (measurable_uniformMinimum m hm).comp (outerCutoffRoundScores_measurePreserving P hn m).measurable

/-- The strict Beta(1,m) CDF of the true score at the observable cutoff. -/
theorem outerCutoff_score_cdf (P : Instance n) (hn : 0<n) (m : ℕ) (hm : 1≤m)
    {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (outerCutoffDataLaw P m).real {p | P.taggedVoidProbability (outerCutoff m hm p)<t}=1-(1-t)^m := by
  have hMP := outerCutoffRoundScores_measurePreserving P hn m
  have hMeas : MeasurableSet {a : Fin m → ℝ | uniformMinimum m hm a<t} :=
    measurableSet_lt (measurable_uniformMinimum m hm) measurable_const
  have h := map_measureReal_apply (μ:=outerCutoffDataLaw P m) hMP.measurable hMeas
  rw [hMP.map_eq] at h
  have hEq : {p | P.taggedVoidProbability (outerCutoff m hm p)<t}=
      outerCutoffRoundScores P hn m ⁻¹' {a | uniformMinimum m hm a<t} := by
    ext p
    simp only [Set.mem_setOf_eq,Set.mem_preimage,outerCutoff_score_eq_minimum P hn m hm]
  rw [hEq,←h,uniformMinimum_cdf m hm ht]

lemma integral_outerCutoff_score (P : Instance n) (hn : 0<n) (m : ℕ) (hm : 1≤m) :
    (∫ p, P.taggedVoidProbability (outerCutoff m hm p) ∂outerCutoffDataLaw P m)=1/((m:ℝ)+1) := by
  have hMP := outerCutoffRoundScores_measurePreserving P hn m
  have h := integral_map (μ:=outerCutoffDataLaw P m) hMP.measurable.aemeasurable
    (measurable_uniformMinimum m hm).aestronglyMeasurable
  rw [hMP.map_eq] at h
  simp_rw [outerCutoff_score_eq_minimum P hn m hm]
  rw [←h,integral_uniformMinimum]

lemma outerCutoff_small_score_probability (P : Instance n) (hn : 0<n) (m : ℕ) (hm : 1≤m) :
    (outerCutoffDataLaw P m).real {p | P.taggedVoidProbability (outerCutoff m hm p)<1/(m:ℝ)^2}≤1/(m:ℝ) := by
  have hMP := outerCutoffRoundScores_measurePreserving P hn m
  have hMeas : MeasurableSet {a : Fin m → ℝ | uniformMinimum m hm a<1/(m:ℝ)^2} :=
    measurableSet_lt (measurable_uniformMinimum m hm) measurable_const
  have h := map_measureReal_apply (μ:=outerCutoffDataLaw P m) hMP.measurable hMeas
  rw [hMP.map_eq] at h
  have hEq : {p | P.taggedVoidProbability (outerCutoff m hm p)<1/(m:ℝ)^2}=
      outerCutoffRoundScores P hn m ⁻¹' {a | uniformMinimum m hm a<1/(m:ℝ)^2} := by
    ext p
    simp only [Set.mem_setOf_eq,Set.mem_preimage,outerCutoff_score_eq_minimum P hn m hm]
  rw [hEq,←h]
  exact uniformMinimum_small_probability m hm

end ProphetSecretary.Statistics
