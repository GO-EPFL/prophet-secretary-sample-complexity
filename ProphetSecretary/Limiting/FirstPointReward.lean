import ProphetSecretary.Limiting.FirstPointTime
import ProphetSecretary.Probability.FiniteKernelIntegral

/-!
# A measurable reward functional of a finite accepted-point measure

Actual configurations have one selected point at their first time almost
surely. The functional is totalized on other finite measures, and its equality
with an executed reward is justified by the singleton first-slice lemma.
-/

open MeasureTheory Set
open scoped Classical ENNReal

namespace ProphetSecretary.Limiting.FirstPoint

noncomputable def firstMarkIntegral (μ : FiniteMeasure Point) : ℝ≥0∞ :=
  ∫⁻ p, if p.1 = time (μ : Measure Point) then ENNReal.ofReal p.2 else 0 ∂(μ : Measure Point)

lemma measurable_firstMarkIntegral : Measurable firstMarkIntegral := by
  unfold firstMarkIntegral
  apply ProphetSecretary.Probability.measurable_lintegral_finiteFamily
    (μ := fun μ : FiniteMeasure Point => μ)
    (f := fun q : FiniteMeasure Point × Point => if q.2.1 = time (q.1 : Measure Point) then ENNReal.ofReal q.2.2 else 0) measurable_id
  have ht : Measurable (fun q : FiniteMeasure Point × Point => time (q.1 : Measure Point)) :=
    measurable_time.comp (measurable_subtype_coe.comp measurable_fst)
  have heq : MeasurableSet {q : FiniteMeasure Point × Point | q.2.1 = time (q.1 : Measure Point)} :=
    measurableSet_eq_fun (measurable_fst.comp measurable_snd) ht
  exact Measurable.ite heq (measurable_snd.comp measurable_snd).ennreal_ofReal measurable_const

noncomputable def reward (a : ℝ) (μ : FiniteMeasure Point) : ℝ :=
  if (μ : Measure Point) univ = 0 then a else (firstMarkIntegral μ).toReal

lemma measurable_reward (a : ℝ) : Measurable (reward a) := by
  have hm : Measurable (fun μ : FiniteMeasure Point => (μ : Measure Point) univ) :=
    (Measure.measurable_coe MeasurableSet.univ).comp measurable_subtype_coe
  exact Measurable.ite (measurableSet_eq_fun hm measurable_const) measurable_const
    measurable_firstMarkIntegral.ennreal_toReal

lemma reward_of_empty (a : ℝ) (μ : FiniteMeasure Point) (hzero : (μ : Measure Point) univ = 0) :
    reward a μ = a := by rw [reward,if_pos hzero]

lemma reward_of_firstSlice (a : ℝ) (μ : FiniteMeasure Point) {x : ℝ} (hx : 0 ≤ x)
    (hne : (μ : Measure Point) univ ≠ 0)
    (hslice : (μ : Measure Point).restrict {p : Point | p.1 = time (μ : Measure Point)} =
      Measure.dirac (time (μ : Measure Point),x)) : reward a μ = x := by
  have hS : MeasurableSet {p : Point | p.1 = time (μ : Measure Point)} :=
    measurableSet_eq_fun measurable_fst measurable_const
  have he : (fun p : Point => if p.1 = time (μ : Measure Point) then ENNReal.ofReal p.2 else 0) =
      {p : Point | p.1 = time (μ : Measure Point)}.indicator (fun p => ENNReal.ofReal p.2) := by
    funext p
    rfl
  rw [reward,if_neg hne,firstMarkIntegral,he,lintegral_indicator hS,hslice,lintegral_dirac]
  exact ENNReal.toReal_ofReal hx

end ProphetSecretary.Limiting.FirstPoint
