import ProphetSecretary.Probability.BinaryPosterior

/-!
# The hidden sign and its observed data

A uniform hidden sign chooses one of two data laws. The sign itself is absent
from the data coordinate. The posterior testing identity derives the exact
averaging formula for data-dependent payoffs, including policies selected from
training data. Paper correspondence: the experiment in `thm:bayes`.
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace ProphetSecretary.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def binaryExperiment (μ ν : Measure Ω) : Measure (Bool × Ω) :=
  (1 / 2 : NNReal) • μ.map (Prod.mk true) + (1 / 2 : NNReal) • ν.map (Prod.mk false)

def binarySign (s : Bool) : ℝ := if s then 1 else -1

lemma measurable_binarySign : Measurable binarySign := measurable_of_finite _

instance binaryExperiment_probability (μ ν : Measure Ω) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (binaryExperiment μ ν) := by
  letI : IsProbabilityMeasure (μ.map (Prod.mk true)) :=
    Measure.isProbabilityMeasure_map measurable_prodMk_left.aemeasurable
  letI : IsProbabilityMeasure (ν.map (Prod.mk false)) :=
    Measure.isProbabilityMeasure_map measurable_prodMk_left.aemeasurable
  constructor
  norm_num [binaryExperiment, ENNReal.inv_two_add_inv_two]

lemma integral_binaryExperiment (μ ν : Measure Ω) {f : Bool × Ω → ℝ} (hf : Measurable f)
    (hμ : Integrable (fun x => f (true, x)) μ) (hν : Integrable (fun x => f (false, x)) ν) :
    (∫ z, f z ∂binaryExperiment μ ν) = (1 / 2 : ℝ) * (∫ x, f (true, x) ∂μ) +
      (1 / 2 : ℝ) * (∫ x, f (false, x) ∂ν) := by
  have hp : Integrable f (μ.map (Prod.mk true)) :=
    (integrable_map_measure hf.aestronglyMeasurable measurable_prodMk_left.aemeasurable).mpr hμ
  have hn : Integrable f (ν.map (Prod.mk false)) :=
    (integrable_map_measure hf.aestronglyMeasurable measurable_prodMk_left.aemeasurable).mpr hν
  rw [binaryExperiment, integral_add_measure hp.smul_measure_nnreal hn.smul_measure_nnreal,
    integral_smul_nnreal_measure, integral_smul_nnreal_measure,
    integral_map measurable_prodMk_left.aemeasurable hf.aestronglyMeasurable,
    integral_map measurable_prodMk_left.aemeasurable hf.aestronglyMeasurable]
  rfl

/-- The observation marginal is the equal mixture. This projection reveals no
hidden sign and is independent of how a policy is chosen from the observed data. -/
lemma binaryExperiment_observation_measurePreserving (μ ν : Measure Ω) :
    MeasurePreserving (Prod.snd : Bool × Ω → Ω) (binaryExperiment μ ν) (binaryMixture μ ν) := by
  refine ⟨measurable_snd, ?_⟩
  rw [binaryExperiment, Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_smul,
    Measure.map_map measurable_snd measurable_prodMk_left,
    Measure.map_map measurable_snd measurable_prodMk_left]
  simp only [Function.comp_def, Measure.map_id']
  rfl

theorem binarySign_mean_zero (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    (∫ z : Bool × Ω, binarySign z.1 ∂binaryExperiment μ ν) = 0 := by
  have hf : Measurable (fun z : Bool × Ω => binarySign z.1) := measurable_binarySign.comp measurable_fst
  rw [integral_binaryExperiment μ ν hf
    (integrable_const _) (integrable_const _)]
  norm_num [binarySign]

/-- Actual posterior averaging for arbitrary integrable data-dependent payoffs.
The hidden sign is used only in the analytical target, not by the data statistic. -/
theorem binaryExperiment_affine_payoff {μ ν : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμν : μ ≪ ν) {a b : Ω → ℝ}
    (ha : Measurable a) (hb : Measurable b)
    (haμ : Integrable a μ) (haν : Integrable a ν) (hbμ : Integrable b μ) (hbν : Integrable b ν) :
    (∫ z : Bool × Ω, (a z.2 + binarySign z.1 * b z.2) ∂binaryExperiment μ ν) =
      (∫ x, a x ∂binaryMixture μ ν) +
        ∫ x, binaryPosterior μ ν x * b x ∂binaryMixture μ ν := by
  have hf : Measurable (fun z : Bool × Ω => a z.2 + binarySign z.1 * b z.2) :=
    (ha.comp measurable_snd).add ((measurable_binarySign.comp measurable_fst).mul (hb.comp measurable_snd))
  rw [integral_binaryExperiment μ ν hf (haμ.add (hbμ.const_mul 1)) (haν.add (hbν.const_mul (-1))),
    integral_binaryMixture haμ haν, binaryPosterior_testing hμν hbμ hbν]
  simp only [binarySign, Bool.false_eq_true, ite_true, ite_false, one_mul, neg_one_mul,
    ← sub_eq_add_neg]
  rw [integral_add haμ hbμ, integral_sub haν hbν]
  ring

end ProphetSecretary.Probability
