import ProphetSecretary.Model.TrainingLaw
import ProphetSecretary.Reach.Pending
import Mathlib.Probability.Distributions.Bernoulli

/-!
# One-marginal jackpot perturbations

The added atom is nonnegative, and an independent Bernoulli indicator couples each
perturbed draw with a draw from the original marginal.
-/

open MeasureTheory ProbabilityTheory Set unitInterval
open scoped ENNReal

namespace ProphetSecretary.Model

/-- Marginal mixture assigning probability `p` to the jackpot and otherwise using `μ`. -/
noncomputable def jackpotLaw (μ : Measure ℝ) (p : unitInterval) (A : ℝ) : Measure ℝ :=
  unitInterval.toNNReal p • Measure.dirac A + unitInterval.toNNReal (unitInterval.symm p) • μ

instance jackpotLaw_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] (p : unitInterval) (A : ℝ) :
    IsProbabilityMeasure (jackpotLaw μ p A) := by
  constructor
  simp [jackpotLaw]

lemma jackpotLaw_nonnegative (μ : Measure ℝ) (hμ : ∀ᵐ x ∂μ, 0 ≤ x)
    (p : unitInterval) {A : ℝ} (hA : 0 ≤ A) : ∀ᵐ x ∂jackpotLaw μ p A, 0 ≤ x := by
  rw [jackpotLaw, ae_add_measure_iff]
  constructor
  · exact Measure.ae_smul_measure (by simpa using hA) _
  · exact Measure.ae_smul_measure hμ _

/-- One Bernoulli coin chooses between the base draw and the jackpot. -/
def realizeJackpot (A : ℝ) (z : Bool × ℝ) : ℝ := if z.1 = true then A else z.2

lemma measurable_realizeJackpot (A : ℝ) : Measurable (realizeJackpot A) := by
  exact Measurable.ite (measurableSet_eq_fun measurable_fst measurable_const) measurable_const measurable_snd

lemma realizeJackpot_measurePreserving (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (p : unitInterval) (A : ℝ) :
    MeasurePreserving (realizeJackpot A) ((bernoulliMeasure true false p).prod μ) (jackpotLaw μ p A) := by
  refine ⟨measurable_realizeJackpot A, ?_⟩
  rw [bernoulliMeasure_def, Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left,
    Measure.map_add _ _ (measurable_realizeJackpot A), Measure.map_smul, Measure.map_smul,
    Measure.dirac_prod, Measure.dirac_prod,
    Measure.map_map (measurable_realizeJackpot A) measurable_prodMk_left,
    Measure.map_map (measurable_realizeJackpot A) measurable_prodMk_left]
  simp [realizeJackpot, Function.comp_def, jackpotLaw]

namespace Instance

variable {n : ℕ}

noncomputable def jackpot (P : Instance n) (i : Fin n) (p : unitInterval) (A : ℝ) (hA : 0 ≤ A) :
    Instance n where
  law := Function.update P.law i (jackpotLaw (P.law i) p A)
  probability j := by
    by_cases hj : j = i
    · subst j; simp only [Function.update_self]; infer_instance
    · simpa only [Function.update_of_ne hj] using P.probability j
  nonnegative j := by
    by_cases hj : j = i
    · subst j; simp only [Function.update_self]; exact jackpotLaw_nonnegative _ (P.nonnegative i) p hA
    · simpa only [Function.update_of_ne hj] using P.nonnegative j

end Instance
end ProphetSecretary.Model
