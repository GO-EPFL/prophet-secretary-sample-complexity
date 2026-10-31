import ProphetSecretary.Statistics.EmpiricalRowShuffles
import ProphetSecretary.Reach.ReachIntegralBounds
import ProphetSecretary.Probability.FourthMoment
import Mathlib.Probability.Moments.Variance

/-!
# Variance contraction by actual independent row shuffles

Averaging a bounded statistic over the constructed training-law-preserving
cyclic shifts preserves its mean and cannot increase its variance. The proof
uses the actual joint law, Jensen's inequality and Fubini; no conditional-
expectation or independence conclusion is assumed as an interface.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Classical NNReal
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

noncomputable def rowSymmetrization (G : ((Fin n × Fin k) → ℝ) → ℝ)
    (y : (Fin n × Fin k) → ℝ) : ℝ := ∫ a, G (shiftTraining a y) ∂empiricalIndicesLaw n k

omit [NeZero k] in
lemma measurable_shifted_statistic {G : ((Fin n × Fin k) → ℝ) → ℝ} (hG : Measurable G) :
    Measurable (fun z : (((Fin n × Fin k) → ℝ) × (Fin n → Fin k)) => G (shiftTraining z.2 z.1)) := by
  apply measurable_from_prod_countable_left
  intro a
  exact hG.comp (measurable_pi_lambda _ fun q => measurable_pi_apply (q.1,q.2+a q.1))

omit [NeZero k] in
lemma measurable_rowSymmetrization {G : ((Fin n × Fin k) → ℝ) → ℝ} (hG : Measurable G) :
    Measurable (rowSymmetrization G) :=
  ((measurable_shifted_statistic hG).stronglyMeasurable.integral_prod_right'
    (ν := empiricalIndicesLaw n k)).measurable

lemma rowSymmetrization_abs_le {G : ((Fin n × Fin k) → ℝ) → ℝ} {C : ℝ}
    (hG : ∀ y, |G y| ≤ C) (y : (Fin n × Fin k) → ℝ) : |rowSymmetrization G y| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := empiricalIndicesLaw n k)
    (f := fun a => G (shiftTraining a y)) (Eventually.of_forall fun a => by
      simpa only [Real.norm_eq_abs] using hG (shiftTraining a y))
  simpa only [rowSymmetrization,Real.norm_eq_abs,probReal_univ,mul_one] using h

lemma integral_shifted_statistic (P : Instance n) {G : ((Fin n × Fin k) → ℝ) → ℝ}
    (hG : Measurable G) (a : Fin n → Fin k) :
    (∫ y, G (shiftTraining a y) ∂P.trainingCoordinateLaw k) = ∫ y, G y ∂P.trainingCoordinateLaw k := by
  have hp := shiftTraining_measurePreserving P a
  have hi := integral_map (μ := P.trainingCoordinateLaw k) hp.measurable.aemeasurable hG.aestronglyMeasurable
  rw [hp.map_eq] at hi
  exact hi.symm

lemma integral_rowSymmetrization (P : Instance n) {G : ((Fin n × Fin k) → ℝ) → ℝ}
    (hG : Measurable G) {C : ℝ} (hbound : ∀ y, |G y| ≤ C) :
    (∫ y, rowSymmetrization G y ∂P.trainingCoordinateLaw k) = ∫ y, G y ∂P.trainingCoordinateLaw k := by
  have hJ : Integrable (fun z : (((Fin n × Fin k) → ℝ) × (Fin n → Fin k)) => G (shiftTraining z.2 z.1))
      ((P.trainingCoordinateLaw k).prod (empiricalIndicesLaw n k)) := by
    apply Integrable.of_bound (measurable_shifted_statistic hG).aestronglyMeasurable C
    exact Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hbound (shiftTraining z.2 z.1)
  unfold rowSymmetrization
  rw [integral_integral_swap hJ]
  simp_rw [integral_shifted_statistic P hG]
  simp only [integral_const,probReal_univ,one_smul]

lemma rowSymmetrization_center_sq_le (G : ((Fin n × Fin k) → ℝ) → ℝ) (m : ℝ)
    (y : (Fin n × Fin k) → ℝ) :
    (rowSymmetrization G y-m)^2 ≤ ∫ a, (G (shiftTraining a y)-m)^2 ∂empiricalIndicesLaw n k := by
  have he : rowSymmetrization G y-m = ∫ a, G (shiftTraining a y)-m ∂empiricalIndicesLaw n k := by
    rw [integral_sub (integrable_empiricalIndicesLaw _) (integrable_const m)]
    simp only [rowSymmetrization,integral_const,probReal_univ,one_smul]
  rw [he]
  exact ProphetSecretary.Reach.sq_integral_le_integral_sq (empiricalIndicesLaw n k)
    (integrable_empiricalIndicesLaw _) (integrable_empiricalIndicesLaw _)

/-- Variance contraction is an unconditional theorem of the actual shuffle
construction, with all measurability and integrability obligations supplied. -/
theorem variance_rowSymmetrization_le (P : Instance n) {G : ((Fin n × Fin k) → ℝ) → ℝ}
    (hG : Measurable G) (C : ℝ≥0) (hbound : ∀ y, |G y| ≤ (C : ℝ)) :
    variance (rowSymmetrization G) (P.trainingCoordinateLaw k) ≤ variance G (P.trainingCoordinateLaw k) := by
  let m := ∫ y, G y ∂P.trainingCoordinateLaw k
  let D : ℝ := (C : ℝ)+|m|
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hcenter (y) : |G y-m| ≤ D := (abs_sub _ _).trans (add_le_add (hbound y) le_rfl)
  have hscenter (y) : |rowSymmetrization G y-m| ≤ D :=
    (abs_sub _ _).trans (add_le_add (rowSymmetrization_abs_le hbound y) le_rfl)
  have hGcCenter : Measurable (fun y => G y-m) := hG.sub measurable_const
  have hGc : Measurable (fun y => (G y-m)^2) := hGcCenter.pow_const 2
  have hsGcCenter : Measurable (fun y => rowSymmetrization G y-m) :=
    (measurable_rowSymmetrization hG).sub measurable_const
  have hsI : Integrable (fun y => (rowSymmetrization G y-m)^2) (P.trainingCoordinateLaw k) :=
    ProphetSecretary.Probability.integrable_pow_of_bound hsGcCenter hD (Eventually.of_forall hscenter) 2
  have hJI : Integrable (fun z : (((Fin n × Fin k) → ℝ) × (Fin n → Fin k)) =>
      (G (shiftTraining z.2 z.1)-m)^2) ((P.trainingCoordinateLaw k).prod (empiricalIndicesLaw n k)) :=
    ProphetSecretary.Probability.integrable_pow_of_bound (measurable_shifted_statistic hGcCenter)
      hD (Eventually.of_forall fun z => hcenter (shiftTraining z.2 z.1)) 2
  rw [variance_eq_integral (measurable_rowSymmetrization hG).aemeasurable,variance_eq_integral hG.aemeasurable,
    integral_rowSymmetrization P hG hbound]
  calc
    _ ≤ ∫ y, ∫ a, (G (shiftTraining a y)-m)^2 ∂empiricalIndicesLaw n k ∂P.trainingCoordinateLaw k :=
      integral_mono hsI hJI.integral_prod_left (rowSymmetrization_center_sq_le G m)
    _ = ∫ a, ∫ y, (G (shiftTraining a y)-m)^2 ∂P.trainingCoordinateLaw k ∂empiricalIndicesLaw n k :=
      integral_integral_swap hJI
    _ = ∫ y, (G y-m)^2 ∂P.trainingCoordinateLaw k := by
      have he (a : Fin n → Fin k) :
          (∫ y, (G (shiftTraining a y)-m)^2 ∂P.trainingCoordinateLaw k) = ∫ y, (G y-m)^2 ∂P.trainingCoordinateLaw k :=
        integral_shifted_statistic P hGc a
      simp_rw [he]
      simp only [integral_const,probReal_univ,one_smul]

end ProphetSecretary.Statistics
