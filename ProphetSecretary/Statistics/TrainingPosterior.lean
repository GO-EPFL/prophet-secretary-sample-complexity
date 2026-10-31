import ProphetSecretary.Probability.BinaryPosterior

/-!
# Posterior bias after adaptive training

The observation includes the learner's independent seed and its actual adaptive
transcript. The budget in `Learner n k` holds on every training outcome. This is
the information-to-posterior step of `thm:bayes`, including adaptive requests.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model.Learner

variable {n k : ℕ}

/-- Explicit posterior-variance bound under a bounded centered product tilt.
The information remains the sum of marginal second moments, independent of n. -/
theorem training_binaryPosterior_secondMoment_le (L : Learner n k) (P : Instance n)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂P.law i = 0)
    {t : ℝ} (ht : |t| ≤ 1 / 4) :
    let Dplus := L.transcriptLaw (P.likelihoodTilt h hh hb hm t ht)
    let Dminus := L.transcriptLaw (P.likelihoodTilt h hh hb hm (-t) (by simpa only [abs_neg] using ht))
    (∫ d, ProphetSecretary.Probability.binaryPosterior Dplus Dminus d ^ 2
      ∂ProphetSecretary.Probability.binaryMixture Dplus Dminus) ≤
        4 * (k : ℝ) * t ^ 2 * ProphetSecretary.Probability.information P.law h := by
  have hInfo := L.symmetric_transcript_tilt_klDiv_le P h hh hb hm ht
  have hI : 0 ≤ 16 * (k : ℝ) * t ^ 2 * ProphetSecretary.Probability.information P.law h :=
    mul_nonneg (by positivity) (ProphetSecretary.Probability.information_nonnegative P.law h)
  have hvar := ProphetSecretary.Probability.binaryPosterior_secondMoment_le_information hI hInfo
  convert hvar using 1
  ring

end ProphetSecretary.Model.Learner
