import ProphetSecretary.LowerBound.CriticalInput
import ProphetSecretary.LowerBound.LikelihoodFamilyLowerBound

/-!
# The universal sample lower bound

This is `thm:main`. The finite experiment is constructed before epsilon and
the learner are chosen. Its actual centered scores, normalized base laws and
negative fixed-optimizer target response discharge every statistical premise
of the Bayesian reduction. Training may be adaptive with a hard budget.
-/

open Set
namespace ProphetSecretary.LowerBound
open ProphetSecretary.Model

theorem sample_lower_bound :
    ∃ a eps0 : ℝ, 0<a ∧ 0<eps0 ∧ ∀ eps : ℝ, eps∈Ioo (0 : ℝ) eps0 →
      ∀ k : ℕ, FeasibleBudget eps k → a/eps≤(k : ℝ) := by
  obtain ⟨sizes,P,H,δ,I,b,L,lams,score,πopt,hH,hδ,hδhalf,hI,hb,hCap,hL,hTail,
    hRange,hNormalized,hCritical,hh,hBound,hMean,hInfo,hOptimal,hNegative⟩ :=
    exists_critical_likelihood_family
  exact likelihood_family_sample_lower_bound_of_optimal sizes P hH hδ hδhalf hI hb
    hCap L hL hTail lams hRange hNormalized hCritical score hh hBound hMean hInfo
    πopt hOptimal hNegative

end ProphetSecretary.LowerBound
