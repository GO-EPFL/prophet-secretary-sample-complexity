import ProphetSecretary.Limiting.DirectIndividualPerturbedApproximation
import ProphetSecretary.Limiting.CountableIndividualLikelihoodMaximum
import ProphetSecretary.Stability.MaximumScoreLimit

/-!
# Actual individual maximum-score convergence in the direct schedule

The whole perturbed benchmark converges with the prescribed base count.
Uniform fixed-payoff curvature then forces convergence of its derivative at
zero. Thus this complete-vector maximum-score limit is proved from actual
perturbed laws, not inferred from base maximum or scalar-value convergence.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model ProphetSecretary.Probability

theorem directIndividual_expectedMaximumScore_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (i : ℕ) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun m => (B.directFiniteApproximation hZero m).expectedMaximumScore
      (directIndividualScore (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f))
      atTop (𝓝 (B.prophetIndividualLikelihoodDerivative i (centeredBoundedScore (B.individuals i : Measure ℝ) f))) := by
  let sizes := fun m => m+B.directVirtualCount hZero m
  let P := fun m => B.directFiniteApproximation hZero m
  let score := fun m => directIndividualScore (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f
  have hMeas : ∀ m j, Measurable (score m j) := fun m =>
    (directIndividualScore_properties (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f).1
  have hBound : ∀ m j, ∀ᵐ x ∂(P m).law j, |score m j x|≤1 := fun m j =>
    Filter.Eventually.of_forall ((directIndividualScore_properties (B.individualPrefix m)
      (B.directVirtualOfferInstance hZero m) i f).2.1 j)
  have hMean : ∀ m j, (∫ x, score m j x ∂(P m).law j)=0 := by
    intro m j
    change (∫ x, score m j x ∂(B.directFiniteApproximation hZero m).law j)=0
    rw [B.directFiniteApproximation_eq_appendVirtual hZero m]
    exact (directIndividualScore_properties (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f).2.2.1 j
  have hInfo : ∀ m, information (P m).law (score m)≤1 := by
    intro m
    change information (B.directFiniteApproximation hZero m).law (score m)≤1
    rw [B.directFiniteApproximation_eq_appendVirtual hZero m]
    exact (directIndividualScore_properties (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f).2.2.2
  have hFamily (m : ℕ) (θ : ℝ) :
      (P m).likelihoodWidePath (score m) (hMeas m) (hBound m) (hMean m) θ=
        B.directIndividualPerturbation hZero i f θ m := by
    apply Model.Instance.eq_of_law_eq
    funext j
    change tiltLaw ((P m).law j) (score m j) (halfParameter θ)=
      tiltLaw (((B.individualPrefix m).appendIndependent (B.directVirtualOfferInstance hZero m)).law j)
        (score m j) (halfParameter θ)
    rw [show P m=(B.individualPrefix m).appendIndependent (B.directVirtualOfferInstance hZero m) from
      B.directFiniteApproximation_eq_appendVirtual hZero m]
  have hF : HasDerivAt (fun θ => (B.individualBoundedScorePath i f θ).expectedMaximum)
      (B.prophetIndividualLikelihoodDerivative i (centeredBoundedScore (B.individuals i : Measure ℝ) f)) 0 :=
    B.hasDerivAt_expectedMaximum_individualLikelihoodPath i (centeredBoundedScore (B.individuals i : Measure ℝ) f)
      (continuous_centeredBoundedScore (B.individuals i : Measure ℝ) f).measurable
      (Filter.Eventually.of_forall (centeredBoundedScore_abs_le_one (B.individuals i : Measure ℝ) f))
      (centeredBoundedScore_mean (B.individuals i : Measure ℝ) f)
  apply Model.expectedMaximumScore_tendsto_of_perturbed_benchmarks sizes P B.cap.property (by norm_num : (0 : ℝ)≤1)
    (B.directFiniteApproximation_bounded hZero) score hMeas hBound hMean hInfo
    (fun θ => (B.individualBoundedScorePath i f θ).expectedMaximum) hF
  intro θ hθ
  simp_rw [hFamily]
  exact B.directIndividualPerturbation_expectedMaximum_tendsto hZero i f (abs_le.mpr hθ)

end ProphetSecretary.Limiting.CountableInstance
