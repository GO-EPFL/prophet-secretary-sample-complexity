import ProphetSecretary.Limiting.DirectScheduledCloudProperties
import ProphetSecretary.Limiting.DirectCloudMaximumScoreLimit

/-!
# Complete maximum-score limits for the actual chosen cloud schedule

The prescribed-count design is exactly the chosen direct finite product law.
Actual quarter-parameter benchmark convergence and its uniform derivative
control therefore give the complete maximum covariance for the scheduled
zero-atom likelihood score, including all values after stopping.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model ProphetSecretary.Probability

lemma directFiniteApproximation_eq_prescribedCount (B : CountableInstance) (hZero : B.terminal=0) (m : ℕ) :
    B.directFiniteApproximation hZero m=B.finiteDirectApproximationAt m (B.markCutoff m)
      (B.terminal_lt_markCutoff m) (B.directVirtualCount hZero m) (B.directVirtualCount_positive hZero m)
      (B.directVirtualCount_rate_le hZero m) := by
  exact ((B.directTruncation m).rareDesign_eq_finitePoissonApproximation (B.directRefinementIndex hZero m)).symm

theorem directScheduled_cloud_expectedMaximumScore_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal:ℝ)<b) (hSub : S⊆Ioi b) :
    Tendsto (fun m => (B.directFiniteApproximation hZero m).expectedMaximumScore (B.directScheduledCloudScore hZero S m))
      atTop (𝓝 (B.prophetBandLikelihoodDerivative S)) := by
  let A := fun m => B.finiteDirectApproximationAt m (B.markCutoff m) (B.terminal_lt_markCutoff m)
    (B.directVirtualCount hZero m) (B.directVirtualCount_positive hZero m) (B.directVirtualCount_rate_le hZero m)
  let score := fun m => B.directScheduledCloudScore hZero S m
  have hEq (m) : A m=B.directFiniteApproximation hZero m := (B.directFiniteApproximation_eq_prescribedCount hZero m).symm
  have hS0 : (0:ℝ)∉S := fun h => not_lt_of_ge (B.terminal.property.trans hb.le) (hSub h)
  have hProps (m) := B.directScheduledCloudScore_properties hZero hS hS0 m
  have hz (m) : ∀ j, (∫ x, score m j x ∂(A m).law j)=0 := by
    rw [hEq m]
    exact (hProps m).2.2.1
  have hInfo (m) : information (A m).law (score m)≤2*B.intensity.real S := by
    rw [hEq m]
    exact B.directScheduledCloudScore_information_le hZero hS hb hSub m
  have h := B.direct_cloud_expectedMaximumScore_tendsto hZero id (B.directVirtualCount hZero) B.markCutoff
    B.terminal_lt_markCutoff (B.directVirtualCount_positive hZero) (B.directVirtualCount_rate_le hZero)
    (B.directVirtualCount_probability_le_half hZero) tendsto_id B.markCutoff_tendsto (B.directVirtualCount_tendsto hZero)
    hS hb hSub (by positivity : 0≤2*B.intensity.real S) (fun m => (hProps m).1)
    (fun m j => Filter.Eventually.of_forall ((hProps m).2.1 j)) hz hInfo
  exact h.congr (fun m => congrArg (fun P => P.expectedMaximumScore (score m)) (hEq m))
end ProphetSecretary.Limiting.CountableInstance
