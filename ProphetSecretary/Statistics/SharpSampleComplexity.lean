import ProphetSecretary.LowerBound.SampleLowerBound
import ProphetSecretary.Statistics.SampleComplexityAsymptotics

/-!
# Sharp sample complexity at the optimal prophet-secretary constant

The lower and upper constants are independent of the instance size. The
minimum is finite and is attained by a hard-budget learner. Guarantees average
training, policy and online randomness; the budget holds on every training
outcome. Paper correspondence: `thm:theta-main`.
-/

open Set
open scoped Topology
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

theorem sharp_sample_complexity_bounds :
    ∃ a A eps0 : ℝ, 0<a ∧ a≤A ∧ 0<eps0 ∧ ∀ eps : ℝ, eps∈Ioo (0 : ℝ) eps0 →
      sampleComplexity eps<⊤ ∧ a/eps≤((sampleComplexity eps).toNat : ℝ) ∧
        ((sampleComplexity eps).toNat : ℝ)≤A/eps := by
  obtain ⟨a,A,eps0,ha,_hA,hEps0,hBounds⟩ :=
    sampleComplexity_bounds_of_feasible_lower LowerBound.sample_lower_bound
  refine ⟨a,max a A,eps0,ha,le_max_left _ _,hEps0,?_⟩
  intro eps hEps
  have h := hBounds eps hEps
  exact ⟨h.1,h.2.1,h.2.2.trans
    (div_le_div_of_nonneg_right (le_max_right a A) hEps.1.le)⟩

theorem sharp_sample_complexity :
    (fun eps : ℝ => ((sampleComplexity eps).toNat : ℝ)) =Θ[𝓝[>] (0 : ℝ)] (fun eps => 1/eps) :=
  sampleComplexity_theta_of_feasible_lower LowerBound.sample_lower_bound

end ProphetSecretary.Statistics
