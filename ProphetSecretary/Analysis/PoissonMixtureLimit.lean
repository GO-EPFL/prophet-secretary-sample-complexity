import ProphetSecretary.Limiting.PoissonCountMoments
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Convergence of uniformly bounded Poisson mixtures

One summable Poisson-weight envelope controls all finite-count branches.
The rate may tend to zero; no convergence of normalized marks is used here.
-/
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace ProphetSecretary.Analysis
open ProphetSecretary.Limiting

lemma poissonWeight_tendsto {rs : ℕ → ℝ≥0} {r : ℝ≥0}
    (hr : Tendsto rs atTop (𝓝 r)) (N : ℕ) :
    Tendsto (fun m => poissonWeight (rs m) N) atTop (𝓝 (poissonWeight r N)) := by
  unfold poissonWeight
  have hExp : Tendsto (fun m => Real.exp (-((rs m):ℝ))) atTop (𝓝 (Real.exp (-(r:ℝ)))) :=
    Real.continuous_exp.continuousAt.tendsto.comp (NNReal.tendsto_coe.2 hr).neg
  exact (hExp.mul ((NNReal.tendsto_coe.2 hr).pow N)).div_const _

lemma poissonWeight_le_envelope {r R : ℝ≥0} (hr : r≤R) (N : ℕ) :
    poissonWeight r N ≤ Real.exp (R:ℝ)*poissonWeight R N := by
  have hExp : Real.exp (R:ℝ)*Real.exp (-(R:ℝ)) = 1 := by
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  have hrR : (r:ℝ)≤(R:ℝ) := by exact_mod_cast hr
  have hr0 : 0≤(r:ℝ) := NNReal.coe_nonneg _
  have hE : Real.exp (-(r:ℝ)) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr0)
  unfold poissonWeight
  calc
    _ ≤ (r:ℝ)^N/(N.factorial:ℝ) := by
      gcongr
      exact mul_le_of_le_one_left (pow_nonneg hr0 _) hE
    _ ≤ (R:ℝ)^N/(N.factorial:ℝ) := by gcongr
    _ = _ := by rw [← mul_div_assoc,← mul_assoc,hExp,one_mul]

lemma summable_poissonWeight (R : ℝ≥0) : Summable (poissonWeight R) := by
  have h : HasSum (poissonWeight R) 1 := by convert! hasSum_one_poissonMeasure R using 1
  exact h.summable

/-- Branch expectations may depend on both the design index and the count.
The global bound is uniform in both; the rate bound is independent of count. -/
theorem poisson_weighted_tsum_tendsto {rs : ℕ → ℝ≥0} {r R : ℝ≥0}
    (hr : Tendsto rs atTop (𝓝 r)) (hR : ∀ m, rs m≤R)
    (b : ℕ → ℕ → ℝ) (v : ℕ → ℝ) {D : ℝ} (_hD : 0≤D)
    (hb : ∀ m N, |b m N|≤D) (hlim : ∀ N, Tendsto (fun m => b m N) atTop (𝓝 (v N))) :
    Tendsto (fun m => ∑' N, poissonWeight (rs m) N*b m N) atTop
      (𝓝 (∑' N, poissonWeight r N*v N)) := by
  have hsum : Summable (fun N => (Real.exp (R:ℝ)*D)*poissonWeight R N) :=
    (summable_poissonWeight R).mul_left _
  apply tendsto_tsum_of_dominated_convergence hsum
  · intro N
    exact (poissonWeight_tendsto hr N).mul (hlim N)
  · exact Eventually.of_forall (fun m N => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (show 0≤poissonWeight (rs m) N by unfold poissonWeight; positivity)]
      calc
        _ ≤ (Real.exp (R:ℝ)*poissonWeight R N)*D :=
          mul_le_mul (poissonWeight_le_envelope (hR m) N) (hb m N) (abs_nonneg _) (by unfold poissonWeight; positivity)
        _ = _ := by ring)
end ProphetSecretary.Analysis
