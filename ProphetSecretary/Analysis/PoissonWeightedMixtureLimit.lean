import ProphetSecretary.Analysis.PoissonMixtureLimit

/-!
# Poisson mixture convergence for count-weighted observables

A bound linear in the analytical total count suffices. The summable envelope
uses the exact first Poisson moment, so score-weighted payoff convergence does
not require bounded realized point counts.
-/
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace ProphetSecretary.Analysis
open ProphetSecretary.Limiting

lemma summable_countWeight (R : ℝ≥0) : Summable (fun N : ℕ => (N:ℝ)*poissonWeight R N) := by
  have h := hasSum_poisson_first R
  simpa only [mul_comm] using h.summable

lemma summable_poissonWeight_linear (R : ℝ≥0) (D : ℝ) :
    Summable (fun N => poissonWeight R N*(D*((N:ℝ)+1))) := by
  have h := ((summable_countWeight R).add (summable_poissonWeight R)).mul_left D
  have he : (fun N : ℕ => poissonWeight R N*(D*((N:ℝ)+1))) =
      (fun N : ℕ => D*((N:ℝ)*poissonWeight R N+poissonWeight R N)) := by
    funext N
    ring
  rw [he]
  exact h

theorem poisson_weighted_tsum_tendsto_of_envelope {rs : ℕ → ℝ≥0} {r R : ℝ≥0}
    (hr : Tendsto rs atTop (𝓝 r)) (hR : ∀ m, rs m≤R)
    (b : ℕ → ℕ → ℝ) (v A : ℕ → ℝ) (_hA : ∀ N, 0≤A N)
    (hSum : Summable (fun N => poissonWeight R N*A N))
    (hb : ∀ m N, |b m N|≤A N) (hlim : ∀ N, Tendsto (fun m => b m N) atTop (𝓝 (v N))) :
    Tendsto (fun m => ∑' N, poissonWeight (rs m) N*b m N) atTop
      (𝓝 (∑' N, poissonWeight r N*v N)) := by
  apply tendsto_tsum_of_dominated_convergence (hSum.mul_left (Real.exp (R:ℝ)))
  · intro N
    exact (poissonWeight_tendsto hr N).mul (hlim N)
  · exact Eventually.of_forall (fun m N => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (show 0≤poissonWeight (rs m) N by unfold poissonWeight; positivity)]
      calc
        _ ≤ (Real.exp (R:ℝ)*poissonWeight R N)*A N :=
          mul_le_mul (poissonWeight_le_envelope (hR m) N) (hb m N) (abs_nonneg _) (by unfold poissonWeight; positivity)
        _ = _ := by ring)

theorem poisson_weighted_tsum_tendsto_of_linear_bound {rs : ℕ → ℝ≥0} {r R : ℝ≥0}
    (hr : Tendsto rs atTop (𝓝 r)) (hR : ∀ m, rs m≤R)
    (b : ℕ → ℕ → ℝ) (v : ℕ → ℝ) {D : ℝ} (hD : 0≤D)
    (hb : ∀ m N, |b m N|≤D*((N:ℝ)+1))
    (hlim : ∀ N, Tendsto (fun m => b m N) atTop (𝓝 (v N))) :
    Tendsto (fun m => ∑' N, poissonWeight (rs m) N*b m N) atTop
      (𝓝 (∑' N, poissonWeight r N*v N)) :=
  poisson_weighted_tsum_tendsto_of_envelope hr hR b v (fun N => D*((N:ℝ)+1))
    (fun N => mul_nonneg hD (by positivity)) (summable_poissonWeight_linear R D) hb hlim
end ProphetSecretary.Analysis
