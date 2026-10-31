import ProphetSecretary.Limiting.CoarseFinitePoissonLimit

/-!
# Vanishing square sums imply rarity of each iid virtual offer

A positive finite virtual count is at least one. The square of each marginal
band probability is therefore bounded by the total independent square sum.
Taking square roots preserves a dimension-independent bound.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting

lemma iid_band_probability_tendsto_zero (N : ℕ → ℕ) (hN : ∀ m, 0<N m)
    (κ : ℕ → Measure ℝ) (S : Set ℝ)
    (hSquares : Tendsto (fun m => (N m:ℝ)*((κ m).real S)^2) atTop (𝓝 (0:ℝ))) :
    Tendsto (fun m => (κ m).real S) atTop (𝓝 (0:ℝ)) := by
  have hBound (m) : (κ m).real S≤Real.sqrt ((N m:ℝ)*((κ m).real S)^2) := by
    have hOne : (1:ℝ)≤N m := by exact_mod_cast (Nat.succ_le_iff.mpr (hN m))
    have hSq := le_mul_of_one_le_left (sq_nonneg ((κ m).real S)) hOne
    have h := Real.sqrt_le_sqrt hSq
    simpa only [Real.sqrt_sq_eq_abs,abs_of_nonneg measureReal_nonneg] using h
  have hRoot : Tendsto (fun m => Real.sqrt ((N m:ℝ)*((κ m).real S)^2)) atTop (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hSquares
  exact squeeze_zero (fun _ => measureReal_nonneg) hBound hRoot
end ProphetSecretary.Limiting
