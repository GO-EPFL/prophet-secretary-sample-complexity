import ProphetSecretary.Limiting.CriticalMinimizingInstance
import ProphetSecretary.Analysis.ReciprocalRank

/-!
# A cap-three mean-one minimizing sequence

The explicit errors are 1/(100(m+1)). Each member is an actual independent
finite instance obtained by clipping a raw near-minimizer. Scalar gaps tend
to zero by their nonnegativity and the explicit error bound, with no total
first-moment restriction.
-/

open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting
open ProphetSecretary.Model

noncomputable def criticalApproximationError (m : ℕ) : ℝ := 1/(100*((m : ℝ)+1))

lemma criticalApproximationError_positive (m : ℕ) : 0<criticalApproximationError m := by
  unfold criticalApproximationError
  positivity

lemma criticalApproximationError_le (m : ℕ) : criticalApproximationError m≤1/100 := by
  unfold criticalApproximationError
  apply one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<100)
  nlinarith only [(show (0 : ℝ)≤(m : ℝ) from Nat.cast_nonneg m)]

lemma criticalApproximationError_tendsto : Tendsto criticalApproximationError atTop (𝓝 (0 : ℝ)) := by
  change Tendsto (fun m : ℕ => 1/(100*((m : ℝ)+1))) atTop (𝓝 (0 : ℝ))
  simpa only [Nat.cast_add,Nat.cast_one] using ProphetSecretary.Analysis.reciprocal_rank_tendsto_zero 100

theorem exists_normalized_nearCritical_sequence :
    ∃ (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) (lam : ℕ → ℝ),
      (∀ m, (P m).HasPositiveFiniteMaximum) ∧
      (∀ m, (P m).expectedMaximum=1) ∧
      (∀ m i, ∀ᵐ x ∂(P m).law i, x≤3) ∧
      (∀ m, lam m∈Icc (1/4 : ℝ) (3/4)) ∧
      (∀ m, normalizedScalarGap (P m) (lam m)<criticalApproximationError m) ∧
      Tendsto (fun m => normalizedScalarGap (P m) (lam m)) atTop (𝓝 (0 : ℝ)) := by
  have hEach := fun m => exists_normalized_nearCritical_instance
    (criticalApproximationError_positive m) (criticalApproximationError_le m)
  choose sizes P lam hP hM hCap hLam hGap using hEach
  refine ⟨sizes,P,lam,hP,hM,hCap,hLam,hGap,?_⟩
  apply squeeze_zero _ (fun m => (hGap m).le) criticalApproximationError_tendsto
  intro m
  exact normalizedScalarGap_nonnegative (P m) (hP m).1
    ⟨by linarith only [(hLam m).1],by linarith only [(hLam m).2]⟩

end ProphetSecretary.Limiting
