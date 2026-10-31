import ProphetSecretary.Statistics.FinitePriorBrier
import ProphetSecretary.Analysis.PosteriorAverageIncrement

/-!
# A deterministic round with inverse-linear posterior energy

The posterior is the actual conditional expectation in the finite-prior
iid experiment. Its square-distance identity gives total energy at most
one. The index is selected from expectations before training, and the
ONLINE column is never requested for this calculation.
-/

open MeasureTheory Set Filter
namespace ProphetSecretary.Statistics.FinitePrior
variable {n : ℕ}

theorem exists_inverse_round_posterior_increment (F : FinitePrior n) (N b m : ℕ) (hm : 0<m) :
    ∃ j<m, Real.sqrt (∫ ω, (F.posterior N b (2*m+j+1) ω-F.posterior N b (2*m+j) ω)^2 ∂F.law N)≤
      1/Real.sqrt (m : ℝ) := by
  let s := fun j : ℕ => ∫ ω, (F.posterior N b (2*m+j) ω)^2 ∂F.law N
  have hUnit (j : ℕ) : s j∈Icc (0 : ℝ) 1 := by
    have hPost : Measurable (F.posterior N b (2*m+j)) :=
      ((F.posterior_stronglyMeasurable N b (2*m+j)).mono (F.dataSigma_le N b (2*m+j))).measurable
    have hZero : ∀ᵐ ω : BaseWorld F N ∂F.law N, (0 : ℝ)∈Icc (0 : ℝ) 1 :=
      Eventually.of_forall (fun _ => ⟨le_rfl,zero_le_one⟩)
    have h := ProphetSecretary.Probability.unit_square_distance_mean_mem (μ:=F.law N)
      hPost
      (measurable_const : Measurable (fun _ : BaseWorld F N => (0 : ℝ)))
      (F.posterior_mem_unit N b (2*m+j))
      hZero
    simpa only [sub_zero] using h
  have hIncrement (j : ℕ) : s (j+1)-s j=
      ∫ ω, (F.posterior N b (2*m+j+1) ω-F.posterior N b (2*m+j) ω)^2 ∂F.law N := by
    have h := F.posterior_brier_identity N b 0 (2*m+j) (Nat.zero_le _)
      (p:=fun _ => (0 : ℝ)) measurable_const (fun _ => by norm_num)
    simpa only [s,Nat.add_assoc,sub_zero] using h
  obtain ⟨j,hj,hBound⟩ := ProphetSecretary.Analysis.exists_averaged_posterior_increment hm s (hUnit 0).1 (hUnit m).2
  rw [hIncrement j] at hBound
  exact ⟨j,hj,hBound⟩

end ProphetSecretary.Statistics.FinitePrior
