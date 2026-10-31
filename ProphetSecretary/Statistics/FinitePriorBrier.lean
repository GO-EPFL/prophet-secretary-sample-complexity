import ProphetSecretary.Statistics.FinitePriorHypothetical

/-!
# Actual posterior movement from a pilot and deterministic round selection

The pilot is a measurable function of a visible training prefix. The squared
movement identity is instantiated for the constructed finite-prior posterior,
and the index is selected from expectations before the observations occur.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Statistics.FinitePrior
variable {n : ℕ}

lemma observedPilot_stronglyMeasurable (F : FinitePrior n) (N b l : ℕ)
    {p : ValueArray n N → ℝ} (hp : Measurable p) :
    StronglyMeasurable[F.dataSigma N b l] (fun ω => p (F.observe N b l ω)) :=
  hp.stronglyMeasurable.comp_measurable (Measurable.of_comap_le le_rfl)

/-- `eq:bayes-brier-identity` for the actual finite-prior experiment. -/
theorem posterior_brier_identity (F : FinitePrior n) (N b l k : ℕ) (hlk : l≤k)
    {p : ValueArray n N → ℝ} (hp : Measurable p) (hpu : ∀ d, p d∈Icc (0:ℝ) 1) :
    (∫ ω, (F.posterior N b (k+1) ω-p (F.observe N b l ω))^2 ∂F.law N)-
      (∫ ω, (F.posterior N b k ω-p (F.observe N b l ω))^2 ∂F.law N)=
      ∫ ω, (F.posterior N b (k+1) ω-F.posterior N b k ω)^2 ∂F.law N :=
  ProphetSecretary.Probability.martingale_square_distance_increment (F.posterior_martingale N b)
    (F.posterior_mem_unit N b) (F.observedPilot_stronglyMeasurable N b l hp)
    (Eventually.of_forall fun _ => hpu _) hlk

/-- Only actual training rounds enter the budget. The index k is deterministic,
prior-dependent, and strictly less than 3m. Preliminary b rounds remain counted. -/
theorem exists_small_training_movement (F : FinitePrior n) (N b m : ℕ)
    (hN : b+3*m≤N) (hm : 8≤m) {α : ℝ} (hα : 0<α) (hα1 : α≤1)
    {p : ValueArray n N → ℝ} (hp : Measurable p) (hpu : ∀ d, p d∈Icc (0:ℝ) 1) :
    ∃ k, 2*m≤k ∧ k<3*m ∧ b+k<N ∧
      Real.sqrt (∫ ω, (F.posterior N b (k+1) ω-F.posterior N b k ω)^2 ∂F.law N)≤
        α*(∫ ω, (F.posterior N b k ω-p (F.observe N b m ω))^2 ∂F.law N)+8/(α*(m:ℝ)) := by
  have hpBase : StronglyMeasurable[F.dataFiltration N b (2*m)] (fun ω => p (F.observe N b m ω)) :=
    (F.observedPilot_stronglyMeasurable N b m hp).mono (F.dataSigma_mono N b (by omega))
  obtain ⟨j,hj,hBound⟩ := ProphetSecretary.Probability.exists_small_martingale_movement
    (F.posterior_martingale N b) (F.posterior_mem_unit N b) hpBase
    (Eventually.of_forall fun _ => hpu _) hm hα hα1
  exact ⟨2*m+j,by omega,by omega,by omega,hBound⟩

end ProphetSecretary.Statistics.FinitePrior
