import ProphetSecretary.Limiting.HybridValueEvaluationRegularity
import ProphetSecretary.Limiting.HybridZeroSimulation

/-!
# Continuity of fixed canonical branch payoffs in observed coordinates

The combined values and clocks are continuous functions of the finite point
array and retained world. Composing with actual regular-world execution gives
reward and elapsed-duration continuity under any independent evaluation law.
-/
open MeasureTheory Set Filter
open scoped Topology Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma continuous_combined_branch_world (N : ℕ) :
    Continuous (fun q : (Fin N → Point) × Model.World n Unit =>
      (combinedValues q.2.1 q.1,combinedClocks q.2.2.1 q.1)) := by
  apply Continuous.prodMk
  · apply continuous_pi
    intro k
    induction k using Fin.addCases with
    | left i => simpa only [combinedValues,Fin.addCases_left] using
        (by fun_prop : Continuous (fun q : (Fin N → Point) × Model.World n Unit => q.2.1 i))
    | right j => simpa only [combinedValues,Fin.addCases_right] using
        (by fun_prop : Continuous (fun q : (Fin N → Point) × Model.World n Unit => (q.1 j).2))
  · apply continuous_pi
    intro k
    induction k using Fin.addCases with
    | left i => simpa only [combinedClocks,Fin.addCases_left] using
        (by fun_prop : Continuous (fun q : (Fin N → Point) × Model.World n Unit => q.2.2.1 i))
    | right j => simpa only [combinedClocks,Fin.addCases_right] using
        (by fun_prop : Continuous (fun q : (Fin N → Point) × Model.World n Unit => (q.1 j).1))

theorem FiniteIntensityHybridInstance.valueRule_branch_payoffs_continuousAt_ae
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (N : ℕ) :
    ∀ᵐ q ∂(arrayLaw μ N).prod (P.worldLaw (Measure.dirac ())),
      ContinuousAt (fun q : (Fin N → Point) × Model.World n Unit =>
        (B.valueRule w c).realizedReward 0 (configurationMk N q.1,q.2)) q ∧
      ContinuousAt (fun q : (Fin N → Point) × Model.World n Unit =>
        (B.valueRule w c).realizedDuration (configurationMk N q.1,q.2)) q := by
  have hReward : (fun q : (Fin N → Point) × Model.World n Unit =>
      (B.valueRule w c).realizedReward 0 (configurationMk N q.1,q.2)) =
      (fun q => ((B.valueRule w c).asFinitePolicy N).reward () Finset.univ
        (combinedValues q.2.1 q.1) (combinedClocks q.2.2.1 q.1)) := by
    funext q
    unfold HybridRule.realizedReward
    rw [HybridZeroSimulation.reward_zero_eq_finite]
    cases q.2.2.2
    rfl
  have hDuration : (fun q : (Fin N → Point) × Model.World n Unit =>
      (B.valueRule w c).realizedDuration (configurationMk N q.1,q.2)) =
      (fun q => ((B.valueRule w c).asFinitePolicy N).stoppingTime () Finset.univ
        (combinedValues q.2.1 q.1) (combinedClocks q.2.2.1 q.1)) := by
    funext q
    cases q.2.2.2
    rfl
  rw [hReward,hDuration]
  filter_upwards [B.valueRule_eval_branch_outcomes_continuousAt_ae ha hw hc P μ N] with q hq
  exact ⟨hq.1.comp' (f := fun q : (Fin N → Point) × Model.World n Unit =>
      (combinedValues q.2.1 q.1,combinedClocks q.2.2.1 q.1)) (continuous_combined_branch_world N).continuousAt,
    hq.2.comp' (f := fun q : (Fin N → Point) × Model.World n Unit =>
      (combinedValues q.2.1 q.1,combinedClocks q.2.2.1 q.1)) (continuous_combined_branch_world N).continuousAt⟩
end ProphetSecretary.Limiting
