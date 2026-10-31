import ProphetSecretary.Limiting.Campbell

/-!
# Poisson union bound from the constructed configuration law

The probability that a configuration contains a point in a measurable set is
at most its intensity. This uses the actual Campbell expectation, without an
independent-increment or policy-information assumption.
-/
open MeasureTheory Set
open scoped Classical ENNReal
namespace ProphetSecretary.Limiting

lemma measurableSet_exists_configuration_point {S : Set Point} (hS : MeasurableSet S) :
    MeasurableSet {ω : Configuration | ∃ j : Fin ω.1, ω.2 j ∈ S} := by
  change MeasurableSet[⨅ N : ℕ,
    (inferInstance : MeasurableSpace (Fin N → Point)).map (configurationMk N)] _
  rw [MeasurableSpace.measurableSet_iInf]
  intro N
  change MeasurableSet {v : Fin N → Point | ∃ j : Fin N, v j ∈ S}
  rw [Set.setOf_exists]
  exact MeasurableSet.iUnion fun j : Fin N => hS.preimage (measurable_pi_apply j)

lemma probability_exists_configuration_point_le_intensity (μ : FiniteMeasure ℝ)
    {S : Set Point} (hS : MeasurableSet S) :
    configurationLaw μ {ω : Configuration | ∃ j : Fin ω.1, ω.2 j ∈ S} ≤ intensity μ S := by
  let E : Set Configuration := {ω | ∃ j : Fin ω.1, ω.2 j ∈ S}
  have hE : MeasurableSet E := measurableSet_exists_configuration_point hS
  have hPoint (ω : Configuration) : E.indicator (fun _ => (1 : ℝ≥0∞)) ω ≤
      pointSum (S.indicator (fun _ => 1)) ω := by
    by_cases h : ω ∈ E
    · obtain ⟨j,hj⟩ := h
      rw [Set.indicator_of_mem (show ω ∈ E from ⟨j,hj⟩)]
      calc
        (1 : ℝ≥0∞) = S.indicator (fun _ => 1) (ω.2 j) := (Set.indicator_of_mem hj (fun _ : Point => (1 : ℝ≥0∞))).symm
        _ ≤ ∑ k : Fin ω.1, S.indicator (fun _ => 1) (ω.2 k) :=
          Finset.single_le_sum (f := fun k : Fin ω.1 => S.indicator (fun _ => (1 : ℝ≥0∞)) (ω.2 k)) (fun _ _ => bot_le) (Finset.mem_univ j)
    · rw [Set.indicator_of_notMem h]
      exact bot_le
  calc
    _ = ∫⁻ ω, E.indicator (fun _ => (1 : ℝ≥0∞)) ω ∂configurationLaw μ :=
      (lintegral_indicator_one hE).symm
    _ ≤ ∫⁻ ω, pointSum (S.indicator (fun _ => 1)) ω ∂configurationLaw μ := lintegral_mono hPoint
    _ = ∫⁻ p, S.indicator (fun _ => (1 : ℝ≥0∞)) p ∂intensity μ :=
      lintegral_pointSum μ _ (measurable_const.indicator hS)
    _ = _ := lintegral_indicator_one hS

end ProphetSecretary.Limiting
