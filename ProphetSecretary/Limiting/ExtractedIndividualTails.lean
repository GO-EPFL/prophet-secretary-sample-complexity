import ProphetSecretary.Limiting.PositiveBandResidual
import ProphetSecretary.Limiting.WeightedResidualAtoms

/-!
# Summable positive tails of extracted individual laws

The actual positive weighted-prefix decomposition bounds every finite sum of
individual tail probabilities by the initial weighted mass divided by b.
Taking the genuine nonnegative series proves local summability of all retained
individual exceedances, without assuming it in a limiting-instance interface.
-/
open MeasureTheory Set
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting

private lemma finiteMeasure_mass_le_of_raw_le (μ ν : FiniteMeasure ℝ) (hle : (μ : Measure ℝ) ≤ (ν : Measure ℝ)) :
    μ.mass ≤ ν.mass := by
  apply ENNReal.coe_le_coe.mp
  simpa only [FiniteMeasure.ennreal_mass] using Measure.le_iff.mp hle Set.univ MeasurableSet.univ

/-- The cap-supported extracted individuals have locally summable tails. -/
theorem extracted_individual_tail_sum_le (H : ℝ≥0) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) (hρ : ∀ N, ρ N = valueWeightedLaw (Q N) H + ρ (N+1))
    (hQ : ∀ i, (Q i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) {b : ℝ} (hb : 0 < b) :
    (∑' i, (Q i : Measure ℝ) (Ioi b)) ≤ ENNReal.ofReal (((ρ 0).mass : ℝ) / b) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro N
  let ν : FiniteMeasure ℝ := ∑ i ∈ Finset.range N, valueWeightedLaw (Q i) H
  have hνle : (ν : Measure ℝ) ≤ (ρ 0 : Measure ℝ) := by
    apply Measure.le_iff.mpr
    intro s hs
    have he := congrArg (fun μ : FiniteMeasure ℝ => (μ : Measure ℝ) s) (extracted_residual_prefix_identity H Q ρ hρ N)
    rw [FiniteMeasure.toMeasure_add,Measure.add_apply] at he
    rw [he]
    exact le_add_of_nonneg_right (show (0 : ENNReal) ≤ (ρ N : Measure ℝ) s from bot_le)
  have hνmass : ν.mass ≤ (ρ 0).mass := finiteMeasure_mass_le_of_raw_le ν (ρ 0) hνle
  have hmap : positiveMarkIntensityAbove ν b hb =
      ∑ i ∈ Finset.range N, (Q i).toFiniteMeasure.restrict (Ioi b) := by
    change positiveBandUnweightHom b hb (∑ i ∈ Finset.range N, valueWeightedLaw (Q i) H) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact positiveBand_valueWeightedLaw _ H (ae_iff.mpr (hQ i)) hb
  calc
    _ = (↑(∑ i ∈ Finset.range N, (Q i).toFiniteMeasure.restrict (Ioi b)) : Measure ℝ) Set.univ := by
      rw [FiniteMeasure.toMeasure_sum,Measure.finsetSum_apply]
      apply Finset.sum_congr rfl
      intro i _
      change (Q i : Measure ℝ) (Ioi b) = ((Q i : Measure ℝ).restrict (Ioi b)) Set.univ
      simp
    _ = (positiveMarkIntensityAbove ν b hb : Measure ℝ) Set.univ := by rw [hmap]
    _ = positiveMarkIntensity ν (Ioi b) := by
      change ((positiveMarkIntensity ν).restrict (Ioi b)) Set.univ = _
      simp
    _ ≤ ENNReal.ofReal ((ν.mass : ℝ) / b) := positiveMarkIntensity_tail_le ν hb
    _ ≤ _ := ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hνmass hb.le)

lemma extracted_individual_tail_sum_lt_top (H : ℝ≥0) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) (hρ : ∀ N, ρ N = valueWeightedLaw (Q N) H + ρ (N+1))
    (hQ : ∀ i, (Q i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) {b : ℝ} (hb : 0 < b) :
    (∑' i, (Q i : Measure ℝ) (Ioi b)) < ⊤ :=
  (extracted_individual_tail_sum_le H Q ρ hρ hQ hb).trans_lt ENNReal.ofReal_lt_top

end ProphetSecretary.Limiting
