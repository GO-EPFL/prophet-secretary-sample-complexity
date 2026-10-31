import ProphetSecretary.Limiting.ReserveBandResidual
import ProphetSecretary.Limiting.ReserveResidualAtoms

/-!
# Summable positive tails of extracted individual laws

The actual positive weighted-prefix decomposition bounds every finite sum of
individual tail probabilities by the initial weighted mass divided by b.
Taking the genuine nonnegative series proves local summability of all retained
individual exceedances, without assuming it in a limiting-instance interface.
-/
open MeasureTheory Set BoundedContinuousFunction
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting

private lemma finiteMeasure_mass_le_of_raw_le (μ ν : FiniteMeasure ℝ) (hle : (μ : Measure ℝ) ≤ (ν : Measure ℝ)) :
    μ.mass ≤ ν.mass := by
  apply ENNReal.coe_le_coe.mp
  simpa only [FiniteMeasure.ennreal_mass] using Measure.le_iff.mp hle Set.univ MeasurableSet.univ

/-- The extracted individuals have locally summable tails. -/
theorem reserve_extracted_individual_tail_sum_le (w : ℝ →ᵇ ℝ) (hw0 : ∀ x, 0 ≤ w x) (a : ℝ) (hw : Monotone w) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) (hρ : ∀ N, ρ N = continuousWeightedLaw (Q N) w + ρ (N+1))
    {b : ℝ} (hb : a < b) (hwb : 0 < w b) :
    (∑' i, (Q i : Measure ℝ) (Ioi b)) ≤ ENNReal.ofReal (((ρ 0).mass : ℝ) / w b) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro N
  let ν : FiniteMeasure ℝ := ∑ i ∈ Finset.range N, continuousWeightedLaw (Q i) w
  have hνle : (ν : Measure ℝ) ≤ (ρ 0 : Measure ℝ) := by
    apply Measure.le_iff.mpr
    intro s hs
    have he := congrArg (fun μ : FiniteMeasure ℝ => (μ : Measure ℝ) s) (continuousWeighted_residual_prefix_identity w Q ρ hρ N)
    rw [FiniteMeasure.toMeasure_add,Measure.add_apply] at he
    rw [he]
    exact le_add_of_nonneg_right (show (0 : ENNReal) ≤ (ρ N : Measure ℝ) s from bot_le)
  have hνmass : ν.mass ≤ (ρ 0).mass := finiteMeasure_mass_le_of_raw_le ν (ρ 0) hνle
  have hmap : reserveMarkIntensityAbove ν w a b hw hb hwb =
      ∑ i ∈ Finset.range N, (Q i).toFiniteMeasure.restrict (Ioi b) := by
    change reserveBandUnweightHom w a b hw hb hwb (∑ i ∈ Finset.range N, continuousWeightedLaw (Q i) w) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact reserveBand_continuousWeightedLaw _ w hw0 a hw hb hwb
  calc
    _ = (↑(∑ i ∈ Finset.range N, (Q i).toFiniteMeasure.restrict (Ioi b)) : Measure ℝ) Set.univ := by
      rw [FiniteMeasure.toMeasure_sum,Measure.finsetSum_apply]
      apply Finset.sum_congr rfl
      intro i _
      change (Q i : Measure ℝ) (Ioi b) = ((Q i : Measure ℝ).restrict (Ioi b)) Set.univ
      simp
    _ = (reserveMarkIntensityAbove ν w a b hw hb hwb : Measure ℝ) Set.univ := by rw [hmap]
    _ = reserveMarkIntensity ν w a (Ioi b) := by
      change ((reserveMarkIntensity ν w a).restrict (Ioi b)) Set.univ = _
      simp
    _ ≤ ENNReal.ofReal ((ν.mass : ℝ) / w b) := reserveMarkIntensity_tail_le ν w a hw hb hwb
    _ ≤ _ := ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hνmass hwb.le)

lemma reserve_extracted_individual_tail_sum_lt_top (w : ℝ →ᵇ ℝ) (hw0 : ∀ x, 0 ≤ w x) (a : ℝ) (hw : Monotone w) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) (hρ : ∀ N, ρ N = continuousWeightedLaw (Q N) w + ρ (N+1))
    {b : ℝ} (hb : a < b) (hwb : 0 < w b) :
    (∑' i, (Q i : Measure ℝ) (Ioi b)) < ⊤ :=
  (reserve_extracted_individual_tail_sum_le w hw0 a hw Q ρ hρ hb hwb).trans_lt ENNReal.ofReal_lt_top

end ProphetSecretary.Limiting
