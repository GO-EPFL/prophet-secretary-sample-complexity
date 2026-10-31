import ProphetSecretary.Limiting.ReserveBandResidual
import ProphetSecretary.Limiting.ReserveResidualAtoms
import ProphetSecretary.Limiting.ContinuousWeightedResidualConvergence
import ProphetSecretary.Limiting.ReserveIndividualTails

/-!
# The two ordered limits of actual residual upper-band measures

The first limit fixes the retained prefix and extracts the finite-instance
sequence. Only afterwards does the retained prefix tend to infinity. The
constructed intensity works at every common continuity level above the
reserve, and every retained tail sum is genuinely finite there.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting

noncomputable def weightOrderedBandResidual {n : ℕ} (P : Model.Instance n)
    (w : ℝ →ᵇ ℝ) (N : ℕ) (b : ℝ) : FiniteMeasure ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => N ≤ i.val),
    (weightOrderedMarginalLaw P w i).toFiniteMeasure.restrict (Ioi b)

lemma extractedContinuousWeightedResidual_mass_le_initial (w : ℝ →ᵇ ℝ)
    (Q : ℕ → ProbabilityMeasure ℝ) (ρ : ℕ → FiniteMeasure ℝ) :
    (extractedContinuousWeightedResidual w Q ρ).mass ≤ (ρ 0).mass := by
  have h := Measure.le_iff.mp (extractedContinuousWeightedResidual_le_initial w Q ρ) Set.univ MeasurableSet.univ
  apply ENNReal.coe_le_coe.mp
  simpa only [FiniteMeasure.ennreal_mass] using h

theorem continuousWeighted_positive_band_limits (H C : ℝ≥0) (a : ℝ) (w : ℝ →ᵇ ℝ)
    (hw0 : ∀ x, 0 ≤ w x) (hw : Monotone w) (hpos : ∀ b, a < b → 0 < w b)
    (Q : ℕ → ProbabilityMeasure ℝ) (ρ : ℕ → FiniteMeasure ℝ)
    (hρ : ∀ N, ρ N = continuousWeightedLaw (Q N) w + ρ (N+1))
    (hρcap : (ρ 0 : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) (hρmass : (ρ 0).mass ≤ C)
    (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (hconv : ∀ N, Tendsto (fun m => weightOrderedResidual (P m) w N) atTop (𝓝 (ρ N))) :
    let η := extractedContinuousWeightedResidual w Q ρ
    let μ := reserveMarkIntensity η w a
    μ (Ioc a H)ᶜ = 0 ∧
    (∀ b, a < b → μ (Ioi b) ≤ ENNReal.ofReal ((C : ℝ) / w b)) ∧
    (∀ b, a < b → (∑' i, (Q i : Measure ℝ) (Ioi b)) ≤ ENNReal.ofReal ((C : ℝ) / w b)) ∧
    ∀ (b : ℝ) (hb : a < b), (∀ i, (Q i : Measure ℝ) {b} = 0) → μ {b} = 0 →
      (∀ N, Tendsto (fun m => weightOrderedBandResidual (P m) w N b) atTop
        (𝓝 (reserveMarkIntensityAbove (ρ N) w a b hw hb (hpos b hb)))) ∧
      Tendsto (fun N => reserveMarkIntensityAbove (ρ N) w a b hw hb (hpos b hb)) atTop
        (𝓝 (reserveMarkIntensityAbove η w a b hw hb (hpos b hb))) := by
  let η := extractedContinuousWeightedResidual w Q ρ
  have hηmass : η.mass ≤ C := (extractedContinuousWeightedResidual_mass_le_initial w Q ρ).trans hρmass
  have hηcap := extractedContinuousWeightedResidual_supported_interval w Q ρ hρcap
  have hηlim : Tendsto ρ atTop (𝓝 η) := extractedContinuousWeightedResidual_tendsto w Q ρ hρ
  refine ⟨reserveMarkIntensity_supported_interval η w a hηcap,?_,?_,?_⟩
  · intro b hb
    exact (reserveMarkIntensity_tail_le η w a hw hb (hpos b hb)).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hηmass (hpos b hb).le))
  · intro b hb
    exact (reserve_extracted_individual_tail_sum_le w hw0 a hw Q ρ hρ hb (hpos b hb)).trans
      (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hρmass (hpos b hb).le))
  · intro b hb hQatom hμatom
    have hAtom := continuousWeighted_initial_atom_zero_of_common w Q ρ hρ hb (hpos b hb) hQatom hμatom
    constructor
    · intro N
      have ht := reserveMarkIntensityAbove_tendsto (hconv N) w a hw hb (hpos b hb)
        (continuousWeighted_prefixResidual_atom_zero w Q ρ hρ hAtom N)
      have heq : (fun m => reserveMarkIntensityAbove (weightOrderedResidual (P m) w N) w a b hw hb (hpos b hb)) =
          fun m => weightOrderedBandResidual (P m) w N b := by
        funext m
        exact reserveBand_weightOrderedResidual (P m) w hw0 a hw N hb (hpos b hb)
      rw [heq] at ht
      exact ht
    · apply reserveMarkIntensityAbove_tendsto hηlim w a hw hb (hpos b hb)
      have h := Measure.le_iff.mp (extractedContinuousWeightedResidual_le_initial w Q ρ) {b} (measurableSet_singleton b)
      rw [hAtom] at h
      exact le_antisymm h bot_le

end ProphetSecretary.Limiting
