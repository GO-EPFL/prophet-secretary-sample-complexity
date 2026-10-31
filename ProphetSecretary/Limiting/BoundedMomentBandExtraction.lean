import ProphetSecretary.Limiting.PositiveBandResidual
import ProphetSecretary.Limiting.WeightedResidualAtoms
import ProphetSecretary.Limiting.OrderedResidualTails
import ProphetSecretary.Limiting.ExtractedIndividualTails

/-!
# Positive-band measure extraction for bounded-total-first-moment sequences

The actual ordered finite marginals and residual aggregate measures converge
on one subsequence. The residual limits are unweighted above each common
positive continuity level; only afterwards does the retained-prefix size tend
to infinity. A genuinely positive, sigma-finite intensity, locally finite above
zero, is constructed by subtraction and reciprocal weighting. No policy or
value convergence, or general H-only terminal-reserve extraction, is claimed.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting

noncomputable def orderedPositiveResidual {n : ℕ} (P : Model.Instance n) (N : ℕ) (b : ℝ) : FiniteMeasure ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => N ≤ i.val),
    (orderedMarginalLaw P i).toFiniteMeasure.restrict (Ioi b)

lemma extractedWeightedResidual_mass_le_initial (H : ℝ≥0) (Q : ℕ → ProbabilityMeasure ℝ) (ρ : ℕ → FiniteMeasure ℝ) :
    (extractedWeightedResidual H Q ρ).mass ≤ (ρ 0).mass := by
  have h := Measure.le_iff.mp (extractedWeightedResidual_le_initial H Q ρ) Set.univ MeasurableSet.univ
  apply ENNReal.coe_le_coe.mp
  simpa only [FiniteMeasure.ennreal_mass] using h

/-- This is the positive-band measure-data part of compact extraction under
S≤S₀, with both limit orders and actual finite input residuals explicit. -/
theorem exists_boundedMoment_positive_band_data (H S₀ : ℝ≥0) (sizes : ℕ → ℕ)
    (P : ∀ m, Model.Instance (sizes m))
    (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ (H : ℝ))
    (hS : ∀ m, (P m).totalFirstMoment ≤ (S₀ : ℝ)) :
    ∃ (Q : ℕ → ProbabilityMeasure ℝ) (ρ : ℕ → FiniteMeasure ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧ (∀ i, (Q i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) ∧
      (∀ i, Tendsto (fun m => orderedPaddedLaw (P (φ m)) i) atTop (𝓝 (Q i))) ∧
      (∀ N, ρ N = valueWeightedLaw (Q N) H + ρ (N+1)) ∧
      let η := extractedWeightedResidual H Q ρ
      let μ := positiveMarkIntensity η
      μ (Ioc (0 : ℝ) H)ᶜ = 0 ∧
      (∀ b > (0 : ℝ), μ (Ioi b) ≤ ENNReal.ofReal ((S₀ : ℝ) / b)) ∧
      (∀ b > (0 : ℝ), (∑' i, (Q i : Measure ℝ) (Ioi b)) ≤ ENNReal.ofReal ((S₀ : ℝ) / b)) ∧
      (∀ (b : ℝ) (hb : 0 < b), (∀ i, (Q i : Measure ℝ) {b} = 0) → μ {b} = 0 →
        (∀ N, Tendsto (fun m => orderedPositiveResidual (P (φ m)) N b) atTop
          (𝓝 (positiveMarkIntensityAbove (ρ N) b hb))) ∧
        Tendsto (fun N => positiveMarkIntensityAbove (ρ N) b hb) atTop
          (𝓝 (positiveMarkIntensityAbove η b hb))) ∧
      ∀ b > (0 : ℝ), ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m j, N ≤ j →
        (orderedPaddedLaw (P (φ m)) j : Measure ℝ).real (Ioi b) < ε := by
  obtain ⟨Q,ρ,φ,hφ,hQ,hρmass,hρcap,hconvQ,hconvρ,hρ⟩ := exists_boundedMoment_measure_data H S₀ sizes P hcap hS
  let η := extractedWeightedResidual H Q ρ
  have hηmass : η.mass ≤ S₀ := (extractedWeightedResidual_mass_le_initial H Q ρ).trans (hρmass 0)
  have hηcap : (η : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0 := extractedWeightedResidual_supported_interval H Q ρ (hρcap 0)
  have hηlim : Tendsto ρ atTop (𝓝 η) := extractedWeightedResidual_tendsto H Q ρ hρ
  refine ⟨Q,ρ,φ,hφ,hQ,hconvQ,hρ,?_,?_,?_,?_,?_⟩
  · exact positiveMarkIntensity_supported_interval η hηcap
  · intro b hb
    apply (positiveMarkIntensity_tail_le η hb).trans
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_right hηmass hb.le
  · intro b hb
    apply (extracted_individual_tail_sum_le H Q ρ hρ hQ hb).trans
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_right (hρmass 0) hb.le
  · intro b hb hQatom hμatom
    have hAtom := extracted_initial_atom_zero_of_common H Q ρ hρ hb hQatom hμatom
    constructor
    · intro N
      have ht := positiveMarkIntensityAbove_tendsto (hconvρ N) hb (extracted_prefixResidual_atom_zero H Q ρ hρ hAtom N)
      have heq : (fun m => positiveMarkIntensityAbove (orderedWeightedResidual (P (φ m)) H N) b hb) =
          fun m => orderedPositiveResidual (P (φ m)) N b := by
        funext m
        exact positiveBand_orderedWeightedResidual (P (φ m)) H (hcap (φ m)) N hb
      rw [heq] at ht
      exact ht
    · exact positiveMarkIntensityAbove_tendsto hηlim hb (extracted_weightedResidual_atom_zero H Q ρ hAtom)
  · intro b hb
    exact orderedPaddedLaw_residual_tail_uniform (fun m => sizes (φ m)) (fun m => P (φ m))
      (fun m => (P (φ m)).integrable_maximum_of_bounded (hcap (φ m))) (fun m => hS (φ m)) hb

end ProphetSecretary.Limiting
