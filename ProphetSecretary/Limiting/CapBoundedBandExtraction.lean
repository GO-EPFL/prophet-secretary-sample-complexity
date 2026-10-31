import ProphetSecretary.Limiting.ReserveMeasureExtraction
import ProphetSecretary.Limiting.ContinuousWeightedBandExtraction
import ProphetSecretary.Limiting.WeightedOrderedSquareTails

/-!
# Cap-only extraction of individuals and locally finite residual intensity

This is the measure-data part of `lem:compact-extract` under its actual cap-only
hypothesis. It constructs the terminal reserve, a continuous ordering weight,
all retained marginal laws and the positive locally finite residual intensity.
Both limits of actual upper-band residual measures are explicit, at every
common continuity level. Divergence below the reserve is preserved on the same
subsequence. Policy, scalar-value and likelihood-score convergence are not
consequences of these measure statements alone and remain separate results.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting

theorem exists_cap_bounded_positive_band_data (H : ℝ≥0) (sizes : ℕ → ℕ)
    (P : ∀ m, Model.Instance (sizes m)) (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ (H : ℝ)) :
    ∃ (a : ℝ) (w : ℝ →ᵇ ℝ) (hw : Monotone w) (hpos : ∀ b, a < b → 0 < w b)
      (Q : ℕ → ProbabilityMeasure ℝ) (ρ : ℕ → FiniteMeasure ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧ a ∈ Icc (0 : ℝ) H ∧ (∀ x, 0 ≤ w x) ∧ (∀ x, x ≤ a → w x = 0) ∧
      (∀ i, (Q i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) ∧ (∀ N, (ρ N).mass ≤ 1) ∧
      (∀ N, (ρ N : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) ∧
      (∀ i, Tendsto (fun m => weightOrderedPaddedLaw (P (φ m)) w i) atTop (𝓝 (Q i))) ∧
      (∀ N, Tendsto (fun m => weightOrderedResidual (P (φ m)) w N) atTop (𝓝 (ρ N))) ∧
      (∀ N, ρ N = continuousWeightedLaw (Q N) w + ρ (N+1)) ∧
      (∀ x, 0 ≤ x → x < a → Tendsto (fun m => extendedTailCount (P (φ m)) x) atTop (𝓝 ⊤)) ∧
      let η := extractedContinuousWeightedResidual w Q ρ
      let μ := reserveMarkIntensity η w a
      μ (Ioc a H)ᶜ = 0 ∧
      (∀ b, a < b → μ (Ioi b) ≤ ENNReal.ofReal (1 / w b)) ∧
      (∀ b, a < b → (∑' i, (Q i : Measure ℝ) (Ioi b)) ≤ ENNReal.ofReal (1 / w b)) ∧
      (∀ (b : ℝ) (hb : a < b), (∀ i, (Q i : Measure ℝ) {b} = 0) → μ {b} = 0 →
        (∀ N, Tendsto (fun m => weightOrderedBandResidual (P (φ m)) w N b) atTop
          (𝓝 (reserveMarkIntensityAbove (ρ N) w a b hw hb (hpos b hb)))) ∧
        Tendsto (fun N => reserveMarkIntensityAbove (ρ N) w a b hw hb (hpos b hb)) atTop
          (𝓝 (reserveMarkIntensityAbove η w a b hw hb (hpos b hb)))) ∧
      (∀ b, a < b → ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m j, N ≤ j →
        (weightOrderedPaddedLaw (P (φ m)) w j : Measure ℝ).real (Ioi b) < ε) ∧
      ∀ b, a < b → ∀ m N,
        (∑ i ∈ Finset.univ.filter (fun i : Fin (sizes (φ m)) => N ≤ i.val),
          (weightOrderedPaddedLaw (P (φ m)) w i.val : Measure ℝ).real (Ioi b)^2) ≤
          1 / ((w b)^2 * (N+1 : ℕ)) := by
  obtain ⟨a,w,Q,ρ,φ,hφ,ha,hw0,hw,hzero,hpos,hWeight,hQ,hρmass,hρcap,hconvQ,hconvρ,hρ,hbelow,hrare⟩ :=
    exists_cap_bounded_reserve_measure_data H sizes P hcap
  have hbands := continuousWeighted_positive_band_limits H 1 a w hw0 hw hpos Q ρ hρ (hρcap 0) (hρmass 0)
    (fun m => sizes (φ m)) (fun m => P (φ m)) hconvρ
  refine ⟨a,w,hw,hpos,Q,ρ,φ,hφ,ha,hw0,hzero,hQ,hρmass,hρcap,hconvQ,hconvρ,hρ,hbelow,
    hbands.1,hbands.2.1,hbands.2.2.1,hbands.2.2.2,hrare,?_⟩
  intro b hb m N
  exact weightOrderedPaddedLaw_residual_tail_square_sum_le (P (φ m)) w hw0 (hzero 0 ha.1)
    (hWeight m) (hpos b hb) (fun x hbx => hw hbx.le) N

end ProphetSecretary.Limiting
