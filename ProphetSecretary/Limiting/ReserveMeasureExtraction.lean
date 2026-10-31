import ProphetSecretary.Limiting.ReserveWeightExpectation
import ProphetSecretary.Limiting.ContinuousWeightedExtraction
import ProphetSecretary.Limiting.WeightedOrderedTails

/-!
# Actual measure-data extraction under the offer cap alone

A genuine subsequence determines a terminal reserve, and a constructed
continuous ordering weight controls all offers strictly above that reserve.
No bound on total first moments is assumed. The extracted marginals remain
laws of the original offers, after an actual permutation and zero padding.
This proves measure extraction and uniform residual rarity; convergence of
online policies, scalar values and score expectations is separate.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting

theorem exists_cap_bounded_reserve_measure_data (H : ℝ≥0) (sizes : ℕ → ℕ)
    (P : ∀ m, Model.Instance (sizes m)) (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ (H : ℝ)) :
    ∃ (a : ℝ) (w : ℝ →ᵇ ℝ) (Q : ℕ → ProbabilityMeasure ℝ)
      (ρ : ℕ → FiniteMeasure ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧ a ∈ Icc (0 : ℝ) H ∧ (∀ x, 0 ≤ w x) ∧ Monotone w ∧
      (∀ x, x ≤ a → w x = 0) ∧ (∀ x, a < x → 0 < w x) ∧
      (∀ m, (∑ i, ∫ x, w x ∂(P (φ m)).law i) ≤ 1) ∧
      (∀ i, (Q i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) ∧
      (∀ N, (ρ N).mass ≤ 1) ∧ (∀ N, (ρ N : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) ∧
      (∀ i, Tendsto (fun m => weightOrderedPaddedLaw (P (φ m)) w i) atTop (𝓝 (Q i))) ∧
      (∀ N, Tendsto (fun m => weightOrderedResidual (P (φ m)) w N) atTop (𝓝 (ρ N))) ∧
      (∀ N, ρ N = continuousWeightedLaw (Q N) w + ρ (N+1)) ∧
      (∀ x, 0 ≤ x → x < a → Tendsto (fun m => extendedTailCount (P (φ m)) x) atTop (𝓝 ⊤)) ∧
      ∀ b, a < b → ∀ ε > (0 : ℝ), ∃ N : ℕ, ∀ m j, N ≤ j →
        (weightOrderedPaddedLaw (P (φ m)) w j : Measure ℝ).real (Ioi b) < ε := by
  obtain ⟨a,ψ,b,B,hψ,ha,_hb,hba,hblim,hB,hbound,hbelow⟩ :=
    exists_finite_instance_reserve_cutoffs H.coe_nonneg sizes P hcap
  let w := reserveOrderingWeight b B
  have hw : ∀ x, 0 ≤ w x := reserveOrderingWeight_nonneg b B hB
  have hwMono : Monotone w := reserveOrderingWeight_monotone b B hB
  have hwZero : ∀ x, x ≤ a → w x = 0 := fun _ hx => reserveOrderingWeight_zero b B hB (fun k => (hba k).1) hx
  have hwPos : ∀ x, a < x → 0 < w x := fun _ hx => reserveOrderingWeight_pos b B hB hblim hx
  have hw0 : w 0 = 0 := hwZero 0 ha.1
  have hWeight (m : ℕ) : (∑ i, ∫ x, w x ∂(P (ψ m)).law i) ≤ 1 :=
    sum_integral_reserveOrderingWeight_le_one (P (ψ m)) b B hB (fun k => hbound k m)
  obtain ⟨Q,ρ,χ,hχ,hQ,hρmass,hρcap,hconvQ,hconvρ,hρ⟩ :=
    exists_continuousWeighted_measure_data H 1 w hw hw0 (fun m => sizes (ψ m)) (fun m => P (ψ m))
      (fun m => hcap (ψ m)) hWeight
  refine ⟨a,w,Q,ρ,ψ ∘ χ,hψ.comp hχ,ha,hw,hwMono,hwZero,hwPos,
    (fun m => hWeight (χ m)),hQ,hρmass,hρcap,hconvQ,hconvρ,hρ,?_,?_⟩
  · intro x hx0 hxa
    exact (hbelow x hx0 hxa).comp hχ.tendsto_atTop
  · intro x hax ε hε
    exact weightOrdered_residual_uniformly_rare (fun m => sizes (ψ (χ m))) (fun m => P (ψ (χ m)))
      w hw hw0 (fun m => hWeight (χ m)) (hwPos x hax) (fun y hxy => hwMono hxy.le) hε

end ProphetSecretary.Limiting
