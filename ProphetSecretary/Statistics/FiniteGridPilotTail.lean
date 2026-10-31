import ProphetSecretary.Statistics.FiniteGridPilotWeight
import ProphetSecretary.Statistics.FixedWeightPilotTail
import ProphetSecretary.Probability.ConvexPilotTail

/-!
# The actual finite-grid pilot's selected-weight tail

At every true level s above a reference weight's gap, the selected pilot
weight has a bad true gap only if the empirical reference is large or one
of two deterministic boundary weights has an unusually small empirical gap.
This is the probability inequality immediately preceding `eq:bayes-pilot`.
The pilot is the measurable finite-table construction, not an assumed selector.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n k : ℕ} [NeZero k]

theorem finiteGridPilotWeight_true_gap_tail (P : Instance n) (G : Finset ℝ)
    (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {lo hi δ : ℝ} (hδ : 0 < δ) (h0 : 0 ≤ lo) (h1 : hi ≤ 1) (hlohi : lo ≤ hi)
    (hInterior : Icc lo hi ⊆ Icc δ (1-δ))
    {a s : ℝ} (ha : a∈Icc lo hi) (hFa : normalizedScalarGap P a ≤ s) :
    (P.trainingCoordinateLaw k).real {y | s < normalizedScalarGap P
      (finiteGridPilotWeight G lo hi h0 h1 hlohi y)} ≤
    (P.trainingCoordinateLaw k).real {y | s/2 < normalizedScalarGap
      (totalEmpiricalInstance (reservoirCoordinates.symm y)) a} +
    2*(Real.exp (-((k : ℝ)*s/(64*pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)))) +
      min 1 (16/((k : ℝ)^2*s^2))) := by
  let F := normalizedScalarGap P
  let H := fun y : (Fin n × Fin k) → ℝ =>
    normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y))
  let b := finiteGridPilotWeight (n := n) (k := k) G lo hi h0 h1 hlohi
  let q := Real.exp (-((k : ℝ)*s/(64*pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)))) +
    min 1 (16/((k : ℝ)^2*s^2))
  have hq : 0 ≤ q := add_nonneg (Real.exp_pos _).le (le_min zero_le_one (by positivity))
  have hP := P.integrable_maximum_of_bounded hcap
  have hSubset : Icc lo hi ⊆ Icc (0 : ℝ) 1 := Icc_subset_Icc h0 h1
  have hF : ConvexOn ℝ (Icc lo hi) F :=
    (normalizedScalarGap_convex P hP).subset hSubset (convex_Icc lo hi)
  have hFc : ContinuousOn F (Icc lo hi) := (normalizedScalarGap_continuousOn P hP).mono hSubset
  have hH : ∀ᵐ y ∂P.trainingCoordinateLaw k, ConvexOn ℝ (Icc lo hi) (H y) := by
    exact Eventually.of_forall fun y =>
      (normalizedScalarGap_convex _ (totalEmpiricalInstance_integrable _)).subset hSubset (convex_Icc lo hi)
  have hb : ∀ᵐ y ∂P.trainingCoordinateLaw k, b y∈Icc lo hi :=
    Eventually.of_forall fun y => finiteGridPilotWeight_mem G lo hi h0 h1 hlohi y
  have hMin : ∀ᵐ y ∂P.trainingCoordinateLaw k, H y (b y) ≤ H y a :=
    finiteGridPilotWeight_isMin_ae P G hG lo hi h0 h1 hlohi a ha
  have hTail : ∀ x∈Icc lo hi, F x = s → (P.trainingCoordinateLaw k).real {y | H y x ≤ s/2} ≤ q := by
    intro x hx hFx
    have h := P.empirical_normalizedGap_lower_tail (k := k) hcap hδ (hInterior hx)
    change normalizedScalarGap P x = s at hFx
    rw [hFx] at h
    exact h
  exact convex_pilot_tail hF hFc ha hFa hq H b hH hb hMin hTail

end ProphetSecretary.Statistics
