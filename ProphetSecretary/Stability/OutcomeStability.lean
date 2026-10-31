import ProphetSecretary.Stability.OutcomeBounds
import ProphetSecretary.Stability.Modulus

/-!
# Uniform stability of nearly optimal finite policies

This is `thm:outcome-stability` and `eq:ps-uniform-outcome-stability`. The modulus
is chosen before the instance, the normalized interior weights, and the competing
randomized policy. Its hypotheses are only the common offer cap and the finite
positive-level tail-count bounds. Both policies use the same complete offer vector
and clocks, with an arbitrary independent seed for the competing policy.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Model

/-- An index for every policy and normalized interior weight pair in a family. -/
structure StabilityComparison {α : Type*} (n : α → ℕ) (δ : ℝ) where
  instanceIndex : α
  rewardWeight : ℝ
  durationWeight : ℝ
  reward_interior : δ ≤ rewardWeight
  duration_interior : δ ≤ durationWeight
  normalized : rewardWeight + durationWeight = 1
  competitor : RandomizedPolicy (n instanceIndex)

/-- Finite `thm:outcome-stability`, with an explicit finite tail profile. There is
no bound on the number of variables or on the competing policy's use of history. -/
theorem finite_outcome_stability_with_profile {α : Type*} (n : α → ℕ)
    (P : ∀ a, Instance (n a)) {H δ : ℝ} (hH : 0 ≤ H) (hδ : 0 < δ)
    (hbound : ∀ a i, ∀ᵐ x ∂(P a).law i, x ≤ H) (L : ℝ → ℝ)
    (hL : ∀ d, 0 < d → 0 ≤ L d)
    (htail : ∀ a d, 0 < d → (P a).tailCount d ≤ L d) :
    ∃ ω : ℝ → ℝ, (∀ t, 0 ≤ ω t ∧ ω t ≤ H + 1) ∧ Monotone ω ∧ ω 0 = 0 ∧
      Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
      (∀ a w c, δ ≤ w → δ ≤ c → w + c = 1 → ∀ π : RandomizedPolicy (n a),
        π.expectedOutcomeError (P a) w c ≤
          ω (optimalScalarValue (P a) w c - π.scalarObjective (P a) w c)) ∧
      (∀ t < 0, ω t = 0) := by
  let E : StabilityComparison n δ → ℝ := fun i =>
    i.competitor.expectedOutcomeError (P i.instanceIndex) i.rewardWeight i.durationWeight
  let r : StabilityComparison n δ → ℝ := fun i =>
    optimalScalarValue (P i.instanceIndex) i.rewardWeight i.durationWeight -
      i.competitor.scalarObjective (P i.instanceIndex) i.rewardWeight i.durationWeight
  let K : ℝ → ℝ := fun b => uniformStabilityBandConstant H δ b (L (b / 4)) (L (b / 2))
  have hE : ∀ i, E i ∈ Icc (0 : ℝ) (H + 1) := by
    intro i
    exact ⟨i.competitor.expectedOutcomeError_nonnegative _ _ _,
      i.competitor.expectedOutcomeError_le_bound _ hH (hbound i.instanceIndex)
        (hδ.trans_le i.reward_interior) (hδ.le.trans i.duration_interior)⟩
  have hr : ∀ i, 0 ≤ r i := by
    intro i
    exact sub_nonneg.mpr (scalarObjective_le_optimal _ _
      ((P i.instanceIndex).integrable_maximum_of_bounded (hbound i.instanceIndex))
      (hδ.le.trans i.reward_interior) (hδ.le.trans i.duration_interior))
  have hK : ∀ b, 0 < b → 0 ≤ K b := by
    intro b hb
    exact (uniformStabilityBandConstant_positive hH hδ hb
      (hL (b / 4) (by positivity)) (hL (b / 2) (by positivity))).le
  have hEstimate : ∀ i b, b ∈ Ioo (0 : ℝ) (δ / 2) → ∀ d, 0 < d → ∀ e,
      e ∈ Ioc (0 : ℝ) (δ * b / 4) →
      E i ≤ (H + 1) * (r i / e + K b * e) + 2 * b / δ + d + (2 * H * b / δ) * L d := by
    intro i b hb d hd e he
    have hb0 := hb.1
    exact i.competitor.expectedOutcomeError_le_uniform _ hH (hbound i.instanceIndex)
      hδ i.reward_interior i.duration_interior i.normalized hb.1 hb.2 hd.le he.1 he.2
      (htail i.instanceIndex (b / 4) (by positivity))
      (htail i.instanceIndex (b / 2) (by positivity)) (htail i.instanceIndex d hd)
  obtain ⟨ω, hω, hmono, hzero, hlim, herror, hneg⟩ :=
    ProphetSecretary.Stability.exists_radiusModulus_of_finite_estimate E r hH hδ hE hr L K hL hK hEstimate
  refine ⟨ω, hω, hmono, hzero, hlim, ?_, hneg⟩
  intro a w c hw hc hsum π
  exact herror ⟨a, w, c, hw, hc, hsum, π⟩

/-- The manuscript's finite-family formulation: a finite uniform tail bound at each
positive level suffices. These bounds are chosen once for the entire family. -/
theorem finite_outcome_stability {α : Type*} (n : α → ℕ)
    (P : ∀ a, Instance (n a)) {H δ : ℝ} (hH : 0 ≤ H) (hδ : 0 < δ)
    (hbound : ∀ a i, ∀ᵐ x ∂(P a).law i, x ≤ H)
    (htail : ∀ d, 0 < d → ∃ L : ℝ, ∀ a, (P a).tailCount d ≤ L) :
    ∃ ω : ℝ → ℝ, (∀ t, 0 ≤ ω t ∧ ω t ≤ H + 1) ∧ Monotone ω ∧ ω 0 = 0 ∧
      Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
      (∀ a w c, δ ≤ w → δ ≤ c → w + c = 1 → ∀ π : RandomizedPolicy (n a),
        π.expectedOutcomeError (P a) w c ≤
          ω (optimalScalarValue (P a) w c - π.scalarObjective (P a) w c)) ∧
      (∀ t < 0, ω t = 0) := by
  classical
  have hchoose : ∀ d : ℝ, ∃ L : ℝ, 0 ≤ L ∧ ∀ a, 0 < d → (P a).tailCount d ≤ L := by
    intro d
    by_cases hd : 0 < d
    · obtain ⟨L, hL⟩ := htail d hd
      exact ⟨max L 0, le_max_right _ _, fun a _ => (hL a).trans (le_max_left _ _)⟩
    · exact ⟨0, le_rfl, fun _ h => False.elim (hd h)⟩
  choose L hL ht using hchoose
  exact finite_outcome_stability_with_profile n P hH hδ hbound L (fun d _ => hL d)
    (fun a d hd => ht d a hd)

end ProphetSecretary.Model
