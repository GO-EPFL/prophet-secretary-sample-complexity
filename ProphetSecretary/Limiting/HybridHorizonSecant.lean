import ProphetSecretary.Limiting.HybridDurationFloor

/-!
# Strict remaining-horizon secants without assuming an optimizer

On a positive scalar band, every sufficiently accurate approximate optimizer
has the proved positive normalized-duration floor. Keep its intensity fixed
while increasing duration weight, then use actual intensity monotonicity.
Letting its scalar error tend to zero yields the secant bound for the actual
full-policy supremum. The variable u denotes remaining horizon throughout.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

/-- The positive secant constant is explicit, uniform in retained dimension,
and does not assert existence of an optimizing policy. -/
theorem FiniteIntensityHybridInstance.continuationValue_secant_lower
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    {w c b : ℝ} (hw : 0 < w) (hc : 0 < c) (hb : 0 < b)
    {u v : ℝ≥0} (huv : u ≤ v) (hv : v ≤ 1)
    (hBand : b ≤ B.continuationValue w c u) :
    c*B.durationBandFloor w c b*((v : ℝ)-(u : ℝ)) ≤
      B.continuationValue w c v-B.continuationValue w c u := by
  have hu : u ≤ 1 := huv.trans hv
  have hΔ : 0 ≤ (v : ℝ)-(u : ℝ) := sub_nonneg.mpr (by exact_mod_cast huv)
  apply le_of_forall_pos_le_add
  intro δ hδ
  let ε := min δ (b/4)
  have hε : 0 < ε := lt_min hδ (by positivity)
  have hεδ : ε ≤ δ := min_le_left _ _
  have hεb : ε ≤ b/4 := min_le_right _ _
  obtain ⟨π,hNear⟩ := (B.remainingHorizon u).exists_policy_near_value w (c*(u : ℝ)) hε
  have hObjective : 3*b/4 ≤ π.scalarObjective (B.remainingHorizon u) w (c*(u : ℝ)) := by
    change b ≤ (B.remainingHorizon u).optimalScalarValue w (c*(u : ℝ)) at hBand
    linarith
  have hT := π.durationBandFloor_le_of_objective B ha hw hc hb hu hObjective
  have hWeight : c*((v : ℝ)-(u : ℝ))*B.durationBandFloor w c b ≤
      c*((v : ℝ)-(u : ℝ))*π.expectedDuration (B.remainingHorizon u) :=
    mul_le_mul_of_nonneg_left hT (mul_nonneg hc.le hΔ)
  have hRaised : π.scalarObjective (B.remainingHorizon u) w (c*(u : ℝ))+
      c*((v : ℝ)-(u : ℝ))*π.expectedDuration (B.remainingHorizon u) =
      π.scalarObjective (B.remainingHorizon u) w (c*(v : ℝ)) := by
    rw [π.scalarObjective_eq,π.scalarObjective_eq]
    ring
  have hUpper : π.scalarObjective (B.remainingHorizon u) w (c*(v : ℝ)) ≤ B.continuationValue w c v :=
    ((B.remainingHorizon u).scalarObjective_le_value π w (c*(v : ℝ))).trans
      (B.remainingHorizon_value_mono_intensity huv hw.le (mul_nonneg hc.le v.property))
  change c*B.durationBandFloor w c b*((v : ℝ)-(u : ℝ)) ≤
    (B.remainingHorizon v).optimalScalarValue w (c*(v : ℝ))-
      (B.remainingHorizon u).optimalScalarValue w (c*(u : ℝ))+δ
  change π.scalarObjective (B.remainingHorizon u) w (c*(v : ℝ)) ≤
    (B.remainingHorizon v).optimalScalarValue w (c*(v : ℝ)) at hUpper
  nlinarith [hNear,hRaised,hWeight,hUpper]

/-- Positive continuation grows strictly with remaining horizon. Therefore,
on a fixed positive band it decreases strictly with elapsed time. -/
theorem FiniteIntensityHybridInstance.continuationValue_lt_of_lt
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    {w c b : ℝ} (hw : 0 < w) (hc : 0 < c) (hb : 0 < b)
    {u v : ℝ≥0} (huv : u < v) (hv : v ≤ 1)
    (hBand : b ≤ B.continuationValue w c u) :
    B.continuationValue w c u < B.continuationValue w c v := by
  have hS := B.continuationValue_secant_lower ha hw hc hb huv.le hv hBand
  have hPos : 0 < c*B.durationBandFloor w c b*((v : ℝ)-(u : ℝ)) :=
    mul_pos (mul_pos hc (B.durationBandFloor_pos hw.le hc hb)) (sub_pos.mpr (by exact_mod_cast huv))
  linarith

end ProphetSecretary.Limiting
