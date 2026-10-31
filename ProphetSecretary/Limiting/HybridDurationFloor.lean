import ProphetSecretary.Limiting.HybridRewardTail
import ProphetSecretary.Limiting.HybridHorizon

/-!
# A dimension-independent duration floor on positive continuation bands

The band parameter b is a scalar value level; its offer cutoff is b/(4w).
All times in expectedDuration are normalized to the remaining horizon. The
terminal reward is zero, as in `lem:canonical-limit`. No optimizer is assumed:
the bound applies to every policy with objective at least 3b/4.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma FiniteIntensityHybridInstance.remainingHorizon_tailCount_le (B : FiniteIntensityHybridInstance n)
    {u : ℝ≥0} (hu : u ≤ 1) (d : ℝ) : (B.remainingHorizon u).tailCount d ≤ B.tailCount d := by
  change B.individuals.tailCount d+(u • (B.intensity : Measure ℝ)).real (Ioi d) ≤ _
  rw [measureReal_nnreal_smul_apply]
  apply add_le_add le_rfl
  change (u : ℝ)*(B.intensity : Measure ℝ).real (Ioi d) ≤ (B.intensity : Measure ℝ).real (Ioi d)
  have huR : (u : ℝ) ≤ 1 := by exact_mod_cast hu
  simpa only [one_mul] using mul_le_mul_of_nonneg_right huR (measureReal_nonneg (μ := (B.intensity : Measure ℝ)) (s := Ioi d))

noncomputable def FiniteIntensityHybridInstance.durationBandCoefficient (B : FiniteIntensityHybridInstance n)
    (w c b : ℝ) : ℝ := 2*w*(B.cap : ℝ)*B.tailCount (b/(4*w))+c

noncomputable def FiniteIntensityHybridInstance.durationBandFloor (B : FiniteIntensityHybridInstance n)
    (w c b : ℝ) : ℝ := b/(2*B.durationBandCoefficient w c b)

lemma FiniteIntensityHybridInstance.durationBandCoefficient_pos (B : FiniteIntensityHybridInstance n)
    {w c b : ℝ} (hw : 0 ≤ w) (hc : 0 < c) : 0 < B.durationBandCoefficient w c b := by
  unfold durationBandCoefficient
  have h := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hw) B.cap.property)
    (B.tailCount_nonnegative (b/(4*w)))
  exact add_pos_of_nonneg_of_pos h hc

lemma FiniteIntensityHybridInstance.durationBandFloor_pos (B : FiniteIntensityHybridInstance n)
    {w c b : ℝ} (hw : 0 ≤ w) (hc : 0 < c) (hb : 0 < b) : 0 < B.durationBandFloor w c b :=
  div_pos hb (mul_pos (by norm_num) (B.durationBandCoefficient_pos hw hc))

lemma RandomizedHybridPolicy.scalarObjective_le_durationBand
    (π : RandomizedHybridPolicy n) (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    {w c b : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (hb : 0 ≤ b) {u : ℝ≥0} (hu : u ≤ 1) :
    π.scalarObjective (B.remainingHorizon u) w (c*(u : ℝ)) ≤
      b/4+π.expectedDuration (B.remainingHorizon u)*B.durationBandCoefficient w c b := by
  let d := b/(4*w)
  have hd : 0 ≤ d := div_nonneg hb (by positivity)
  have hwd : w*d = b/4 := by dsimp [d]; field_simp [hw.ne']
  have hR := π.expectedReward_le_cutoff_add_tailCount (B.remainingHorizon u) hd
    (show ((B.remainingHorizon u).terminal : ℝ) ≤ d by change (B.terminal : ℝ) ≤ d; simpa only [ha,NNReal.coe_zero] using hd)
  have hT := π.expectedDuration_nonnegative (B.remainingHorizon u)
  have hL := B.remainingHorizon_tailCount_le hu d
  have hR' : π.expectedReward (B.remainingHorizon u) ≤ d+
      2*π.expectedDuration (B.remainingHorizon u)*(B.cap : ℝ)*B.tailCount d :=
    hR.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hL (by positivity)))
  have hU : c*(u : ℝ)*π.expectedDuration (B.remainingHorizon u) ≤
      c*π.expectedDuration (B.remainingHorizon u) := by
    have huR : (u : ℝ) ≤ 1 := by exact_mod_cast hu
    simpa only [mul_one] using mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left huR hc) hT
  rw [π.scalarObjective_eq]
  calc
    _ ≤ w*(d+2*π.expectedDuration (B.remainingHorizon u)*(B.cap : ℝ)*B.tailCount d)+
        c*π.expectedDuration (B.remainingHorizon u) :=
      add_le_add (mul_le_mul_of_nonneg_left hR' hw.le) hU
    _ = b/4+π.expectedDuration (B.remainingHorizon u)*B.durationBandCoefficient w c b := by
      unfold FiniteIntensityHybridInstance.durationBandCoefficient
      dsimp only [d] at hwd ⊢
      nlinarith [hwd]

/-- A positive scalar band forces normalized duration at least the explicit
floor b/[2(2wHL_{b/(4w)}+c)]. This applies to epsilon-optimal policies too. -/
theorem RandomizedHybridPolicy.durationBandFloor_le_of_objective
    (π : RandomizedHybridPolicy n) (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    {w c b : ℝ} (hw : 0 < w) (hc : 0 < c) (hb : 0 < b) {u : ℝ≥0} (hu : u ≤ 1)
    (hObj : 3*b/4 ≤ π.scalarObjective (B.remainingHorizon u) w (c*(u : ℝ))) :
    B.durationBandFloor w c b ≤ π.expectedDuration (B.remainingHorizon u) := by
  have hUpper := π.scalarObjective_le_durationBand B ha hw hc.le hb.le hu
  have hK := B.durationBandCoefficient_pos hw.le hc (b := b)
  unfold FiniteIntensityHybridInstance.durationBandFloor
  apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hK)).mpr
  nlinarith [hObj,hUpper]

end ProphetSecretary.Limiting
