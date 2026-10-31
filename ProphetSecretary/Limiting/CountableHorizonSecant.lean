import ProphetSecretary.Limiting.CountablePositiveTail
import ProphetSecretary.Limiting.CountableContinuationApproximation
import ProphetSecretary.Limiting.CountableFiniteMask
import ProphetSecretary.Limiting.HybridHorizonSecant

/-!
# Strict positive-band secants for actual countable continuation values

A half-sized value band survives finite approximation. Its explicit duration
floor uses only the original positive-level tail count, so the constant is
uniform over all unseen masks and retained dimensions. The parameter is
remaining horizon; elapsed-time inequalities have the opposite sign.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal Classical

namespace ProphetSecretary.Limiting.CountableInstance

lemma continuationBandLevel_above_reserve (B : CountableInstance) (hZero : B.terminal = 0)
    {w b : ℝ} (hw : 0 < w) (hb : 0 < b) : (B.terminal : ℝ) < b/(8*w) := by
  rw [hZero,NNReal.coe_zero]
  exact div_pos hb (mul_pos (by norm_num) hw)

noncomputable def continuationBandCoefficient (B : CountableInstance) (hZero : B.terminal = 0)
    (w c b : ℝ) (hw : 0 < w) (hb : 0 < b) : ℝ :=
  2*w*(B.cap : ℝ)*B.positiveTailCount (b/(8*w)) (B.continuationBandLevel_above_reserve hZero hw hb)+c

noncomputable def continuationBandFloor (B : CountableInstance) (hZero : B.terminal = 0)
    (w c b : ℝ) (hw : 0 < w) (hb : 0 < b) : ℝ := b/(4*B.continuationBandCoefficient hZero w c b hw hb)

lemma continuationBandCoefficient_pos (B : CountableInstance) (hZero : B.terminal = 0)
    {w c b : ℝ} (hw : 0 < w) (hc : 0 < c) (hb : 0 < b) :
    0 < B.continuationBandCoefficient hZero w c b hw hb := by
  have hL := B.positiveTailCount_nonnegative (b/(8*w)) (B.continuationBandLevel_above_reserve hZero hw hb)
  unfold continuationBandCoefficient
  positivity

lemma continuationBandFloor_pos (B : CountableInstance) (hZero : B.terminal = 0)
    {w c b : ℝ} (hw : 0 < w) (hc : 0 < c) (hb : 0 < b) :
    0 < B.continuationBandFloor hZero w c b hw hb :=
  div_pos hb (mul_pos (by norm_num) (B.continuationBandCoefficient_pos hZero hw hc hb))

lemma continuationBandFloor_le_finiteMask (B : CountableInstance) (hZero : B.terminal = 0)
    (N : ℕ) (cut : ℝ) (hcut : (B.terminal : ℝ) < cut) (keep : Fin N → Bool)
    {w c b : ℝ} (hw : 0 < w) (hc : 0 < c) (hb : 0 < b) :
    B.continuationBandFloor hZero w c b hw hb ≤ (B.finiteMaskState N cut hcut keep).durationBandFloor w c (b/2) := by
  let D := B.finiteMaskState N cut hcut keep
  let K := B.continuationBandCoefficient hZero w c b hw hb
  have hTail := B.finiteMaskState_tailCount_le N cut hcut keep (b/(8*w))
    (B.continuationBandLevel_above_reserve hZero hw hb)
  have hLevel : (b/2)/(4*w) = b/(8*w) := by rw [div_div]; congr 1; ring
  have hCoef : D.durationBandCoefficient w c (b/2) ≤ K := by
    change 2*w*(B.cap : ℝ)*D.tailCount ((b/2)/(4*w))+c ≤
      2*w*(B.cap : ℝ)*B.positiveTailCount (b/(8*w)) (B.continuationBandLevel_above_reserve hZero hw hb)+c
    rw [hLevel]
    exact add_le_add (mul_le_mul_of_nonneg_left hTail (by positivity)) le_rfl
  have hDiv : (b/2)/(2*K) ≤ (b/2)/(2*D.durationBandCoefficient w c (b/2)) :=
    div_le_div_of_nonneg_left (by positivity) (mul_pos (by norm_num) (D.durationBandCoefficient_pos hw.le hc))
      (mul_le_mul_of_nonneg_left hCoef (by norm_num))
  have he : (b/2)/(2*K) = b/(4*K) := by rw [div_div]; congr 1; ring
  change b/(4*K) ≤ (b/2)/(2*D.durationBandCoefficient w c (b/2))
  exact he.symm.le.trans hDiv

/-- The explicit secant constant depends on positive-level tail counts of B,
not on the number of retained variables or the unseen mask. -/
theorem continuationValue_secant_lower (B : CountableInstance) (hZero : B.terminal = 0)
    (keep : IndividualMask) {w c b : ℝ} (hw : 0 < w) (hc : 0 < c) (hb : 0 < b)
    {u v : ℝ≥0} (huv : u ≤ v) (hv : v ≤ 1) (hBand : b ≤ B.continuationValue keep w c u) :
    c*B.continuationBandFloor hZero w c b hw hb*((v : ℝ)-(u : ℝ)) ≤
      B.continuationValue keep w c v-B.continuationValue keep w c u := by
  let D := fun N => B.finiteMaskState N (B.markCutoff N) (B.terminal_lt_markCutoff N) (restrictIndividualMask N keep)
  have hFixed (r : ℝ≥0) : Tendsto (fun N => (D N).continuationValue w c r) atTop
      (𝓝 (B.continuationValue keep w c r)) := by
    have h := (B.truncatedContinuationValue_uniform_limit hw.le hc.le).tendsto_at (keep,r)
    have he : (fun N => B.truncatedContinuationValue N (B.markCutoff N) (B.terminal_lt_markCutoff N) keep w c r) =
        (fun N => (D N).continuationValue w c r) := by
      funext N
      exact congrArg (fun C : FiniteIntensityHybridInstance N => C.optimalScalarValue w (c*(r : ℝ)))
        (B.remainingState_truncation_eq keep r N (B.markCutoff N) (B.terminal_lt_markCutoff N))
    rwa [he] at h
  have hβ : 0 < b/2 := by positivity
  have hBand' : b/2 < B.continuationValue keep w c u := by linarith only [hBand,hb]
  have hNBand := (hFixed u).eventually (lt_mem_nhds hBand')
  apply le_of_tendsto_of_tendsto tendsto_const_nhds ((hFixed v).sub (hFixed u))
  filter_upwards [hNBand] with N hN
  have hSecant := (D N).continuationValue_secant_lower hZero hw hc hβ huv hv hN.le
  have hFloor := B.continuationBandFloor_le_finiteMask hZero N (B.markCutoff N) (B.terminal_lt_markCutoff N)
    (restrictIndividualMask N keep) hw hc hb
  have hΔ : 0 ≤ (v : ℝ)-(u : ℝ) := sub_nonneg.mpr (by exact_mod_cast huv)
  have hCompare := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hFloor hc.le) hΔ
  exact hCompare.trans hSecant

theorem continuationValue_lt_of_lt (B : CountableInstance) (hZero : B.terminal = 0)
    (keep : IndividualMask) {w c b : ℝ} (hw : 0 < w) (hc : 0 < c) (hb : 0 < b)
    {u v : ℝ≥0} (huv : u < v) (hv : v ≤ 1) (hBand : b ≤ B.continuationValue keep w c u) :
    B.continuationValue keep w c u < B.continuationValue keep w c v := by
  have h := B.continuationValue_secant_lower hZero keep hw hc hb huv.le hv hBand
  have hp : 0 < c*B.continuationBandFloor hZero w c b hw hb*((v : ℝ)-(u : ℝ)) :=
    mul_pos (mul_pos hc (B.continuationBandFloor_pos hZero hw hc hb)) (sub_pos.mpr (by exact_mod_cast huv))
  linarith only [h,hp]

end ProphetSecretary.Limiting.CountableInstance
