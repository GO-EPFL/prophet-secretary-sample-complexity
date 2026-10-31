import ProphetSecretary.Limiting.CountablePrefixValueError
import ProphetSecretary.Limiting.CountableBenchmarkUniform
import ProphetSecretary.Limiting.HybridBenchmarkTerminal

/-!
# Uniform prefix/cutoff neighborhoods with terminal reward equal to the cutoff

The scalar estimate is uniform over bounded reward weights and all duration
weights. The benchmark radius comes from its actual joint cofinal limit.
-/

open MeasureTheory Set Filter
open scoped NNReal

namespace ProphetSecretary.Limiting.CountableInstance

lemma prefixIntensityState_value_uniform (B : CountableInstance) {W ε : ℝ} (hW : 0 ≤ W) (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N, N0 ≤ N → ∀ (b : ℝ≥0) (hb : (B.terminal : ℝ) < b) (hbH : b ≤ B.cap),
      (b : ℝ) < (B.terminal : ℝ)+ε/(4*(W+1)) → ∀ w c : ℝ,
      0 ≤ w → w ≤ W → 0 ≤ c →
      |(B.prefixIntensityState N b hbH (B.intensityAbove b hb)
        (B.truncation N b hb).intensity_supported).optimalScalarValue w c-B.optimalScalarValue w c| < ε := by
  let η := ε/(4*(W+1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hEq : η*(4*(W+1)) = ε := div_mul_cancel₀ _ (by positivity)
  have hSmall : W*(3*η) < ε := by
    have hn : 0 ≤ W*η := mul_nonneg hW hη.le
    nlinarith only [hEq,hη,hn]
  have he := B.expectedIndividualTailExcessMaximum_tendsto.eventually (gt_mem_nhds hη)
  obtain ⟨N0,hN0⟩ := eventually_atTop.mp he
  refine ⟨N0,?_⟩
  intro N hN b hb hbH hbd w c hw hwW hc
  have hE := hN0 N hN
  have hd : (b : ℝ)-(B.terminal : ℝ) < η := by linarith only [hbd]
  have hn : 0 ≤ B.expectedIndividualTailExcessMaximum N+2*((b : ℝ)-B.terminal) :=
    add_nonneg (B.expectedIndividualTailExcessMaximum_nonnegative N) (mul_nonneg (by norm_num) (sub_nonneg.mpr hb.le))
  calc
    _ ≤ w*(B.expectedIndividualTailExcessMaximum N+2*((b : ℝ)-B.terminal)) := B.prefixIntensityState_value_error_le N b hb hbH hw hc
    _ ≤ W*(B.expectedIndividualTailExcessMaximum N+2*((b : ℝ)-B.terminal)) := mul_le_mul_of_nonneg_right hwW hn
    _ ≤ W*(3*η) := mul_le_mul_of_nonneg_left (by linarith only [hE,hd]) hW
    _ < ε := hSmall

lemma prefixIntensityState_benchmark_uniform (B : CountableInstance) {ε : ℝ} (hε : 0 < ε) :
    ∃ N0 : ℕ, ∃ δ > (0 : ℝ), ∀ N, N0 ≤ N →
      ∀ (b : ℝ≥0) (hb : (B.terminal : ℝ) < b) (hbH : b ≤ B.cap),
      (b : ℝ) < (B.terminal : ℝ)+δ →
      |(B.prefixIntensityState N b hbH (B.intensityAbove b hb)
        (B.truncation N b hb).intensity_supported).expectedMaximum-B.expectedMaximum| < ε := by
  obtain ⟨N0,δ,hδ,hNear⟩ := B.truncation_expectedMaximum_uniform (ε/2) (by positivity)
  refine ⟨N0,min δ (ε/4),lt_min hδ (by positivity),?_⟩
  intro N hN b hb hbH hbd
  let C := B.truncation N b hb
  let D := B.prefixIntensityState N b hbH (B.intensityAbove b hb) C.intensity_supported
  have hTerminal := C.expectedMaximum_terminal_abs_sub_le D rfl rfl
  have ht : |D.expectedMaximum-C.expectedMaximum| ≤ (b : ℝ)-B.terminal := by
    rw [abs_sub_comm]
    have he : |(C.terminal : ℝ)-D.terminal| = (b : ℝ)-B.terminal := by
      change |(B.terminal : ℝ)-(b : ℝ)| = _
      rw [abs_of_neg (sub_neg.mpr hb),neg_sub]
    rwa [he] at hTerminal
  have hδ' : (b : ℝ) < (B.terminal : ℝ)+δ := hbd.trans_le (add_le_add le_rfl (min_le_left _ _))
  have hWidth : (b : ℝ)-(B.terminal : ℝ) < ε/4 := by
    have h := hbd.trans_le (add_le_add le_rfl (min_le_right δ (ε/4)))
    linarith only [h]
  have hC := hNear N b hb hN hδ'
  change |C.expectedMaximum-B.expectedMaximum| < ε/2 at hC
  change |D.expectedMaximum-B.expectedMaximum| < ε
  calc
    _ ≤ |D.expectedMaximum-C.expectedMaximum|+|C.expectedMaximum-B.expectedMaximum| := abs_sub_le _ _ _
    _ < ε := by linarith only [ht,hWidth,hC,hε]

end ProphetSecretary.Limiting.CountableInstance
