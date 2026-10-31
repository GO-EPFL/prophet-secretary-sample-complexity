import ProphetSecretary.Limiting.CountableTruncationLower
import ProphetSecretary.Limiting.CountableTruncationUpper

/-!
# Full-policy values equal the truncation limits in `def:limiting-body`

The first theorem retains the explicit error and all dependencies. The joint
limit and bounded-reward-weight uniform version follow from that error, for
the actual full admissible policy class, without optimizer convergence.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Limiting.CountableInstance

lemma truncation_value_error_le (B : CountableInstance) (N : ℕ) {b : ℝ} (hb : (B.terminal : ℝ) < b)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    |(B.truncation N b hb).optimalScalarValue w c-B.optimalScalarValue w c| ≤
      w * (B.expectedIndividualTailExcessMaximum N + (b-(B.terminal : ℝ))) := by
  have hl := B.truncation_value_le N hb w c
  have hu := B.value_le_truncation_add N hb hw hc
  rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr hl)]
  linarith only [hu]

lemma truncation_value_tendsto (B : CountableInstance) (Ns : ℕ → ℕ) (bs : ℕ → ℝ)
    (hbs : ∀ m, (B.terminal : ℝ) < bs m) (hN : Tendsto Ns atTop atTop)
    (hb : Tendsto bs atTop (𝓝 (B.terminal : ℝ))) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Tendsto (fun m => (B.truncation (Ns m) (bs m) (hbs m)).optimalScalarValue w c) atTop
      (𝓝 (B.optimalScalarValue w c)) := by
  have hE := B.expectedIndividualTailExcessMaximum_tendsto.comp hN
  change Tendsto (fun m => B.expectedIndividualTailExcessMaximum (Ns m)) atTop (𝓝 0) at hE
  have hWidth : Tendsto (fun m => bs m-(B.terminal : ℝ)) atTop (𝓝 0) := by
    simpa only [sub_self] using hb.sub_const (B.terminal : ℝ)
  have hErr : Tendsto (fun m => w * (B.expectedIndividualTailExcessMaximum (Ns m) +
      (bs m-(B.terminal : ℝ)))) atTop (𝓝 0) := by
    simpa only [add_zero,mul_zero] using (hE.add hWidth).const_mul w
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hErr
  intro m
  simpa only [Real.norm_eq_abs] using B.truncation_value_error_le (Ns m) (hbs m) hw hc

lemma truncation_value_uniform (B : CountableInstance) {W ε : ℝ} (hW : 0 ≤ W) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ b (hb : (B.terminal : ℝ) < b),
      b < (B.terminal : ℝ)+ε/(4*(W+1)) → ∀ w c : ℝ, 0 ≤ w → w ≤ W → 0 ≤ c →
      |(B.truncation N b hb).optimalScalarValue w c-B.optimalScalarValue w c| < ε := by
  let η := ε / (4*(W+1))
  have hη : 0 < η := div_pos hε (by positivity)
  have hEq : η * (4*(W+1)) = ε := div_mul_cancel₀ ε (by positivity)
  have hSmall : W*(2*η) < ε := by
    have hp : 0 ≤ W*η := mul_nonneg hW hη.le
    nlinarith only [hEq,hη,hp]
  have he := B.expectedIndividualTailExcessMaximum_tendsto.eventually (gt_mem_nhds hη)
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp he
  refine ⟨N₀,?_⟩
  intro N hN b hb hB w c hw hwW hc
  have hEN := hN₀ N hN
  have hWidth : b-(B.terminal : ℝ) < η := by linarith only [hB]
  have hNonneg : 0 ≤ B.expectedIndividualTailExcessMaximum N + (b-(B.terminal : ℝ)) :=
    add_nonneg (B.expectedIndividualTailExcessMaximum_nonnegative N) (sub_nonneg.mpr hb.le)
  calc
    _ ≤ w*(B.expectedIndividualTailExcessMaximum N+(b-(B.terminal : ℝ))) := B.truncation_value_error_le N hb hw hc
    _ ≤ W*(B.expectedIndividualTailExcessMaximum N+(b-(B.terminal : ℝ))) := mul_le_mul_of_nonneg_right hwW hNonneg
    _ ≤ W*(2*η) := mul_le_mul_of_nonneg_left (by linarith only [hEN,hWidth]) hW
    _ < ε := hSmall

end ProphetSecretary.Limiting.CountableInstance
