import ProphetSecretary.Limiting.CountableBenchmark
import ProphetSecretary.Model.ExcessPositiveTail
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Explicit error from omitted individual values above reserve

The bound is on the actual independent infinite product. A fixed positive
excess level d gives error d plus H times the omitted tail count; that tail
vanishes with the retained prefix. No policy convergence is used.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal ENNReal Topology

namespace ProphetSecretary.Limiting.CountableInstance

variable (B : CountableInstance)

noncomputable def individualTailExcessMaximum (N : ℕ) (x : ℕ → ℝ) : ℝ :=
  countableMaximum 0 (fun k => Model.excessValueMap B.terminal (x (k+N)))

lemma measurable_individualTailExcessMaximum (N : ℕ) : Measurable (B.individualTailExcessMaximum N) :=
  measurable_countableMaximum 0 (fun k => (Model.measurable_excessValueMap B.terminal).comp (measurable_pi_apply (k+N)))

lemma individualTailExcessMaximum_bounded (N : ℕ) :
    ∀ᵐ x ∂B.individualValuesLaw, B.individualTailExcessMaximum N x ∈ Icc (0 : ℝ) B.cap := by
  filter_upwards [B.individual_values_supported] with x hx
  have hc (k : ℕ) : Model.excessValueMap B.terminal (x (k+N)) ≤ (B.cap : ℝ) :=
    (Model.excessValueMap_le_self B.terminal.property _).trans (hx (k+N)).2
  exact ⟨terminal_le_countableMaximum B.cap.property B.cap.property _ hc,
    countableMaximum_le B.cap.property B.cap.property _ hc⟩

lemma integrable_individualTailExcessMaximum (N : ℕ) :
    Integrable (B.individualTailExcessMaximum N) B.individualValuesLaw := by
  apply Integrable.of_bound (B.measurable_individualTailExcessMaximum N).aestronglyMeasurable B.cap
  filter_upwards [B.individualTailExcessMaximum_bounded N] with x hx
  rw [Real.norm_eq_abs,abs_of_nonneg hx.1]
  exact hx.2

noncomputable def expectedIndividualTailExcessMaximum (N : ℕ) : ℝ :=
  ∫ x, B.individualTailExcessMaximum N x ∂B.individualValuesLaw

lemma expectedIndividualTailExcessMaximum_nonnegative (N : ℕ) :
    0 ≤ B.expectedIndividualTailExcessMaximum N :=
  integral_nonneg_of_ae ((B.individualTailExcessMaximum_bounded N).mono (fun _ hx => hx.1))

lemma expectedIndividualTailExcessMaximum_le (N : ℕ) {d : ℝ} (hd : 0 < d) :
    B.expectedIndividualTailExcessMaximum N ≤
      d + (B.cap : ℝ) * (∑' k, (B.individuals (k+N) : Measure ℝ) (Ioi ((B.terminal : ℝ)+d))).toReal := by
  let S : Set (ℕ → ℝ) := {x | ∃ k, d < Model.excessValueMap B.terminal (x (k+N))}
  have hset : S = ⋃ k, {x : ℕ → ℝ | d < Model.excessValueMap B.terminal (x (k+N))} := by
    ext x
    simp only [S,mem_setOf_eq,mem_iUnion]
  have hs : MeasurableSet S := by
    rw [hset]
    apply MeasurableSet.iUnion
    intro k
    exact measurableSet_lt measurable_const
      ((Model.measurable_excessValueMap B.terminal).comp (measurable_pi_apply (k+N)))
  have he (k : ℕ) : B.individualValuesLaw {x | d < Model.excessValueMap B.terminal (x (k+N))} =
      (B.individuals (k+N) : Measure ℝ) (Ioi ((B.terminal : ℝ)+d)) := by
    have hset' : {x : ℕ → ℝ | d < Model.excessValueMap B.terminal (x (k+N))} =
        (fun x : ℕ → ℝ => x (k+N)) ⁻¹' Ioi ((B.terminal : ℝ)+d) := by
      ext x
      exact Model.excessValueMap_gt_iff B.terminal.property hd.le
    rw [hset']
    exact (B.individualValue_measurePreserving (k+N)).measure_preimage measurableSet_Ioi.nullMeasurableSet
  have hprob : B.individualValuesLaw S ≤
      ∑' k, (B.individuals (k+N) : Measure ℝ) (Ioi ((B.terminal : ℝ)+d)) := by
    rw [hset]
    exact (measure_iUnion_le _).trans_eq (tsum_congr he)
  have hg : Integrable (fun x : ℕ → ℝ => d + S.indicator (fun _ => (B.cap : ℝ)) x) B.individualValuesLaw :=
    (integrable_const d).add ((integrable_const (B.cap : ℝ)).indicator hs)
  have hpoint : ∀ᵐ x ∂B.individualValuesLaw, B.individualTailExcessMaximum N x ≤
      d + S.indicator (fun _ => (B.cap : ℝ)) x := by
    filter_upwards [B.individualTailExcessMaximum_bounded N] with x hx
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem hxS]
      exact hx.2.trans (le_add_of_nonneg_left hd.le)
    · rw [indicator_of_notMem hxS,add_zero]
      apply countableMaximum_le hd.le hd.le
      intro k
      exact le_of_not_gt (fun hk => hxS ⟨k,hk⟩)
  have hint := integral_mono_ae (B.integrable_individualTailExcessMaximum N) hg hpoint
  rw [integral_add (integrable_const d) ((integrable_const (B.cap : ℝ)).indicator hs),
    integral_const,integral_indicator_const _ hs] at hint
  simp only [probReal_univ,smul_eq_mul,one_mul] at hint
  have hle : (∑' k, (B.individuals (k+N) : Measure ℝ) (Ioi ((B.terminal : ℝ)+d))) ≤
      ∑' k, (B.individuals k : Measure ℝ) (Ioi ((B.terminal : ℝ)+d)) :=
    ENNReal.tsum_comp_le_tsum_of_injective (fun i j h => Nat.add_right_cancel h) _
  have htop : (∑' k, (B.individuals (k+N) : Measure ℝ) (Ioi ((B.terminal : ℝ)+d))) ≠ ⊤ :=
    (hle.trans_lt (B.individual_tail_finite _ (lt_add_of_pos_right _ hd))).ne
  have hpReal : B.individualValuesLaw.real S ≤
      (∑' k, (B.individuals (k+N) : Measure ℝ) (Ioi ((B.terminal : ℝ)+d))).toReal :=
    ENNReal.toReal_mono htop hprob
  have hm : B.individualValuesLaw.real S * (B.cap : ℝ) ≤
      (B.cap : ℝ) * (∑' k, (B.individuals (k+N) : Measure ℝ) (Ioi ((B.terminal : ℝ)+d))).toReal := by
    calc
      _ ≤ (∑' k, (B.individuals (k+N) : Measure ℝ) (Ioi ((B.terminal : ℝ)+d))).toReal * (B.cap : ℝ) :=
        mul_le_mul_of_nonneg_right hpReal B.cap.property
      _ = _ := mul_comm _ _
  exact hint.trans (add_le_add le_rfl hm)

lemma expectedIndividualTailExcessMaximum_tendsto :
    Tendsto B.expectedIndividualTailExcessMaximum atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro l hl
    exact Filter.Eventually.of_forall (fun N => hl.trans_le (B.expectedIndividualTailExcessMaximum_nonnegative N))
  · intro ε hε
    let d : ℝ := ε / 2
    have hd : 0 < d := by dsimp only [d]; positivity
    let f : ℕ → ℝ≥0∞ := fun i => (B.individuals i : Measure ℝ) (Ioi ((B.terminal : ℝ)+d))
    have hfin : (∑' i, f i) ≠ ⊤ := (B.individual_tail_finite _ (lt_add_of_pos_right _ hd)).ne
    have htail : Tendsto (fun N => (∑' k, f (k+N)).toReal) atTop (𝓝 0) := by
      have he := (ENNReal.tendsto_toReal (show (0 : ℝ≥0∞) ≠ ⊤ by simp)).comp (ENNReal.tendsto_sum_nat_add f hfin)
      change Tendsto (fun N => (∑' k, f (k+N)).toReal) atTop (𝓝 (0 : ℝ≥0∞).toReal) at he
      rw [ENNReal.toReal_zero] at he
      exact he
    have hscaled : Tendsto (fun N => (B.cap : ℝ) * (∑' k, f (k+N)).toReal) atTop (𝓝 0) := by
      simpa only [mul_zero] using htail.const_mul (B.cap : ℝ)
    have he := hscaled.eventually (gt_mem_nhds (show (0 : ℝ) < ε/2 by positivity))
    filter_upwards [he] with N hN
    have hupper := B.expectedIndividualTailExcessMaximum_le N hd
    change (B.cap : ℝ) * (∑' k, (B.individuals (k+N) : Measure ℝ) (Ioi ((B.terminal : ℝ)+d))).toReal < ε/2 at hN
    exact hupper.trans_lt (by dsimp only [d]; linarith only [hN])

end ProphetSecretary.Limiting.CountableInstance
