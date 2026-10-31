import ProphetSecretary.Model.ScalarBands
import ProphetSecretary.Analysis.ThresholdLoss

/-!
# Conditional clock domination for duration-weight regret

The candidate clock is integrated after fixing the complete residual vector.
The resulting quadratic bound is uniform in the candidate value and the other
clocks; finite cardinality is allowed here, before the sharp selection charge.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.durationActionLoss (P : Instance n) (z z' : ℝ) (i : Fin n)
    (x : ℝ) (u : Fin n → ℝ) (t : ℝ) : ℝ :=
  let old := P.continuationValue (otherUnseen u i t) (max 0 (1 - t)) 1 z
  let new := P.continuationValue (otherUnseen u i t) (max 0 (1 - t)) 1 z'
  max x new - if old ≤ x then x else new

lemma Instance.durationActionLoss_nonnegative (P : Instance n) (z z' : ℝ) (i : Fin n)
    (x : ℝ) (u : Fin n → ℝ) (t : ℝ) : 0 ≤ P.durationActionLoss z z' i x u t := by
  unfold Instance.durationActionLoss
  dsimp only
  split_ifs
  · exact sub_nonneg.mpr (le_max_left _ _)
  · exact sub_nonneg.mpr (le_max_right _ _)

lemma Instance.measurable_durationActionLoss (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z')
    (i : Fin n) (x : ℝ) (u : Fin n → ℝ) : Measurable (P.durationActionLoss z z' i x u) := by
  have hmap : Measurable (fun t : ℝ ↦ (otherUnseen u i t, t)) :=
    (measurable_otherUnseen u i).prodMk measurable_id
  have ho := (P.measurable_stateElapsedValue hP zero_le_one hz).comp hmap
  have hn := (P.measurable_stateElapsedValue hP zero_le_one hz').comp hmap
  exact (measurable_const.max hn).sub (Measurable.ite
    (measurableSet_le ho measurable_const) measurable_const hn)

lemma Instance.durationActionLoss_le_band (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z')
    (i : Fin n) (x : ℝ) (u : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    P.durationActionLoss z z' i x u t ≤
      if |P.candidateGap 1 z' i x u t| ≤ |z - z'| then |z - z'| else 0 := by
  have hrem0 : 0 ≤ max 0 (1 - t) := le_max_left _ _
  have hrem1 : max 0 (1 - t) ≤ 1 := max_le zero_le_one (sub_le_self 1 ht)
  have h := optimalScalarValue_durationWeight_lipschitz (P.restrictTo (otherUnseen u i t))
    (P.restrictTo_integrable_maximum _ hP) zero_le_one (mul_nonneg hz hrem0) (mul_nonneg hz' hrem0)
  have hshift : |P.continuationValue (otherUnseen u i t) (max 0 (1 - t)) 1 z -
      P.continuationValue (otherUnseen u i t) (max 0 (1 - t)) 1 z'| ≤ |z - z'| := by
    change |optimalScalarValue _ 1 (z * max 0 (1 - t)) -
      optimalScalarValue _ 1 (z' * max 0 (1 - t))| ≤ _
    apply h.trans
    rw [← sub_mul, abs_mul, abs_of_nonneg hrem0]
    exact (mul_le_mul_of_nonneg_left hrem1 (abs_nonneg _)).trans_eq (mul_one _)
  have hl := ProphetSecretary.Analysis.max_action_loss_le_band (a := x) hshift
  simpa only [Instance.durationActionLoss, Instance.candidateGap, one_mul] using hl

lemma Instance.integrable_durationActionLoss (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z')
    (i : Fin n) (x : ℝ) (u : Fin n → ℝ) :
    Integrable (P.durationActionLoss z z' i x u) Instance.uniformClock := by
  apply Integrable.of_bound (P.measurable_durationActionLoss hP hz hz' i x u).aestronglyMeasurable |z - z'|
  filter_upwards [(ae_restrict_mem measurableSet_Icc)] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (P.durationActionLoss_nonnegative z z' i x u t)]
  have h := P.durationActionLoss_le_band hP hz hz' i x u ht.1
  split_ifs at h
  · exact h
  · exact h.trans (abs_nonneg _)

/-- The conditional candidate-clock bound, before averaging any residual data. -/
theorem Instance.integral_durationActionLoss_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 < z')
    (i : Fin n) (x : ℝ) (u : Fin n → ℝ) :
    (∫ t : ℝ, P.durationActionLoss z z' i x u t ∂Instance.uniformClock) ≤
      8 * (1 + (n : ℝ)) * (z - z') ^ 2 / z' := by
  let E := ProphetSecretary.Analysis.thresholdBand (P.candidateGap 1 z' i x u) |z - z'|
  have hE : MeasurableSet E :=
    ProphetSecretary.Analysis.measurableSet_thresholdBand (P.measurable_candidateGap hP zero_le_one hz'.le i x u) _
  have hpoint : ∀ᵐ t : ℝ ∂Instance.uniformClock,
      P.durationActionLoss z z' i x u t ≤ E.indicator (fun _ ↦ |z - z'|) t := by
    filter_upwards [(ae_restrict_mem measurableSet_Icc)] with t ht
    have h := P.durationActionLoss_le_band hP hz hz'.le i x u ht.1
    by_cases he : t ∈ E
    · rw [Set.indicator_of_mem he]
      exact h.trans (by split_ifs <;> simp_all only [le_refl, abs_nonneg])
    · rw [Set.indicator_of_notMem he]
      have hn : ¬ |P.candidateGap 1 z' i x u t| ≤ |z - z'| := fun hh ↦ he ⟨ht, hh⟩
      simpa only [if_neg hn] using h
  have hb := integral_mono_ae (P.integrable_durationActionLoss hP hz hz'.le i x u)
    ((integrable_const |z - z'|).indicator hE) hpoint
  rw [integral_indicator_const _ hE, smul_eq_mul] at hb
  have heq : Instance.uniformClock.real E = volume.real E := by
    unfold Instance.uniformClock Measure.real
    rw [Measure.restrict_apply hE, inter_eq_left.mpr (fun _ ht ↦ ht.1)]
  rw [heq] at hb
  have hv := P.candidateGap_band_volume hP zero_lt_one hz' (abs_nonneg (z - z')) i x u
  calc
    _ ≤ volume.real E * |z - z'| := hb
    _ ≤ (2 * |z - z'| / (z' / (4 * (1 + (n : ℝ))))) * |z - z'| :=
      mul_le_mul_of_nonneg_right hv (abs_nonneg _)
    _ = _ := by
      rw [← sq_abs (z - z')]
      field_simp [hz'.ne', (show (4 : ℝ) * (1 + (n : ℝ)) ≠ 0 by positivity)]
      ring

end ProphetSecretary.Model
