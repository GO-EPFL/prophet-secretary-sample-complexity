import ProphetSecretary.Statistics.MixedEmpiricalScalarIncrementMoments
import ProphetSecretary.Statistics.ResidualEnvelopeContinuity

/-!
# Increments of the actual mixed residual envelope

The scalar envelope is continuous and its second/sixth moment increments scale
with the corresponding power of scalar separation. All expectations include
independent training and complete clocks, and all constants are independent
of the instance size and declared known marginals.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma mixedEnvelopeDifference_joint_integrable_pow (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') (p : ℕ) :
    Integrable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      |(mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2 -
       (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z' v.2| ^ p)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
  have hm (c : ℝ) (hc : 0 ≤ c) : Measurable (fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) =>
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 c v.2) :=
    P.measurable_mixedResidualSuffixEnvelope (k := k) (P.integrable_maximum_of_bounded hbound) known
      (y := fun v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) => reservoirCoordinates.symm v.1)
      (c := fun _ => c) (u := Prod.snd)
      (fun i j => (measurable_pi_apply (i, j)).comp measurable_fst) measurable_const (fun _ => hc)
      (fun i => (measurable_pi_apply i).comp measurable_snd)
  apply Integrable.of_bound ((continuous_abs.measurable.comp ((hm z hz).sub (hm z' hz'))).pow_const p).aestronglyMeasurable ((n : ℝ) ^ p)
  have hv : MeasurePreserving (Prod.fst : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ((Fin n × Fin k) → ℝ))
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) (P.trainingCoordinateLaw k) := measurePreserving_fst
  filter_upwards [hv.quasiMeasurePreserving.ae (trainingCoordinates_unit_ae P hbound)] with v hv
  let Q := mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)
  have ha := P.mixedResidualSuffixEnvelope_le_card hbound known (reservoirCoordinates.symm v.1) hv hz v.2
  have hb := P.mixedResidualSuffixEnvelope_le_card hbound known (reservoirCoordinates.symm v.1) hv hz' v.2
  have ha0 : 0 ≤ Q.residualSuffixEnvelope P 1 z v.2 := ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _
  have hb0 : 0 ≤ Q.residualSuffixEnvelope P 1 z' v.2 := ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _
  have hd : |Q.residualSuffixEnvelope P 1 z v.2 - Q.residualSuffixEnvelope P 1 z' v.2| ≤ n := by
    rw [abs_le]
    constructor <;> linarith
  change ‖|Q.residualSuffixEnvelope P 1 z v.2 - Q.residualSuffixEnvelope P 1 z' v.2| ^ p‖ ≤ (n : ℝ) ^ p
  rw [Real.norm_eq_abs, abs_pow, abs_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) hd p

lemma Instance.mixedEnvelopeDifferenceMoment_le_normalized (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (p : ℕ) :
    (∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
      |(mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2 -
       (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z' v.2| ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      (z' - z) ^ p * P.mixedSlopeSuffixMoment known k z z' p := by
  have h := integral_mono (mixedEnvelopeDifference_joint_integrable_pow (k := k) P known hbound hz (hz.trans hzz.le) p)
    ((mixedSlopeSuffix_joint_integrable_pow (k := k) P known hbound hz hzz p).const_mul ((z' - z) ^ p)) (fun v =>
      (pow_le_pow_left₀ (abs_nonneg _) ((mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).abs_residualSuffixEnvelope_sub_le_increment P hzz v.2) p).trans_eq
        (mul_pow _ _ p))
  rw [integral_const_mul] at h
  exact h

/-- The complete scalar-envelope increment has a uniform second-moment bound. -/
theorem Instance.mixedEnvelopeDifference_secondMoment (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    (∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
      |(mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2 -
       (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z' v.2| ^ 2
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤ 4 / (k : ℝ) * (z' - z) ^ 2 := by
  apply (P.mixedEnvelopeDifferenceMoment_le_normalized known hbound hz hzz 2).trans
  exact (mul_le_mul_of_nonneg_left (P.mixedSlopeSuffixMoment_two_uniform known hbound hz hzz)
    (sq_nonneg (z' - z))).trans_eq (mul_comm _ _)

/-- The sixth-moment counterpart needed for uniform-weight chaining. -/
theorem Instance.mixedEnvelopeDifference_sixthMoment (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    (∫ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)),
      |(mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2 -
       (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z' v.2| ^ 6
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      ((106000000000 ^ 2 + 212000000000) / (k : ℝ) ^ 3) * (z' - z) ^ 6 := by
  apply (P.mixedEnvelopeDifferenceMoment_le_normalized known hbound hz hzz 6).trans
  exact (mul_le_mul_of_nonneg_left (P.mixedSlopeSuffixMoment_six_uniform known hbound hz hzz)
    (pow_nonneg (sub_nonneg.mpr hzz.le) 6)).trans_eq (mul_comm _ _)

end ProphetSecretary.Model
