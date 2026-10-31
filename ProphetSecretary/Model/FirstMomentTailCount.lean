import ProphetSecretary.Model.Instance
import ProphetSecretary.Probability.CompensatedCloudScore

/-!
# First-moment control of positive tail counts and cloud information

Markov's inequality gives L_b≤S/b. Together with the proved score variance,
this supplies the common Fisher-information bound 2S/b in `updual:scorelift`.
The argument permits arbitrary independent marginals and any positive band.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

theorem Instance.mul_tailCount_le_totalFirstMoment (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {b : ℝ} (hb : 0 ≤ b) :
    b * P.tailCount b ≤ P.totalFirstMoment := by
  unfold Instance.tailCount Instance.totalFirstMoment
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := P.law i) (f := fun x : ℝ => x)
    (P.nonnegative i) (P.integrable_maximum_iff.mp hP i) b
  have hsub : (P.law i).real (Ioi b) ≤ (P.law i).real (Ici b) :=
    measureReal_mono Ioi_subset_Ici_self
  exact (mul_le_mul_of_nonneg_left hsub hb).trans hmarkov

lemma Instance.tailCount_le_totalFirstMoment_div (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {b : ℝ} (hb : 0 < b) :
    P.tailCount b ≤ P.totalFirstMoment / b := by
  apply (le_div_iff₀ hb).mpr
  have h := P.mul_tailCount_le_totalFirstMoment hP hb.le
  simpa only [mul_comm] using h

/-- The source information bound for complement compensation, without a zero atom. -/
theorem Instance.compensatedBand_information_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {B : Set ℝ} (hB : MeasurableSet B)
    (hp : ∀ i, (P.law i).real B ≤ 1 / 2) {b : ℝ} (hb : 0 < b) (hsub : B ⊆ Ioi b) :
    ProphetSecretary.Probability.information P.law
      (fun i => ProphetSecretary.Probability.compensatedBandScore (P.law i) B) ≤
        2 * P.totalFirstMoment / b := by
  have hi := ProphetSecretary.Probability.compensatedCloudScore_information_le P.law hB hp
  have hm : (∑ i, (P.law i).real B) ≤ P.tailCount b :=
    Finset.sum_le_sum fun i _ => measureReal_mono hsub
  have ht := P.tailCount_le_totalFirstMoment_div hP hb
  have htwice := mul_le_mul_of_nonneg_left (hm.trans ht) (by norm_num : (0 : ℝ) ≤ 2)
  exact hi.trans (by simpa only [mul_div_assoc] using htwice)

end ProphetSecretary.Model
