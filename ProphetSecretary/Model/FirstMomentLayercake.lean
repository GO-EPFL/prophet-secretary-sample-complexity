import ProphetSecretary.Model.LogTailBound
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Layer-cake representation of total first moment

For offers in [0,1], S is the integral from zero to one of the sum of closed
marginal tails. The integrability bound may depend on finite n; the subsequent
estimates use L and are uniform in n.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.closedTailCount (P : Instance n) (t : ℝ) : ℝ :=
  ∑ i, (P.law i).real (Ici t)

lemma Instance.closedTailCount_nonnegative (P : Instance n) (t : ℝ) : 0 ≤ P.closedTailCount t :=
  Finset.sum_nonneg fun _ _ => measureReal_nonneg

lemma Instance.closedTailCount_antitone (P : Instance n) : Antitone P.closedTailCount := by
  intro a b hab
  exact Finset.sum_le_sum fun i _ => measureReal_mono (Ici_subset_Ici.mpr hab)

lemma Instance.closedTailCount_le_positiveCount (P : Instance n) {t : ℝ} (ht : 0 < t) :
    P.closedTailCount t ≤ P.positiveCount := by
  apply Finset.sum_le_sum
  intro i _
  exact measureReal_mono (fun x hx => ht.trans_le hx)

lemma Instance.integrableOn_closedTailCount (P : Instance n) :
    IntegrableOn P.closedTailCount (Ioc (0 : ℝ) 1) := by
  apply Integrable.of_bound P.closedTailCount_antitone.measurable.aestronglyMeasurable.restrict (n : ℝ)
  exact Eventually.of_forall fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (P.closedTailCount_nonnegative t)]
    calc
      _ ≤ ∑ _i : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => measureReal_le_one
      _ = (n : ℝ) := by simp

/-- The bounded layer-cake formula used in `upmom:integrated`. -/
theorem Instance.totalFirstMoment_eq_integral_closedTailCount (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) :
    P.totalFirstMoment = ∫ t in Ioc (0 : ℝ) 1, P.closedTailCount t := by
  have hm (i : Fin n) : Antitone (fun t : ℝ => (P.law i).real (Ici t)) :=
    fun _ _ hab => measureReal_mono (Ici_subset_Ici.mpr hab)
  have hI (i : Fin n) : IntegrableOn (fun t : ℝ => (P.law i).real (Ici t)) (Ioc (0 : ℝ) 1) := by
    apply Integrable.of_bound (hm i).measurable.aestronglyMeasurable.restrict 1
    exact Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  unfold Instance.totalFirstMoment Instance.closedTailCount
  rw [integral_finsetSum _ (fun i _ => hI i)]
  apply Finset.sum_congr rfl
  intro i _
  exact (P.integrable_maximum_iff.mp (P.integrable_maximum_of_bounded hcap) i).integral_eq_integral_Ioc_meas_le
    (P.nonnegative i) (hcap i)

lemma Instance.totalFirstMoment_le_positiveCount (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) : P.totalFirstMoment ≤ P.positiveCount := by
  rw [P.totalFirstMoment_eq_integral_closedTailCount hcap]
  have h := integral_mono_ae P.integrableOn_closedTailCount (integrable_const P.positiveCount)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact P.closedTailCount_le_positiveCount ht.1)
  simpa only [integral_const, Measure.real, Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal zero_le_one, one_smul,
    Measure.restrict_apply MeasurableSet.univ, Set.univ_inter] using h

end ProphetSecretary.Model
