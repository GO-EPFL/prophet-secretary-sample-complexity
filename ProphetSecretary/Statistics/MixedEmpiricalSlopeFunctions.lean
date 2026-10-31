import ProphetSecretary.Statistics.EmpiricalSlopeFunctions
import ProphetSecretary.Statistics.MixedEmpiricalFreshStep

/-!
# Scalar premium increments for mixed design laws

The normalized positive-part difference at two fixed scalars is bounded by the
remaining horizon and ignores all unseen known-law sample rows. Measurability,
clock bounds and actual true-marginal integration are proved for this mixed law.
-/

open MeasureTheory
open scoped Classical BigOperators

namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

noncomputable def mixedOfferSlope (P : Instance n) (known : Finset (Fin n)) (z z' : ℝ) (u : Fin n → ℝ) (i : Fin n)
    (v : (((Fin n × Fin k) → ℝ) × ℝ)) : ℝ :=
  (max (max 0 v.2 - mixedArrivalContinuation P known 1 z u i v.1) 0 -
    max (max 0 v.2 - mixedArrivalContinuation P known 1 z' u i v.1) 0) / (z' - z)

lemma measurable_mixedOfferSlope (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z')
    (u : Fin n → ℝ) (i : Fin n) : Measurable (mixedOfferSlope (k := k) P known z z' u i) := by
  have hθ : Measurable (fun v : (((Fin n × Fin k) → ℝ) × ℝ) => mixedArrivalContinuation P known 1 z u i v.1) := (measurable_mixedArrivalContinuation (k := k) P hP known (by norm_num : (0 : ℝ) < 1) hz u i).comp measurable_fst
  have hθ' : Measurable (fun v : (((Fin n × Fin k) → ℝ) × ℝ) => mixedArrivalContinuation P known 1 z' u i v.1) := (measurable_mixedArrivalContinuation (k := k) P hP known (by norm_num : (0 : ℝ) < 1) hz' u i).comp measurable_fst
  exact (((measurable_const.max measurable_snd).sub hθ).max measurable_const |>.sub
    (((measurable_const.max measurable_snd).sub hθ').max measurable_const)).div_const _

lemma mixedOfferSlope_bounds (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z')
    (u : Fin n → ℝ) (i : Fin n) (hui : 0 ≤ u i)
    (a : (Fin n × Fin k) → ℝ) (x : ℝ) :
    0 ≤ mixedOfferSlope P known z z' u i (a, x) ∧ mixedOfferSlope P known z z' u i (a, x) ≤ 1 := by
  let Q := mixedEmpiricalInstance P known (reservoirCoordinates.symm a)
  have hθ := Q.continuationAtArrival_coefficient_difference (mixedEmpiricalInstance_integrable P hP known _) hz hzz.le u i
  have hp := positivePart_threshold_difference (max 0 x) (sub_nonneg.mp hθ.1)
  have hd := sub_pos.mpr hzz
  change 0 ≤ (max (max 0 x - Q.continuationAtArrival 1 z (fun _ => 0) u i) 0 -
      max (max 0 x - Q.continuationAtArrival 1 z' (fun _ => 0) u i) 0) / (z' - z) ∧ _
  refine ⟨div_nonneg hp.1 hd.le, ?_⟩
  apply (div_le_iff₀ hd).mpr
  have hs : max (0 : ℝ) (1 - u i) ≤ 1 := max_le (by norm_num) (by linarith)
  have h := mul_le_mul_of_nonneg_left hs hd.le
  change max (max 0 x - Q.continuationAtArrival 1 z (fun _ => 0) u i) 0 -
      max (max 0 x - Q.continuationAtArrival 1 z' (fun _ => 0) u i) 0 ≤ 1 * (z' - z)
  nlinarith [hp.2, hθ.2]

lemma mixedOfferSlope_mask (P : Instance n) (known : Finset (Fin n)) (z z' : ℝ) (u : Fin n → ℝ) (i : Fin n)
    (s : Finset (Fin n × Fin k))
    (hfuture : ∀ q∈futureSampleRows u i, q∉known → ∀ j : Fin k, (q,j)∈s)
    (a : (Fin n × Fin k) → ℝ) (x : ℝ) :
    mixedOfferSlope P known z z' u i (ProphetSecretary.Probability.maskCoordinates s a, x) =
      mixedOfferSlope P known z z' u i (a, x) := by
  simp only [mixedOfferSlope, mixedArrivalContinuation_mask P known 1 z u i s hfuture,
    mixedArrivalContinuation_mask P known 1 z' u i s hfuture]

lemma integral_mixedOfferSlope (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    (z z' : ℝ) (u : Fin n → ℝ) (i : Fin n) (a : (Fin n × Fin k) → ℝ) :
    (∫ x, mixedOfferSlope P known z z' u i (a, x) ∂P.law i) =
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).clockPremiumSlopeUnder P z z' u i := by
  let θ := mixedArrivalContinuation (k := k) P known 1 z u i a
  let θ' := mixedArrivalContinuation (k := k) P known 1 z' u i a
  have hfi (v : ℝ) : Integrable (fun x => max (max 0 x - v) 0) (P.law i) :=
    (((integrable_const 0).sup (P.integrable_maximum_iff.mp hP i)).sub (integrable_const v)).sup (integrable_const 0)
  have he (v : ℝ) : (∫ x, max (max 0 x - v) 0 ∂P.law i) = positivePremium (P.law i) 1 v := by
    apply integral_congr_ae
    filter_upwards [P.nonnegative i] with x hx
    simp only [max_eq_right hx, one_mul]
  change (∫ x, (max (max 0 x - θ) 0 - max (max 0 x - θ') 0) / (z' - z) ∂P.law i) = _
  rw [integral_div, integral_sub (hfi θ) (hfi θ'), he θ, he θ']
  rfl

end ProphetSecretary.Model
