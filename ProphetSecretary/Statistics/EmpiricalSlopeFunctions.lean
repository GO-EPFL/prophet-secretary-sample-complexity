import ProphetSecretary.Statistics.PremiumSlopes
import ProphetSecretary.Statistics.EmpiricalFreshStep

/-!
# Empirical premium difference functions

Both scalar weights are fixed before sampling. The normalized positive-part
difference is measurable in the revealed samples and candidate offer, lies in
`[0,1]` on the clock domain, and ignores every sample in the candidate row.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma positivePart_threshold_difference (x : ℝ) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ max (x - a) 0 - max (x - b) 0 ∧
      max (x - a) 0 - max (x - b) 0 ≤ b - a := by
  constructor
  · exact sub_nonneg.mpr (max_le_max (by linarith) le_rfl)
  · have h : max (x - a) 0 ≤ max (x - b) 0 + (b - a) := by
      apply max_le
      · linarith [le_max_left (x - b) 0]
      · linarith [le_max_right (x - b) 0]
    linarith

lemma Instance.continuationAtArrival_coefficient_difference (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z ≤ z')
    (u : Fin n → ℝ) (i : Fin n) :
    0 ≤ Q.continuationAtArrival 1 z' (fun _ => 0) u i - Q.continuationAtArrival 1 z (fun _ => 0) u i ∧
      Q.continuationAtArrival 1 z' (fun _ => 0) u i - Q.continuationAtArrival 1 z (fun _ => 0) u i ≤
        (z' - z) * max 0 (1 - u i) := by
  let A := (unseen (history Finset.univ (fun _ => 0) u (u i))).erase i
  let s := max 0 (1 - u i)
  have hs : 0 ≤ s := le_max_left _ _
  have hD := Q.restrictTo_integrable_maximum A hQ
  have hm := optimalScalarValue_mono (Q.restrictTo A) hD zero_le_one (mul_nonneg hz hs)
    (le_refl (1 : ℝ)) (mul_le_mul_of_nonneg_right hzz hs)
  have hl := optimalScalarValue_durationWeight_lipschitz (Q.restrictTo A) hD zero_le_one
    (mul_nonneg (hz.trans hzz) hs) (mul_nonneg hz hs)
  rw [abs_of_nonneg (sub_nonneg.mpr hm), ← sub_mul,
    abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hzz) hs)] at hl
  exact ⟨sub_nonneg.mpr hm, hl⟩

noncomputable def empiricalOfferSlope (z z' : ℝ) (u : Fin n → ℝ) (i : Fin n)
    (v : (((Fin n × Fin k) → ℝ) × ℝ)) : ℝ :=
  (max (max 0 v.2 - empiricalArrivalContinuation 1 z u i v.1) 0 -
    max (max 0 v.2 - empiricalArrivalContinuation 1 z' u i v.1) 0) / (z' - z)

lemma measurable_empiricalOfferSlope {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z')
    (u : Fin n → ℝ) (i : Fin n) : Measurable (empiricalOfferSlope (k := k) z z' u i) := by
  have hθ : Measurable (fun v : (((Fin n × Fin k) → ℝ) × ℝ) => empiricalArrivalContinuation 1 z u i v.1) := (measurable_empiricalArrivalContinuation (k := k) (by norm_num : (0 : ℝ) < 1) hz u i).comp measurable_fst
  have hθ' : Measurable (fun v : (((Fin n × Fin k) → ℝ) × ℝ) => empiricalArrivalContinuation 1 z' u i v.1) := (measurable_empiricalArrivalContinuation (k := k) (by norm_num : (0 : ℝ) < 1) hz' u i).comp measurable_fst
  exact (((measurable_const.max measurable_snd).sub hθ).max measurable_const |>.sub
    (((measurable_const.max measurable_snd).sub hθ').max measurable_const)).div_const _

lemma empiricalOfferSlope_bounds {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z')
    (u : Fin n → ℝ) (i : Fin n) (hui : 0 ≤ u i)
    (a : (Fin n × Fin k) → ℝ) (x : ℝ) :
    0 ≤ empiricalOfferSlope z z' u i (a, x) ∧ empiricalOfferSlope z z' u i (a, x) ≤ 1 := by
  let Q := totalEmpiricalInstance (reservoirCoordinates.symm a)
  have hθ := Q.continuationAtArrival_coefficient_difference (totalEmpiricalInstance_integrable _) hz hzz.le u i
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

lemma empiricalOfferSlope_mask (z z' : ℝ) (u : Fin n → ℝ) (i : Fin n)
    (s : Finset (Fin n × Fin k))
    (hfuture : ∀ q ∈ futureSampleRows u i, ∀ j : Fin k, (q, j) ∈ s)
    (a : (Fin n × Fin k) → ℝ) (x : ℝ) :
    empiricalOfferSlope z z' u i (ProphetSecretary.Probability.maskCoordinates s a, x) =
      empiricalOfferSlope z z' u i (a, x) := by
  simp only [empiricalOfferSlope, empiricalArrivalContinuation_mask 1 z u i s hfuture,
    empiricalArrivalContinuation_mask 1 z' u i s hfuture]

noncomputable def Instance.clockPremiumSlopeUnder (Q P : Instance n) (z z' : ℝ) (u : Fin n → ℝ) (i : Fin n) : ℝ :=
  (positivePremium (P.law i) 1 (Q.continuationAtArrival 1 z (fun _ => 0) u i) -
    positivePremium (P.law i) 1 (Q.continuationAtArrival 1 z' (fun _ => 0) u i)) / (z' - z)

lemma integral_empiricalOfferSlope (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (z z' : ℝ) (u : Fin n → ℝ) (i : Fin n) (a : (Fin n × Fin k) → ℝ) :
    (∫ x, empiricalOfferSlope z z' u i (a, x) ∂P.law i) =
      (totalEmpiricalInstance (reservoirCoordinates.symm a)).clockPremiumSlopeUnder P z z' u i := by
  let θ := empiricalArrivalContinuation (k := k) 1 z u i a
  let θ' := empiricalArrivalContinuation (k := k) 1 z' u i a
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
