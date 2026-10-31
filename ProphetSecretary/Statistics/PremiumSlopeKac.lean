import ProphetSecretary.Statistics.PremiumSlopes

/-!
# Uniform moments of premium difference quotients

The mean of every future normalized premium sum is at most one. First-arrival
induction gives the same constants three and thirteen as `upstat:kac`, without a
factor involving the number of offers or the scalar value.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.premiumSlopeSum_firstStep (Q : Instance (n + 1))
    (hQ : Integrable Instance.maximum Q.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z')
    (i : Fin (n + 1)) {t : ℝ} (ht : t < 1)
    (v : Fin (remainingSet i).card → ℝ) (hv : ∀ j, 0 < v j) :
    Q.premiumSlopeSum z z' (Instance.firstChildClocks i (t, v)) =
      (positivePremium (Q.law i) 1 (Q.bellmanContinuation i 1 z t) -
        positivePremium (Q.law i) 1 (Q.bellmanContinuation i 1 z' t)) / (z' - z) +
      (1 - t) * (Q.restrictTo (remainingSet i)).premiumSlopeSum (z * (1 - t)) (z' * (1 - t)) v := by
  have hβ : 1 - t ≠ 0 := ne_of_gt (sub_pos.mpr ht)
  have hδ : z' - z ≠ 0 := ne_of_gt (sub_pos.mpr hzz)
  have hd : z' * (1 - t) - z * (1 - t) ≠ 0 := by rw [← sub_mul]; exact mul_ne_zero hδ hβ
  simp only [Instance.premiumSlopeSum,
    Q.unstoppedPremium_firstStep hQ (by norm_num : (0 : ℝ) < 1) hz i ht v hv,
    Q.unstoppedPremium_firstStep hQ (by norm_num : (0 : ℝ) < 1) (hz.trans hzz.le) i ht v hv]
  field_simp; ring

lemma Instance.firstPremiumSlope_bounds (Q : Instance (n + 1))
    (hQ : Integrable Instance.maximum Q.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z')
    (i : Fin (n + 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1 ∧ t < 1) :
    let a := (positivePremium (Q.law i) 1 (Q.bellmanContinuation i 1 z t) -
      positivePremium (Q.law i) 1 (Q.bellmanContinuation i 1 z' t)) / (z' - z)
    0 ≤ a ∧ a ≤ 1 := by
  have hv : ∀ _j : Fin (remainingSet i).card, 0 < (1 : ℝ) := fun _ => by norm_num
  have h := Q.clockPremiumSlope_bounds hQ hz hzz (Instance.firstChildClocks i (t, fun _ => 1)) i
  simp only [Instance.clockPremiumSlope] at h
  rw [Q.clockPremium_first 1 z i ht.2 (fun _ => 1) hv,
    Q.clockPremium_first 1 z' i ht.2 (fun _ => 1) hv] at h
  simp only [Instance.firstChildClocks, insertCandidate_same] at h
  exact ⟨h.1, h.2.trans (show max (0 : ℝ) (1 - t) ≤ 1 from
    max_le (by norm_num) (by linarith [ht.1.1]))⟩

/-- Strengthened Kac estimates for actual difference quotients of design premiums. -/
theorem Instance.premiumSlopeSum_kac_strengthened {m : ℕ} (Q : Instance m)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    (∫ u, Q.premiumSlopeSum z z' u ^ 2 ∂Instance.clocksLaw m) ≤
      3 * (∫ u, Q.premiumSlopeSum z z' u ∂Instance.clocksLaw m) ∧
    (∫ u, Q.premiumSlopeSum z z' u ^ 3 ∂Instance.clocksLaw m) ≤
      13 * (∫ u, Q.premiumSlopeSum z z' u ∂Instance.clocksLaw m) := by
  induction m using Nat.strong_induction_on generalizing z z' with
  | h m ih =>
    cases m with
    | zero => simp [Instance.premiumSlopeSum, Instance.unstoppedPremium]
    | succ n =>
      let F : Fin (n + 1) → ℕ → ℝ → ℝ := fun i p t => ∫ a,
        Q.premiumSlopeSum z z' (Instance.firstChildClocks i (t, a)) ^ p
          ∂Instance.clocksLaw (remainingSet i).card
      have hIF (i : Fin (n + 1)) (p : ℕ) : Integrable (F i p) (Instance.firstChildTimeLaw i) :=
        ((Instance.firstChildClocks_measurePreserving i).integrable_comp_of_integrable
          (Q.integrable_premiumSlopeSum_pow hQ hz hzz p).integrableOn).integral_prod_left
      have hDecomp (p : ℕ) : (∫ u, Q.premiumSlopeSum z z' u ^ p ∂Instance.clocksLaw (n + 1)) =
          ∑ i : Fin (n + 1), ∫ t, F i p t ∂Instance.firstChildTimeLaw i :=
        Instance.integral_firstArrival_child ((Q.measurable_premiumSlopeSum hQ hz (hz.trans hzz.le)).pow_const p)
          (Q.integrable_premiumSlopeSum_pow hQ hz hzz p)
      have hpoint (i : Fin (n + 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1 ∧ t < 1) :
          F i 2 t ≤ 3 * F i 1 t ∧ F i 3 t ≤ 13 * F i 1 t := by
        let D := Q.restrictTo (remainingSet i)
        let β := 1 - t
        let a := (positivePremium (Q.law i) 1 (Q.bellmanContinuation i 1 z t) -
          positivePremium (Q.law i) 1 (Q.bellmanContinuation i 1 z' t)) / (z' - z)
        let S := D.premiumSlopeSum (z * β) (z' * β)
        let B : (Fin (remainingSet i).card → ℝ) → ℝ := fun u => β * S u
        let b := ∫ u, B u ∂Instance.clocksLaw (remainingSet i).card
        have hD := Q.restrictTo_integrable_maximum (remainingSet i) hQ
        have hβ : 0 < β := sub_pos.mpr ht.2
        have hβ1 : β ≤ 1 := by dsimp [β]; linarith [ht.1.1]
        have hzβ : 0 ≤ z * β := mul_nonneg hz hβ.le
        have hzzβ : z * β < z' * β := mul_lt_mul_of_pos_right hzz hβ
        have ha := Q.firstPremiumSlope_bounds hQ hz hzz i ht
        have hmean := D.integral_premiumSlopeSum_bounds hD hzβ hzzβ
        have hchild := ih (remainingSet i).card (remainingSet_card_lt i) D hD hzβ hzzβ
        have hSI (p : ℕ) : Integrable (fun u => S u ^ p) (Instance.clocksLaw (remainingSet i).card) :=
          D.integrable_premiumSlopeSum_pow hD hzβ hzzβ p
        have hBI (p : ℕ) : Integrable (fun u => B u ^ p) (Instance.clocksLaw (remainingSet i).card) := by
          simpa only [B, mul_pow] using (hSI p).const_mul (β ^ p)
        have hB1 : Integrable B (Instance.clocksLaw (remainingSet i).card) := by simpa only [pow_one] using hBI 1
        have hbEq : b = β * (∫ u, S u ∂Instance.clocksLaw (remainingSet i).card) := integral_const_mul β S
        have hb : 0 ≤ b ∧ b ≤ 1 := by rw [hbEq]; exact ⟨mul_nonneg hβ.le hmean.1, (mul_le_mul hβ1 hmean.2 hmean.1 (by norm_num)).trans_eq (by ring)⟩
        have hB2 : (∫ u, B u ^ 2 ∂Instance.clocksLaw (remainingSet i).card) ≤ 3 * b := by
          simp only [B, mul_pow, integral_const_mul]
          rw [hbEq]
          calc
            _ ≤ β ^ 2 * (3 * (∫ u, S u ∂Instance.clocksLaw (remainingSet i).card)) :=
              mul_le_mul_of_nonneg_left hchild.1 (sq_nonneg β)
            _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hβ.le (sub_nonneg.mpr hβ1)) hmean.1]
        have hB3 : (∫ u, B u ^ 3 ∂Instance.clocksLaw (remainingSet i).card) ≤ 13 * b := by
          simp only [B, mul_pow, integral_const_mul]
          rw [hbEq]
          calc
            _ ≤ β ^ 3 * (13 * (∫ u, S u ∂Instance.clocksLaw (remainingSet i).card)) :=
              mul_le_mul_of_nonneg_left hchild.2 (pow_nonneg hβ.le 3)
            _ ≤ _ := by
              have hpow : β ^ 3 ≤ β := by nlinarith [mul_nonneg (mul_nonneg hβ.le (sub_nonneg.mpr hβ1)) (by linarith : 0 ≤ 1 + β)]
              nlinarith [mul_le_mul_of_nonneg_right hpow hmean.1]
        have heq (p : ℕ) : F i p t = ∫ u, (a + B u) ^ p ∂Instance.clocksLaw (remainingSet i).card := by
          apply integral_congr_ae
          filter_upwards [Instance.clocks_positive (m := (remainingSet i).card)] with u hu
          exact congrArg (fun x : ℝ => x ^ p) (Q.premiumSlopeSum_firstStep hQ hz hzz i ht.2 u hu)
        have hF1 : F i 1 t = a + b := by
          rw [heq 1]
          simp only [pow_one]
          rw [integral_add (f := fun _ => a) (g := B) (integrable_const _) hB1, integral_const, probReal_univ, one_smul]
        have hF2 : F i 2 t = a ^ 2 + 2 * a * b + ∫ u, B u ^ 2 ∂Instance.clocksLaw (remainingSet i).card := by
          rw [heq 2]
          exact ProphetSecretary.Statistics.integral_const_add_pow_two _ a hB1 (hBI 2)
        have hF3 : F i 3 t = a ^ 3 + 3 * a ^ 2 * b + 3 * a * (∫ u, B u ^ 2 ∂Instance.clocksLaw (remainingSet i).card) +
            ∫ u, B u ^ 3 ∂Instance.clocksLaw (remainingSet i).card := by
          rw [heq 3]
          exact ProphetSecretary.Statistics.integral_const_add_pow_three _ a hB1 (hBI 2) (hBI 3)
        constructor
        · rw [hF2, hF1]
          simpa using ProphetSecretary.Statistics.kac_quadratic_step ha.1 hb.1 (by norm_num : (0 : ℝ) ≤ 1)
            (by norm_num : (0 : ℝ) ≤ 1) ha.2 hb.2 (le_refl (1 : ℝ)) (by simpa using hB2)
        · rw [hF3, hF1]
          simpa using ProphetSecretary.Statistics.kac_cubic_step ha.1 hb.1 (by norm_num : (0 : ℝ) ≤ 1)
            (by norm_num : (0 : ℝ) ≤ 1) ha.2 hb.2 (le_refl (1 : ℝ)) (by simpa using hB2) (by simpa using hB3)
      have hintegrate (p : ℕ) (K : ℝ)
          (hpt : ∀ (i : Fin (n + 1)) {t : ℝ}, t ∈ Icc (0 : ℝ) 1 ∧ t < 1 → F i p t ≤ K * F i 1 t) :
          (∫ u, Q.premiumSlopeSum z z' u ^ p ∂Instance.clocksLaw (n + 1)) ≤
            K * (∫ u, Q.premiumSlopeSum z z' u ∂Instance.clocksLaw (n + 1)) := by
        rw [hDecomp p]
        calc
          _ ≤ ∑ i : Fin (n + 1), ∫ t, K * F i 1 t ∂Instance.firstChildTimeLaw i := by
            apply Finset.sum_le_sum
            intro i _
            apply integral_mono_ae (hIF i p) ((hIF i 1).const_mul K)
            filter_upwards [Instance.firstChildTimeLaw_mem_unitInterval i] with t ht
            exact hpt i ht
          _ = K * (∑ i : Fin (n + 1), ∫ t, F i 1 t ∂Instance.firstChildTimeLaw i) := by
            simp only [integral_const_mul, Finset.mul_sum]
          _ = K * (∫ u, Q.premiumSlopeSum z z' u ∂Instance.clocksLaw (n + 1)) := by
            rw [← hDecomp 1]
            simp only [pow_one]
      exact ⟨hintegrate 2 3 (fun i _ ht => (hpoint i ht).1), hintegrate 3 13 (fun i _ ht => (hpoint i ht).2)⟩

/-- Explicit uniform second and third moments for normalized scalar increments. -/
theorem Instance.premiumSlopeSum_kac {m : ℕ} (Q : Instance m)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    (∫ u, Q.premiumSlopeSum z z' u ^ 2 ∂Instance.clocksLaw m) ≤ 3 ∧
    (∫ u, Q.premiumSlopeSum z z' u ^ 3 ∂Instance.clocksLaw m) ≤ 13 := by
  have h := Q.premiumSlopeSum_kac_strengthened hQ hz hzz
  have hm := (Q.integral_premiumSlopeSum_bounds hQ hz hzz).2
  constructor <;> linarith

end ProphetSecretary.Model
