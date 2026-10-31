import ProphetSecretary.Statistics.PremiumRecursion
import ProphetSecretary.Statistics.PremiumKacAlgebra

/-!
# Finite positive-premium Kac bounds

Paper correspondence: `upstat:kac`. Strong finite induction uses actual first-arrival
sampling and the exact premium mean. The strengthened bounds retain the first moment,
then yield the manuscript's constants three and thirteen uniformly in instance size.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.integrable_firstChild_unstoppedPremium_pow (Q : Instance (n + 1))
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (i : Fin (n + 1)) (p : ℕ) :
    Integrable (fun z : ℝ × (Fin (remainingSet i).card → ℝ) =>
      Q.unstoppedPremium w c (Instance.firstChildClocks i z) ^ p)
      ((Instance.firstChildTimeLaw i).prod (Instance.clocksLaw (remainingSet i).card)) :=
  (Instance.firstChildClocks_measurePreserving i).integrable_comp_of_integrable
    (Q.integrable_unstoppedPremium_pow hQ hw hc p).integrableOn

/-- Strengthened second and third moments before discarding the mean factor. -/
theorem Instance.unstoppedPremium_kac_strengthened {m : ℕ} (Q : Instance m)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (∫ u, Q.unstoppedPremium w c u ^ 2 ∂Instance.clocksLaw m) ≤
      3 * optimalScalarValue Q w c * (∫ u, Q.unstoppedPremium w c u ∂Instance.clocksLaw m) ∧
    (∫ u, Q.unstoppedPremium w c u ^ 3 ∂Instance.clocksLaw m) ≤
      13 * optimalScalarValue Q w c ^ 2 * (∫ u, Q.unstoppedPremium w c u ∂Instance.clocksLaw m) := by
  induction m using Nat.strong_induction_on generalizing w c with
  | h m ih =>
    cases m with
    | zero => simp [Instance.unstoppedPremium]
    | succ n =>
      let v := optimalScalarValue Q w c
      have hv : 0 ≤ v := optimalScalarValue_nonnegative Q hQ hw.le hc
      let F : Fin (n + 1) → ℕ → ℝ → ℝ := fun i p t => ∫ a,
        Q.unstoppedPremium w c (Instance.firstChildClocks i (t, a)) ^ p
          ∂Instance.clocksLaw (remainingSet i).card
      have hIF (i : Fin (n + 1)) (p : ℕ) : Integrable (F i p) (Instance.firstChildTimeLaw i) :=
        (Q.integrable_firstChild_unstoppedPremium_pow hQ hw hc i p).integral_prod_left
      have hDecomp (p : ℕ) : (∫ u, Q.unstoppedPremium w c u ^ p ∂Instance.clocksLaw (n + 1)) =
          ∑ i : Fin (n + 1), ∫ t, F i p t ∂Instance.firstChildTimeLaw i :=
        Instance.integral_firstArrival_child ((Q.measurable_unstoppedPremium hQ hw hc).pow_const p)
          (Q.integrable_unstoppedPremium_pow hQ hw hc p)
      have hpoint (i : Fin (n + 1)) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1 ∧ t < 1) :
          F i 2 t ≤ 3 * v * F i 1 t ∧ F i 3 t ≤ 13 * v ^ 2 * F i 1 t := by
        let D := Q.restrictTo (remainingSet i)
        let d := c * (1 - t)
        let s := optimalScalarValue D w d
        let a := positivePremium (Q.law i) w (Q.bellmanContinuation i w c t)
        let B : (Fin (remainingSet i).card → ℝ) → ℝ := D.unstoppedPremium w d
        let b := ∫ u, B u ∂Instance.clocksLaw (remainingSet i).card
        have hD := Q.restrictTo_integrable_maximum (remainingSet i) hQ
        have hd : 0 ≤ d := mul_nonneg hc (sub_nonneg.mpr ht.1.2)
        have hs : 0 ≤ s := optimalScalarValue_nonnegative D hD hw.le hd
        have ha : 0 ≤ a := positivePremium_nonnegative _ _ _
        have hb : 0 ≤ b := integral_nonneg (D.unstoppedPremium_nonnegative w d)
        have hav : a ≤ v := Q.firstPremium_le_initialValue hQ hw hc t i
        have hsv : s ≤ v := by
          have h := Q.bellmanContinuation_le_initialValue hQ hw hc ht.1.1 i
          change optimalScalarValue D w (c * max 0 (1 - t)) ≤ v at h
          rw [max_eq_right (sub_nonneg.mpr ht.1.2)] at h
          exact h
        have hbs : b ≤ s := by
          have h := D.integral_unstoppedPremium hD hw hd
          change b = s - d at h
          linarith
        have hB1 : Integrable B (Instance.clocksLaw (remainingSet i).card) := by
          simpa only [pow_one] using D.integrable_unstoppedPremium_pow hD hw hd 1
        have hB2 : Integrable (fun u => B u ^ 2) (Instance.clocksLaw (remainingSet i).card) :=
          D.integrable_unstoppedPremium_pow hD hw hd 2
        have hB3 : Integrable (fun u => B u ^ 3) (Instance.clocksLaw (remainingSet i).card) :=
          D.integrable_unstoppedPremium_pow hD hw hd 3
        have hchild := ih (remainingSet i).card (remainingSet_card_lt i) D hD hw hd
        have heq (p : ℕ) : F i p t = ∫ u, (a + B u) ^ p ∂Instance.clocksLaw (remainingSet i).card := by
          apply integral_congr_ae
          filter_upwards [Instance.clocks_positive (m := (remainingSet i).card)] with u hu
          exact congrArg (fun z : ℝ => z ^ p) (Q.unstoppedPremium_firstStep hQ hw hc i ht.2 u hu)
        have hF1 : F i 1 t = a + b := by
          rw [heq 1]
          simp only [pow_one]
          rw [integral_add (f := fun _ => a) (g := B) (integrable_const _) hB1,
            integral_const, probReal_univ, one_smul]
        have hF2 : F i 2 t = a ^ 2 + 2 * a * b + ∫ u, B u ^ 2 ∂Instance.clocksLaw (remainingSet i).card := by
          rw [heq 2]
          exact ProphetSecretary.Statistics.integral_const_add_pow_two _ a hB1 hB2
        have hF3 : F i 3 t = a ^ 3 + 3 * a ^ 2 * b + 3 * a * (∫ u, B u ^ 2 ∂Instance.clocksLaw (remainingSet i).card) +
            ∫ u, B u ^ 3 ∂Instance.clocksLaw (remainingSet i).card := by
          rw [heq 3]
          exact ProphetSecretary.Statistics.integral_const_add_pow_three _ a hB1 hB2 hB3
        constructor
        · rw [hF2, hF1]
          exact ProphetSecretary.Statistics.kac_quadratic_step ha hb hs hv hav hbs hsv hchild.1
        · rw [hF3, hF1]
          exact ProphetSecretary.Statistics.kac_cubic_step ha hb hs hv hav hbs hsv hchild.1 hchild.2
      have hintegrate (p : ℕ) (K : ℝ)
          (hpt : ∀ (i : Fin (n + 1)) {t : ℝ}, t ∈ Icc (0 : ℝ) 1 ∧ t < 1 → F i p t ≤ K * F i 1 t) :
          (∫ u, Q.unstoppedPremium w c u ^ p ∂Instance.clocksLaw (n + 1)) ≤
            K * (∫ u, Q.unstoppedPremium w c u ∂Instance.clocksLaw (n + 1)) := by
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
          _ = K * (∫ u, Q.unstoppedPremium w c u ∂Instance.clocksLaw (n + 1)) := by
            rw [← hDecomp 1]
            simp only [pow_one]
      exact ⟨hintegrate 2 (3 * v) (fun i _ ht => (hpoint i ht).1),
        hintegrate 3 (13 * v ^ 2) (fun i _ ht => (hpoint i ht).2)⟩

/-- The manuscript's finite quadratic and cubic Kac bounds, with explicit constants. -/
theorem Instance.unstoppedPremium_kac {m : ℕ} (Q : Instance m)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (∫ u, Q.unstoppedPremium w c u ^ 2 ∂Instance.clocksLaw m) ≤ 3 * optimalScalarValue Q w c ^ 2 ∧
    (∫ u, Q.unstoppedPremium w c u ^ 3 ∂Instance.clocksLaw m) ≤ 13 * optimalScalarValue Q w c ^ 3 := by
  have h := Q.unstoppedPremium_kac_strengthened hQ hw hc
  have hm := Q.integral_unstoppedPremium hQ hw hc
  rw [hm] at h
  have hv := optimalScalarValue_nonnegative Q hQ hw.le hc
  constructor <;> nlinarith [mul_nonneg hv hc, mul_nonneg (sq_nonneg (optimalScalarValue Q w c)) hc]

end ProphetSecretary.Model
