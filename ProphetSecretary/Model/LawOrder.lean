import ProphetSecretary.Model.BellmanOptimal

/-!
# Stop-loss order and the optimal scalar value

For independent finite offers, increasing every marginal stop-loss transform
can only increase the optimal scalar value. The proof uses the actual finite
Bellman equation against the unrestricted policy class; it does not assert
monotonicity for arbitrary history-dependent policies.
-/

open MeasureTheory Set
open scoped BigOperators

namespace ProphetSecretary.Model

noncomputable def stopLoss (μ : Measure ℝ) (b : ℝ) : ℝ := ∫ x, max 0 (x - b) ∂μ

lemma integrable_stopLoss (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : Integrable id μ) (b : ℝ) :
    Integrable (fun x => max 0 (x - b)) μ :=
  (integrable_const 0).sup (hμ.sub (integrable_const b))

lemma integral_max_eq_stopLoss (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) {w : ℝ} (hw : 0 < w) (v : ℝ) :
    (∫ x, max (w * x) v ∂μ) = v + w * stopLoss μ (v / w) := by
  have hpoint (x : ℝ) : max (w * x) v = v + w * max 0 (x - v / w) := by
    by_cases hx : v ≤ w * x
    · have hdiv : v / w ≤ x := (div_le_iff₀ hw).mpr (by nlinarith)
      rw [max_eq_left hx, max_eq_right (sub_nonneg.mpr hdiv)]
      nlinarith [div_mul_cancel₀ v hw.ne']
    · have hle : w * x ≤ v := (lt_of_not_ge hx).le
      have hdiv : x ≤ v / w := (le_div_iff₀ hw).mpr (by nlinarith)
      rw [max_eq_right hle, max_eq_left (sub_nonpos.mpr hdiv), mul_zero, add_zero]
  have heq : (∫ x, max (w * x) v ∂μ) = ∫ x, v + w * max 0 (x - v / w) ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall hpoint)
  rw [heq, integral_add (integrable_const v) ((integrable_stopLoss μ hμ (v / w)).const_mul w),
    integral_const_mul]
  simp only [integral_const, probReal_univ, one_smul, stopLoss]

/-- Marginal stop-loss order, with all real thresholds. -/
def Instance.StopLossLE {n : ℕ} (P Q : Instance n) : Prop :=
  ∀ i b, stopLoss (P.law i) b ≤ stopLoss (Q.law i) b

lemma Instance.stopLossLE_restrictTo {n : ℕ} (P Q : Instance n) (hPQ : P.StopLossLE Q)
    (A : Finset (Fin n)) : (P.restrictTo A).StopLossLE (Q.restrictTo A) :=
  fun i b => hPQ (stateEmbedding A i) b

lemma Instance.integral_max_comparison {n : ℕ} (P Q : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hPQ : P.StopLossLE Q) (i : Fin n) {w v v' : ℝ} (hw : 0 < w) (hv : v ≤ v') :
    (∫ x, max (w * x) v ∂P.law i) ≤ ∫ x, max (w * x) v' ∂Q.law i := by
  have hp := (P.integrable_maximum_iff.mp hP) i
  have hq := (Q.integrable_maximum_iff.mp hQ) i
  have hfirst : (∫ x, max (w * x) v ∂P.law i) ≤ ∫ x, max (w * x) v' ∂P.law i :=
    integral_mono ((hp.const_mul w).sup (integrable_const v))
      ((hp.const_mul w).sup (integrable_const v')) (fun x => max_le_max le_rfl hv)
  apply hfirst.trans
  rw [integral_max_eq_stopLoss _ hp hw, integral_max_eq_stopLoss _ hq hw]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (hPQ i (v' / w)) hw.le)

/-- Stop-loss monotonicity of the actual general-policy optimum. The induction
also ranges over every nonnegative duration coefficient in every remaining state. -/
theorem Instance.optimalScalarValue_mono_stopLoss {n : ℕ} (P Q : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hPQ : P.StopLossLE Q) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    optimalScalarValue P w c ≤ optimalScalarValue Q w c := by
  suffices h : ∀ m (P Q : Instance m), Integrable Instance.maximum P.valuesLaw →
      Integrable Instance.maximum Q.valuesLaw → P.StopLossLE Q →
      ∀ w c : ℝ, 0 < w → 0 ≤ c → optimalScalarValue P w c ≤ optimalScalarValue Q w c from
    h n P Q hP hQ hPQ w c hw hc
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro P Q hP hQ hPQ w c hw hc
    cases m with
    | zero => rw [optimalScalarValue_empty, optimalScalarValue_empty]
    | succ n =>
      rw [P.optimalScalarValue_eq_bellmanValue hP hw hc,
        Q.optimalScalarValue_eq_bellmanValue hQ hw hc, Instance.bellmanValue, Instance.bellmanValue]
      apply Finset.sum_le_sum
      intro i _
      have hPfirst := P.integrable_bellmanFirstPayoff hP i hw.le hc
      have hQfirst := Q.integrable_bellmanFirstPayoff hQ i hw.le hc
      rw [integral_prod _ hPfirst, integral_prod _ hQfirst]
      apply integral_mono hPfirst.integral_prod_left hQfirst.integral_prod_left
      intro t
      have hchild : P.bellmanContinuation i w c t ≤ Q.bellmanContinuation i w c t :=
        ih (remainingSet i).card (remainingSet_card_lt i)
          (P.restrictTo (remainingSet i)) (Q.restrictTo (remainingSet i))
          (P.restrictTo_integrable_maximum _ hP) (Q.restrictTo_integrable_maximum _ hQ)
          (P.stopLossLE_restrictTo Q hPQ _) w (c * max 0 (1 - t)) hw
          (mul_nonneg hc (le_max_left _ _))
      have hp := (P.integrable_maximum_iff.mp hP) i
      have hq := (Q.integrable_maximum_iff.mp hQ) i
      have hpmax : Integrable (fun x => max (w * x) (P.bellmanContinuation i w c t)) (P.law i) :=
        (hp.const_mul w).sup (integrable_const _)
      have hqmax : Integrable (fun x => max (w * x) (Q.bellmanContinuation i w c t)) (Q.law i) :=
        (hq.const_mul w).sup (integrable_const _)
      change (∫ x, c * t + max (w * x) (P.bellmanContinuation i w c t) ∂P.law i) ≤
        ∫ x, c * t + max (w * x) (Q.bellmanContinuation i w c t) ∂Q.law i
      rw [integral_add (integrable_const (c * t)) hpmax,
        integral_add (integrable_const (c * t)) hqmax]
      simp only [integral_const, probReal_univ, one_smul]
      exact add_le_add le_rfl (P.integral_max_comparison Q hP hQ hPQ i hw hchild)

theorem Instance.optimalScalarValue_mono_stopLoss_nonnegative {n : ℕ} (P Q : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (hPQ : P.StopLossLE Q) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue P w c ≤ optimalScalarValue Q w c := by
  by_cases hw0 : w = 0
  · subst w
    rw [optimalScalarValue_zero_rewardWeight P hc, optimalScalarValue_zero_rewardWeight Q hc]
  · exact P.optimalScalarValue_mono_stopLoss Q hP hQ hPQ (lt_of_le_of_ne hw (Ne.symm hw0)) hc

end ProphetSecretary.Model
