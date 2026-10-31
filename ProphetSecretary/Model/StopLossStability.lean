import ProphetSecretary.Model.LawOrder
import ProphetSecretary.Model.FirstArrivalIntegral

/-!
# Quantitative stop-loss comparison

A marginal stop-loss error d_i contributes at most w*d_i to the general-policy
scalar optimum. The sum is explicit and there is no additional instance-size
factor. This includes deleting a rare variable and finite coupling comparisons.
-/

open MeasureTheory Set
open scoped BigOperators

namespace ProphetSecretary.Model

lemma sum_stateEmbedding {n : ℕ} (A : Finset (Fin n)) (d : Fin n → ℝ) :
    (∑ j : Fin A.card, d (stateEmbedding A j)) = ∑ i ∈ A, d i := by
  have hA : Finset.univ.image (stateEmbedding A) = A := A.image_orderEmbOfFin_univ rfl
  calc
    _ = ∑ i ∈ Finset.univ.image (stateEmbedding A), d i :=
      (Finset.sum_image (by intro i _ j _ hij; exact (stateEmbedding A).injective hij)).symm
    _ = _ := congrArg (fun S : Finset (Fin n) => ∑ i ∈ S, d i) hA

lemma sum_remaining_state_add {n : ℕ} (i : Fin (n + 1)) (d : Fin (n + 1) → ℝ) :
    (∑ j : Fin (remainingSet i).card, d (stateEmbedding (remainingSet i) j)) + d i = ∑ j, d j := by
  rw [sum_stateEmbedding]
  exact Finset.sum_erase_add _ _ (Finset.mem_univ i)

lemma Instance.firstChildTimeLaws_totalMass (n : ℕ) :
    (∑ i : Fin (n + 1), (firstChildTimeLaw i).real Set.univ) = 1 := by
  have h := Instance.integral_firstArrival_child (n := n) (f := fun _ => (1 : ℝ))
    measurable_const (integrable_const 1)
  simpa only [integral_const, probReal_univ, one_smul, smul_eq_mul, mul_one] using h.symm

lemma Instance.integral_max_error_comparison {n : ℕ} (P Q : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (d : Fin n → ℝ) (herror : ∀ i b, stopLoss (P.law i) b ≤ stopLoss (Q.law i) b + d i)
    (i : Fin n) {w v v' z : ℝ} (hw : 0 < w) (hz : 0 ≤ z) (hv : v ≤ v' + z) :
    (∫ x, max (w * x) v ∂P.law i) ≤ (∫ x, max (w * x) v' ∂Q.law i) + z + w * d i := by
  have hp := (P.integrable_maximum_iff.mp hP) i
  have hq := (Q.integrable_maximum_iff.mp hQ) i
  have hpv : Integrable (fun x => max (w * x) v) (P.law i) :=
    (hp.const_mul w).sup (integrable_const v)
  have hpv' : Integrable (fun x => max (w * x) v') (P.law i) :=
    (hp.const_mul w).sup (integrable_const v')
  have hpoint (x : ℝ) : max (w * x) v ≤ max (w * x) v' + z := by
    apply max_le
    · have h := le_max_left (w * x) v'
      linarith only [h, hz]
    · have h := le_max_right (w * x) v'
      linarith only [h, hv]
  have hshift : (∫ x, max (w * x) v ∂P.law i) ≤ (∫ x, max (w * x) v' ∂P.law i) + z := by
    have h := integral_mono hpv (hpv'.add (integrable_const z)) hpoint
    change (∫ x, max (w * x) v ∂P.law i) ≤ ∫ x, max (w * x) v' + z ∂P.law i at h
    rw [integral_add hpv' (integrable_const z)] at h
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hlaw : (∫ x, max (w * x) v' ∂P.law i) ≤
      (∫ x, max (w * x) v' ∂Q.law i) + w * d i := by
    rw [integral_max_eq_stopLoss _ hp hw, integral_max_eq_stopLoss _ hq hw]
    have h := mul_le_mul_of_nonneg_left (herror i (v' / w)) hw.le
    nlinarith only [h]
  nlinarith only [hshift, hlaw]

/-- Explicit marginal-error budget for the actual optimum over all randomized,
history-dependent policies. The Bellman proof accounts for every removed identity. -/
theorem Instance.optimalScalarValue_le_of_stopLoss_error {n : ℕ} (P Q : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (hQ : Integrable Instance.maximum Q.valuesLaw)
    (d : Fin n → ℝ) (hd : ∀ i, 0 ≤ d i)
    (herror : ∀ i b, stopLoss (P.law i) b ≤ stopLoss (Q.law i) b + d i)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    optimalScalarValue P w c ≤ optimalScalarValue Q w c + w * ∑ i, d i := by
  suffices h : ∀ m (P Q : Instance m), Integrable Instance.maximum P.valuesLaw →
      Integrable Instance.maximum Q.valuesLaw → ∀ d : Fin m → ℝ, (∀ i, 0 ≤ d i) →
      (∀ i b, stopLoss (P.law i) b ≤ stopLoss (Q.law i) b + d i) →
      ∀ w c : ℝ, 0 < w → 0 ≤ c →
        optimalScalarValue P w c ≤ optimalScalarValue Q w c + w * ∑ i, d i from
    h n P Q hP hQ d hd herror w c hw hc
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro P Q hP hQ d hd herror w c hw hc
    cases m with
    | zero => simp [optimalScalarValue_empty]
    | succ n =>
      let budget := w * ∑ j : Fin (n + 1), d j
      have hper (i : Fin (n + 1)) :
          (∫ z, P.bellmanFirstPayoff i w c z ∂(firstChildTimeLaw i).prod (P.law i)) ≤
          (∫ z, Q.bellmanFirstPayoff i w c z ∂(firstChildTimeLaw i).prod (Q.law i)) +
            budget * (firstChildTimeLaw i).real Set.univ := by
        have hPfirst := P.integrable_bellmanFirstPayoff hP i hw.le hc
        have hQfirst := Q.integrable_bellmanFirstPayoff hQ i hw.le hc
        have hinner (t : ℝ) :
            (∫ x, P.bellmanFirstPayoff i w c (t, x) ∂P.law i) ≤
              (∫ x, Q.bellmanFirstPayoff i w c (t, x) ∂Q.law i) + budget := by
          let dchild : Fin (remainingSet i).card → ℝ := fun j => d (stateEmbedding (remainingSet i) j)
          let childBudget := w * ∑ j, dchild j
          have hchild : P.bellmanContinuation i w c t ≤ Q.bellmanContinuation i w c t + childBudget :=
            ih (remainingSet i).card (remainingSet_card_lt i)
              (P.restrictTo (remainingSet i)) (Q.restrictTo (remainingSet i))
              (P.restrictTo_integrable_maximum _ hP) (Q.restrictTo_integrable_maximum _ hQ)
              dchild (fun j => hd _) (fun j b => herror _ b) w (c * max 0 (1 - t)) hw
              (mul_nonneg hc (le_max_left _ _))
          have hchildBudget : 0 ≤ childBudget := by
            dsimp [childBudget]
            exact mul_nonneg hw.le (Finset.sum_nonneg fun j _ => hd _)
          have hbudget : childBudget + w * d i = budget := by
            dsimp [childBudget, budget, dchild]
            rw [← mul_add, sum_remaining_state_add]
          have hmean := P.integral_max_error_comparison Q hP hQ d herror i hw hchildBudget hchild
          have hpmax : Integrable (fun x => max (w * x) (P.bellmanContinuation i w c t)) (P.law i) :=
            (((P.integrable_maximum_iff.mp hP) i).const_mul w).sup (integrable_const _)
          have hqmax : Integrable (fun x => max (w * x) (Q.bellmanContinuation i w c t)) (Q.law i) :=
            (((Q.integrable_maximum_iff.mp hQ) i).const_mul w).sup (integrable_const _)
          change (∫ x, c * t + max (w * x) (P.bellmanContinuation i w c t) ∂P.law i) ≤
            (∫ x, c * t + max (w * x) (Q.bellmanContinuation i w c t) ∂Q.law i) + budget
          rw [integral_add (integrable_const _) hpmax, integral_add (integrable_const _) hqmax]
          simp only [integral_const, probReal_univ, one_smul]
          nlinarith only [hmean, hbudget]
        have houter := integral_mono hPfirst.integral_prod_left
          (hQfirst.integral_prod_left.add (integrable_const budget)) hinner
        change (∫ t, (∫ x, P.bellmanFirstPayoff i w c (t, x) ∂P.law i) ∂firstChildTimeLaw i) ≤
          ∫ t, (∫ x, Q.bellmanFirstPayoff i w c (t, x) ∂Q.law i) + budget ∂firstChildTimeLaw i at houter
        rw [integral_add hQfirst.integral_prod_left (integrable_const budget)] at houter
        rw [integral_prod _ hPfirst, integral_prod _ hQfirst]
        simpa only [integral_const, smul_eq_mul, mul_comm] using houter
      rw [P.optimalScalarValue_eq_bellmanValue hP hw hc, Q.optimalScalarValue_eq_bellmanValue hQ hw hc]
      unfold Instance.bellmanValue
      calc
        _ ≤ ∑ i : Fin (n + 1), ((∫ z, Q.bellmanFirstPayoff i w c z
            ∂(firstChildTimeLaw i).prod (Q.law i)) + budget * (firstChildTimeLaw i).real Set.univ) :=
          Finset.sum_le_sum fun i _ => hper i
        _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Instance.firstChildTimeLaws_totalMass, mul_one]

end ProphetSecretary.Model
