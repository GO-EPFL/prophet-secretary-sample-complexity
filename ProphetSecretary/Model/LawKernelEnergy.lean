import ProphetSecretary.Model.LawConditionalKernelLimit

/-! # Energy at a continuation indifference root
The law derivative keeps the continuation coefficient fixed. The coefficient
slope is the actual canonical duration, so the marginal-gain energy estimate
cancels that duration rather than replacing it by a cardinality bound.
-/
open MeasureTheory Set
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

theorem Instance.lawRoot_energy_ratio (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (A : Finset (Fin n)) (x : ℝ)
    (hx : 0 ≤ x) (hd : 0 < P.lawStateRoot hbound h hh hb hm w θ A x) :
    let d := P.lawStateRoot hbound h hh hb hm w θ A x
    P.lawStateParameterDerivative h hh hb hm w θ A d ^ 2 /
      (c * P.lawStateCoefficientDerivative h hh hb hm w θ A d) ≤
        4 * w ^ 2 * H * x * information P.law h / c := by
  let d := P.lawStateRoot hbound h hh hb hm w θ A x
  have hAbs : |θ| ≤ 1 / 2 := abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩
  let Q := (P.restrictTo A).likelihoodWideTilt (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) θ hAbs
  have hQB := (P.restrictTo A).likelihoodWideTilt_bounded (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) θ hAbs
    (fun j ↦ hbound (stateEmbedding A j))
  have hQ := Q.integrable_maximum_of_bounded hQB
  let C := Q.valuePolicy hQ hw.le hd.le
  have hDur : P.lawStateCoefficientDerivative h hh hb hm w θ A d = C.expectedDuration Q := by
    unfold Instance.lawStateCoefficientDerivative
    rw [(P.restrictTo A).likelihoodWidePath_of_mem (fun j ↦ h (stateEmbedding A j))
      (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) hAbs]
    simpa only [mul_one, one_mul] using remainingScalarValue_deriv_eq_canonicalDuration Q hQ hw zero_le_one hd
  have hT : 0 < C.expectedDuration Q := by
    rw [← hDur]
    exact P.lawStateCoefficientDerivative_positive hw hd hbound h hh hb hm θ A
  have hValue : w * C.expectedReward Q + d * C.expectedDuration Q = w * x := by
    rw [← C.scalarObjective_eq Q hQ, Q.valuePolicy_optimal hQ hw hd.le]
    have hV := P.lawStateRoot_value hw hbound h hh hb hm θ A x hd
    rw [(P.restrictTo A).likelihoodWidePath_of_mem (fun j ↦ h (stateEmbedding A j))
      (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) hAbs] at hV
    exact hV
  have hR : C.expectedReward Q ≤ x := by nlinarith [mul_nonneg hd.le hT.le]
  have hE := (P.restrictTo A).optimalScalarValue_likelihoodWidePath_gradient_energy_base hw hd hH
    (fun j ↦ hbound (stateEmbedding A j)) (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) hθ
  change P.lawStateParameterDerivative h hh hb hm w θ A d ^ 2 ≤
    4 * w ^ 2 * H * C.expectedDuration Q * C.expectedReward Q *
      information (P.restrictTo A).law (fun j ↦ h (stateEmbedding A j)) at hE
  have hI := P.information_restrictTo_le A h
  have hEnergy : P.lawStateParameterDerivative h hh hb hm w θ A d ^ 2 ≤
      4 * w ^ 2 * H * C.expectedDuration Q * x * information P.law h := by
    apply hE.trans
    have hFirst := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 4 * w ^ 2 * H * C.expectedDuration Q))
      (information_nonnegative (P.restrictTo A).law (fun j ↦ h (stateEmbedding A j)))
    exact hFirst.trans (mul_le_mul_of_nonneg_left hI (by positivity))
  change P.lawStateParameterDerivative h hh hb hm w θ A d ^ 2 /
    (c * P.lawStateCoefficientDerivative h hh hb hm w θ A d) ≤ _
  rw [hDur]
  apply (div_le_iff₀ (mul_pos hc hT)).2
  apply hEnergy.trans_eq
  field_simp

end ProphetSecretary.Model
