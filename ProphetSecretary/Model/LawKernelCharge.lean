import ProphetSecretary.Model.LawKernelEnergy

/-! # Charging all state kernels for one candidate
The candidate's unseen-state path can visit at most one interior indifference
root. This deterministic uniqueness is applied before averaging offers.
-/
open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

theorem Instance.sum_lawAdaptationKernel_le (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (i : Fin n) (ω : World n Unit)
    (hx : 0 ≤ ω.1 i) :
    (∑ A : Finset (Fin n), P.lawAdaptationKernel hw hc.le hbound h hh hb hm θ i A ω) ≤
      4 * w ^ 2 * H * ω.1 i * information P.law h / c := by
  classical
  let Q := P.likelihoodWidePath h hh hb hm θ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  let π : Policy Unit n := (Q.valuePolicy hQ hw.le hc.le).rule
  let d := fun A ↦ P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i)
  let m := fun A ↦ π.branchMultiplier () ω.1 ω.2.1 i A (1 - d A / c)
  let E := fun A ↦ 0 < d A ∧ d A < c ∧ m A ≠ 0
  have hCross (A : Finset (Fin n)) (hA : E A) : Q.InteriorCrossing hQ i (c / w) (ω.1 i) A ω.2.1 := by
    let R := Q.restrictTo A
    have hR := Q.restrictTo_integrable_maximum A hQ
    have hRoot : d A = w * R.durationRoot hR (ω.1 i) :=
      P.lawStateRoot_eq_instanceRoot hbound h hh hb hm w θ A (ω.1 i)
    have hLevel : optimalScalarValue R 1 0 < ω.1 i := by
      by_contra hn
      have hz := R.durationRoot_eq_zero_of_le hR (le_of_not_gt hn)
      have hd0 : d A = 0 := by rw [hRoot, hz, mul_zero]
      exact hA.1.ne' hd0
    have hlt : R.durationRoot hR (ω.1 i) < c / w := by
      apply (lt_div_iff₀ hw).2
      nlinarith [hA.2.1]
    have hTime : 1 - d A / c = R.crossingTime hR (c / w) (ω.1 i) := by
      rw [hRoot]
      unfold Instance.crossingTime
      field_simp
    have hMask : (1 - d A / c) ∈ Icc (0 : ℝ) 1 ∧ otherUnseen ω.2.1 i (1 - d A / c) = A ∧
        (1 - d A / c) ≤ π.pendingTime () ω.1 ω.2.1 i := by
      by_contra hn
      have hm0 : m A = 0 := by dsimp only [m]; unfold Policy.branchMultiplier; rw [if_neg hn]
      exact hA.2.2 hm0
    have hUnseen := hMask.2.1
    rw [hTime] at hUnseen
    exact ⟨by rw [← hUnseen]; exact otherUnseen_not_mem _ _ _, hLevel, hlt, hUnseen⟩
  have hRep (A : Finset (Fin n)) : P.lawAdaptationKernel hw hc.le hbound h hh hb hm θ i A ω =
      if E A then P.lawAdaptationKernel hw hc.le hbound h hh hb hm θ i A ω else 0 := by
    by_cases hA : E A
    · rw [if_pos hA]
    rw [if_neg hA]
    change (if 0 < d A ∧ d A < c then m A * _ / (c * _) else 0) = 0
    split_ifs with hd
    · have hm0 : m A = 0 := by by_contra hn; exact hA ⟨hd.1, hd.2, hn⟩
      rw [hm0, zero_mul, zero_div]
    · rfl
  have hUnique : ∀ A B, E A → E B → A = B := by
    intro A B hA hB
    exact (hCross A hA).unique Q hQ (div_pos hc hw) (hCross B hB)
  have hBound : ∀ A, E A → P.lawAdaptationKernel hw hc.le hbound h hh hb hm θ i A ω ≤
      4 * w ^ 2 * H * ω.1 i * information P.law h / c := by
    intro A hA
    have hRatio := P.lawRoot_energy_ratio hw hc hH hbound h hh hb hm hθ A (ω.1 i) hx hA.1
    change P.lawStateParameterDerivative h hh hb hm w θ A (d A) ^ 2 /
      (c * P.lawStateCoefficientDerivative h hh hb hm w θ A (d A)) ≤ _ at hRatio
    change (if 0 < d A ∧ d A < c then m A * _ / (c * _) else 0) ≤ _
    rw [if_pos ⟨hA.1, hA.2.1⟩]
    calc
      _ = m A * (P.lawStateParameterDerivative h hh hb hm w θ A (d A) ^ 2 /
        (c * P.lawStateCoefficientDerivative h hh hb hm w θ A (d A))) := by ring
      _ ≤ P.lawStateParameterDerivative h hh hb hm w θ A (d A) ^ 2 /
        (c * P.lawStateCoefficientDerivative h hh hb hm w θ A (d A)) :=
          mul_le_of_le_one_left (div_nonneg (sq_nonneg _) (mul_pos hc
            (P.lawStateCoefficientDerivative_positive hw hA.1 hbound h hh hb hm θ A)).le)
            (π.branchMultiplier_mem_unit () ω.1 ω.2.1 i A _).2
      _ ≤ _ := hRatio
  have hInfo := information_nonnegative P.law h
  have hSum := sum_le_of_unique_event E
    (fun A ↦ P.lawAdaptationKernel hw hc.le hbound h hh hb hm θ i A ω)
    (by positivity : 0 ≤ 4 * w ^ 2 * H * ω.1 i * information P.law h / c) hUnique hBound
  calc
    _ = ∑ A : Finset (Fin n), if E A then P.lawAdaptationKernel hw hc.le hbound h hh hb hm θ i A ω else 0 :=
      Finset.sum_congr rfl (fun A _ ↦ hRep A)
    _ ≤ _ := by
      convert hSum using 1
      congr 1
      funext A
      by_cases hA : E A <;> simp [hA]

end ProphetSecretary.Model
