import ProphetSecretary.Probability.PoissonFixedPayoff

/-!
# Uniform second-order Poisson payoff remainder

The payoff is fixed throughout interpolation of the likelihood parameter.
The explicit bound 2C rate θ² is independent of the underlying realization
space, count magnitude and instance size.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal

namespace ProphetSecretary.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

lemma poissonPayoff_taylor_bound (μ : Measure Ω) [IsProbabilityMeasure μ] (rate : ℝ≥0)
    (N : Ω → ℕ) (hN : Measurable N) (hLaw : HasLaw N (poissonMeasure rate) μ)
    (F : Ω → ℝ) (hF : Measurable F) {C : ℝ} (hC : 0 ≤ C)
    (hBound : ∀ᵐ x ∂μ, |F x| ≤ C) {θ : ℝ} (hθ : |θ| ≤ 1/4) :
    |poissonPayoffMean μ rate N F θ-poissonPayoffMean μ rate N F 0-
      θ*poissonPayoffFirst μ rate N F 0| ≤ 2*C*θ^2*(rate : ℝ) := by
  let f := fun s : ℝ => poissonPayoffMean μ rate N F (θ*s)
  let fd := fun s : ℝ => θ*poissonPayoffFirst μ rate N F (θ*s)
  let fdd := fun s : ℝ => θ^2*poissonPayoffSecond μ rate N F (θ*s)
  have hParam (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : |θ*s| ≤ 1/4 := by
    rw [abs_mul,abs_of_nonneg hs.1]
    exact (mul_le_mul_of_nonneg_left hs.2 (abs_nonneg θ)).trans (by simpa only [mul_one] using hθ)
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : HasDerivAt f (fd s) s := by
    have h := (poissonPayoff_derivatives μ rate N hN hLaw F hF hC hBound (hParam s hs)).1.comp s
      ((hasDerivAt_id s).const_mul θ)
    simp only [mul_one] at h
    change HasDerivAt (fun u : ℝ => poissonPayoffMean μ rate N F (θ*u))
      (poissonPayoffFirst μ rate N F (θ*s)*θ) s at h
    rw [mul_comm (poissonPayoffFirst μ rate N F (θ*s)) θ] at h
    exact h
  have hdd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : HasDerivAt fd (fdd s) s := by
    have h := ((poissonPayoff_derivatives μ rate N hN hLaw F hF hC hBound (hParam s hs)).2.comp s
      ((hasDerivAt_id s).const_mul θ)).const_mul θ
    simp only [mul_one] at h
    change HasDerivAt (fun u : ℝ => θ*poissonPayoffFirst μ rate N F (θ*u))
      (θ*(poissonPayoffSecond μ rate N F (θ*s)*θ)) s at h
    have hCoefficient : θ*(poissonPayoffSecond μ rate N F (θ*s)*θ)=
        θ^2*poissonPayoffSecond μ rate N F (θ*s) := by ring
    rw [hCoefficient] at h
    exact h
  have hMeas : Measurable fdd := measurable_const.mul
    ((measurable_poissonPayoffSecond μ rate N hN F hF).comp (measurable_const.mul measurable_id))
  have hSecondBound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : |fdd s| ≤ 4*C*(rate : ℝ)*θ^2 := by
    dsimp only [fdd]
    rw [abs_mul,abs_of_nonneg (sq_nonneg θ)]
    have h := mul_le_mul_of_nonneg_left
      (poissonPayoffSecond_abs_le μ rate N hN hLaw F hF hC hBound (hParam s hs)) (sq_nonneg θ)
    nlinarith only [h]
  have h := unit_secondOrder_remainder_bound hd hdd hMeas hSecondBound
  dsimp only [f,fd] at h
  simpa only [mul_one,mul_zero,
    show (4*C*(rate : ℝ)*θ^2)/2=2*C*θ^2*(rate : ℝ) by ring] using h

end ProphetSecretary.Probability
