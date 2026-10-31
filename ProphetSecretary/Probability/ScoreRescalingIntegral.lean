import ProphetSecretary.Probability.ScoreRescaling

/-!
# Integral and information identities for a fixed score scale

The scale is fixed before the law or approximation index varies. These
identities recover literal centered bounded observables from the unit scores
used in likelihood estimates, with the corresponding squared information
factor. Integrability in applications is established by boundedness.
-/

open MeasureTheory BoundedContinuousFunction
namespace ProphetSecretary.Probability

lemma information_const_mul {n : ℕ} (μ : Fin n → Measure ℝ)
    (a : ℝ) (h : Fin n → ℝ → ℝ) :
    information μ (fun i x => a*h i x)=a^2*information μ h := by
  simp only [information,mul_pow,integral_const_mul,Finset.mul_sum]

lemma mul_integral_centeredBoundedScore {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure ℝ) (f : ℝ →ᵇ ℝ) (ν : Measure Ω) (X G : Ω → ℝ) :
    boundedScoreScale f*(∫ v, centeredBoundedScore μ f (X v)*G v ∂ν)=
      ∫ v, (f (X v)-∫ x, f x ∂μ)*G v ∂ν := by
  rw [←integral_const_mul]
  simp only [←mul_assoc,boundedScoreScale_mul_centeredBoundedScore]

end ProphetSecretary.Probability
