import ProphetSecretary.Probability.QuarterLikelihoodBounds

/-!
# Uniform likelihood regularity for lifted finite-array scores

The common quarter interval is fixed before the array index. The Fisher,
first-moment and optimized scalar curvature constants depend only on the
common cap, moment bound, information bound and interior weight margin.
Paper correspondence: the final assertion of `updual:scorelift`.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting
open ProphetSecretary.Model ProphetSecretary.Probability ProphetSecretary.Analysis

theorem finite_score_likelihood_regularity
    (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {H S0 I δ : ℝ}
    (hH : 0≤H) (hS0 : 0≤S0) (_hI : 0≤I) (hδ : 0<δ)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H) (hS : ∀ m, (P m).totalFirstMoment≤S0)
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hMeas : ∀ m i, Measurable (score m i))
    (hBound : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hMean : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0)
    (hInfo : ∀ m, information (P m).law (score m)≤I) :
    (∀ m θ, |θ|≤1/4 →
      information ((P m).likelihoodWidePath (score m) (hMeas m) (hBound m) (hMean m) θ).law
        (fun i => tiltedScore (score m i) θ)≤(4/3)*I) ∧
    (∀ m θ, |θ|≤1/4 →
      ((P m).likelihoodWidePath (score m) (hMeas m) (hBound m) (hMean m) θ).totalFirstMoment≤(5/4)*S0) ∧
    (∀ m lam, lam∈Icc δ (1-δ) →
      let f := fun θ => optimalScalarValue ((P m).likelihoodWidePath (score m) (hMeas m) (hBound m) (hMean m) θ) lam (1-lam)
      let K := lawCoefficientRangeConstant H 1 1 δ*(1+S0)*I
      (∀ θ∈Icc (-(1/4):ℝ) (1/4), DifferentiableAt ℝ f θ) ∧
      (∀ θ∈Icc (-(1/4):ℝ) (1/4), ∀ ρ∈Icc (-(1/4):ℝ) (1/4),
        |deriv f ρ-deriv f θ|≤K*|ρ-θ|) ∧
      (∀ᵐ θ ∂volume.restrict (Ioo (-(1/4):ℝ) (1/4)), |deriv (deriv f) θ|≤K)) := by
  have hCoeff : 0≤lawCoefficientRangeConstant H 1 1 δ := by
    unfold lawCoefficientRangeConstant
    positivity
  have hK (m) : lawCoefficientRangeConstant H 1 1 δ*(1+(P m).totalFirstMoment)*information (P m).law (score m)≤
      lawCoefficientRangeConstant H 1 1 δ*(1+S0)*I := by
    have hProd := mul_le_mul (show 1+(P m).totalFirstMoment≤1+S0 by linarith only [hS m]) (hInfo m)
      (information_nonnegative (P m).law (score m)) (by positivity : 0≤1+S0)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hProd hCoeff
  refine ⟨?_,?_,?_⟩
  · intro m θ hθ
    exact ((P m).information_likelihoodWidePath_quarter_le (score m) (hMeas m) (hBound m) (hMean m) hθ).trans
      (mul_le_mul_of_nonneg_left (hInfo m) (by norm_num : (0:ℝ)≤4/3))
  · intro m θ hθ
    exact ((P m).totalFirstMoment_likelihoodWidePath_quarter_le
      ((P m).integrable_maximum_of_bounded (hCap m)) (score m) (hMeas m) (hBound m) (hMean m) hθ).trans
      (mul_le_mul_of_nonneg_left (hS m) (by norm_num : (0:ℝ)≤5/4))
  · intro m lam hlam
    have hw : 0<lam := hδ.trans_le hlam.1
    have hc : 0<1-lam := by linarith only [hlam.2,hδ]
    have hCurv := (P m).law_curvature (W := 1) (C := 1) hH hδ hw (by linarith only [hlam.2,hδ]) hc
      (by linarith only [hlam.1,hδ]) (by linarith only [hlam.2]) (hCap m)
      (score m) (hMeas m) (hBound m) (hMean m)
    refine ⟨hCurv.1,?_,?_⟩
    · intro θ hθ ρ hρ
      exact (hCurv.2.1 θ hθ ρ hρ).trans (mul_le_mul_of_nonneg_right (hK m) (abs_nonneg _))
    · exact hCurv.2.2.mono (fun _ hx => hx.trans (hK m))
end ProphetSecretary.Limiting
