import ProphetSecretary.Statistics.FirstProjectionGap
import ProphetSecretary.Probability.VarianceChernoff

/-!
# Gap-sensitive concentration of the pilot's first-order term

The policy and scalar are fixed before training. The summands below are the
original conditional projections of its actual kernel. Their variance bound
comes from likelihood curvature, uniformly over the number of distributions.
This supplies the exponential term in `eq:bayes-fixed-tail`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace ProphetSecretary.Model
open ProphetSecretary.Probability ProphetSecretary.Analysis
open ProphetSecretary.Probability.Hoeffding
open ProphetSecretary.Statistics.Hoeffding

lemma pilotFirstProjectionConstant_ge_one {δ : ℝ} (hδ : 0 < δ) :
    1 ≤ pilotFirstProjectionConstant δ := by
  have h := lawCurvatureConstant_nonnegative zero_le_one hδ
  unfold pilotFirstProjectionConstant
  linarith

variable {n k : ℕ} [NeZero k]

/-- The strictly positive gap case. A zero gap is treated by the trivial
probability bound rather than division by that gap. -/
theorem RandomizedPolicy.firstOrder_sample_lower_tail (π : RandomizedPolicy n) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) {δ lam : ℝ} (hδ : 0 < δ)
    (hlam : lam ∈ Icc δ (1-δ))
    (hOpt : π.scalarObjective P lam (1-lam) = optimalScalarValue P lam (1-lam))
    (hs : 0 < normalizedScalarGap P lam) :
    (P.trainingCoordinateLaw k).real {y | (k : ℝ)⁻¹*∑ q : Fin n × Fin k,
      firstProjection P.law (π.normalizedGameKernel lam) q.1 (y q) ≤
        -normalizedScalarGap P lam/4} ≤
      Real.exp (-((k : ℝ)*normalizedScalarGap P lam/
        (64*pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)))) := by
  let s := normalizedScalarGap P lam
  let K := pilotFirstProjectionConstant δ
  let T := 1+P.totalFirstMoment
  have hk : 0 < (k : ℝ) := by exact_mod_cast NeZero.pos k
  have hK : 1 ≤ K := pilotFirstProjectionConstant_ge_one hδ
  have hT : 1 ≤ T := by dsimp only [T]; linarith only [P.totalFirstMoment_nonnegative]
  have hKT : 1 ≤ K*T := one_le_mul_of_one_le_of_one_le hK hT
  have hKP : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hTP : 0 < T := lt_of_lt_of_le zero_lt_one hT
  let X := fun q : Fin n × Fin k => fun y : (Fin n × Fin k) → ℝ =>
    (k : ℝ)⁻¹*firstProjection P.law (π.normalizedGameKernel lam) q.1 (y q)
  let b : ℝ≥0 := ⟨2/(k : ℝ),by positivity⟩
  have hLam : lam ∈ Ioc (0 : ℝ) 1 := ⟨hδ.trans_le hlam.1,by linarith only [hlam.2,hδ]⟩
  have hf := π.measurable_normalizedGameKernel lam
  have hb := π.normalizedGameKernel_abs_le_ae P hcap hLam
  have hInd : iIndepFun X (P.trainingCoordinateLaw k) := firstOrder_summands_independent P.law hf
  have hMeas (q : Fin n × Fin k) : Measurable (X q) :=
    ((measurable_firstProjection P.law hf q.1).comp (measurable_pi_apply q)).const_mul _
  have hcoe : (b : ℝ) = 2/(k : ℝ) := rfl
  have hBound (q : Fin n × Fin k) : ∀ᵐ y ∂P.trainingCoordinateLaw k, |X q y| ≤ b :=
    by
      rw [hcoe]
      simpa only [X,Instance.trainingCoordinateLaw,NNReal.coe_one,mul_one]
        using firstOrder_summand_abs_le_of_ae_bounded P.law hf 1 hb q
  have hMean (q : Fin n × Fin k) : (∫ y, X q y ∂P.trainingCoordinateLaw k) = 0 :=
    firstOrder_summand_integral_zero_of_ae_bounded P.law hf 1 hb q
  have hSum (y : (Fin n × Fin k) → ℝ) :
      (∑ q, X q y) = (k : ℝ)⁻¹*∑ q : Fin n × Fin k,
        firstProjection P.law (π.normalizedGameKernel lam) q.1 (y q) := by
    exact (Finset.mul_sum _ _ _).symm
  have hVar : variance (fun y => ∑ q, X q y) (P.trainingCoordinateLaw k) ≤ K*T*s/(k : ℝ) := by
    simpa only [hSum] using π.firstOrder_sample_variance_le_normalizedGap P hcap hδ hlam hOpt
  have hRange : (s/4)*(b : ℝ) ≤ 2*(K*T*s/(k : ℝ)) := by
    change (s/4)*(2/(k : ℝ)) ≤ _
    have h := mul_le_mul_of_nonneg_right hKT hs.le
    calc
      (s/4)*(2/(k : ℝ)) = (s/2)/(k : ℝ) := by ring
      _ ≤ (2*(K*T*s))/(k : ℝ) := div_le_div_of_nonneg_right (by nlinarith) hk.le
      _ = _ := by ring
  have h := measure_sum_le_neg hInd hMeas b hBound hMean
    (r := s/4) (v := K*T*s/(k : ℝ)) (by positivity) (by positivity) hVar hRange
  simp only [hSum] at h
  have heq : (s/4)^2/(4*(K*T*s/(k : ℝ))) = (k : ℝ)*s/(64*K*T) := by
    field_simp
    ring
  rw [heq] at h
  simpa only [s,K,T,neg_div] using h

end ProphetSecretary.Model
