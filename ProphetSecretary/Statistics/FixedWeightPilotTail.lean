import ProphetSecretary.Statistics.FirstProjectionConcentration
import ProphetSecretary.Statistics.EmpiricalRemainderConcentration
import ProphetSecretary.Statistics.EmpiricalGapKernel

/-!
# The fixed-weight pilot lower-tail estimate

This is `eq:bayes-fixed-tail`. The scalar and true optimal policy are frozen
before training. First-order likelihood curvature and the exact higher-order
ANOVA remainder give the two terms. The actual empirical optimum dominates
the frozen policy on almost every valid training array.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators NNReal

namespace ProphetSecretary.Model
open ProphetSecretary.Probability.Hoeffding ProphetSecretary.Statistics.Hoeffding

variable {n k : ℕ} [NeZero k]

theorem RandomizedPolicy.empiricalMean_normalizedGameKernel_lower_tail
    (π : RandomizedPolicy n) (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) {δ lam : ℝ} (hδ : 0 < δ)
    (hlam : lam ∈ Icc δ (1-δ))
    (hOpt : π.scalarObjective P lam (1-lam) = optimalScalarValue P lam (1-lam))
    (hs : 0 < normalizedScalarGap P lam) :
    (P.trainingCoordinateLaw k).real
      {y | empiricalMean (π.normalizedGameKernel lam) y ≤ normalizedScalarGap P lam/2} ≤
      Real.exp (-((k : ℝ)*normalizedScalarGap P lam/
        (64*pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)))) +
      min 1 (16/((k : ℝ)^2*(normalizedScalarGap P lam)^2)) := by
  let f := π.normalizedGameKernel lam
  let s := normalizedScalarGap P lam
  have hLam : lam ∈ Ioc (0 : ℝ) 1 := ⟨hδ.trans_le hlam.1,by linarith only [hlam.2,hδ]⟩
  have hf := π.measurable_normalizedGameKernel lam
  have hb := π.normalizedGameKernel_abs_le_ae P hcap hLam
  have hMean : (∫ x, f x ∂Measure.pi P.law) = s := by
    have h := π.integral_normalizedGameKernel P hcap hLam
    rw [hOpt] at h
    exact h
  let A := {y : (Fin n × Fin k) → ℝ | (k : ℝ)⁻¹*∑ q : Fin n × Fin k,
    firstProjection P.law f q.1 (y q) ≤ -s/4}
  let B := {y : (Fin n × Fin k) → ℝ | empiricalRemainder P.law f y ≤ -s/4}
  have hSub : {y | empiricalMean f y ≤ s/2} ⊆ A ∪ B := by
    intro y hy
    by_cases hA : y ∈ A
    · exact Or.inl hA
    · right
      change ¬((k : ℝ)⁻¹*∑ q : Fin n × Fin k, firstProjection P.law f q.1 (y q) ≤ -s/4) at hA
      change empiricalRemainder P.law f y ≤ -s/4
      unfold empiricalRemainder
      rw [hMean]
      change empiricalMean f y ≤ s/2 at hy
      linarith
  have hA := π.firstOrder_sample_lower_tail (k := k) P hcap hδ hlam hOpt hs
  have hB := empiricalRemainder_lower_tail (k := k) P.law hf hb hs
  exact (measureReal_mono (μ := P.trainingCoordinateLaw k) hSub).trans
    ((measureReal_union_le A B).trans (add_le_add hA hB))

/-- The policy witness is supplied by the actual finite canonical optimizer;
no existence of a base-optimal competing policy is assumed. -/
theorem Instance.empirical_normalizedGap_lower_tail_of_pos (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) {δ lam : ℝ} (hδ : 0 < δ)
    (hlam : lam ∈ Icc δ (1-δ)) (hs : 0 < normalizedScalarGap P lam) :
    (P.trainingCoordinateLaw k).real
      {y | normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y)) lam ≤
        normalizedScalarGap P lam/2} ≤
      Real.exp (-((k : ℝ)*normalizedScalarGap P lam/
        (64*pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)))) +
      min 1 (16/((k : ℝ)^2*(normalizedScalarGap P lam)^2)) := by
  obtain ⟨π,hOpt,_⟩ := P.exists_optimal_policy_with_firstProjection_bound hcap hδ hlam
  have hLam : lam ∈ Ioc (0 : ℝ) 1 := ⟨hδ.trans_le hlam.1,by linarith only [hlam.2,hδ]⟩
  have hAE := P.empiricalMean_normalizedGameKernel_le_gap_ae (k := k) hcap π hLam
  have hSub : {y | normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y)) lam ≤
      normalizedScalarGap P lam/2} ≤ᵐ[P.trainingCoordinateLaw k]
      {y | empiricalMean (π.normalizedGameKernel lam) y ≤ normalizedScalarGap P lam/2} := by
    filter_upwards [hAE] with y hy
    intro hGap
    exact hy.trans hGap
  have hM := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hSub)
  exact hM.trans (π.empiricalMean_normalizedGameKernel_lower_tail P hcap hδ hlam hOpt hs)

/-- The complete fixed-weight bound, including zero gap. The two explicit
constants depend only on the prescribed interior interval. -/
theorem Instance.empirical_normalizedGap_lower_tail (P : Instance n)
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ 1) {δ lam : ℝ} (hδ : 0 < δ)
    (hlam : lam ∈ Icc δ (1-δ)) :
    (P.trainingCoordinateLaw k).real
      {y | normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y)) lam ≤
        normalizedScalarGap P lam/2} ≤
      Real.exp (-((k : ℝ)*normalizedScalarGap P lam/
        (64*pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)))) +
      min 1 (16/((k : ℝ)^2*(normalizedScalarGap P lam)^2)) := by
  have hLam : lam ∈ Icc (0 : ℝ) 1 :=
    ⟨(hδ.trans_le hlam.1).le,by linarith only [hlam.2,hδ]⟩
  have hs := normalizedScalarGap_nonnegative P (P.integrable_maximum_of_bounded hcap) hLam
  by_cases hs0 : normalizedScalarGap P lam = 0
  · have hRhs : Real.exp (-((k : ℝ)*normalizedScalarGap P lam/
        (64*pilotFirstProjectionConstant δ*(1+P.totalFirstMoment)))) +
        min 1 (16/((k : ℝ)^2*(normalizedScalarGap P lam)^2)) = 1 := by
      rw [hs0]
      norm_num
    rw [hRhs]
    exact (measureReal_mono (μ := P.trainingCoordinateLaw k) (subset_univ _)).trans_eq probReal_univ
  · exact P.empirical_normalizedGap_lower_tail_of_pos hcap hδ hlam (lt_of_le_of_ne hs (Ne.symm hs0))

end ProphetSecretary.Model
