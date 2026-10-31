import ProphetSecretary.Limiting.HybridScalarMixture
import ProphetSecretary.Limiting.FinitePotentialBranch
import ProphetSecretary.Model.VariableDeletion

/-!
# First-moment cost of the anonymous component

The bound applies to every shared hybrid rule, including randomized policies
that use the entire observed anonymous past. It follows from finite-law
stop-loss stability and the actual integrable count mixture.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ}

lemma appendIID_value_le_firstMoment (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (N : ℕ) (hP : Integrable Model.Instance.maximum P.valuesLaw)
    (hI : Integrable id κ) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Model.optimalScalarValue (appendIID P κ hκ N) w c ≤
      Model.optimalScalarValue P w c + w * (N : ℝ) * ∫ x, x ∂κ := by
  let d : Fin (n + N) → ℝ := Fin.addCases (fun _ => 0) (fun _ => ∫ x, x ∂κ)
  have hd (i : Fin (n + N)) : 0 ≤ d i := by
    induction i using Fin.addCases with
    | left i => simp [d]
    | right j => simpa only [d, Fin.addCases_right] using integral_nonneg_of_ae hκ
  have herror (i : Fin (n + N)) (b : ℝ) :
      Model.stopLoss ((appendIID P κ hκ N).law i) b ≤ Model.stopLoss ((P.appendZeros N).law i) b + d i := by
    induction i using Fin.addCases with
    | left i => simp [appendIID, Model.Instance.appendZeros, d]
    | right j =>
      simpa only [appendIID, Model.Instance.appendZeros, d, Fin.addCases_right] using
        Model.stopLoss_le_zero_add_mean κ hI hκ b
  have hI' : Integrable (fun x : ℝ => x) κ := by convert! hI using 1
  have h := (appendIID P κ hκ N).optimalScalarValue_le_of_stopLoss_error (P.appendZeros N)
    (appendIID_integrable_maximum P κ hκ N hP hI') (P.appendZeros_integrable_maximum N hP) d hd herror hw hc
  rw [P.optimalScalarValue_appendZeros N hP hw.le hc] at h
  have hsum : (∑ i, d i) = (N : ℝ) * ∫ x, x ∂κ := by simp [d, Fin.sum_univ_add]
  rw [hsum] at h
  simpa only [mul_assoc] using h

lemma RandomizedHybridPolicy.scalarObjective_le_finiteValue_add_firstMoment (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity ≠ 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    π.scalarObjective B w c ≤ Model.optimalScalarValue B.individuals w c +
      w * (B.intensity.mass : ℝ) * ∫ x, x ∂(B.intensity.normalize : Measure ℝ) := by
  let κ : Measure ℝ := B.intensity.normalize
  have hκ : ∀ᵐ x ∂κ, 0 ≤ x :=
    (normalized_ae B.intensity hμ B.intensity_supported).mono (fun _ hx => hx.1.le)
  have hP := B.individuals.integrable_maximum_of_bounded B.individual_bounded
  have hI := B.normalizedMark_integrable hμ
  have hs := π.hasSum_scalarObjective_branches B ha hμ w c
  have hwts : HasSum (poissonWeight B.intensity.mass) 1 := by
    convert! hasSum_one_poissonMeasure B.intensity.mass using 1
  let V := Model.optimalScalarValue B.individuals w c
  let m := ∫ x, x ∂κ
  have hu := (hwts.mul_right V).add ((hasSum_poisson_first B.intensity.mass).mul_right (w * m))
  have hle := Summable.tsum_le_tsum
    (fun N => ?_) hs.summable hu.summable
  · rw [hs.tsum_eq, hu.tsum_eq] at hle
    dsimp only [V, m, κ] at hle
    nlinarith only [hle]
  · have hN := (Model.scalarObjective_le_optimal (π.finiteEvaluation N) (appendIID B.individuals κ hκ N)
      (appendIID_integrable_maximum B.individuals κ hκ N hP (by convert! hI using 1)) hw.le hc).trans
        (appendIID_value_le_firstMoment B.individuals κ hκ N hP hI hw hc)
    have hn : 0 ≤ poissonWeight B.intensity.mass N := by unfold poissonWeight; positivity
    have hb := mul_le_mul_of_nonneg_left hN hn
    dsimp only [V, m]
    convert hb using 1
    ring

lemma FiniteIntensityHybridInstance.value_le_finiteValue_add_firstMoment (B : FiniteIntensityHybridInstance n)
    (ha : B.terminal = 0) (hμ : B.intensity ≠ 0) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    B.optimalScalarValue w c ≤ Model.optimalScalarValue B.individuals w c +
      w * (B.intensity.mass : ℝ) * ∫ x, x ∂(B.intensity.normalize : Measure ℝ) := by
  apply csSup_le (B.scalarPayoffs_nonempty w c)
  rintro _ ⟨π, rfl⟩
  exact π.scalarObjective_le_finiteValue_add_firstMoment B ha hμ hw hc

end ProphetSecretary.Limiting
