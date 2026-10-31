import ProphetSecretary.Limiting.HybridValueThreshold

/-!
# Positive scaling of actual hybrid scalar weights

A fixed policy's objective scales linearly. Passing this identity through the
unrestricted policy supremum proves homogeneity without selecting an optimizer.
The actual-continuation threshold rule is unchanged by positive scaling.
-/
open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma RandomizedHybridPolicy.scalarObjective_smul (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (a w c : ℝ) :
    π.scalarObjective B (a*w) (a*c) = a*π.scalarObjective B w c := by
  rw [π.scalarObjective_eq,π.scalarObjective_eq]
  ring

lemma FiniteIntensityHybridInstance.optimalScalarValue_smul (B : FiniteIntensityHybridInstance n)
    {a w c : ℝ} (ha : 0 ≤ a) :
    B.optimalScalarValue (a*w) (a*c) = a*B.optimalScalarValue w c := by
  have hUpper : B.optimalScalarValue (a*w) (a*c) ≤ a*B.optimalScalarValue w c := by
    apply csSup_le (B.scalarPayoffs_nonempty (a*w) (a*c))
    rintro v ⟨π,rfl⟩
    change π.scalarObjective B (a*w) (a*c) ≤ a*B.optimalScalarValue w c
    rw [π.scalarObjective_smul]
    exact mul_le_mul_of_nonneg_left (B.scalarObjective_le_value π w c) ha
  apply le_antisymm hUpper
  by_cases ha0 : a=0
  · subst a
    simpa only [zero_mul] using B.optimalScalarValue_nonnegative (w := 0) (c := 0) le_rfl le_rfl
  have haP : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hLower : B.optimalScalarValue w c ≤ B.optimalScalarValue (a*w) (a*c)/a := by
    apply csSup_le (B.scalarPayoffs_nonempty w c)
    rintro v ⟨π,rfl⟩
    apply (le_div_iff₀ haP).mpr
    have h := B.scalarObjective_le_value π (a*w) (a*c)
    rw [π.scalarObjective_smul] at h
    simpa only [mul_comm] using h
  have h := (le_div_iff₀ haP).mp hLower
  simpa only [mul_comm] using h

lemma FiniteIntensityHybridInstance.continuationValue_smul (B : FiniteIntensityHybridInstance n)
    {a w c : ℝ} (ha : 0 ≤ a) (u : ℝ≥0) :
    B.continuationValue (a*w) (a*c) u = a*B.continuationValue w c u := by
  unfold FiniteIntensityHybridInstance.continuationValue
  rw [mul_assoc a c (u : ℝ),(B.remainingHorizon u).optimalScalarValue_smul ha]

lemma FiniteIntensityHybridInstance.valueHybridThreshold_smul (B : FiniteIntensityHybridInstance n)
    {a w c : ℝ} (ha : 0 < a) (A : Finset (Fin n)) (t : ℝ) (i : Option (Fin n)) :
    B.valueHybridThreshold (a*w) (a*c) () A t i = B.valueHybridThreshold w c () A t i := by
  unfold FiniteIntensityHybridInstance.valueHybridThreshold
  rw [FiniteIntensityHybridInstance.continuationValue_smul _ ha.le]
  exact mul_div_mul_left _ _ ha.ne'

lemma FiniteIntensityHybridInstance.valueRule_smul (B : FiniteIntensityHybridInstance n)
    {a w c : ℝ} (ha : 0 < a) : B.valueRule (a*w) (a*c) = B.valueRule w c := by
  unfold FiniteIntensityHybridInstance.valueRule
  congr 1
  funext r A t i
  cases r
  exact B.valueHybridThreshold_smul ha A t i

end ProphetSecretary.Limiting
