import ProphetSecretary.Limiting.HybridScalarObjectives

/-!
# Terminal-reward Lipschitz continuity of the actual hybrid benchmark

The pointwise maximum is 1-Lipschitz in its fixed terminal reward. Both
expectations use the same actual retained and anonymous value law.
-/

open MeasureTheory

namespace ProphetSecretary.Limiting

variable {n : ℕ}

theorem FiniteIntensityHybridInstance.expectedMaximum_terminal_abs_sub_le
    (B D : FiniteIntensityHybridInstance n) (hP : D.individuals = B.individuals)
    (hμ : D.intensity = B.intensity) :
    |B.expectedMaximum-D.expectedMaximum| ≤ |(B.terminal : ℝ)-D.terminal| := by
  have hlaw : hybridValueLaw D.individuals D.intensity = hybridValueLaw B.individuals B.intensity := by
    rw [hP,hμ]
  have hDI : Integrable (hybridMaximum (n := n) D.terminal) (hybridValueLaw B.individuals B.intensity) :=
    hlaw ▸ D.integrable_maximum
  have h := norm_integral_le_of_norm_le_const (μ := hybridValueLaw B.individuals B.intensity)
    (f := fun v => hybridMaximum B.terminal v-hybridMaximum D.terminal v)
    (Filter.Eventually.of_forall fun v => by
      rw [Real.norm_eq_abs]
      exact abs_max_sub_max_le_abs (B.terminal : ℝ) D.terminal
        (Model.Instance.maximum (combinedValues v.2 v.1.2)))
  rw [integral_sub B.integrable_maximum hDI,Real.norm_eq_abs] at h
  simp only [probReal_univ,mul_one] at h
  have hB : B.expectedMaximum = ∫ v, hybridMaximum (n := n) B.terminal v ∂hybridValueLaw B.individuals B.intensity := rfl
  have hD : D.expectedMaximum = ∫ v, hybridMaximum (n := n) D.terminal v ∂hybridValueLaw B.individuals B.intensity := by
    change (∫ v, hybridMaximum (n := n) D.terminal v ∂hybridValueLaw D.individuals D.intensity) = _
    rw [hlaw]
  rw [hB,hD]
  exact h

end ProphetSecretary.Limiting
