import ProphetSecretary.Probability.FiniteProbabilityGrid

/-! # An explicit denominator for a uniform probability-rounding tolerance -/

namespace ProphetSecretary.Probability

noncomputable def probabilityMeshDenominator (D η : ℝ) : ℕ := ⌈D/η⌉₊+1

lemma probabilityMeshDenominator_positive (D η : ℝ) : 0<probabilityMeshDenominator D η := by
  unfold probabilityMeshDenominator
  omega

lemma probabilityMeshDenominator_bound (D η : ℝ) (hη : 0<η) :
    D/(probabilityMeshDenominator D η : ℝ)≤η := by
  have hN : (0 : ℝ)<probabilityMeshDenominator D η := by
    exact_mod_cast probabilityMeshDenominator_positive D η
  apply (div_le_iff₀ hN).mpr
  have hCeil := Nat.le_ceil (D/η)
  have hMul := (div_le_iff₀ hη).mp hCeil
  have hGrow : (⌈D/η⌉₊ : ℝ)≤(probabilityMeshDenominator D η : ℝ) := by
    simp only [probabilityMeshDenominator,Nat.cast_add,Nat.cast_one]
    linarith
  simpa only [mul_comm] using hMul.trans (mul_le_mul_of_nonneg_right hGrow hη.le)

end ProphetSecretary.Probability
