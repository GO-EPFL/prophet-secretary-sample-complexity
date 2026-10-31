import ProphetSecretary.Limiting.CountableValuePolicy

/-!
# Positive homogeneity and the actual countable canonical rule

Positive scaling of both weights preserves every threshold decision on every
history, including zero identities and acceptance equalities. Consequently
normalizing weights to sum to one changes neither the canonical callback nor
its independent Unit seed. This is a policy identity, not an inference from
equality of optimized scalar values.
-/

open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Limiting

lemma RandomizedCountablePolicy.scalarObjective_smul {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (a w c : ℝ) :
    π.scalarObjective (a*w) (a*c)=a*π.scalarObjective w c := by
  unfold scalarObjective
  ring

namespace CountableInstance

lemma optimalScalarValue_smul (B : CountableInstance) {a w c : ℝ} (ha : 0≤a) :
    B.optimalScalarValue (a*w) (a*c)=a*B.optimalScalarValue w c := by
  have hUpper : B.optimalScalarValue (a*w) (a*c)≤a*B.optimalScalarValue w c := by
    apply csSup_le (B.scalarPayoffs_nonempty (a*w) (a*c))
    rintro v ⟨π,rfl⟩
    change π.scalarObjective (a*w) (a*c)≤a*B.optimalScalarValue w c
    rw [π.scalarObjective_smul]
    exact mul_le_mul_of_nonneg_left (B.scalarObjective_le_value π w c) ha
  apply le_antisymm hUpper
  by_cases ha0 : a=0
  · subst a
    simp only [zero_mul]
    exact (B.optimalScalarValue_zero (le_refl (0:ℝ))).ge
  have haP : 0<a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hLower : B.optimalScalarValue w c≤B.optimalScalarValue (a*w) (a*c)/a := by
    apply csSup_le (B.scalarPayoffs_nonempty w c)
    rintro v ⟨π,rfl⟩
    apply (le_div_iff₀ haP).mpr
    have h := B.scalarObjective_le_value π (a*w) (a*c)
    rw [π.scalarObjective_smul] at h
    simpa only [mul_comm] using h
  have h := (le_div_iff₀ haP).mp hLower
  simpa only [mul_comm] using h

lemma continuationValue_smul (B : CountableInstance) {a w c : ℝ} (ha : 0≤a)
    (keep : IndividualMask) (u : ℝ≥0) :
    B.continuationValue keep (a*w) (a*c) u=a*B.continuationValue keep w c u := by
  unfold continuationValue
  rw [mul_assoc a c (u:ℝ),(B.remainingState keep u).optimalScalarValue_smul ha]

lemma valueRule_smul (B : CountableInstance) {a w c : ℝ} (ha : 0<a) :
    B.valueRule (a*w) (a*c)=B.valueRule w c := by
  unfold valueRule
  congr 1
  · funext r t i x H M
    simp only [B.continuationValue_smul ha.le,mul_assoc,mul_le_mul_iff_right₀ ha]
  · funext r t x H M
    simp only [B.continuationValue_smul ha.le,mul_assoc,mul_le_mul_iff_right₀ ha]

lemma valueRule_weightNormalized (B : CountableInstance) {w c : ℝ} (hw : 0<w) (hc : 0≤c) :
    B.valueRule w c=B.valueRule (w/(w+c)) (c/(w+c)) := by
  have hSum : 0<w+c := add_pos_of_pos_of_nonneg hw hc
  simpa only [div_eq_inv_mul] using
    (B.valueRule_smul (a:=(w+c)⁻¹) (w:=w) (c:=c) (inv_pos.mpr hSum)).symm

lemma valuePolicy_smul (B : CountableInstance) {a w c : ℝ}
    (ha : 0<a) (hw : 0<w) (hc : 0<c) :
    B.valuePolicy (mul_pos ha hw) (mul_pos ha hc)=B.valuePolicy hw hc := by
  unfold valuePolicy
  congr 1
  exact B.valueRule_smul ha

lemma valuePolicy_weightNormalized (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) :
    B.valuePolicy hw hc=
      B.valuePolicy (div_pos hw (add_pos hw hc)) (div_pos hc (add_pos hw hc)) := by
  have h := B.valuePolicy_smul (inv_pos.mpr (add_pos hw hc)) hw hc
  simpa only [div_eq_inv_mul] using h.symm

end CountableInstance
end ProphetSecretary.Limiting
