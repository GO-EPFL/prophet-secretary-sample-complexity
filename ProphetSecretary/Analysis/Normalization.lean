import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Algebra of the bounded normalization

In `lem:clipping`, `a=w*M_cap`, `b=c_cap`, `V` is the original scalar value,
and `D0` is the original benchmark. The clipping comparison supplies the inequalities
used here. This lemma establishes the normalization algebra only.
-/

namespace ProphetSecretary.Analysis

/-- The two normalized coefficients and normalized cap from the clipping proof. -/
theorem normalization_parameters {V D0 a b : ℝ}
    (hD0 : 0 < D0) (hV : 0 ≤ V) (hVlt : V < D0)
    (haV : a ≤ V) (hbV : b ≤ V) (hD : D0 ≤ a + b) :
    0 < a ∧ 0 < b ∧ 0 < a + b ∧
      a / (a + b) + b / (a + b) = 1 ∧
      (1 - V / D0 ≤ a / (a + b) ∧ a / (a + b) ≤ V / D0) ∧
      (1 - V / D0 ≤ b / (a + b) ∧ b / (a + b) ≤ V / D0) ∧
      V / a ≤ (V / D0) / (1 - V / D0) := by
  have hgap : 0 < D0 - V := sub_pos.mpr hVlt
  have hapos : 0 < a := by linarith
  have hbpos : 0 < b := by linarith
  have hsum : 0 < a + b := hD0.trans_le hD
  have hsumone : a / (a + b) + b / (a + b) = 1 := by
    rw [← add_div, div_self hsum.ne']
  have hVdiv : V / (a + b) ≤ V / D0 :=
    div_le_div_of_nonneg_left hV hD0 hD
  have haupper : a / (a + b) ≤ V / D0 :=
    (div_le_div_of_nonneg_right haV hsum.le).trans hVdiv
  have hbupper : b / (a + b) ≤ V / D0 :=
    (div_le_div_of_nonneg_right hbV hsum.le).trans hVdiv
  have halower : 1 - V / D0 ≤ a / (a + b) := by linarith
  have hblower : 1 - V / D0 ≤ b / (a + b) := by linarith
  have hcap : V / a ≤ V / (D0 - V) :=
    div_le_div_of_nonneg_left hV hgap (by linarith)
  have heq : V / (D0 - V) = (V / D0) / (1 - V / D0) := by
    field_simp
  exact ⟨hapos, hbpos, hsum, hsumone, ⟨halower, haupper⟩, ⟨hblower, hbupper⟩, hcap.trans_eq heq⟩

/-- The value/benchmark ratio cannot increase when the numerator falls and the
positive benchmark rises. This comparison is applied after clipping. -/
theorem normalized_ratio_le {V V' D0 D : ℝ} (hV : 0 ≤ V) (hD0 : 0 < D0)
    (hDD : D0 ≤ D) (hVV : V' ≤ V) : V' / D ≤ V / D0 :=
  (div_le_div_of_nonneg_right hVV (hD0.trans_le hDD).le).trans
    (div_le_div_of_nonneg_left hV hD0 hDD)

end ProphetSecretary.Analysis
