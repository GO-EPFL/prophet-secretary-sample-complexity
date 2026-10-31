import ProphetSecretary.Limiting.CountableScalarObjectives

/-!
# The cap-reserve endpoint of the actual countable model
-/

open MeasureTheory

namespace ProphetSecretary.Limiting.CountableInstance

lemma expectedMaximum_mem_terminal_cap (B : CountableInstance) :
    B.expectedMaximum ∈ Set.Icc (B.terminal : ℝ) B.cap := by
  have he : (∫ x, B.maximum x ∂B.valueLaw) = B.expectedMaximum := rfl
  have hl := integral_mono_ae (integrable_const (B.terminal : ℝ)) B.integrable_maximum
    (B.maximum_bounded.mono (fun _ hx => hx.1))
  have hu := integral_mono_ae B.integrable_maximum (integrable_const (B.cap : ℝ))
    (B.maximum_bounded.mono (fun _ hx => hx.2))
  rw [integral_const,he] at hl
  rw [integral_const,he] at hu
  simpa only [Set.mem_Icc,probReal_univ,one_smul] using And.intro hl hu

lemma expectedMaximum_eq_cap_of_terminal (B : CountableInstance) (h : B.terminal = B.cap) :
    B.expectedMaximum = (B.cap : ℝ) := by
  have hb := B.expectedMaximum_mem_terminal_cap
  rw [h] at hb
  exact le_antisymm hb.2 hb.1

lemma value_eq_cap_of_terminal (B : CountableInstance) (h : B.terminal = B.cap)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    B.optimalScalarValue w c = w*(B.cap : ℝ)+c := by
  have hUpper := B.optimalScalarValue_le hw hc
  rw [B.expectedMaximum_eq_cap_of_terminal h] at hUpper
  have hLower := B.waiting_le_value w c
  rw [h] at hLower
  exact le_antisymm hUpper hLower

end ProphetSecretary.Limiting.CountableInstance
