import ProphetSecretary.Limiting.CountableValuePolicy

/-!
# Evaluating the constructed rule under another independent instance

The design continuation values remain fixed. A new evaluation instance whose
reserve is at most the design reserve has the same positive linear acceptance
floor, hence actual first-acceptance admissibility. This asserts no optimized
value or derivative transfer.
-/

open MeasureTheory
open scoped NNReal

namespace ProphetSecretary.Limiting.CountableInstance

lemma valueRule_admissible_eval (B Eval : CountableInstance) (hReserve : Eval.terminal ≤ B.terminal)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) : (B.valueRule w c).Admissible Eval (Measure.dirac ()) := by
  apply CountableRule.admissible_of_linear_floor Eval (Measure.dirac ()) (B.valueRule w c) (div_pos hc hw)
  intro v i hi
  have hFloor := B.valueRule_code_floor hw v i hi
  exact (add_le_add (show (Eval.terminal : ℝ) ≤ B.terminal by exact_mod_cast hReserve) le_rfl).trans hFloor

noncomputable def fixedValuePolicy (B Eval : CountableInstance) (hReserve : Eval.terminal ≤ B.terminal)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) : RandomizedCountablePolicy Eval where
  Seed := Unit
  seedLaw := Measure.dirac ()
  rule := B.valueRule w c
  measurable_rule := B.valueRule_isMeasurable hw.le hc.le
  admissible := B.valueRule_admissible_eval Eval hReserve hw hc

end ProphetSecretary.Limiting.CountableInstance
