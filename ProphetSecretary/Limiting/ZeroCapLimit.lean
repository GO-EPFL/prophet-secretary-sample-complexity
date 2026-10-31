import ProphetSecretary.Limiting.CountableCapReserve
import ProphetSecretary.Model.TerminalBenchmarkBounds
import ProphetSecretary.Model.TerminalZeroDefault

/-!
# The zero-cap endpoint of bounded-instance compact extraction

Every actual finite and countable maximum is zero and waiting has scalar
value c. Empty instances and arbitrary independent policy randomness remain.
-/

open MeasureTheory Set Filter
open scoped NNReal

namespace ProphetSecretary.Limiting

lemma zero_cap_convergence (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (B : CountableInstance) (hCap : B.cap = 0)
    (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ (B.cap : ℝ)) :
    ∀ ε > (0 : ℝ), ∀ᶠ m in atTop,
      (∀ w c : ℝ, 0 ≤ w → 0 ≤ c →
        |Model.optimalScalarValue (P m) w c-B.optimalScalarValue w c| < ε) ∧
      |(P m).expectedMaximum-B.expectedMaximum| < ε := by
  have hReserve : B.terminal = B.cap := by
    apply le_antisymm B.terminal_le_cap
    rw [hCap]
    exact zero_le
  have hBM : B.expectedMaximum = 0 := by
    simpa only [hCap,NNReal.coe_zero] using B.expectedMaximum_eq_cap_of_terminal hReserve
  intro ε hε
  filter_upwards [] with m
  have hPcap : ∀ i, ∀ᵐ x ∂(P m).law i, x ≤ (0 : ℝ) := by
    simpa only [hCap,NNReal.coe_zero] using hcap m
  have hP := (P m).integrable_maximum_of_bounded hPcap
  have hTM : (P m).expectedTerminalMaximum 0 = 0 := (P m).expectedTerminalMaximum_at_cap 0 hPcap
  have hBounds := (P m).terminal_benchmark_comparison hP (show (0 : ℝ) ≤ 0 from le_rfl)
  have hPM : (P m).expectedMaximum = 0 :=
    (sub_eq_zero.mp (le_antisymm hBounds.2 hBounds.1)).symm.trans hTM
  constructor
  · intro w c hw hc
    have hTV : Model.optimalTerminalScalarValue (P m) 0 w c = c := by
      simpa only [NNReal.coe_zero,mul_zero,zero_add] using (P m).optimalTerminalScalarValue_at_cap 0 hPcap hw hc
    have hPV : Model.optimalScalarValue (P m) w c = c :=
      (Model.optimalTerminalScalarValue_zero_terminal (P m) w c).symm.trans hTV
    have hBV : B.optimalScalarValue w c = c := by
      simpa only [hCap,NNReal.coe_zero,mul_zero,zero_add] using B.value_eq_cap_of_terminal hReserve hw hc
    calc
      _ = |c-c| := congrArg abs (congrArg₂ (fun x y : ℝ => x-y) hPV hBV)
      _ = 0 := by simp only [sub_self,abs_zero]
      _ < ε := hε
  · calc
      _ = |(0 : ℝ)-0| := congrArg abs (congrArg₂ (fun x y : ℝ => x-y) hPM hBM)
      _ = 0 := by simp only [sub_self,abs_zero]
      _ < ε := hε

end ProphetSecretary.Limiting
