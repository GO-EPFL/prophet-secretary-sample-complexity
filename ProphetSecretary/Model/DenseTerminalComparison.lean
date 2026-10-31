import ProphetSecretary.Model.TerminalFallbackExpected
import ProphetSecretary.Model.TerminalValueComparison

/-!
# Approximating a fixed terminal reward by dense finite offers

This is the terminal-window inequality in the proof of `lem:compact-extract`.
The same independent finite instance supplies the fallback offers. The bound
retains the duration-weight times window term, so it is uniform on compact
weight sets, not on all nonnegative duration weights at once.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

theorem Instance.dense_terminal_value_comparison (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {η ℓ b H w c : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hℓ : 0 ≤ ℓ) (hℓb : ℓ ≤ b) (hbH : b ≤ H)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) (hw : 0 < w) (hc : 0 ≤ c) :
    optimalTerminalScalarValue P b w c -
        (w*(b-ℓ+H*η*P.tailCount b+H*Real.exp (-η*P.tailCount ℓ))+c*η)
      ≤ optimalScalarValue P w c ∧
    optimalScalarValue P w c ≤ optimalTerminalScalarValue P b w c := by
  let π := P.terminalOptimalPolicy hP (hℓ.trans hℓb) hw hc
  have hπ := P.terminalOptimalPolicy_acceptsAbove hP (hℓ.trans hℓb) hw hc
  have h := π.fallbackAfter_scalar_comparison P hP hη0 hη1 hℓ hℓb hbH hcap hπ hw.le hc
  have hOpt := P.terminalOptimalPolicy_optimal hP (hℓ.trans hℓb) hw hc
  change π.terminalScalarObjective P b w c = optimalTerminalScalarValue P b w c at hOpt
  rw [hOpt] at h
  have hUpper := scalarObjective_le_optimal (π.fallbackAfter (1-η) ℓ) P hP hw.le hc
  refine ⟨by linarith only [h,hUpper],(P.terminal_value_comparison hP (hℓ.trans hℓb) hw hc).1⟩

/-- The paper's parameters ℓ=a−δ give its exact displayed constants. -/
theorem Instance.dense_terminal_value_comparison_reserve (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {η δ a b H w c : ℝ}
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hδ0 : 0 ≤ δ) (hδ : δ ≤ a) (hab : a ≤ b) (hbH : b ≤ H)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) (hw : 0 < w) (hc : 0 ≤ c) :
    optimalTerminalScalarValue P b w c-w*(b-a+δ)-w*H*η*P.tailCount b-
      w*H*Real.exp (-η*P.tailCount (a-δ))-c*η ≤ optimalScalarValue P w c := by
  have h := (P.dense_terminal_value_comparison hP hη0 hη1
    (by linarith : 0 ≤ a-δ) (by linarith : a-δ ≤ b) hbH hcap hw hc).1
  nlinarith only [h]

end ProphetSecretary.Model
