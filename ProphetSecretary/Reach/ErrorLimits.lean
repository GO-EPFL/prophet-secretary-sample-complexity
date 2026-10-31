import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Order.Field

/-!
# Removing explicit finite-approximation errors

These limit lemmas apply only after the preceding statements have supplied an
explicit, policy-uniform error constant. They do not interchange the jackpot
limit with the number of appended dummy variables.
-/

open Filter
open scoped Topology

namespace ProphetSecretary.Reach

/-- A fixed inverse-square-root error vanishes as the finite dummy count grows. -/
theorem le_of_forall_nat_sqrt_error {a b K : ℝ}
    (h : ∀ N : ℕ, 0 < N → a ≤ b + K / Real.sqrt (N : ℝ)) : a ≤ b := by
  have hs : Tendsto (fun N : ℕ => Real.sqrt (N : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have he : Tendsto (fun N : ℕ => K / Real.sqrt (N : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    hs.const_div_atTop K
  have hlim : Tendsto (fun N : ℕ => b + K / Real.sqrt (N : ℝ)) atTop (𝓝 b) := by
    simpa only [add_zero] using tendsto_const_nhds.add he
  apply ge_of_tendsto hlim
  exact Filter.eventually_atTop.mpr ⟨1, fun N hN => h N (Nat.zero_lt_of_lt hN)⟩

end ProphetSecretary.Reach
