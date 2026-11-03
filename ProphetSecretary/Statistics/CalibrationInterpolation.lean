import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Linear interpolation for the validation root

The duration curve in `eq:calibration-duration-curve` is a concatenation of
linear pieces. Its empirical mean is found by scanning the knot values and
interpolating in the first piece crossing the target. These operations are
computable over rational inputs.
-/

namespace ProphetSecretary.Statistics

variable {Value : Type*} [Field Value] [LinearOrder Value] [IsStrictOrderedRing Value]

/-- First knot at or above the target, found with at most `N` comparisons.
The zero-length case is a total fallback; the correctness lemma excludes it. -/
def calibrationCrossing (v : ℕ → Value) (ρ : Value) : ℕ → ℕ
  | 0 => 0
  | N + 1 => if ρ ≤ v 1 then 1 else calibrationCrossing (fun j => v (j + 1)) ρ N + 1

omit [Field Value] [IsStrictOrderedRing Value] in
/-- A successful scan supplies a positive interpolation denominator. -/
theorem calibrationCrossing_bounds (v : ℕ → Value) (ρ : Value) (N : ℕ)
    (h0 : v 0 < ρ) (hN : ρ ≤ v N) :
    1 ≤ calibrationCrossing v ρ N ∧ calibrationCrossing v ρ N ≤ N ∧
      v (calibrationCrossing v ρ N - 1) < ρ ∧ ρ ≤ v (calibrationCrossing v ρ N) := by
  induction N generalizing v with
  | zero => exact False.elim (not_le_of_gt h0 hN)
  | succ N ih =>
    by_cases hfirst : ρ ≤ v 1
    · simp only [calibrationCrossing, if_pos hfirst, Nat.sub_self]
      exact ⟨le_rfl, Nat.succ_le_succ (Nat.zero_le N), h0, hfirst⟩
    · have hs := ih (fun j => v (j + 1)) (lt_of_not_ge hfirst) hN
      simp only [calibrationCrossing, if_neg hfirst]
      refine ⟨by omega, by omega, ?_, hs.2.2.2⟩
      convert hs.2.2.1 using 1
      congr 1
      omega

/-- The fraction along the selected linear segment. -/
def calibrationMixingFraction (v : ℕ → Value) (ρ : Value) (N : ℕ) : Value :=
  let j := calibrationCrossing v ρ N
  (ρ - v (j - 1)) / (v j - v (j - 1))

theorem calibrationMixingFraction_mem_unit (v : ℕ → Value) (ρ : Value) (N : ℕ)
    (h0 : v 0 < ρ) (hN : ρ ≤ v N) :
    0 < calibrationMixingFraction v ρ N ∧ calibrationMixingFraction v ρ N ≤ 1 := by
  obtain ⟨_, _, hlo, hhi⟩ := calibrationCrossing_bounds v ρ N h0 hN
  have hd : 0 < v (calibrationCrossing v ρ N) - v (calibrationCrossing v ρ N - 1) := by
    linarith
  unfold calibrationMixingFraction
  exact ⟨div_pos (sub_pos.mpr hlo) hd, (div_le_one hd).mpr (by linarith)⟩

/-- The computed mixture calibrates the empirical duration exactly. -/
theorem calibrationMixingFraction_equation (v : ℕ → Value) (ρ : Value) (N : ℕ)
    (h0 : v 0 < ρ) (hN : ρ ≤ v N) :
    let j := calibrationCrossing v ρ N
    let α := calibrationMixingFraction v ρ N
    (1 - α) * v (j - 1) + α * v j = ρ := by
  obtain ⟨_, _, hlo, hhi⟩ := calibrationCrossing_bounds v ρ N h0 hN
  have hd : v (calibrationCrossing v ρ N) - v (calibrationCrossing v ρ N - 1) ≠ 0 := by
    linarith
  dsimp [calibrationMixingFraction]
  field_simp
  ring

/-- The scan's comparison count on its actual execution path. -/
def calibrationCrossingComparisons (v : ℕ → Value) (ρ : Value) : ℕ → ℕ
  | 0 => 0
  | N + 1 => 1 + if ρ ≤ v 1 then 0 else calibrationCrossingComparisons (fun j => v (j + 1)) ρ N

omit [Field Value] [IsStrictOrderedRing Value] in
lemma calibrationCrossingComparisons_le (v : ℕ → Value) (ρ : Value) (N : ℕ) :
    calibrationCrossingComparisons v ρ N ≤ N := by
  induction N generalizing v with
  | zero => simp [calibrationCrossingComparisons]
  | succ N ih =>
    simp only [calibrationCrossingComparisons]
    split_ifs
    · omega
    · have h := ih (fun j => v (j + 1))
      omega

end ProphetSecretary.Statistics
