import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# A small posterior increment (`lem:bayes-brier`)

The reciprocal potential decreases too quickly if every increment is larger
than the square of its stated bound. Only the finite prefix through m is
constrained; no assumption concerns later values of the sequence.
-/

open Set
open scoped BigOperators

namespace ProphetSecretary.Analysis

private lemma reciprocalPotential_drop {α A B Δ : ℝ}
    (hα : 0 < α) (hA : 0 < A) (hB : 0 < B) (hΔ : 0 ≤ Δ)
    (hRel : B = A+α*Δ) (hSmall : A^2 < Δ) (hCoeff : α*A ≤ 2) :
    α/3 < 1/A-1/B := by
  have hMul := mul_le_mul_of_nonneg_right hCoeff hΔ
  have hAB : A*B < 3*Δ := by
    rw [hRel]
    nlinarith only [hSmall,hMul]
  have hPhi : 1/A-1/B = α*Δ/(A*B) := by
    field_simp [hA.ne',hB.ne']
    nlinarith only [hRel]
  rw [hPhi]
  apply (lt_div_iff₀ (mul_pos hA hB)).mpr
  nlinarith only [mul_lt_mul_of_pos_left hAB hα]

/-- The deterministic small-increment lemma used for the posterior Brier
sequence. All bounds are on the stated finite prefix. -/
theorem exists_small_posterior_increment {m : ℕ} (hm : 8 ≤ m) (s : ℕ → ℝ)
    (hs : ∀ j ≤ m, s j ∈ Icc (0 : ℝ) 1)
    (hStep : ∀ j < m, s j ≤ s (j+1)) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ j < m, Real.sqrt (s (j+1)-s j) ≤ α*s j+8/(α*(m : ℝ)) := by
  classical
  have hmNat : 0 < m := lt_of_lt_of_le (by decide : 0 < 8) hm
  have hmPos : 0 < (m : ℝ) := Nat.cast_pos.mpr hmNat
  let β : ℝ := 8/(α*(m : ℝ))
  let A := fun j => α*s j+β
  let Φ := fun j => 1/A j
  have hβ : 0 < β := by dsimp only [β]; positivity
  have hA (j : ℕ) (hj : j ≤ m) : 0 < A j := by
    have hsj := (hs j hj).1
    dsimp only [A]
    positivity
  have hαβ : α*β = 8/(m : ℝ) := by
    dsimp only [β]
    field_simp [hα.ne',hmPos.ne']
  have h8 : 8/(m : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hmPos).mpr
    simpa only [one_mul] using (show (8 : ℝ) ≤ (m : ℝ) by exact_mod_cast hm)
  have hαSq : α^2 ≤ 1 := by
    simpa only [pow_two,one_mul] using mul_le_mul hα1 hα1 hα.le zero_le_one
  have hCoeff (j : ℕ) (hj : j ≤ m) : α*A j ≤ 2 := by
    have hsj := (hs j hj).2
    have hmul := mul_le_mul_of_nonneg_left hsj hα.le
    have hAj : A j ≤ α+β := by dsimp only [A]; linarith only [hmul]
    have hαAj := mul_le_mul_of_nonneg_left hAj hα.le
    nlinarith only [hαAj,hαSq,hαβ,h8]
  by_contra hNo
  have hDrop (j : ℕ) (hj : j < m) : α/3 < Φ j-Φ (j+1) := by
    have hFail : A j < Real.sqrt (s (j+1)-s j) := by
      apply lt_of_not_ge
      intro h
      exact hNo ⟨j,hj,h⟩
    have hSmall : A j^2 < s (j+1)-s j := (Real.lt_sqrt (hA j hj.le).le).mp hFail
    have hRel : A (j+1) = A j+α*(s (j+1)-s j) := by dsimp only [A]; ring
    exact reciprocalPotential_drop hα (hA j hj.le) (hA (j+1) (Nat.succ_le_of_lt hj))
      (sub_nonneg.mpr (hStep j hj)) hRel hSmall (hCoeff j hj.le)
  have hSum : (m : ℝ)*(α/3) < Φ 0-Φ m := by
    calc
      _ = ∑ _j ∈ Finset.range m, α/3 := by simp
      _ < ∑ j ∈ Finset.range m, (Φ j-Φ (j+1)) :=
        Finset.sum_lt_sum_of_nonempty ⟨0,Finset.mem_range.mpr hmNat⟩
          (fun j hj => hDrop j (Finset.mem_range.mp hj))
      _ = _ := Finset.sum_range_sub' Φ m
  have hInitial : Φ 0 ≤ 1/β := by
    apply one_div_le_one_div_of_le hβ
    have hs0 := (hs 0 (Nat.zero_le m)).1
    dsimp only [A]
    nlinarith only [mul_nonneg hα.le hs0]
  have hTerminal : 0 ≤ Φ m := one_div_nonneg.mpr (hA m le_rfl).le
  have hInv : 1/β = α*(m : ℝ)/8 := by
    dsimp only [β]
    field_simp [hα.ne',hmPos.ne']
  rw [hInv] at hInitial
  nlinarith only [hSum,hInitial,hTerminal,mul_pos hα hmPos]

end ProphetSecretary.Analysis
