import ProphetSecretary.Model.Rounding

/-!
# Downward rounding by a bounded comparison scan

The scan takes at most the public mesh size many comparisons. The real floor
used in the mathematical formula is never queried by the program.
-/

open scoped NNReal

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {K : Type*} [Field K] [LinearOrder K]

def countedMeshIndex (H y : K) : ℕ → ℕ × ℕ
  | 0 => (0,1)
  | k+1 => if (k+1 : ℕ) * H ≤ y then (k+1,4)
      else let q := countedMeshIndex H y k; (q.1,q.2+4)

lemma countedMeshIndex_work (H y : K) (k : ℕ) :
    (countedMeshIndex H y k).2 ≤ 4*k+1 := by
  induction k with
  | zero => simp [countedMeshIndex]
  | succ k ih =>
    rw [countedMeshIndex]
    split <;> dsimp only <;> omega

lemma countedMeshIndex_value {H : ℝ} (hH : 0 < H) {y : ℝ} (hy : 0 ≤ y) (k : ℕ) :
    (countedMeshIndex H y k).1 = min k ⌊y/H⌋₊ := by
  induction k with
  | zero => simp [countedMeshIndex]
  | succ k ih =>
    have he : (k+1 : ℕ) * H ≤ y ↔ k+1 ≤ ⌊y/H⌋₊ := by
      rw [Nat.le_floor_iff (div_nonneg hy hH.le), le_div_iff₀ hH]
    rw [countedMeshIndex]
    split_ifs with h
    · exact (min_eq_left (he.mp h)).symm
    · rw [ih]
      have hf : ⌊y/H⌋₊ ≤ k := by have := mt he.mpr h; omega
      rw [min_eq_right hf, min_eq_right (hf.trans (Nat.le_succ k))]

def countedMeshRound (H : K) (m : ℕ) (x : K) : K × ℕ :=
  if H ≤ x then (H,2)
  else if x ≤ 0 then (0,3)
  else let q := countedMeshIndex H ((m : K)*x) m
       (H/(m : K)*(q.1 : K),q.2+8)

lemma countedMeshRound_work (H : K) (m : ℕ) (x : K) :
    (countedMeshRound H m x).2 ≤ 4*m+9 := by
  unfold countedMeshRound
  have := countedMeshIndex_work H ((m : K)*x) m
  split_ifs <;> simp only <;> omega

lemma countedMeshRound_value (H : ℝ≥0) (hH : (0 : ℝ) < H) (m : ℕ) (x : ℝ) :
    (countedMeshRound (H : ℝ) m x).1 = meshRound H m x := by
  unfold countedMeshRound meshRound
  split_ifs with hcap hx
  · rfl
  · have h := Nat.floor_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m) hx) hH.le)
    simp [h]
  · have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hf : ⌊(m : ℝ)*x/(H : ℝ)⌋₊ ≤ m := by
      apply Nat.floor_le_of_le
      apply (div_le_iff₀ hH).mpr
      exact mul_le_mul_of_nonneg_left (le_of_not_ge hcap) hm
    dsimp only
    rw [countedMeshIndex_value hH (mul_nonneg hm (le_of_not_ge hx)), min_eq_right hf]

end ProphetSecretary.Statistics.Calibration
