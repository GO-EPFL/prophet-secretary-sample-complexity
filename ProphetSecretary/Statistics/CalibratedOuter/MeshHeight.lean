import ProphetSecretary.Statistics.CalibratedOuter.CountedMesh
import ProphetSecretary.Analysis.RationalHeight

/-!
# Rational operands in the outer mesh scan

Every comparison uses a grid index bounded by the public mesh size. The
reported value is either an endpoint or the cap times that index divided by
the mesh size.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis

lemma countedMeshIndex_index_le (H y : ℚ) (k : ℕ) : (countedMeshIndex H y k).1 ≤ k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    rw [countedMeshIndex]
    split_ifs
    · exact le_rfl
    · exact ih.trans (Nat.le_succ _)

theorem countedMeshRound_operands_height (H x : ℚ) (m B X P : ℕ)
    (hH : RationalHeight H B) (hX : RationalHeight x X) (hm : m ≤ 2^P) :
    RationalHeight ((m:ℚ)*x) (P+X) ∧
      (∀ j : ℕ, j ≤ m → RationalHeight ((j:ℚ)*H) (P+B)) ∧
      RationalHeight (H/(m:ℚ)) (B+P) ∧
      RationalHeight (countedMeshRound H m x).1 (B+2*P) := by
  have hm' := rationalHeight_natCast m P hm
  have hdiv := hH.div hm'
  refine ⟨hm'.mul hX,fun j hj => (rationalHeight_natCast j P (hj.trans hm)).mul hH,hdiv,?_⟩
  unfold countedMeshRound
  split_ifs
  · exact hH.mono (by omega)
  · exact rationalHeight_zero.mono (Nat.zero_le _)
  · let q := countedMeshIndex H ((m:ℚ)*x) m
    have hq := rationalHeight_natCast q.1 P ((countedMeshIndex_index_le H ((m:ℚ)*x) m).trans hm)
    exact (hdiv.mul hq).mono (by omega)

end ProphetSecretary.Statistics.Calibration
