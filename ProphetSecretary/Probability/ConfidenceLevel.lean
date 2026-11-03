import Mathlib.Data.Nat.Find
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Choosing confidence levels by arithmetic search

The executable search starts at one and repeatedly divides by four. Logarithms
are used only in its complexity proof, not by the procedure.
-/

namespace ProphetSecretary.Probability

private lemma confidence_search_lt {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : K) (H : ∃ n : ℕ, (1 / 4 : K) ^ n ≤ p) (n : ℕ) (a : K)
    (ha : a = (1 / 4 : K) ^ n) (hStop : ¬a ≤ p) : n < Nat.find H := by
  by_contra hn
  have hpow := pow_right_anti₀ (by norm_num : (0 : K) ≤ 1 / 4)
    (by norm_num : (1 / 4 : K) ≤ 1) (Nat.le_of_not_gt hn)
  exact hStop (ha.trans_le (hpow.trans (Nat.find_spec H)))

/-- Work counts each comparison, division and level increment. The least
successful level appears only in the termination proof. -/
def countedConfidenceSearch {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : K) (H : ∃ n : ℕ, (1 / 4 : K) ^ n ≤ p) (n : ℕ) (a : K)
    (ha : a = (1 / 4 : K) ^ n) : ℕ × ℕ :=
  if hStop : a ≤ p then (n, 1) else
    let q := countedConfidenceSearch p H (n + 1) (a / 4) (by rw [ha, pow_succ]; ring)
    (q.1, q.2 + 3)
termination_by Nat.find H - n
decreasing_by
  have hn := confidence_search_lt p H n a ha hStop
  omega

lemma countedConfidenceSearch_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : K) (H : ∃ n : ℕ, (1 / 4 : K) ^ n ≤ p) (n : ℕ) (a : K)
    (ha : a = (1 / 4 : K) ^ n) (hn : n ≤ Nat.find H) :
    (countedConfidenceSearch p H n a ha).1 = Nat.find H ∧
      (countedConfidenceSearch p H n a ha).2 = 3 * (Nat.find H - n) + 1 := by
  rw [countedConfidenceSearch]
  split_ifs with hStop
  · have hmin : Nat.find H ≤ n := Nat.find_min' H (by rwa [← ha])
    constructor <;> dsimp <;> omega
  · have hlt := confidence_search_lt p H n a ha hStop
    have hi := countedConfidenceSearch_spec p H (n + 1) (a / 4)
      (by rw [ha, pow_succ]; ring) (by omega)
    constructor
    · exact hi.1
    · dsimp
      omega
termination_by Nat.find H - n
decreasing_by omega

def countedConfidenceLevel {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : K) (H : ∃ n : ℕ, (1 / 4 : K) ^ n ≤ p) : ℕ × ℕ :=
  countedConfidenceSearch p H 0 1 (by simp)

lemma countedConfidenceLevel_spec {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : K) (H : ∃ n : ℕ, (1 / 4 : K) ^ n ≤ p) :
    (countedConfidenceLevel p H).1 = Nat.find H ∧
      (countedConfidenceLevel p H).2 = 3 * Nat.find H + 1 := by
  exact countedConfidenceSearch_spec p H 0 1 (by simp) (Nat.zero_le _)

lemma quarter_pow_eq_exp (n : ℕ) :
    (1 / 4 : ℝ) ^ n = Real.exp (-(n : ℝ) * Real.log 4) := by
  have he : (1 / 4 : ℝ) = Real.exp (-Real.log 4) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    norm_num
  rw [he, ← Real.exp_nat_mul]
  congr 1
  ring

lemma confidence_ceil_level {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    (1 / 4 : ℝ) ^ (Nat.ceil (Real.log (1 / p) / Real.log 4)) ≤ p ∧
      ((Nat.ceil (Real.log (1 / p) / Real.log 4) : ℕ) : ℝ) <
        Real.log (1 / p) / Real.log 4 + 1 := by
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hInv : (1 : ℝ) < 1 / p := (lt_div_iff₀ hp).2 (by simpa only [one_mul] using hp1)
  have hlogp : 0 < Real.log (1 / p) := Real.log_pos hInv
  have hα : 0 ≤ Real.log (1 / p) / Real.log 4 := (div_pos hlogp hlog4).le
  have hc := Nat.le_ceil (Real.log (1 / p) / Real.log 4)
  have hmul := (div_le_iff₀ hlog4).1 hc
  constructor
  · rw [quarter_pow_eq_exp]
    calc
      _ ≤ Real.exp (-Real.log (1 / p)) := Real.exp_le_exp.mpr (by linarith)
      _ = p := by rw [Real.exp_neg, Real.exp_log (one_div_pos.mpr hp)]; simp
  · exact Nat.ceil_lt_add_one hα

lemma exists_confidence_level {p : ℝ} (hp : 0 < p) (hp1 : p < 1) :
    ∃ n : ℕ, (1 / 4 : ℝ) ^ n ≤ p :=
  ⟨Nat.ceil (Real.log (1 / p) / Real.log 4), (confidence_ceil_level hp hp1).1⟩

/-- An odd number of copies, selected by the arithmetic search. -/
def confidenceCopyCount {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : K) (H : ∃ n : ℕ, (1 / 4 : K) ^ n ≤ p) : ℕ :=
  2 * (countedConfidenceLevel p H).1 + 1

lemma confidenceCopyCount_failure {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : K) (H : ∃ n : ℕ, (1 / 4 : K) ^ n ≤ p) :
    (1 / 4 : K) ^ confidenceCopyCount p H ≤ p := by
  rw [confidenceCopyCount, (countedConfidenceLevel_spec p H).1]
  exact (pow_right_anti₀ (by norm_num : (0 : K) ≤ 1 / 4)
    (by norm_num : (1 / 4 : K) ≤ 1) (by omega : Nat.find H ≤ 2 * Nat.find H + 1)).trans
      (Nat.find_spec H)

lemma confidenceCopyCount_log_bound {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (H : ∃ n : ℕ, (1 / 4 : ℝ) ^ n ≤ p) :
    (confidenceCopyCount p H : ℝ) < 2 * (Real.log (1 / p) / Real.log 4) + 3 := by
  have hc := confidence_ceil_level hp hp1
  have hmin := Nat.find_min' H hc.1
  have hminR : (Nat.find H : ℝ) ≤ (Nat.ceil (Real.log (1 / p) / Real.log 4) : ℝ) := by
    exact_mod_cast hmin
  rw [confidenceCopyCount, (countedConfidenceLevel_spec p H).1]
  push_cast
  linarith [hc.2]

lemma countedConfidenceLevel_work_le_copyCount {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (p : K) (H : ∃ n : ℕ, (1 / 4 : K) ^ n ≤ p) :
    (countedConfidenceLevel p H).2 ≤ 2 * confidenceCopyCount p H := by
  rw [confidenceCopyCount, (countedConfidenceLevel_spec p H).1, (countedConfidenceLevel_spec p H).2]
  omega

end ProphetSecretary.Probability
