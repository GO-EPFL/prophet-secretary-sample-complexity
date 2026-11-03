import ProphetSecretary.Statistics.ScalarPlannerFairQuery

/-!
# Selecting the grid precision

The requested one-step tolerance gives a single grid precision for the
whole query. The arithmetic search uses division by four and chooses an
odd number of bits. Its logarithmic bound is an analysis of the search.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Probability

def plannerGridTolerance {K : Type*} [Field K] (n : ℕ) (β h : K) : K :=
  3*h/(4*β*(10*(n:K)+4))

lemma plannerGridTolerance_pos (n : ℕ) {β h : ℝ} (hβ : 0 < β) (hh : 0 < h) :
    0 < plannerGridTolerance n β h := by
  unfold plannerGridTolerance
  positivity

lemma plannerGridTolerance_lt_one (n : ℕ) {β h : ℝ} (hβ : 1 ≤ β) (hh : h ≤ 1) :
    plannerGridTolerance n β h < 1 := by
  have hb : 0 < β := zero_lt_one.trans_le hβ
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [plannerGridTolerance, div_lt_iff₀ (by positivity)]
  nlinarith [mul_nonneg hb.le hn]

def countedPlannerBitPrecision {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (n : ℕ) (β h : K) (H : ∃ j : ℕ, (1/4 : K)^j ≤ plannerGridTolerance n β h) : ℕ × ℕ :=
  let q := countedConfidenceLevel (plannerGridTolerance n β h) H
  (2*q.1+1,q.2+8)

theorem countedPlannerBitPrecision_correct (n : ℕ) {β h : ℝ} (hβ : 1 ≤ β)
    (hh : 0 < h) (hh1 : h ≤ 1) (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ plannerGridTolerance n β h) :
    let q := countedPlannerBitPrecision n β h H
    1 ≤ q.1 ∧ β * ((10*(n:ℝ)+4)/(3*((2^q.1:ℕ):ℝ))) ≤ h/4 ∧
      (q.1:ℝ) < 2*(Real.log (1/plannerGridTolerance n β h)/Real.log 4)+3 ∧ q.2 ≤ 2*q.1+8 := by
  let δ := plannerGridTolerance n β h
  let c := countedConfidenceLevel δ H
  let b := confidenceCopyCount δ H
  have hb0 : 0 < β := zero_lt_one.trans_le hβ
  have hβN : 0 < β * (10*(n:ℝ)+4) := by positivity
  have hc : (1/4 : ℝ)^c.1 ≤ δ := by
    rw [(countedConfidenceLevel_spec δ H).1]
    exact Nat.find_spec H
  have hpow : (1/(2^b:ℝ)) ≤ δ := by
    rw [← one_div_pow]
    calc
      (1/2 : ℝ)^b = (1/4 : ℝ)^c.1*(1/2) := by
        dsimp [b, confidenceCopyCount, c]
        rw [pow_add, pow_mul]
        norm_num
      _ ≤ (1/4 : ℝ)^c.1 := mul_le_of_le_one_right (by positivity) (by norm_num)
      _ ≤ δ := hc
  have hprec : β * ((10*(n:ℝ)+4)/(3*((2^b:ℕ):ℝ))) ≤ h/4 := by
    push_cast
    calc
      _ = (β*(10*(n:ℝ)+4)/3)*(1/(2^b:ℝ)) := by ring
      _ ≤ (β*(10*(n:ℝ)+4)/3)*δ := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = _ := by
        dsimp [δ, plannerGridTolerance]
        field_simp [hβN.ne', hb0.ne', show 10*(n:ℝ)+4 ≠ 0 by positivity]
  change 1 ≤ b ∧ _ ∧ _ ∧ c.2+8 ≤ 2*b+8
  exact ⟨by dsimp [b, confidenceCopyCount]; omega, hprec,
    confidenceCopyCount_log_bound (plannerGridTolerance_pos n hb0 hh)
      (plannerGridTolerance_lt_one n hβ hh1) H,
    Nat.add_le_add_right (countedConfidenceLevel_work_le_copyCount δ H) 8⟩

/-- Explicit logarithmic precision bound in terms of the empirical positive
count, the public identity bound, and the requested error. -/
theorem countedPlannerBitPrecision_log_bound (n : ℕ) {β h L : ℝ}
    (hβ : 1 ≤ β) (hL : β ≤ Real.exp (4*L)) (hh : 0 < h) (hh1 : h ≤ 1)
    (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ plannerGridTolerance n β h) :
    ((countedPlannerBitPrecision n β h H).1:ℝ) <
      2*((Real.log (40/3) + Real.log ((n:ℝ)+1) + 4*L + Real.log (1/h))/Real.log 4)+3 := by
  have hβ0 : 0 < β := zero_lt_one.trans_le hβ
  have hb := (countedPlannerBitPrecision_correct n hβ hh hh1 H).2.2.1
  have hN : (4/3 : ℝ)*(10*(n:ℝ)+4) ≤ (40/3)*((n:ℝ)+1) := by linarith
  have hlog : Real.log (1/plannerGridTolerance n β h) ≤
      Real.log (40/3) + Real.log ((n:ℝ)+1) + 4*L + Real.log (1/h) := calc
    _ = Real.log (((4/3)*(10*(n:ℝ)+4))*β*(1/h)) := by
      congr 1
      unfold plannerGridTolerance
      field_simp
    _ ≤ Real.log (((40/3)*((n:ℝ)+1))*Real.exp (4*L)*(1/h)) :=
      Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right
        (mul_le_mul hN hL hβ0.le (by positivity)) (by positivity))
    _ = _ := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity), Real.log_exp]
  exact hb.trans_le (add_le_add_left (mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hlog (Real.log_pos (by norm_num : (1:ℝ) < 4)).le)
      (by norm_num : (0:ℝ) ≤ 2)) 3)

end ProphetSecretary.Statistics
