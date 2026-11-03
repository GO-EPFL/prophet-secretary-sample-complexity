import ProphetSecretary.Statistics.ScalarPlannerRecursion
import ProphetSecretary.Analysis.MultilevelAccuracy
import ProphetSecretary.Probability.MedianConfidence

/-!
# Accuracy of an actual empirical scalar query

The multilevel estimator is evaluated with the empirical recursion, and its
output is rescaled by the product weight. Fresh iid trees provide the copies
for the counted median. Work here counts recursion units, together with the
scalar confidence-search and sorting operations.
-/

open MeasureTheory Set

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n : ℕ} {k : Fin n → ℕ}

noncomputable def scalarPlannerSingle (y : (i : Fin n) → Fin (k i) → ℝ)
    (x : ScalarPlannerState n) (r : ℕ) (t : MultilevelTree (PlannerUniformSeed n) r) : ℝ × ℕ :=
  (scalarPlannerWeight y x.1 * multilevelEstimate (scalarPlannerRecursion y) r x t,
    multilevelTreeWork r t + 1)

lemma scalarPlannerSingle_work (y : (i : Fin n) → Fin (k i) → ℝ)
    (x : ScalarPlannerState n) (r : ℕ) (t : MultilevelTree (PlannerUniformSeed n) r) :
    (scalarPlannerSingle y x r t).2 ≤ 4 * 16 ^ r + 1 := by
  have h := multilevelTreeWork_le r t
  have hn : multilevelTreeWork r t ≤ 4 * 16 ^ r := by exact_mod_cast h
  exact Nat.add_le_add_right hn 1

lemma measurable_scalarPlannerSingle_value (y : (i : Fin n) → Fin (k i) → ℝ)
    (x : ScalarPlannerState n) (r : ℕ) : Measurable (fun t => (scalarPlannerSingle y x r t).1) :=
  ((measurable_multilevelEstimate (scalarPlannerRecursion y) (scalarPlannerRecursion_measurable y) r).comp
    ((measurable_const (a := x)).prodMk measurable_id)).const_mul (scalarPlannerWeight y x.1)

variable [∀ i, NeZero (k i)]

theorem scalarPlannerNormalizedEstimate_error (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (hcap : ∀ i j, y i j ≤ 1) (x : ScalarPlannerState n) (r : ℕ) :
    (∫ t, (multilevelEstimate (scalarPlannerRecursion y) r x t - scalarPlannerNormalizedValue y hy x)^2
      ∂multilevelTreeLaw (plannerUniformSeedLaw n) r) ≤ 25 * (1/2 : ℝ)^r :=
  integral_multilevelEstimate_sq_error_le (scalarPlannerRecursion y) (scalarPlannerRecursion_measurable y)
    (fun _ o _ ha _ => scalarPlannerPayoff_bounds y hcap o ha)
    (fun _ o => scalarPlannerPayoff_lipschitz y o)
    (scalarPlannerNormalizedValue y hy) (measurable_scalarPlannerNormalizedValue y hy)
    (scalarPlannerNormalizedValue_bounds y hy hcap) (scalarPlannerNormalizedValue_empty y hy)
    (plannerUniformSeedLaw n) (scalarPlannerRecursion_coefficient_bounds y)
    (scalarPlannerNormalizedValue_fixed y hy hcap) r x

lemma scalarPlannerSingle_error_identity (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (x : ScalarPlannerState n) (r : ℕ)
    (t : MultilevelTree (PlannerUniformSeed n) r) :
    ((scalarPlannerSingle y x r t).1 - scalarPlannerValue y hy x)^2 =
      (scalarPlannerWeight y x.1)^2 *
        (multilevelEstimate (scalarPlannerRecursion y) r x t - scalarPlannerNormalizedValue y hy x)^2 := by
  have he : scalarPlannerWeight y x.1 * scalarPlannerNormalizedValue y hy x =
      scalarPlannerValue y hy x := by
    unfold scalarPlannerNormalizedValue
    field_simp [(scalarPlannerWeight_pos y x.1).ne']
  change (scalarPlannerWeight y x.1 * multilevelEstimate (scalarPlannerRecursion y) r x t -
    scalarPlannerValue y hy x)^2 = _
  rw [← he]
  ring

lemma integrable_scalarPlannerSingle_sq_error (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (hcap : ∀ i j, y i j ≤ 1) (x : ScalarPlannerState n) (r : ℕ) :
    Integrable (fun t => ((scalarPlannerSingle y x r t).1 - scalarPlannerValue y hy x)^2)
      (multilevelTreeLaw (plannerUniformSeedLaw n) r) := by
  have hEmpty : ∀ z, (scalarPlannerRecursion y).isEmpty z = true →
      0 ≤ (scalarPlannerRecursion y).emptyValue z ∧ (scalarPlannerRecursion y).emptyValue z ≤ 5 := by
    intro z hz
    rw [scalarPlannerNormalizedValue_empty y hy z hz]
    exact scalarPlannerNormalizedValue_bounds y hy hcap z
  have hb := scalarPlannerNormalizedValue_bounds y hy hcap x
  have hi := (integrable_multilevelEstimate_sq_error (scalarPlannerRecursion y)
    (scalarPlannerRecursion_measurable y) hEmpty (plannerUniformSeedLaw n) r x hb.1 hb.2).const_mul
      ((scalarPlannerWeight y x.1)^2)
  exact hi.congr (ae_of_all _ (fun t => (scalarPlannerSingle_error_identity y hy x r t).symm))

theorem scalarPlannerSingle_sq_error (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (hcap : ∀ i j, y i j ≤ 1) (x : ScalarPlannerState n) (r : ℕ) :
    (∫ t, ((scalarPlannerSingle y x r t).1 - scalarPlannerValue y hy x)^2
      ∂multilevelTreeLaw (plannerUniformSeedLaw n) r) ≤
      25 * (scalarPlannerWeight y x.1)^2 * (1/2 : ℝ)^r := by
  simp_rw [scalarPlannerSingle_error_identity y hy x r]
  rw [integral_const_mul]
  have he := mul_le_mul_of_nonneg_left (scalarPlannerNormalizedEstimate_error y hy hcap x r)
    (sq_nonneg (scalarPlannerWeight y x.1))
  nlinarith

noncomputable def scalarPlannerQueryAtLevel (y : (i : Fin n) → Fin (k i) → ℝ)
    (x : ScalarPlannerState n) (r : ℕ) (p : ℝ) (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ p)
    (seed : Fin (confidenceCopyCount p H) → MultilevelTree (PlannerUniformSeed n) r) :
    MedianCopiesResult ℝ :=
  if (scalarPlannerRecursion y).isEmpty x then
    { value := (scalarPlannerRecursion y).emptyValue x, work := 1, copies := 0 }
  else
    let q := confidenceMedianCopies p H (scalarPlannerSingle y x r) seed
    { value := clipFive q.value, work := q.work + 2, copies := q.copies }

/-- A level meeting the explicit squared-error tolerance gives a complete
confidence-amplified query, including the exact empty-state return. -/
theorem scalarPlannerQueryAtLevel_correct (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (hcap : ∀ i j, y i j ≤ 1) (x : ScalarPlannerState n) (r : ℕ)
    (h p : ℝ) (hh : 0 < h) (hp : 0 < p) (hp1 : p < 1) (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ p)
    (hprec : 25 * (scalarPlannerWeight y x.1)^2 * (1/2 : ℝ)^r ≤ h^2/64) :
    Measurable (fun seed => (scalarPlannerQueryAtLevel y x r p H seed).value) ∧
      (Measure.pi (fun _ : Fin (confidenceCopyCount p H) =>
        multilevelTreeLaw (plannerUniformSeedLaw n) r)).real
          {seed | h < |(scalarPlannerQueryAtLevel y x r p H seed).value - scalarPlannerValue y hy x|} ≤ p ∧
      ∀ seed, (scalarPlannerQueryAtLevel y x r p H seed).copies ≤ confidenceCopyCount p H ∧
        (scalarPlannerQueryAtLevel y x r p H seed).work ≤
          confidenceCopyCount p H * (4 * 16^r + 1) + 10 * (confidenceCopyCount p H + 1)^2 + 2 := by
  let μ := multilevelTreeLaw (plannerUniformSeedLaw n) r
  let C := confidenceCopyCount p H
  let ν : Measure (Fin C → MultilevelTree (PlannerUniformSeed n) r) := Measure.pi (fun _ => μ)
  by_cases hx : (scalarPlannerRecursion y).isEmpty x = true
  · have he : plannerActive y x.1 = ∅ := of_decide_eq_true hx
    have hv : (scalarPlannerRecursion y).emptyValue x = scalarPlannerValue y hy x := by
      simp [scalarPlannerRecursion, scalarPlannerValue, he, Model.Instance.continuationValue_empty]
    simp only [scalarPlannerQueryAtLevel, hx, if_true, hv, measurable_const, sub_self, abs_zero,
      not_lt.mpr hh.le, Set.setOf_false, measureReal_empty, Nat.zero_le, true_and]
    exact ⟨hp.le, fun _ => by omega⟩
  · have hc := confidenceMedianCopies_correct μ (scalarPlannerSingle y x r)
      (measurable_scalarPlannerSingle_value y x r) (scalarPlannerValue y hy x) h p hh hp hp1 H
      (integrable_scalarPlannerSingle_sq_error y hy hcap x r)
      ((scalarPlannerSingle_sq_error y hy hcap x r).trans hprec)
      (4 * 16^r + 1) (scalarPlannerSingle_work y x r)
    have hv := scalarPlannerValue_bounds y hy hcap x
    have hClip : Measurable (clipFive (Value := ℝ)) := measurable_const.max (measurable_const.min measurable_id)
    refine ⟨?_, ?_, ?_⟩
    · simpa only [scalarPlannerQueryAtLevel, if_neg hx, Function.comp_def] using hClip.comp hc.1
    · have hsub : {seed | h < |(scalarPlannerQueryAtLevel y x r p H seed).value - scalarPlannerValue y hy x|} ⊆
          {seed | h < |(confidenceMedianCopies p H (scalarPlannerSingle y x r) seed).value - scalarPlannerValue y hy x|} := by
        intro seed hb
        have hclip := clipFive_abs_sub_le (confidenceMedianCopies p H (scalarPlannerSingle y x r) seed).value hv.1 hv.2
        simp only [Set.mem_setOf_eq, scalarPlannerQueryAtLevel, if_neg hx] at hb
        exact hb.trans_le hclip
      exact (measureReal_mono (μ := ν) hsub (measure_ne_top _ _)).trans hc.2.1
    · intro seed
      obtain ⟨hCopies, hWork⟩ := hc.2.2.2 seed
      simp only [scalarPlannerQueryAtLevel, if_neg hx]
      exact ⟨hCopies.le, Nat.add_le_add_right hWork 2⟩

def scalarPlannerPrecisionRatio {K : Type*} [Field K] (β h : K) : K := h^2 / (1600 * β^2)

lemma scalarPlannerPrecisionRatio_mem {β h : ℝ} (hβ : 1 ≤ β) (hh : h ∈ Ioo (0 : ℝ) 1) :
    scalarPlannerPrecisionRatio β h ∈ Ioo (0 : ℝ) 1 := by
  have hb : 0 < β := zero_lt_one.trans_le hβ
  have hd : 0 < 1600 * β^2 := by positivity
  have hbsq : 1 ≤ β^2 := by nlinarith [sq_nonneg (β-1)]
  have hhsq : h^2 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hh.2) (by linarith [hh.1] : 0 < 1+h)]
  exact ⟨div_pos (sq_pos_of_pos hh.1) hd, (div_lt_one hd).2 (by linarith)⟩

lemma scalarPlannerPrecision_exists {β h : ℝ} (hβ : 1 ≤ β) (hh : h ∈ Ioo (0 : ℝ) 1) :
    ∃ j : ℕ, (1/4 : ℝ)^j ≤ scalarPlannerPrecisionRatio β h :=
  exists_confidence_level (scalarPlannerPrecisionRatio_mem hβ hh).1 (scalarPlannerPrecisionRatio_mem hβ hh).2

def countedQuarterPower {K : Type*} [Field K] : ℕ → K × ℕ
  | 0 => (1, 1)
  | j + 1 => let q := countedQuarterPower j; (q.1 / 4, q.2 + 2)

lemma countedQuarterPower_value {K : Type*} [Field K] (j : ℕ) :
    (countedQuarterPower (K := K) j).1 = (1/4 : K)^j := by
  induction j with
  | zero => simp [countedQuarterPower]
  | succ j ih => simp [countedQuarterPower, ih, pow_succ, div_eq_mul_inv]

lemma countedQuarterPower_work {K : Type*} [Field K] (j : ℕ) :
    (countedQuarterPower (K := K) j).2 = 1 + 2*j := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [countedQuarterPower, ih]; omega

/-- Search the even levels, then test the preceding odd level. This finds
the least level meeting the tolerance using only arithmetic and comparisons. -/
def countedScalarPlannerLevel {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (β h : K) (H : ∃ j : ℕ, (1/4 : K)^j ≤ scalarPlannerPrecisionRatio β h) : ℕ × ℕ :=
  let ρ := scalarPlannerPrecisionRatio β h
  let q := countedConfidenceLevel ρ H
  let a := countedQuarterPower (K := K) q.1
  (if 2*a.1 ≤ ρ then 2*q.1-1 else 2*q.1, q.2+a.2+16)

lemma countedScalarPlannerLevel_value {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (β h : K) (H : ∃ j : ℕ, (1/4 : K)^j ≤ scalarPlannerPrecisionRatio β h) :
    (countedScalarPlannerLevel β h H).1 =
      if 2*(1/4 : K)^Nat.find H ≤ scalarPlannerPrecisionRatio β h
        then 2*Nat.find H-1 else 2*Nat.find H := by
  simp only [countedScalarPlannerLevel, (countedConfidenceLevel_spec _ H).1, countedQuarterPower_value]

private lemma countedScalarPlannerLevel_odd_power (j : ℕ) (hj : 0 < j) :
    (1/2 : ℝ)^(2*j-1) = 2*(1/4 : ℝ)^j := by
  have he : (1/2 : ℝ)^(2*j-1)*(1/2) = (1/4 : ℝ)^j := by
    rw [← pow_succ, show 2*j-1+1 = 2*j by omega, pow_mul]
    norm_num
  linarith

private lemma scalarPlannerPrecision_find_pos {β h : ℝ} (hβ : 1 ≤ β) (hh : h ∈ Ioo (0 : ℝ) 1)
    (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ scalarPlannerPrecisionRatio β h) : 0 < Nat.find H := by
  by_contra hj
  have hz : Nat.find H = 0 := by omega
  have hf := Nat.find_spec H
  rw [hz, pow_zero] at hf
  exact (not_le.mpr (scalarPlannerPrecisionRatio_mem hβ hh).2) hf

lemma countedScalarPlannerLevel_precision {β h : ℝ} (hβ : 1 ≤ β) (hh : h ∈ Ioo (0 : ℝ) 1)
    (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ scalarPlannerPrecisionRatio β h) :
    (1/2 : ℝ)^(countedScalarPlannerLevel β h H).1 ≤ scalarPlannerPrecisionRatio β h := by
  rw [countedScalarPlannerLevel_value]
  split_ifs with hc
  · rwa [countedScalarPlannerLevel_odd_power _ (scalarPlannerPrecision_find_pos hβ hh H)]
  · have he : (1/2 : ℝ)^(2*Nat.find H) = (1/4 : ℝ)^Nat.find H := by rw [pow_mul]; norm_num
    rw [he]
    exact Nat.find_spec H

lemma countedScalarPlannerLevel_least {β h : ℝ} (hβ : 1 ≤ β) (hh : h ∈ Ioo (0 : ℝ) 1)
    (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ scalarPlannerPrecisionRatio β h)
    (l : ℕ) (hl : l < (countedScalarPlannerLevel β h H).1) :
    scalarPlannerPrecisionRatio β h < (1/2 : ℝ)^l := by
  let j := Nat.find H
  have hj : 0 < j := scalarPlannerPrecision_find_pos hβ hh H
  have hanti := pow_right_anti₀ (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ) ≤ 1)
  rw [countedScalarPlannerLevel_value] at hl
  split_ifs at hl with hc
  · have hprev : scalarPlannerPrecisionRatio β h < (1/4 : ℝ)^(j-1) :=
      lt_of_not_ge (Nat.find_min H (by omega : j-1 < j))
    have he : (1/2 : ℝ)^(2*(j-1)) = (1/4 : ℝ)^(j-1) := by rw [pow_mul]; norm_num
    rw [← he] at hprev
    exact hprev.trans_le (hanti (by dsimp [j] at *; omega : l ≤ 2*(j-1)))
  · have hprev : scalarPlannerPrecisionRatio β h < (1/2 : ℝ)^(2*j-1) := by
      rw [countedScalarPlannerLevel_odd_power j hj]
      exact lt_of_not_ge hc
    exact hprev.trans_le (hanti (by dsimp [j] at *; omega : l ≤ 2*j-1))

lemma countedScalarPlannerLevel_error {β h : ℝ} (hβ : 1 ≤ β) (hh : h ∈ Ioo (0 : ℝ) 1)
    (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ scalarPlannerPrecisionRatio β h) :
    25 * β^2 * (1/2 : ℝ)^(countedScalarPlannerLevel β h H).1 ≤ h^2/64 := by
  have hb : 0 < β := zero_lt_one.trans_le hβ
  calc
    _ ≤ 25 * β^2 * scalarPlannerPrecisionRatio β h :=
      mul_le_mul_of_nonneg_left (countedScalarPlannerLevel_precision hβ hh H) (by positivity)
    _ = _ := by unfold scalarPlannerPrecisionRatio; field_simp; ring

lemma countedScalarPlannerLevel_work {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (β h : K) (H : ∃ j : ℕ, (1/4 : K)^j ≤ scalarPlannerPrecisionRatio β h) :
    (countedScalarPlannerLevel β h H).2 ≤ 3*(countedScalarPlannerLevel β h H).1 + 21 := by
  simp only [countedScalarPlannerLevel, (countedConfidenceLevel_spec _ H).1,
    (countedConfidenceLevel_spec _ H).2, countedQuarterPower_value, countedQuarterPower_work]
  split_ifs <;> omega

theorem countedScalarPlannerLevel_tree_factor {β h : ℝ} (hβ : 1 ≤ β) (hh : h ∈ Ioo (0 : ℝ) 1)
    (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ scalarPlannerPrecisionRatio β h) :
    (16 : ℝ)^(countedScalarPlannerLevel β h H).1 ≤ (6400 : ℝ)^4 * (β/h)^8 := by
  let R := scalarPlannerPrecisionRatio β h
  let j := Nat.find H
  have hR : R ∈ Ioo (0 : ℝ) 1 := scalarPlannerPrecisionRatio_mem hβ hh
  have hj : 0 < j := by
    by_contra hj
    have hz : j = 0 := by omega
    have hs : (1/4 : ℝ)^j ≤ R := Nat.find_spec H
    rw [hz, pow_zero] at hs
    exact (not_le.mpr hR.2) hs
  have hprev : R < (1/4 : ℝ)^(j-1) := lt_of_not_ge (Nat.find_min H (by omega : j-1 < j))
  rw [one_div_pow] at hprev
  have hprod := (lt_div_iff₀ (by positivity : 0 < (4 : ℝ)^(j-1))).1 hprev
  have hpow : (4 : ℝ)^j ≤ 4 * (1/R) := by
    have hA : (4 : ℝ)^(j-1) ≤ 1/R :=
      ((lt_div_iff₀ hR.1).2 (by simpa only [mul_comm] using hprod)).le
    calc
      _ = (4 : ℝ)^(j-1) * 4 := by
        conv_lhs => rw [show j = (j-1)+1 by omega, pow_succ]
      _ ≤ (1/R) * 4 := mul_le_mul_of_nonneg_right hA (by norm_num)
      _ = _ := by ring
  have hb : 0 < β := zero_lt_one.trans_le hβ
  have hr : (countedScalarPlannerLevel β h H).1 ≤ 2*j := by
    rw [countedScalarPlannerLevel_value]
    split_ifs <;> omega
  calc
    (16 : ℝ)^(countedScalarPlannerLevel β h H).1 ≤ (16 : ℝ)^(2*j) :=
      pow_le_pow_right₀ (by norm_num) hr
    _ = ((4 : ℝ)^j)^4 := by
      rw [pow_mul, pow_right_comm (4 : ℝ) j 4]
      norm_num
    _ ≤ (4*(1/R))^4 := pow_le_pow_left₀ (by positivity) hpow 4
    _ = _ := by dsimp [R, scalarPlannerPrecisionRatio]; field_simp [hh.1.ne', hb.ne']; ring

noncomputable def scalarPlannerQuery (y : (i : Fin n) → Fin (k i) → ℝ)
    (x : ScalarPlannerState n) (h p : ℝ)
    (Hlevel : ∃ j : ℕ, (1/4 : ℝ)^j ≤ scalarPlannerPrecisionRatio (scalarPlannerWeight y x.1) h)
    (Hconf : ∃ j : ℕ, (1/4 : ℝ)^j ≤ p)
    (seed : Fin (confidenceCopyCount p Hconf) → MultilevelTree (PlannerUniformSeed n)
      (countedScalarPlannerLevel (scalarPlannerWeight y x.1) h Hlevel).1) : MedianCopiesResult ℝ :=
  if (scalarPlannerRecursion y).isEmpty x then
    { value := (scalarPlannerRecursion y).emptyValue x, work := 1, copies := 0 }
  else
    let q := countedScalarPlannerLevel (scalarPlannerWeight y x.1) h Hlevel
    let ans := scalarPlannerQueryAtLevel y x q.1 p Hconf seed
    { ans with work := q.2 + ans.work }

/-- The scalar query has failure probability at most `p`, with a hard
recursion-unit bound and an explicit polynomial tree factor. -/
theorem scalarPlannerQuery_correct (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (hcap : ∀ i j, y i j ≤ 1) (x : ScalarPlannerState n)
    (h p : ℝ) (hh : h ∈ Ioo (0 : ℝ) 1) (hp : p ∈ Ioo (0 : ℝ) (1/2))
    (Hlevel : ∃ j : ℕ, (1/4 : ℝ)^j ≤ scalarPlannerPrecisionRatio (scalarPlannerWeight y x.1) h)
    (Hconf : ∃ j : ℕ, (1/4 : ℝ)^j ≤ p) :
    let β := scalarPlannerWeight y x.1
    let r := (countedScalarPlannerLevel β h Hlevel).1
    let C := confidenceCopyCount p Hconf
    Measurable (fun seed => (scalarPlannerQuery y x h p Hlevel Hconf seed).value) ∧
      (Measure.pi (fun _ : Fin C => multilevelTreeLaw (plannerUniformSeedLaw n) r)).real
        {seed | h < |(scalarPlannerQuery y x h p Hlevel Hconf seed).value - scalarPlannerValue y hy x|} ≤ p ∧
      (16 : ℝ)^r ≤ (6400 : ℝ)^4 * (β/h)^8 ∧
      (C : ℝ) < 2 * (Real.log (1/p)/Real.log 4) + 3 ∧
      ∀ seed, (scalarPlannerQuery y x h p Hlevel Hconf seed).copies ≤ C ∧
        (scalarPlannerQuery y x h p Hlevel Hconf seed).work ≤
          C*(4*16^r+1) + 10*(C+1)^2 + 2 + (3*r+21) := by
  dsimp only
  let β := scalarPlannerWeight y x.1
  let q := countedScalarPlannerLevel β h Hlevel
  have hb : 1 ≤ β := scalarPlannerWeight_ge_one y x.1
  have hp1 : p < 1 := hp.2.trans (by norm_num)
  have hc := scalarPlannerQueryAtLevel_correct y hy hcap x q.1 h p hh.1 hp.1 hp1 Hconf
    (countedScalarPlannerLevel_error hb hh Hlevel)
  have hv : (fun seed => (scalarPlannerQuery y x h p Hlevel Hconf seed).value) =
      (fun seed => (scalarPlannerQueryAtLevel y x q.1 p Hconf seed).value) := by
    funext seed
    by_cases hx : (scalarPlannerRecursion y).isEmpty x = true <;>
      simp [scalarPlannerQuery, scalarPlannerQueryAtLevel, hx, q, β]
  refine ⟨?_, ?_, countedScalarPlannerLevel_tree_factor hb hh Hlevel,
    confidenceCopyCount_log_bound hp.1 hp1 Hconf, ?_⟩
  · rw [hv]
    exact hc.1
  · simp_rw [congrFun hv]
    exact hc.2.1
  · intro seed
    obtain ⟨hCopies, hWork⟩ := hc.2.2 seed
    have hLevel := countedScalarPlannerLevel_work β h Hlevel
    by_cases hx : (scalarPlannerRecursion y).isEmpty x = true
    · simp only [scalarPlannerQuery, hx, if_true]
      exact ⟨Nat.zero_le _, by omega⟩
    · simp only [scalarPlannerQuery, if_neg hx]
      refine ⟨hCopies, ?_⟩
      change q.2 + (scalarPlannerQueryAtLevel y x q.1 p Hconf seed).work ≤
        confidenceCopyCount p Hconf * (4*16^q.1+1) +
          10*(confidenceCopyCount p Hconf + 1)^2 + 2 + (3*q.1+21)
      change q.2 ≤ 3*q.1+21 at hLevel
      omega

end ProphetSecretary.Statistics
