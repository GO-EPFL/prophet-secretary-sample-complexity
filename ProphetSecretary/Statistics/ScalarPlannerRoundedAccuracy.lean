import ProphetSecretary.Statistics.ScalarPlannerRoundedValue
import ProphetSecretary.Statistics.ScalarPlannerAccuracy

/-!
# Accuracy of the rounded scalar estimator

All levels use the same rounded transition. The stochastic error is measured
at the rounded fixed point; the deterministic operator error transfers the
confidence bound to the original continuation.
-/

open MeasureTheory Set

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n : ℕ} {k : Fin n → ℕ}

noncomputable def scalarPlannerRoundedSingle (y : (i : Fin n) → Fin (k i) → ℝ)
    (N : ℕ) (hN : 0 < N) (x : ScalarPlannerState n) (r : ℕ)
    (t : MultilevelTree (PlannerUniformSeed n) r) : ℝ × ℕ :=
  (scalarPlannerWeight y x.1 * multilevelEstimate (scalarPlannerRoundedRecursion y N hN) r x t,
    multilevelTreeWork r t + 1)

lemma measurable_scalarPlannerRoundedSingle_value (y : (i : Fin n) → Fin (k i) → ℝ)
    (N : ℕ) (hN : 0 < N) (x : ScalarPlannerState n) (r : ℕ) :
    Measurable (fun t => (scalarPlannerRoundedSingle y N hN x r t).1) :=
  ((measurable_multilevelEstimate (scalarPlannerRoundedRecursion y N hN)
    (scalarPlannerRoundedRecursion_measurable y N hN) r).comp
    ((measurable_const (a := x)).prodMk measurable_id)).const_mul (scalarPlannerWeight y x.1)

lemma scalarPlannerRoundedSingle_work (y : (i : Fin n) → Fin (k i) → ℝ)
    (N : ℕ) (hN : 0 < N) (x : ScalarPlannerState n) (r : ℕ) (t : MultilevelTree (PlannerUniformSeed n) r) :
    (scalarPlannerRoundedSingle y N hN x r t).2 ≤ 4 * 16^r + 1 :=
  scalarPlannerSingle_work y x r t

theorem scalarPlannerNormalizedRoundedEstimate_sq_error (y : (i : Fin n) → Fin (k i) → ℝ)
    (hcap : ∀ i j, y i j ≤ 1) (N : ℕ) (hN : 0 < N) (x : ScalarPlannerState n) (r : ℕ) :
    (∫ t, (multilevelEstimate (scalarPlannerRoundedRecursion y N hN) r x t -
      scalarPlannerNormalizedRoundedValue y N hN x)^2 ∂multilevelTreeLaw (plannerUniformSeedLaw n) r) ≤
      25 * (1/2 : ℝ)^r := by
  apply integral_multilevelEstimate_sq_error_le _ (scalarPlannerRoundedRecursion_measurable y N hN)
    (fun _ o _ ha _ => scalarPlannerPayoff_bounds y hcap o ha)
    (fun _ o => scalarPlannerPayoff_lipschitz y o) _ (measurable_scalarPlannerNormalizedRoundedValue y N hN)
    (scalarPlannerNormalizedRoundedValue_bounds y hcap N hN)
    (scalarPlannerNormalizedRoundedValue_empty y N hN) _ (scalarPlannerRecursion_coefficient_bounds y)
  intro s hs
  have hf := scalarPlannerNormalizedRoundedValue_fixed y N hN s
  simpa only [finiteRankStep, hs, Bool.false_eq_true, if_false] using hf

lemma scalarPlannerRoundedSingle_error_identity (y : (i : Fin n) → Fin (k i) → ℝ)
    (N : ℕ) (hN : 0 < N) (x : ScalarPlannerState n) (r : ℕ)
    (t : MultilevelTree (PlannerUniformSeed n) r) :
    ((scalarPlannerRoundedSingle y N hN x r t).1 -
      scalarPlannerWeight y x.1 * scalarPlannerNormalizedRoundedValue y N hN x)^2 =
    (scalarPlannerWeight y x.1)^2 *
      (multilevelEstimate (scalarPlannerRoundedRecursion y N hN) r x t -
        scalarPlannerNormalizedRoundedValue y N hN x)^2 := by
  simp only [scalarPlannerRoundedSingle]
  ring

lemma integrable_scalarPlannerRoundedSingle_sq_error (y : (i : Fin n) → Fin (k i) → ℝ)
    (hcap : ∀ i j, y i j ≤ 1) (N : ℕ) (hN : 0 < N) (x : ScalarPlannerState n) (r : ℕ) :
    Integrable (fun t => ((scalarPlannerRoundedSingle y N hN x r t).1 -
      scalarPlannerWeight y x.1 * scalarPlannerNormalizedRoundedValue y N hN x)^2)
      (multilevelTreeLaw (plannerUniformSeedLaw n) r) := by
  have hb := scalarPlannerNormalizedRoundedValue_bounds y hcap N hN x
  have hEmpty (s : ScalarPlannerState n) (_ : (scalarPlannerRoundedRecursion y N hN).isEmpty s = true) :
      0 ≤ (scalarPlannerRoundedRecursion y N hN).emptyValue s ∧
      (scalarPlannerRoundedRecursion y N hN).emptyValue s ≤ 5 :=
    ⟨(scalarPlannerRecursion_empty_bounds y s).1, (scalarPlannerRecursion_empty_bounds y s).2.trans (by norm_num)⟩
  have hi := (integrable_multilevelEstimate_sq_error (scalarPlannerRoundedRecursion y N hN)
    (scalarPlannerRoundedRecursion_measurable y N hN) hEmpty (plannerUniformSeedLaw n) r x hb.1 hb.2).const_mul
      ((scalarPlannerWeight y x.1)^2)
  exact hi.congr (ae_of_all _ (fun t => (scalarPlannerRoundedSingle_error_identity y N hN x r t).symm))

theorem scalarPlannerRoundedSingle_sq_error (y : (i : Fin n) → Fin (k i) → ℝ)
    (hcap : ∀ i j, y i j ≤ 1) (N : ℕ) (hN : 0 < N) (x : ScalarPlannerState n) (r : ℕ) :
    (∫ t, ((scalarPlannerRoundedSingle y N hN x r t).1 -
      scalarPlannerWeight y x.1 * scalarPlannerNormalizedRoundedValue y N hN x)^2
      ∂multilevelTreeLaw (plannerUniformSeedLaw n) r) ≤
      25 * (scalarPlannerWeight y x.1)^2 * (1/2 : ℝ)^r := by
  simp_rw [scalarPlannerRoundedSingle_error_identity y N hN x r]
  rw [integral_const_mul]
  have he := mul_le_mul_of_nonneg_left (scalarPlannerNormalizedRoundedEstimate_sq_error y hcap N hN x r)
    (sq_nonneg (scalarPlannerWeight y x.1))
  nlinarith

noncomputable def scalarPlannerRoundedQuery (y : (i : Fin n) → Fin (k i) → ℝ)
    (N : ℕ) (hN : 0 < N) (x : ScalarPlannerState n) (r : ℕ) (p : ℝ)
    (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ p)
    (seed : Fin (confidenceCopyCount p H) → MultilevelTree (PlannerUniformSeed n) r) : MedianCopiesResult ℝ :=
  if (scalarPlannerRecursion y).isEmpty x then
    { value := (scalarPlannerRecursion y).emptyValue x, work := 1, copies := 0 }
  else
    let q := confidenceMedianCopies p H (scalarPlannerRoundedSingle y N hN x r) seed
    { value := clipFive q.value, work := q.work + 2, copies := q.copies }

variable [∀ i, NeZero (k i)]

theorem scalarPlannerRoundedQuery_correct (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (hcap : ∀ i j, y i j ≤ 1)
    (N : ℕ) (hN : 0 < N) (x : ScalarPlannerState n) (r : ℕ) (h p : ℝ)
    (hh : 0 < h) (hp : 0 < p) (hp1 : p < 1) (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ p)
    (hprec : 25 * (scalarPlannerWeight y x.1)^2 * (1/2 : ℝ)^r ≤ (h/2)^2 / 64)
    (hgrid : scalarPlannerWeight y x.1 * ((10*(n:ℝ)+4)/(3*(N:ℝ))) ≤ h/4) :
    let μ := multilevelTreeLaw (plannerUniformSeedLaw n) r
    let Q := scalarPlannerRoundedQuery y N hN x r p H
    Measurable (fun seed => (Q seed).value) ∧
      (Measure.pi (fun _ : Fin (confidenceCopyCount p H) => μ)).real
        {seed | h < |(Q seed).value - scalarPlannerValue y hy x|} ≤ p ∧
      ∀ seed, (Q seed).copies ≤ confidenceCopyCount p H ∧
        (Q seed).work ≤ confidenceCopyCount p H * (4 * 16^r+1) + 10 * (confidenceCopyCount p H+1)^2 + 2 := by
  dsimp only
  let v := scalarPlannerValue y hy x
  let w := scalarPlannerWeight y x.1 * scalarPlannerNormalizedRoundedValue y N hN x
  let μ := multilevelTreeLaw (plannerUniformSeedLaw n) r
  have hv := scalarPlannerValue_bounds y hy hcap x
  by_cases hx : (scalarPlannerRecursion y).isEmpty x = true
  · have he : (scalarPlannerRecursion y).emptyValue x = v := by
      have ha : plannerActive y x.1 = ∅ := of_decide_eq_true hx
      simp [v, scalarPlannerValue, scalarPlannerRecursion, ha, Model.Instance.continuationValue_empty]
    simp only [scalarPlannerRoundedQuery, hx, if_true, he, v, measurable_const, sub_self, abs_zero,
      not_lt.mpr hh.le, Set.setOf_false, measureReal_empty, hp.le, Nat.zero_le, true_and]
    intro seed
    omega
  · have hβ := scalarPlannerWeight_pos y x.1
    have hvw : |w-v| ≤ h/4 := by
      have he : v = scalarPlannerWeight y x.1 * scalarPlannerNormalizedValue y hy x := by
        simp [v, scalarPlannerNormalizedValue, mul_div_cancel₀ _ hβ.ne']
      dsimp [w]
      rw [he, ← mul_sub, abs_mul, abs_of_pos hβ, abs_sub_comm]
      exact (mul_le_mul_of_nonneg_left (scalarPlannerNormalizedRoundedValue_error y hy hcap N hN x)
        hβ.le).trans hgrid
    have hc := confidenceMedianCopies_correct μ (scalarPlannerRoundedSingle y N hN x r)
      (measurable_scalarPlannerRoundedSingle_value y N hN x r) w (h/2) p (by positivity) hp hp1 H
      (integrable_scalarPlannerRoundedSingle_sq_error y hcap N hN x r)
      ((scalarPlannerRoundedSingle_sq_error y hcap N hN x r).trans hprec)
      (4*16^r+1) (scalarPlannerRoundedSingle_work y N hN x r)
    have hClip : Measurable (clipFive (Value := ℝ)) := measurable_const.max (measurable_const.min measurable_id)
    refine ⟨?_, ?_, ?_⟩
    · simpa only [scalarPlannerRoundedQuery, if_neg hx, Function.comp_def] using hClip.comp hc.1
    · refine (measureReal_mono ?_).trans hc.2.1
      intro seed hs
      have hs' : h < |clipFive (confidenceMedianCopies p H (scalarPlannerRoundedSingle y N hN x r) seed).value - v| := by
        simpa only [Set.mem_setOf_eq, scalarPlannerRoundedQuery, if_neg hx, v] using hs
      by_contra! hn
      let a := (confidenceMedianCopies p H (scalarPlannerRoundedSingle y N hN x r) seed).value
      have he : |a-v| ≤ |a-w| + |w-v| := by
        calc
          _ = |(a-w)+(w-v)| := by ring_nf
          _ ≤ _ := abs_add_le _ _
      have htotal := (clipFive_abs_sub_le a hv.1 hv.2).trans he
      have hn' : |a-w| ≤ h/2 := le_of_not_gt hn
      change h < |clipFive a-v| at hs'
      linarith
    · intro seed
      simp only [scalarPlannerRoundedQuery, if_neg hx]
      exact ⟨(hc.2.2.2 seed).1.le, Nat.add_le_add_right (hc.2.2.2 seed).2 2⟩

end ProphetSecretary.Statistics
