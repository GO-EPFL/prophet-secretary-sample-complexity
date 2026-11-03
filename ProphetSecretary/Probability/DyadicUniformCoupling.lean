import ProphetSecretary.Probability.DyadicUniform
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Comparison errors under uniform-grid rounding

A downward-rounded uniform changes a fixed Bernoulli comparison only within
one grid width of its boundary. If the threshold also moves by a grid width,
the two-sided margin has length four grid widths. These estimates do not
assume a density for the offer distributions.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Probability

lemma measurableSet_decide_disagreement {Ω : Type*} [MeasurableSpace Ω]
    (p q : Ω → Prop) [DecidablePred p] [DecidablePred q]
    (hp : MeasurableSet {ω | p ω}) (hq : MeasurableSet {ω | q ω}) :
    MeasurableSet {ω | decide (p ω) ≠ decide (q ω)} := by
  have he : {ω | decide (p ω) ≠ decide (q ω)} =
      ({ω | p ω} \ {ω | q ω}) ∪ ({ω | q ω} \ {ω | p ω}) := by
    ext ω
    by_cases hp' : p ω <;> by_cases hq' : q ω <;> simp [hp', hq']
  rw [he]
  exact (hp.diff hq).union (hq.diff hp)

lemma uniformClock_interval_le_length (a b : ℝ) (hab : a ≤ b) :
    Model.Instance.uniformClock.real (Icc a b) ≤ b - a := by
  have hm : Model.Instance.uniformClock (Icc a b) ≤ volume (Icc a b) :=
    Measure.restrict_le_self _
  have ht : volume (Icc a b) ≠ ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have h := ENNReal.toReal_mono ht hm
  rw [Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] at h
  exact h

lemma uniformClock_halfOpen_interval_le_length (a b : ℝ) (hab : a ≤ b) :
    Model.Instance.uniformClock.real (Ioc a b) ≤ b - a :=
  (measureReal_mono (Set.Ioc_subset_Icc_self)).trans (uniformClock_interval_le_length a b hab)

lemma uniformGridRound_comparison_probability (N : ℕ) (hN : 0 < N) (r : ℝ) :
    Model.Instance.uniformClock.real
      {u | decide (u ≤ r) ≠ decide (uniformGridRound N hN u ≤ r)} ≤ 1 / (N : ℝ) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hAE : {u | decide (u ≤ r) ≠ decide (uniformGridRound N hN u ≤ r)} ≤ᵐ[Model.Instance.uniformClock]
      Ioc r (r + 1 / (N : ℝ)) := by
    filter_upwards [uniformClock_mem_open_unit] with u hu
    intro hbad
    change decide (u ≤ r) ≠ decide (uniformGridRound N hN u ≤ r) at hbad
    have hb := uniformGridRound_bounds N hN ⟨hu.1.le, hu.2.le⟩
    by_cases hur : u ≤ r
    · have hr : uniformGridRound N hN u ≤ r := hb.2.1.trans hur
      simp [hur, hr] at hbad
    · have hr : uniformGridRound N hN u ≤ r := by
        by_contra hr
        simp [hur, hr] at hbad
      exact ⟨lt_of_not_ge hur, by linarith [hb.2.2]⟩
  have hm : Model.Instance.uniformClock.real
      {u | decide (u ≤ r) ≠ decide (uniformGridRound N hN u ≤ r)} ≤
        Model.Instance.uniformClock.real (Ioc r (r + 1 / (N : ℝ))) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hAE)
  have hi := uniformClock_halfOpen_interval_le_length r (r + 1 / (N : ℝ))
    (by linarith [one_div_pos.mpr hNr])
  linarith

/-- Strict comparisons implement the categorical cumulative-probability
scan. Endpoint conventions do not change the one-width probability bound. -/
lemma uniformGridRound_strict_comparison_probability (N : ℕ) (hN : 0 < N) (r : ℝ) :
    Model.Instance.uniformClock.real
      {u | decide (u < r) ≠ decide (uniformGridRound N hN u < r)} ≤ 1 / (N : ℝ) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hAE : {u | decide (u < r) ≠ decide (uniformGridRound N hN u < r)} ≤ᵐ[Model.Instance.uniformClock]
      Icc r (r + 1 / (N : ℝ)) := by
    filter_upwards [uniformClock_mem_open_unit] with u hu
    intro hbad
    change decide (u < r) ≠ decide (uniformGridRound N hN u < r) at hbad
    have hb := uniformGridRound_bounds N hN ⟨hu.1.le, hu.2.le⟩
    by_cases hur : u < r
    · have hr : uniformGridRound N hN u < r := hb.2.1.trans_lt hur
      simp [hur, hr] at hbad
    · have hr : uniformGridRound N hN u < r := by
        by_contra hr
        simp [hur, hr] at hbad
      exact ⟨le_of_not_gt hur, by linarith [hb.2.2]⟩
  have hm : Model.Instance.uniformClock.real
      {u | decide (u < r) ≠ decide (uniformGridRound N hN u < r)} ≤
        Model.Instance.uniformClock.real (Icc r (r + 1 / (N : ℝ))) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hAE)
  have hi := uniformClock_interval_le_length r (r + 1 / (N : ℝ))
    (by linarith [one_div_pos.mpr hNr])
  linarith

lemma comparison_disagreement_margin {u u' t t' η : ℝ}
    (hu : |u - u'| ≤ η) (ht : |t - t'| ≤ η)
    (hbad : decide (u ≤ t) ≠ decide (u' ≤ t')) :
    u ∈ Icc (t - 2 * η) (t + 2 * η) := by
  have hu' := abs_le.mp hu
  have ht' := abs_le.mp ht
  by_cases h : u ≤ t
  · have hn : ¬u' ≤ t' := by intro h'; simp [h, h'] at hbad
    constructor <;> linarith [lt_of_not_ge hn]
  · have hy : u' ≤ t' := by by_contra hy; simp [h, hy] at hbad
    constructor <;> linarith [lt_of_not_ge h]

/-- The four-width bound used for tail inclusions when the sampled time
threshold and its independent membership uniform are both rounded. -/
lemma uniformGridRound_moving_comparison_probability (N : ℕ) (hN : 0 < N) (t t' : ℝ)
    (ht : |t - t'| ≤ 1 / (N : ℝ)) :
    Model.Instance.uniformClock.real
      {u | decide (u ≤ t) ≠ decide (uniformGridRound N hN u ≤ t')} ≤ 4 / (N : ℝ) := by
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hAE : {u | decide (u ≤ t) ≠ decide (uniformGridRound N hN u ≤ t')} ≤ᵐ[Model.Instance.uniformClock]
      Icc (t - 2 * (1 / (N : ℝ))) (t + 2 * (1 / (N : ℝ))) := by
    filter_upwards [uniformClock_mem_open_unit] with u hu
    intro hbad
    have hb := uniformGridRound_bounds N hN ⟨hu.1.le, hu.2.le⟩
    have he : |u - uniformGridRound N hN u| ≤ 1 / (N : ℝ) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hb.2.1)]
      exact hb.2.2
    exact comparison_disagreement_margin he ht hbad
  have hm : Model.Instance.uniformClock.real
      {u | decide (u ≤ t) ≠ decide (uniformGridRound N hN u ≤ t')} ≤
        Model.Instance.uniformClock.real
          (Icc (t - 2 * (1 / (N : ℝ))) (t + 2 * (1 / (N : ℝ)))) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hAE)
  have hi := uniformClock_interval_le_length
    (t - 2 * (1 / (N : ℝ))) (t + 2 * (1 / (N : ℝ)))
      (by linarith [one_div_pos.mpr hNr])
  have he : t + 2 * (1 / (N : ℝ)) - (t - 2 * (1 / (N : ℝ))) = 4 / (N : ℝ) := by ring
  rw [he] at hi
  exact hm.trans hi

lemma uniformGridRound_sup'_bounds {ι : Type*} [DecidableEq ι] (N : ℕ) (hN : 0 < N)
    (D : Finset ι) (hD : D.Nonempty) (u : ι → ℝ) (hu : ∀ i ∈ D, u i ∈ Icc (0 : ℝ) 1) :
    D.sup' hD (fun i => uniformGridRound N hN (u i)) ≤ D.sup' hD u ∧
      D.sup' hD u - D.sup' hD (fun i => uniformGridRound N hN (u i)) ≤ 1 / (N : ℝ) := by
  constructor
  · apply Finset.sup'_le
    intro i hi
    exact (uniformGridRound_bounds N hN (hu i hi)).2.1.trans (Finset.le_sup' u hi)
  · have hmax : D.sup' hD u ≤ D.sup' hD (fun i => uniformGridRound N hN (u i)) + 1 / (N : ℝ) := by
      apply Finset.sup'_le
      intro i hi
      have hb := uniformGridRound_bounds N hN (hu i hi)
      have hm := Finset.le_sup' (fun j => uniformGridRound N hN (u j)) hi
      linarith [hb.2.2]
    linarith

end ProphetSecretary.Probability
