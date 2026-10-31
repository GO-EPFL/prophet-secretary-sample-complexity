import ProphetSecretary.Model.Duration
import ProphetSecretary.Model.BellmanBase
import Mathlib.Tactic.Linarith

/-!
# Quantitative finite duration lower bounds

A policy cannot select before an arrival. If it rejects zero, it cannot select before
a positive arrival, even though all zero identities remain in its observation history.
The resulting constants depend on the cardinality or on the expected positive tail count.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

lemma Instance.uniformClock_probability_lt {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Instance.uniformClock.real (Iio s) = s := by
  have he : Iio s ∩ Icc (0 : ℝ) 1 = Ico 0 s := by
    ext x
    constructor
    · rintro ⟨hxs, hx⟩
      exact ⟨hx.1, hxs⟩
    · rintro ⟨hx0, hxs⟩
      exact ⟨hxs, hx0, hxs.le.trans hs1⟩
  unfold Measure.real Instance.uniformClock
  rw [Measure.restrict_apply measurableSet_Iio, he, Real.volume_Ico]
  simp only [sub_zero, ENNReal.toReal_ofReal hs0]

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma Instance.world_clock_probability_lt (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin n) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (P.worldLaw ν).real {ω : World n Seed | ω.2.1 i < s} = s := by
  have hp := P.world_clock_measurePreserving ν i
  calc
    _ = ((P.worldLaw ν).map (fun ω : World n Seed => ω.2.1 i)).real (Iio s) :=
      (map_measureReal_apply hp.measurable measurableSet_Iio).symm
    _ = Instance.uniformClock.real (Iio s) := by rw [hp.map_eq]
    _ = s := Instance.uniformClock_probability_lt hs0 hs1

lemma Instance.world_positiveArrival_probability (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin n) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (P.worldLaw ν).real {ω : World n Seed | 0 < ω.1 i ∧ ω.2.1 i < s} =
      s * (P.law i (Ioi 0)).toReal := by
  have hp := P.world_candidate_measurePreserving ν i
  calc
    _ = ((P.worldLaw ν).map (fun ω : World n Seed => (ω.1 i, ω.2.1 i))).real
        (Ioi 0 ×ˢ Iio s) :=
      (map_measureReal_apply hp.measurable (measurableSet_Ioi.prod measurableSet_Iio)).symm
    _ = ((P.law i).prod Instance.uniformClock).real (Ioi 0 ×ˢ Iio s) := by rw [hp.map_eq]
    _ = (P.law i).real (Ioi 0) * Instance.uniformClock.real (Iio s) := measureReal_prod_prod _ _
    _ = _ := by
      rw [Instance.uniformClock_probability_lt hs0 hs1]
      change (P.law i (Ioi 0)).toReal * s = s * (P.law i (Ioi 0)).toReal
      ring

/-- Zero rejection is a condition on reached preterminal arrivals only. -/
def Policy.RejectsReachedZero (π : Policy Seed n) (r : Seed) (x u : Fin n → ℝ) : Prop :=
  ∀ i, π.Reaches r x u i → x i = 0 → u i < 1 → π.action r Finset.univ x u i = false

omit [MeasurableSpace Seed] in
lemma Policy.le_stoppingTime_of_selected_after (π : Policy Seed n) (r : Seed)
    (x u : Fin n → ℝ) {s : ℝ} (hs1 : s ≤ 1)
    (hsel : ∀ i, π.ActualSelects r Finset.univ x u i → s ≤ u i) :
    s ≤ π.stoppingTime r Finset.univ x u := by
  rcases π.stoppingTime_eq_one_or_actualSelects r Finset.univ x u with heq | ⟨i, hi⟩
  · rw [heq]
    exact hs1
  · exact (hsel i hi).trans_eq hi.1.2

omit [MeasurableSpace Seed] in
lemma Policy.le_stoppingTime_of_no_positiveArrival (π : Policy Seed n) (r : Seed)
    (x u : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) (hz : π.RejectsReachedZero r x u)
    {s : ℝ} (hs1 : s ≤ 1) (hno : ∀ i, ¬(0 < x i ∧ u i < s)) :
    s ≤ π.stoppingTime r Finset.univ x u := by
  apply π.le_stoppingTime_of_selected_after r x u hs1
  intro i hi
  by_contra hu
  have hui : u i < s := lt_of_not_ge hu
  have hxpos : 0 < x i := by
    by_contra hx'
    have hxi : x i = 0 := le_antisymm (le_of_not_gt hx') (hx i)
    have hr := π.selects_implies_reaches r x u hi.1
    have hfalse := hz i hr hxi (hui.trans_le hs1)
    have htrue := (π.mem_accepted r Finset.univ x u i |>.mp hi.1.1).2
    exact Bool.false_ne_true (hfalse.symm.trans htrue)
  exact hno i ⟨hxpos, hui⟩

/-- An avoidance event supplies a lower bound without independence from stopping. -/
lemma integral_ge_window_avoidance {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {T : Ω → ℝ} (hT : Integrable T μ)
    (hT0 : ∀ᵐ ω ∂μ, 0 ≤ T ω) {B : Set Ω} (hB : MeasurableSet B) {s C : ℝ}
    (hs : 0 ≤ s) (hprob : μ.real B ≤ s * C)
    (hgood : ∀ᵐ ω ∂μ, ω ∉ B → s ≤ T ω) :
    s * (1 - s * C) ≤ ∫ ω, T ω ∂μ := by
  have hi : Integrable (Bᶜ.indicator (fun _ : Ω => s)) μ := (integrable_const s).indicator hB.compl
  have h := integral_mono_ae hi hT (by
    filter_upwards [hT0, hgood] with ω hω0 hωg
    by_cases hω : ω ∈ B
    · rw [Set.indicator_of_notMem (show ω ∉ Bᶜ from by simpa using hω)]
      exact hω0
    · rw [Set.indicator_of_mem hω]
      exact hωg hω)
  rw [integral_indicator_const s hB.compl, smul_eq_mul, measureReal_compl hB, probReal_univ] at h
  nlinarith [mul_le_mul_of_nonneg_left hprob hs]

/-- The universal quarter constant after choosing the early time window. -/
lemma duration_window_quarter {C T : ℝ} (hC : 0 ≤ C)
    (h : (2 * (1 + C))⁻¹ * (1 - (2 * (1 + C))⁻¹ * C) ≤ T) :
    1 / (4 * (1 + C)) ≤ T := by
  let s : ℝ := (2 * (1 + C))⁻¹
  have hden : 0 < 2 * (1 + C) := by linarith
  have hs : 0 < s := inv_pos.mpr hden
  have heq : s * (2 * (1 + C)) = 1 := inv_mul_cancel₀ hden.ne'
  have hsC : s * C ≤ 1 / 2 := by nlinarith
  have hlow : s / 2 ≤ s * (1 - s * C) := by
    nlinarith [mul_le_mul_of_nonneg_left hsC hs.le]
  have hhalf : s / 2 = 1 / (4 * (1 + C)) := by
    dsimp [s]
    field_simp
    norm_num
  rw [← hhalf]
  exact hlow.trans h

/-- Every admissible finite execution has a cardinality-dependent duration floor. -/
theorem Policy.meanDuration_ge_card_bound (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    1 / (4 * (1 + (n : ℝ))) ≤ π.meanDuration P ν := by
  classical
  let μ := P.worldLaw ν
  let s : ℝ := (2 * (1 + (n : ℝ)))⁻¹
  have hden : 0 < 2 * (1 + (n : ℝ)) := by positivity
  have hs : 0 < s := inv_pos.mpr hden
  have heq : s * (2 * (1 + (n : ℝ))) = 1 := inv_mul_cancel₀ hden.ne'
  have hs1 : s ≤ 1 := by nlinarith [mul_nonneg hs.le (Nat.cast_nonneg n : 0 ≤ (n : ℝ))]
  let B : Set (World n Seed) := ⋃ i : Fin n, {ω | ω.2.1 i < s}
  have hBm : MeasurableSet B := MeasurableSet.iUnion fun i =>
    measurableSet_lt ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)) measurable_const
  have hprob : μ.real B ≤ s * n := by
    have h := measureReal_iUnion_fintype_le (μ := μ) (fun i : Fin n => {ω : World n Seed | ω.2.1 i < s})
    have he (i : Fin n) : μ.real {ω : World n Seed | ω.2.1 i < s} = s :=
      P.world_clock_probability_lt ν i hs.le hs1
    simp only [he, Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at h
    simpa only [B, mul_comm] using h
  have hgood : ∀ᵐ ω : World n Seed ∂μ, ω ∉ B → s ≤ π.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 := by
    filter_upwards [] with ω hω
    apply (π.le_stoppingTime_iff _ _ _ _ s).mpr
    refine ⟨hs1, ?_⟩
    intro i _
    exact le_of_not_gt (fun hi => hω (Set.mem_iUnion.mpr ⟨i, hi⟩))
  apply duration_window_quarter (Nat.cast_nonneg n)
  exact integral_ge_window_avoidance μ (P.integrable_worldTime ν π hπ Finset.univ)
    ((P.worldTime_mem_unitInterval ν π Finset.univ).mono fun _ h => h.1) hBm hs.le hprob hgood

/-- Zero-rejecting policies wait for positive arrivals; the bound depends on `L`,
not on the number of observed zero identities. -/
theorem Policy.meanDuration_ge_positiveCount_bound (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hz : ∀ᵐ ω : World n Seed ∂P.worldLaw ν, π.RejectsReachedZero ω.2.2 ω.1 ω.2.1) :
    1 / (4 * (1 + P.positiveCount)) ≤ π.meanDuration P ν := by
  classical
  let μ := P.worldLaw ν
  let C := P.positiveCount
  have hC : 0 ≤ C := P.tailCount_nonnegative 0
  let s : ℝ := (2 * (1 + C))⁻¹
  have hden : 0 < 2 * (1 + C) := by linarith
  have hs : 0 < s := inv_pos.mpr hden
  have heq : s * (2 * (1 + C)) = 1 := inv_mul_cancel₀ hden.ne'
  have hs1 : s ≤ 1 := by nlinarith [mul_nonneg hs.le hC]
  let B : Set (World n Seed) := ⋃ i : Fin n, {ω | 0 < ω.1 i ∧ ω.2.1 i < s}
  have hEvent (i : Fin n) : MeasurableSet {ω : World n Seed | 0 < ω.1 i ∧ ω.2.1 i < s} :=
    (measurableSet_lt measurable_const ((measurable_pi_apply i).comp measurable_fst)).inter
      (measurableSet_lt ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)) measurable_const)
  have hBm : MeasurableSet B := MeasurableSet.iUnion hEvent
  have hprob : μ.real B ≤ s * C := by
    have h := measureReal_iUnion_fintype_le (μ := μ)
      (fun i : Fin n => {ω : World n Seed | 0 < ω.1 i ∧ ω.2.1 i < s})
    have he (i : Fin n) : μ.real {ω : World n Seed | 0 < ω.1 i ∧ ω.2.1 i < s} =
        s * (P.law i (Ioi 0)).toReal := P.world_positiveArrival_probability ν i hs.le hs1
    simp only [he] at h
    calc
      μ.real B ≤ ∑ i, s * (P.law i (Ioi 0)).toReal := h
      _ = s * C := by rw [← Finset.mul_sum]; rfl
  have hvalues : ∀ᵐ ω : World n Seed ∂μ, ∀ i, 0 ≤ ω.1 i :=
    (measurePreserving_fst : MeasurePreserving (fun ω : World n Seed => ω.1) μ P.valuesLaw).quasiMeasurePreserving.ae
      P.ae_nonnegative
  have hgood : ∀ᵐ ω : World n Seed ∂μ, ω ∉ B → s ≤ π.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 := by
    filter_upwards [hvalues, hz] with ω hx hzero hω
    apply π.le_stoppingTime_of_no_positiveArrival ω.2.2 ω.1 ω.2.1 hx hzero hs1
    intro i hi
    exact hω (Set.mem_iUnion.mpr ⟨i, hi⟩)
  apply duration_window_quarter hC
  exact integral_ge_window_avoidance μ (P.integrable_worldTime ν π hπ Finset.univ)
    ((P.worldTime_mem_unitInterval ν π Finset.univ).mono fun _ h => h.1) hBm hs.le hprob hgood

lemma RandomizedPolicy.expectedDuration_ge_card_bound (π : RandomizedPolicy n) (P : Instance n) :
    1 / (4 * (1 + (n : ℝ))) ≤ π.expectedDuration P :=
  π.rule.meanDuration_ge_card_bound π.measurable_rule P π.seedLaw

lemma RandomizedPolicy.expectedDuration_ge_positiveCount_bound (π : RandomizedPolicy n) (P : Instance n)
    (hz : ∀ᵐ ω : π.World ∂P.worldLaw π.seedLaw, π.rule.RejectsReachedZero ω.2.2 ω.1 ω.2.1) :
    1 / (4 * (1 + P.positiveCount)) ≤ π.expectedDuration P :=
  π.rule.meanDuration_ge_positiveCount_bound π.measurable_rule P π.seedLaw hz

/-- Every preterminal zero observation is rejected by positive scalar value thresholds.
The observation itself remains in all later histories. -/
lemma Instance.valuePolicy_rejectsReachedZero (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (r : Unit) (x u : Fin n → ℝ) :
    (P.valuePolicy hP hw.le hc.le).rule.RejectsReachedZero r x u := by
  cases r
  intro i _hr hi hut
  exact P.valueThreshold_rejects_zero hP hw hc x u i hut hi

/-- The duration floor is valid even under another evaluation law. -/
lemma Instance.valuePolicy_duration_ge_positiveCount (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    (Q : Instance n) :
    1 / (4 * (1 + Q.positiveCount)) ≤ (P.valuePolicy hP hw.le hc.le).expectedDuration Q := by
  apply RandomizedPolicy.expectedDuration_ge_positiveCount_bound
  exact Filter.Eventually.of_forall fun ω => P.valuePolicy_rejectsReachedZero hP hw hc ω.2.2 ω.1 ω.2.1

end ProphetSecretary.Model


