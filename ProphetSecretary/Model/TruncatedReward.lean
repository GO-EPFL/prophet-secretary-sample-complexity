import ProphetSecretary.Model.RewardDuration
import ProphetSecretary.Model.Restriction
import ProphetSecretary.Model.ContinuationSlope

/-!
# Reward and duration at a positive reward level

The small selected value contributes at most the cutoff; larger values are charged
to reached positive-tail events. This yields a bound uniform in the number of offers
using expected tail counts, while keeping every observed zero identity.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

private lemma sum_embedding_le {m n : ℕ} (e : Fin m ↪ Fin n) (f : Fin n → ℝ)
    (hf : ∀ i, 0 ≤ f i) : (∑ i, f (e i)) ≤ ∑ i, f i := by
  calc
    (∑ i, f (e i)) = ∑ j ∈ (Finset.univ : Finset (Fin m)).map e, f j := by rw [Finset.sum_map]
    _ ≤ ∑ j : Fin n, f j :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hf j)

lemma Instance.tailCount_restrictBy_le {n m : ℕ} (P : Instance n) (e : Fin m ↪ Fin n) (b : ℝ) :
    (P.restrictBy e).tailCount b ≤ P.tailCount b :=
  sum_embedding_le e (fun i => (P.law i (Ioi b)).toReal) (fun _ => ENNReal.toReal_nonneg)

lemma Instance.tailCount_restrictTo_le {n : ℕ} (P : Instance n) (A : Finset (Fin n)) (b : ℝ) :
    (P.restrictTo A).tailCount b ≤ P.tailCount b :=
  P.tailCount_restrictBy_le (stateEmbedding A) b

lemma Instance.totalFirstMoment_restrictBy_le {n m : ℕ} (P : Instance n) (e : Fin m ↪ Fin n) :
    (P.restrictBy e).totalFirstMoment ≤ P.totalFirstMoment :=
  sum_embedding_le e (fun i => ∫ x, x ∂P.law i) (fun i => integral_nonneg_of_ae (P.nonnegative i))

lemma Instance.totalFirstMoment_restrictTo_le {n : ℕ} (P : Instance n) (A : Finset (Fin n)) :
    (P.restrictTo A).totalFirstMoment ≤ P.totalFirstMoment :=
  P.totalFirstMoment_restrictBy_le (stateEmbedding A)

variable {n : ℕ} {Seed : Type*}

lemma Policy.reward_le_cutoff_add_reached_tail (π : Policy Seed n) (r : Seed)
    (x u : Fin n → ℝ) {b H : ℝ} (hb : 0 ≤ b) (hH : 0 ≤ H) (hx : ∀ i, x i ≤ H) :
    π.reward r Finset.univ x u ≤ b + H *
      ∑ i, (if π.Reaches r x u i ∧ b < x i then (1 : ℝ) else 0) := by
  have hcount : 0 ≤ ∑ i, (if π.Reaches r x u i ∧ b < x i then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hright : b ≤ b + H * ∑ i, (if π.Reaches r x u i ∧ b < x i then (1 : ℝ) else 0) :=
    le_add_of_nonneg_right (mul_nonneg hH hcount)
  by_cases h : ∃ i, π.ActualSelects r Finset.univ x u i
  · obtain ⟨i, hi⟩ := h
    rw [π.reward_eq_of_actualSelects _ _ _ _ hi]
    by_cases hxi : x i ≤ b
    · exact hxi.trans hright
    · have hr := π.selects_implies_reaches _ _ _ hi.1
      have hterm : (1 : ℝ) ≤ ∑ j, (if π.Reaches r x u j ∧ b < x j then (1 : ℝ) else 0) := by
        have hh := Finset.single_le_sum
          (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
            show 0 ≤ (if π.Reaches r x u j ∧ b < x j then (1 : ℝ) else 0) from by split_ifs <;> norm_num)
          (Finset.mem_univ i)
        simpa only [hr, lt_of_not_ge hxi, and_self, if_true] using hh
      have hHc := mul_le_mul_of_nonneg_left hterm hH
      nlinarith [hx i]
  · rw [π.reward_eq_zero_of_no_actualSelection _ _ _ _ (fun i hi => h ⟨i, hi⟩)]
    exact hb.trans hright

variable [MeasurableSpace Seed]

lemma Policy.reachedTailProbability_eq (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) (b : ℝ) :
    (P.worldLaw ν).real {ω : World n Seed | π.Reaches ω.2.2 ω.1 ω.2.1 i ∧ b < ω.1 i} =
      π.reachProbability P ν i * (P.law i (Ioi b)).toReal := by
  classical
  let I : World n Seed → ℝ := fun ω => if π.Reaches ω.2.2 ω.1 ω.2.1 i then 1 else 0
  have hInd := ProphetSecretary.Probability.reachIndicator_value_independent P ν i π hπ
  have h := hInd.measure_inter_preimage_eq_mul ({1} : Set ℝ) (Ioi b)
    (measurableSet_singleton 1) measurableSet_Ioi
  have hpre : I ⁻¹' ({1} : Set ℝ) = {ω : World n Seed | π.Reaches ω.2.2 ω.1 ω.2.1 i} := by
    ext ω
    change (if π.Reaches ω.2.2 ω.1 ω.2.1 i then (1 : ℝ) else 0) = 1 ↔ π.Reaches ω.2.2 ω.1 ω.2.1 i
    by_cases hr : π.Reaches ω.2.2 ω.1 ω.2.1 i <;> simp [hr]
  change (P.worldLaw ν) (I ⁻¹' {1} ∩ (fun ω : World n Seed => ω.1 i) ⁻¹' Ioi b) =
    (P.worldLaw ν) (I ⁻¹' {1}) * (P.worldLaw ν) ((fun ω : World n Seed => ω.1 i) ⁻¹' Ioi b) at h
  rw [hpre] at h
  have hv : MeasurePreserving (fun ω : World n Seed => ω.1 i) (P.worldLaw ν) (P.law i) :=
    (measurePreserving_eval P.law i).comp measurePreserving_fst
  rw [hv.measure_preimage measurableSet_Ioi.nullMeasurableSet] at h
  have hset : ({ω : World n Seed | π.Reaches ω.2.2 ω.1 ω.2.1 i} ∩
      (fun ω : World n Seed => ω.1 i) ⁻¹' Ioi b) =
      {ω : World n Seed | π.Reaches ω.2.2 ω.1 ω.2.1 i ∧ b < ω.1 i} := rfl
  rw [hset] at h
  have hr := congrArg ENNReal.toReal h
  simpa only [ENNReal.toReal_mul, Measure.real, Policy.reachProbability] using hr

/-- The positive-tail reward estimate is uniform over general policies and instance size. -/
theorem RandomizedPolicy.expectedReward_le_cutoff_add_tailCount (π : RandomizedPolicy n) (P : Instance n)
    {H b : ℝ} (hH : 0 ≤ H) (hb : 0 ≤ b) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) :
    π.expectedReward P ≤ b + 2 * π.expectedDuration P * H * P.tailCount b := by
  classical
  let μ := P.worldLaw π.seedLaw
  let E : Fin n → Set π.World := fun i => {ω | π.rule.Reaches ω.2.2 ω.1 ω.2.1 i ∧ b < ω.1 i}
  let J : Fin n → π.World → ℝ := fun i ω => if ω ∈ E i then 1 else 0
  have hEm (i : Fin n) : MeasurableSet (E i) :=
    (π.rule.measurableSet_reaches π.measurable_rule (measurable_snd.comp measurable_snd)
      (fun j => (measurable_pi_apply j).comp measurable_fst)
      (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i).inter
      (measurableSet_lt measurable_const ((measurable_pi_apply i).comp measurable_fst))
  have hJI (i : Fin n) : Integrable (J i) μ := by
    apply Integrable.of_bound (Measurable.ite (hEm i) measurable_const measurable_const).aestronglyMeasurable 1
    filter_upwards [] with ω
    dsimp [J]
    split_ifs <;> norm_num
  have hJeq (i : Fin n) : (∫ ω, J i ω ∂μ) =
      π.rule.reachProbability P π.seedLaw i * (P.law i (Ioi b)).toReal := by
    have h : (∫ ω, J i ω ∂μ) = μ.real (E i) := by
      simpa only [J, Set.indicator_apply, Pi.one_apply] using (integral_indicator_one (μ := μ) (hEm i))
    exact h.trans (π.rule.reachedTailProbability_eq π.measurable_rule P π.seedLaw i b)
  have hvals : ∀ᵐ ω : π.World ∂μ, ∀ i, ω.1 i ≤ H := by
    have hv : ∀ᵐ x ∂P.valuesLaw, ∀ i, x i ≤ H := by
      rw [ae_all_iff]
      intro i
      exact (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hbound i)
    exact (measurePreserving_fst : MeasurePreserving (fun ω : π.World => ω.1) μ P.valuesLaw).quasiMeasurePreserving.ae hv
  have hsum : Integrable (fun ω : π.World => ∑ i, J i ω) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hJI i)
  have hR := integral_mono_ae (π.integrable_realizedReward P (P.integrable_maximum_of_bounded hbound))
    ((integrable_const b).add (hsum.const_mul H)) (by
      filter_upwards [hvals] with ω hω
      exact π.rule.reward_le_cutoff_add_reached_tail _ _ _ hb hH hω)
  change (∫ ω : π.World, π.realizedReward ω ∂μ) ≤ ∫ ω : π.World, b + H * ∑ i, J i ω ∂μ at hR
  rw [integral_add (f := fun _ : π.World => b) (g := fun ω : π.World => H * ∑ i, J i ω)
      (integrable_const b) (hsum.const_mul H), integral_const_mul,
      integral_finsetSum Finset.univ (fun i _ => hJI i)] at hR
  simp only [integral_const, probReal_univ, one_smul, hJeq] at hR
  have htail : (∑ i, π.rule.reachProbability P π.seedLaw i * (P.law i (Ioi b)).toReal) ≤
      (2 * π.expectedDuration P) * P.tailCount b := by
    calc
      _ ≤ ∑ i, (2 * π.expectedDuration P) * (P.law i (Ioi b)).toReal := by
        apply Finset.sum_le_sum
        intro i _
        have hq : π.rule.reachProbability P π.seedLaw i ≤ 2 * π.expectedDuration P :=
          π.rule.reachProbability_le_twice_meanDuration π.measurable_rule P π.seedLaw i
        exact mul_le_mul_of_nonneg_right hq ENNReal.toReal_nonneg
      _ = _ := by rw [← Finset.mul_sum]; rfl
  have hHtail := mul_le_mul_of_nonneg_left htail hH
  change π.expectedReward P ≤ b + H *
    ∑ i, π.rule.reachProbability P π.seedLaw i * (P.law i (Ioi b)).toReal at hR
  nlinarith

/-- The value bound behind the positive-level duration estimate in outcome stability. -/
lemma Instance.valuePolicy_value_le_duration_tailCount (P : Instance n)
    {H b w c u : ℝ} (hH : 0 ≤ H) (hb : 0 ≤ b)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) (hw : 0 < w) (hc : 0 ≤ c) (hu : 0 ≤ u) :
    let hP := P.integrable_maximum_of_bounded hbound
    let π := P.valuePolicy hP hw.le (mul_nonneg hc hu)
    remainingScalarValue P w c u ≤ w * b +
      π.expectedDuration P * (2 * w * H * P.tailCount b + c * u) := by
  dsimp only
  let hP := P.integrable_maximum_of_bounded hbound
  let π := P.valuePolicy hP hw.le (mul_nonneg hc hu)
  have hR := π.expectedReward_le_cutoff_add_tailCount P hH hb hbound
  have hwR := mul_le_mul_of_nonneg_left hR hw.le
  have hJ := P.valuePolicy_optimal hP hw (mul_nonneg hc hu)
  rw [RandomizedPolicy.scalarObjective_eq _ P hP] at hJ
  change remainingScalarValue P w c u ≤ w * b + π.expectedDuration P * (2 * w * H * P.tailCount b + c * u)
  change w * π.expectedReward P + (c * u) * π.expectedDuration P = remainingScalarValue P w c u at hJ
  nlinarith

/-- A positive value band forces substantial duration. The supplied tail-count bound
can be a uniform bound for a whole family; no cardinality enters the conclusion. -/
lemma Instance.valuePolicy_duration_ge_positiveValue (P : Instance n)
    {H b w c u L : ℝ} (hH : 0 ≤ H) (hb : 0 < b)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) (hw : 0 < w) (hc : 0 < c)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hL : P.tailCount (b / 4) ≤ L)
    (hlevel : 3 * w * b / 4 ≤ remainingScalarValue P w c u) :
    let hP := P.integrable_maximum_of_bounded hbound
    let π := P.valuePolicy hP hw.le (mul_nonneg hc.le hu0)
    w * b / (2 * (2 * w * H * L + c)) ≤ π.expectedDuration P := by
  dsimp only
  let hP := P.integrable_maximum_of_bounded hbound
  let π := P.valuePolicy hP hw.le (mul_nonneg hc.le hu0)
  have hT : 0 ≤ π.expectedDuration P := π.expectedDuration_nonnegative P
  have hL0 : 0 ≤ L := (P.tailCount_nonnegative (b / 4)).trans hL
  have hden : 0 < 2 * (2 * w * H * L + c) := by positivity
  have hV := P.valuePolicy_value_le_duration_tailCount (b := b / 4) (w := w) (c := c) (u := u)
    hH (div_nonneg hb.le (by norm_num)) hbound hw hc.le hu0
  have htail := mul_le_mul_of_nonneg_left hL (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hw.le) hH)
  have hu := mul_le_mul_of_nonneg_left hu1 hc.le
  have hcoef := mul_le_mul_of_nonneg_left (add_le_add htail (by simpa only [mul_one] using hu)) hT
  change remainingScalarValue P w c u ≤ w * (b / 4) +
    π.expectedDuration P * (2 * w * H * P.tailCount (b / 4) + c * u) at hV
  apply (div_le_iff₀ hden).mpr
  nlinarith

end ProphetSecretary.Model

