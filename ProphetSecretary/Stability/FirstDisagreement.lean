import ProphetSecretary.Model.Outcome
import ProphetSecretary.Model.BellmanLossProbability

/-!
# First disagreement on a common execution

The policies receive the same offers and clocks. A difference in their selected
reward or time has a first jointly reached action disagreement. This is the pathwise
step in `eq:ps-first-disagreement` and `eq:ps-duration-stability-explicit`.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed OtherSeed : Type*}

def Policy.OutcomesDiffer (π : Policy Seed n) (ρ : Policy OtherSeed n)
    (r : Seed) (s : OtherSeed) (x u : Fin n → ℝ) : Prop :=
  π.reward r Finset.univ x u ≠ ρ.reward s Finset.univ x u ∨
    π.stoppingTime r Finset.univ x u ≠ ρ.stoppingTime s Finset.univ x u

def Policy.EarlyOutcomeDifference (π : Policy Seed n) (ρ : Policy OtherSeed n)
    (r : Seed) (s : OtherSeed) (x u : Fin n → ℝ) (cut : ℝ) : Prop :=
  π.OutcomesDiffer ρ r s x u ∧
    min (π.stoppingTime r Finset.univ x u) (ρ.stoppingTime s Finset.univ x u) < cut

lemma Policy.not_outcomesDiffer_of_same_selection (π : Policy Seed n) (ρ : Policy OtherSeed n)
    (r : Seed) (s : OtherSeed) (x u : Fin n → ℝ) {i : Fin n}
    (hi : π.ActualSelects r Finset.univ x u i) (hj : ρ.ActualSelects s Finset.univ x u i) :
    ¬π.OutcomesDiffer ρ r s x u := by
  intro hd
  rcases hd with hR | hT
  · exact hR ((π.reward_eq_of_actualSelects _ _ _ _ hi).trans (ρ.reward_eq_of_actualSelects _ _ _ _ hj).symm)
  · exact hT (hi.1.2.symm.trans hj.1.2)

lemma Policy.outcomesDiffer_symm (π : Policy Seed n) (ρ : Policy OtherSeed n)
    (r : Seed) (s : OtherSeed) (x u : Fin n → ℝ) :
    π.OutcomesDiffer ρ r s x u ↔ ρ.OutcomesDiffer π s r x u := by
  exact or_congr ne_comm ne_comm

lemma Policy.disagreement_witness_of_left_earlier (π : Policy Seed n) (ρ : Policy OtherSeed n)
    (r : Seed) (s : OtherSeed) (x u : Fin n → ℝ) (hu : Function.Injective u)
    {cut : ℝ} (hcut : cut ≤ 1) (hdiff : π.OutcomesDiffer ρ r s x u)
    (horder : π.stoppingTime r Finset.univ x u ≤ ρ.stoppingTime s Finset.univ x u)
    (hearly : π.stoppingTime r Finset.univ x u < cut) :
    ∃ i, u i < cut ∧ π.Reaches r x u i ∧
      u i ≤ ρ.stoppingTime s Finset.univ x u ∧
      π.action r Finset.univ x u i ≠ ρ.action s Finset.univ x u i := by
  rcases π.stoppingTime_eq_one_or_actualSelects r Finset.univ x u with h1 | ⟨i, hi⟩
  · rw [h1] at hearly
    exact False.elim ((not_lt_of_ge hcut) hearly)
  · have hiTime : u i = π.stoppingTime r Finset.univ x u := hi.1.2
    have hiReach := π.selects_implies_reaches r x u hi.1
    have hρReach : u i ≤ ρ.stoppingTime s Finset.univ x u := hiTime.le.trans horder
    refine ⟨i, hiTime.trans_lt hearly, hiReach, hρReach, ?_⟩
    intro heq
    have hπa := (π.mem_accepted r Finset.univ x u i |>.mp hi.1.1).2
    have hρa : ρ.action s Finset.univ x u i = true := heq.symm.trans hπa
    have hρacc : i ∈ ρ.accepted s Finset.univ x u :=
      (ρ.mem_accepted s Finset.univ x u i).mpr ⟨Finset.mem_univ _, hρa⟩
    have hρTime : u i = ρ.stoppingTime s Finset.univ x u :=
      le_antisymm hρReach (ρ.stoppingTime_le_of_accepted _ _ _ _ _ hρacc)
    have hρsel : ρ.ActualSelects s Finset.univ x u i :=
      (ρ.actualSelects_iff_selects s Finset.univ x u hu i).mpr ⟨hρacc, hρTime⟩
    exact π.not_outcomesDiffer_of_same_selection ρ r s x u hi hρsel hdiff

/-- The first selected arrival at which outcomes differ is reached by both policies. -/
lemma Policy.earlyOutcomeDifference_witness (π : Policy Seed n) (ρ : Policy OtherSeed n)
    (r : Seed) (s : OtherSeed) (x u : Fin n → ℝ) (hu : Function.Injective u)
    {cut : ℝ} (hcut : cut ≤ 1) (h : π.EarlyOutcomeDifference ρ r s x u cut) :
    ∃ i, u i < cut ∧ π.Reaches r x u i ∧
      u i ≤ ρ.stoppingTime s Finset.univ x u ∧
      π.action r Finset.univ x u i ≠ ρ.action s Finset.univ x u i := by
  rcases le_total (π.stoppingTime r Finset.univ x u) (ρ.stoppingTime s Finset.univ x u) with hle | hle
  · exact π.disagreement_witness_of_left_earlier ρ r s x u hu hcut h.1 hle
      (by simpa only [min_eq_left hle] using h.2)
  · have hd := (π.outcomesDiffer_symm ρ r s x u).mp h.1
    obtain ⟨i, hi, hρr, hπr, ha⟩ := ρ.disagreement_witness_of_left_earlier π s r x u hu hcut hd hle
      (by simpa only [min_eq_right hle] using h.2)
    exact ⟨i, hi, hπr, hρr, Ne.symm ha⟩

/-- Outside an early disagreement, either the outcomes agree or both times lie
in the final window. The error is bounded on every valid clock vector. -/
lemma Policy.duration_difference_le_window (π : Policy Seed n) (ρ : Policy OtherSeed n)
    (r : Seed) (s : OtherSeed) (x u : Fin n → ℝ) (hu0 : ∀ i, 0 ≤ u i)
    {window : ℝ} (hw : 0 ≤ window) :
    |π.stoppingTime r Finset.univ x u - ρ.stoppingTime s Finset.univ x u| ≤
      window + (if π.EarlyOutcomeDifference ρ r s x u (1 - window) then 1 else 0) := by
  have hπ0 := π.stoppingTime_nonneg r Finset.univ x u hu0
  have hρ0 := ρ.stoppingTime_nonneg s Finset.univ x u hu0
  have hπ1 := π.stoppingTime_le_one r Finset.univ x u
  have hρ1 := ρ.stoppingTime_le_one s Finset.univ x u
  by_cases he : π.EarlyOutcomeDifference ρ r s x u (1 - window)
  · rw [if_pos he, abs_le]
    constructor <;> linarith
  · rw [if_neg he, add_zero]
    by_cases hd : π.OutcomesDiffer ρ r s x u
    · have hm : 1 - window ≤ min (π.stoppingTime r Finset.univ x u) (ρ.stoppingTime s Finset.univ x u) := by
        by_contra hh
        exact he ⟨hd, lt_of_not_ge hh⟩
      have hp := hm.trans (min_le_left _ _)
      have hr := hm.trans (min_le_right _ _)
      rw [abs_le]
      constructor <;> linarith
    · have ht : π.stoppingTime r Finset.univ x u = ρ.stoppingTime s Finset.univ x u := by
        by_contra hh
        exact hd (Or.inr hh)
      rw [ht, sub_self, abs_zero]
      exact hw

/-- Maximum of all offers in a terminal time window; it is not conditioned on survival. -/
noncomputable def lateMaximum (x u : Fin n → ℝ) (cut : ℝ) : ℝ :=
  Instance.maximum (fun i => if cut ≤ u i then x i else 0)

lemma lateMaximum_nonnegative (x u : Fin n → ℝ) (cut : ℝ) : 0 ≤ lateMaximum x u cut :=
  Instance.maximum_nonnegative _

lemma lateMaximum_le (x u : Fin n → ℝ) (cut : ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hx : ∀ i, x i ≤ H) : lateMaximum x u cut ≤ H := by
  apply Instance.maximum_le _ hH
  intro i
  split_ifs
  · exact hx i
  · exact hH

lemma Policy.reward_le_lateMaximum_of_time_ge (π : Policy Seed n) (r : Seed)
    (x u : Fin n → ℝ) {cut : ℝ} (ht : cut ≤ π.stoppingTime r Finset.univ x u) :
    π.reward r Finset.univ x u ≤ lateMaximum x u cut := by
  by_cases h : ∃ i, π.ActualSelects r Finset.univ x u i
  · obtain ⟨i, hi⟩ := h
    rw [π.reward_eq_of_actualSelects _ _ _ _ hi]
    have hui : cut ≤ u i := ht.trans_eq hi.1.2.symm
    have hmax := Instance.le_maximum (fun j => if cut ≤ u j then x j else 0) i
    change x i ≤ Instance.maximum (fun j => if cut ≤ u j then x j else 0)
    simpa only [if_pos hui] using hmax
  · rw [π.reward_eq_zero_of_no_actualSelection _ _ _ _ (fun i hi => h ⟨i, hi⟩)]
    exact lateMaximum_nonnegative _ _ _

/-- A late disagreement has both rewards bounded by the unconditional terminal maximum. -/
lemma Policy.reward_difference_le_window (π : Policy Seed n) (ρ : Policy OtherSeed n)
    (r : Seed) (s : OtherSeed) (x u : Fin n → ℝ) {H cut : ℝ} (hH : 0 ≤ H)
    (hx0 : ∀ i, 0 ≤ x i) (hxH : ∀ i, x i ≤ H) :
    |π.reward r Finset.univ x u - ρ.reward s Finset.univ x u| ≤
      H * (if π.EarlyOutcomeDifference ρ r s x u cut then 1 else 0) + lateMaximum x u cut := by
  have hπ0 := π.reward_nonnegative r Finset.univ x u hx0
  have hρ0 := ρ.reward_nonnegative s Finset.univ x u hx0
  have hπH := (π.reward_le_maximum r Finset.univ x u).trans (Instance.maximum_le x hH hxH)
  have hρH := (ρ.reward_le_maximum s Finset.univ x u).trans (Instance.maximum_le x hH hxH)
  by_cases he : π.EarlyOutcomeDifference ρ r s x u cut
  · rw [if_pos he, mul_one]
    have hd : |π.reward r Finset.univ x u - ρ.reward s Finset.univ x u| ≤ H := by
      rw [abs_le]
      constructor <;> linarith
    exact hd.trans (le_add_of_nonneg_right (lateMaximum_nonnegative _ _ _))
  · rw [if_neg he, mul_zero, zero_add]
    by_cases hdiff : π.OutcomesDiffer ρ r s x u
    · have hm : cut ≤ min (π.stoppingTime r Finset.univ x u) (ρ.stoppingTime s Finset.univ x u) := by
        by_contra hh
        exact he ⟨hdiff, lt_of_not_ge hh⟩
      have hp := π.reward_le_lateMaximum_of_time_ge r x u (hm.trans (min_le_left _ _))
      have hr := ρ.reward_le_lateMaximum_of_time_ge s x u (hm.trans (min_le_right _ _))
      rw [abs_le]
      constructor <;> linarith
    · have hr : π.reward r Finset.univ x u = ρ.reward s Finset.univ x u := by
        by_contra hh
        exact hdiff (Or.inl hh)
      rw [hr, sub_self, abs_zero]
      exact lateMaximum_nonnegative _ _ _

lemma lateMaximum_le_cutoff_add_tail_count (x u : Fin n → ℝ) {H d cut : ℝ}
    (hH : 0 ≤ H) (hd : 0 ≤ d) (hx : ∀ i, x i ≤ H) :
    lateMaximum x u cut ≤ d + H * ∑ i, (if cut ≤ u i ∧ d < x i then (1 : ℝ) else 0) := by
  have hC : 0 ≤ ∑ i, (if cut ≤ u i ∧ d < x i then (1 : ℝ) else 0) :=
    Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num
  have hr : d ≤ d + H * ∑ i, (if cut ≤ u i ∧ d < x i then (1 : ℝ) else 0) :=
    le_add_of_nonneg_right (mul_nonneg hH hC)
  apply Instance.maximum_le _ (hd.trans hr)
  intro i
  by_cases hui : cut ≤ u i
  · rw [if_pos hui]
    by_cases hxi : x i ≤ d
    · exact hxi.trans hr
    · have hOne : (1 : ℝ) ≤ ∑ j, (if cut ≤ u j ∧ d < x j then (1 : ℝ) else 0) := by
        have hh := Finset.single_le_sum
          (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) =>
            show 0 ≤ (if cut ≤ u j ∧ d < x j then (1 : ℝ) else 0) from by split_ifs <;> norm_num)
          (Finset.mem_univ i)
        simpa only [hui, lt_of_not_ge hxi, and_self, if_true] using hh
      nlinarith [mul_le_mul_of_nonneg_left hOne hH, hx i]
  · rw [if_neg hui]
    exact hd.trans hr

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed] [MeasurableSpace OtherSeed]

lemma Policy.measurableSet_earlyOutcomeDifference (π : Policy Seed n) (hπ : π.IsMeasurable)
    (ρ : Policy OtherSeed n) (hρ : ρ.IsMeasurable)
    {r : Ω → Seed} {s : Ω → OtherSeed} {x u : Ω → Fin n → ℝ} {cut : Ω → ℝ}
    (hr : Measurable r) (hs : Measurable s)
    (hx : ∀ i, Measurable fun ω => x ω i) (hu : ∀ i, Measurable fun ω => u ω i)
    (hcut : Measurable cut) :
    MeasurableSet {ω | π.EarlyOutcomeDifference ρ (r ω) (s ω) (x ω) (u ω) (cut ω)} := by
  have hπR := π.measurable_reward hπ hr hx hu Finset.univ
  have hρR := ρ.measurable_reward hρ hs hx hu Finset.univ
  have hπT := π.measurable_stoppingTime hπ hr hx hu Finset.univ
  have hρT := ρ.measurable_stoppingTime hρ hs hx hu Finset.univ
  exact ((measurableSet_eq_fun hπR hρR).compl.union (measurableSet_eq_fun hπT hρT).compl).inter
    (measurableSet_lt (hπT.min hρT) hcut)

lemma measurable_lateMaximum {x u : Ω → Fin n → ℝ} {cut : Ω → ℝ}
    (hx : ∀ i, Measurable fun ω => x ω i) (hu : ∀ i, Measurable fun ω => u ω i)
    (hcut : Measurable cut) : Measurable fun ω => lateMaximum (x ω) (u ω) (cut ω) := by
  exact Instance.measurable_maximum.comp (measurable_pi_lambda _ fun i =>
    Measurable.ite (measurableSet_le hcut (hu i)) (hx i) measurable_const)

end Measurability
end ProphetSecretary.Model

