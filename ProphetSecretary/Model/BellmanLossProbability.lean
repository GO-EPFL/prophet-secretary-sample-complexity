import ProphetSecretary.Model.BellmanPerformance

/-!
# Probabilities controlled by Bellman regret

A reached action with loss at least `e>0` forces the nonnegative full loss sum
to be at least `e`. Markov's inequality and the exact performance-difference
identity therefore give probability at most `regret/e`, with constant one.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

def Policy.reachedLossEvent (π : Policy Seed n) (P : Instance n) (w c e : ℝ) : Set (World n Seed) :=
  {ω | ∃ i, π.Reaches ω.2.2 ω.1 ω.2.1 i ∧ e ≤ π.arrivalBellmanLoss P w c ω.2.2 ω.1 ω.2.1 i}

lemma Policy.reachedLossEvent_subset_level (π : Policy Seed n) (P : Instance n) (w c e : ℝ) :
    π.reachedLossEvent P w c e ⊆ {ω : World n Seed | e ≤ π.reachedBellmanLoss P w c ω.2.2 ω.1 ω.2.1} := by
  rintro ω ⟨i, hi, he⟩
  have hs : (if π.Reaches ω.2.2 ω.1 ω.2.1 i then
      π.arrivalBellmanLoss P w c ω.2.2 ω.1 ω.2.1 i else 0) ≤
      π.reachedBellmanLoss P w c ω.2.2 ω.1 ω.2.1 := by
    unfold Policy.reachedBellmanLoss
    apply Finset.single_le_sum (s := Finset.univ) (a := i)
      (f := fun j : Fin n ↦ if π.Reaches ω.2.2 ω.1 ω.2.1 j then
        π.arrivalBellmanLoss P w c ω.2.2 ω.1 ω.2.1 j else 0)
    · intro j _hj
      split_ifs
      · exact π.arrivalBellmanLoss_nonnegative P w c _ _ _ j
      · exact le_rfl
    · exact Finset.mem_univ i
  rw [if_pos hi] at hs
  exact he.trans hs

lemma Policy.measurableSet_reachedLossEvent [MeasurableSpace Seed]
    (π : Policy Seed n) (hπ : π.IsMeasurable) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (e : ℝ) :
    MeasurableSet (π.reachedLossEvent P w c e) := by
  unfold Policy.reachedLossEvent
  rw [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  exact (π.measurableSet_reaches hπ (measurable_snd.comp measurable_snd)
    (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
    (fun j ↦ (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i).inter
      (measurableSet_le measurable_const (π.measurable_arrivalBellmanLoss hπ P hP hw hc
        (measurable_snd.comp measurable_snd) (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
        (fun j ↦ (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i))

/-- Universal, dimension-independent probability bound for a large reached loss. -/
theorem RandomizedPolicy.reachedLoss_probability_le_regret (π : RandomizedPolicy n)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) {w c e : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (he : 0 < e) :
    (P.worldLaw π.seedLaw).real (π.rule.reachedLossEvent P w c e) ≤
      (optimalScalarValue P w c - π.scalarObjective P w c) / e := by
  have hn : 0 ≤ᵐ[P.worldLaw π.seedLaw]
      (fun ω : π.World ↦ π.rule.reachedBellmanLoss P w c ω.2.2 ω.1 ω.2.1) :=
    Filter.Eventually.of_forall (fun ω ↦ π.rule.reachedBellmanLoss_nonnegative P w c _ _ _)
  have hi := π.rule.integrable_reachedBellmanLoss π.measurable_rule P hP π.seedLaw hw hc
  have hm := mul_meas_ge_le_integral_of_nonneg hn hi e
  have hs := measureReal_mono (μ := P.worldLaw π.seedLaw)
    (π.rule.reachedLossEvent_subset_level P w c e)
  have h := (mul_le_mul_of_nonneg_left hs he.le).trans hm
  change e * (P.worldLaw π.seedLaw).real (π.rule.reachedLossEvent P w c e) ≤
    π.expectedReachedBellmanLoss P w c at h
  rw [← π.bellman_performanceDifference P hP hw hc] at h
  exact (le_div_iff₀ he).mpr (by simpa only [mul_comm] using h)

/-- Canonical value thresholds choose a maximizing Bellman action at every
observation, including ties and values sampled from a different evaluation law. -/
lemma Instance.valueThreshold_arrivalLoss_zero (P : Instance n) {w : ℝ} (hw : 0 < w)
    (c : ℝ) (x u : Fin n → ℝ) (i : Fin n) :
    (thresholdPolicy (fun (_ : Unit) A t j ↦ P.valueThreshold w c A t j)).arrivalBellmanLoss P w c () x u i = 0 := by
  let π : Policy Unit n := thresholdPolicy (fun (_ : Unit) A t j ↦ P.valueThreshold w c A t j)
  have ha : π.action () Finset.univ x u i = true ↔ P.continuationAtArrival w c x u i ≤ w * x i := by
    change Decidable.decide (P.continuationAtArrival w c x u i / w ≤ x i) = true ↔ _
    rw [decide_eq_true_eq, div_le_iff₀ hw, mul_comm (x i) w]
  change π.arrivalBellmanLoss P w c () x u i = 0
  unfold Policy.arrivalBellmanLoss
  by_cases h : P.continuationAtArrival w c x u i ≤ w * x i
  · rw [if_pos (ha.mpr h), max_eq_left h, sub_self]
  · rw [if_neg (fun ht ↦ h (ha.mp ht)), max_eq_right (le_of_not_ge h), sub_self]

/-- Disagreeing with the canonical Bellman action incurs precisely the absolute
acceptance/continuation gap, even if that gap is zero at a tie. -/
lemma Policy.disagreementLoss_eq_absGap (π : Policy Seed n) (P : Instance n)
    {w : ℝ} (hw : 0 < w) (c : ℝ) (r : Seed) (x u : Fin n → ℝ) (i : Fin n)
    (hdiff : π.action r Finset.univ x u i ≠
      (thresholdPolicy (fun (_ : Unit) A t j ↦ P.valueThreshold w c A t j)).action () Finset.univ x u i) :
    π.arrivalBellmanLoss P w c r x u i = |w * x i - P.continuationAtArrival w c x u i| := by
  let ρ : Policy Unit n := thresholdPolicy (fun (_ : Unit) A t j ↦ P.valueThreshold w c A t j)
  change π.action r Finset.univ x u i ≠ ρ.action () Finset.univ x u i at hdiff
  have hρ : ρ.action () Finset.univ x u i = true ↔ P.continuationAtArrival w c x u i ≤ w * x i := by
    change Decidable.decide (P.continuationAtArrival w c x u i / w ≤ x i) = true ↔ _
    rw [decide_eq_true_eq, div_le_iff₀ hw, mul_comm (x i) w]
  unfold Policy.arrivalBellmanLoss
  by_cases h : P.continuationAtArrival w c x u i ≤ w * x i
  · have hnot : ¬π.action r Finset.univ x u i = true := fun ha ↦ hdiff (ha.trans (hρ.mpr h).symm)
    rw [if_neg hnot, max_eq_left h, abs_of_nonneg (sub_nonneg.mpr h)]
  · have hf : ρ.action () Finset.univ x u i = false := by
      cases ha : ρ.action () Finset.univ x u i <;> simp_all
    have ht : π.action r Finset.univ x u i = true := by
      cases ha : π.action r Finset.univ x u i <;> simp_all
    rw [if_pos ht, max_eq_right (le_of_not_ge h), abs_of_neg (sub_neg.mpr (lt_of_not_ge h))]
    ring

/-- Probability of a reached disagreement away from an acceptance boundary.
A first-disagreement event is a subset of this event. -/
theorem RandomizedPolicy.reachedDisagreement_probability_le_regret (π : RandomizedPolicy n)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) {w c e : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (he : 0 < e) :
    (P.worldLaw π.seedLaw).real {ω : π.World | ∃ i,
      π.rule.Reaches ω.2.2 ω.1 ω.2.1 i ∧
      π.rule.action ω.2.2 Finset.univ ω.1 ω.2.1 i ≠
        (thresholdPolicy (fun (_ : Unit) A t j ↦ P.valueThreshold w c A t j)).action () Finset.univ ω.1 ω.2.1 i ∧
      e ≤ |w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i|} ≤
        (optimalScalarValue P w c - π.scalarObjective P w c) / e := by
  apply (measureReal_mono (μ := P.worldLaw π.seedLaw) ?_).trans (π.reachedLoss_probability_le_regret P hP hw hc he)
  rintro ω ⟨i, hr, hd, hgap⟩
  exact ⟨i, hr, by simpa only [π.rule.disagreementLoss_eq_absGap P hw c ω.2.2 ω.1 ω.2.1 i hd] using hgap⟩

end ProphetSecretary.Model
