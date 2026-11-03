import ProphetSecretary.Statistics.PlannerRoundedEvents

/-!
# The rounded planner's discrete coupling

The coupling records the intermediate subset together with the final identity
and child set. This stronger record controls the time fraction on its
complementary good event, as required for the operator comparison.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability

lemma plannerRecordedSubset_eq_of_no_rounding_events {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (N : ℕ) (hN : 0 < N) (seed : PlannerUniformSeed n)
    (h0 : seed ∉ plannerChoiceRoundingEvent A p hA N hN)
    (h1 : seed ∉ plannerCoinRoundingEvent p N hN) :
    plannerRecordedSubset A p seed.1 = plannerRecordedSubset A p (plannerRoundSeed N hN seed).1 := by
  have hk : plannerFirstSuccessChoice A p hA seed.1.1 =
      plannerFirstSuccessChoice A p hA (uniformGridRound N hN seed.1.1) := by
    simpa only [plannerChoiceRoundingEvent, Set.mem_setOf_eq, not_ne_iff] using h0
  have hcoins (i : Fin n) : (seed.1.2 i ≤ plannerBernoulliProbability (p i)) ↔
      (uniformGridRound N hN (seed.1.2 i) ≤ plannerBernoulliProbability (p i)) := by
    apply decide_eq_decide.mp
    by_contra h
    exact h1 ⟨i, h⟩
  simp only [plannerRecordedSubset, dif_pos hA, plannerRoundSeed, plannerRoundFirstSeed,
    plannerFirstSuccessUniform, hk]
  unfold plannerFirstSuccessSet
  congr 1
  ext i
  simp only [bernoulliSubset, Finset.mem_filter, plannerRoundVector]
  exact and_congr Iff.rfl (hcoins i)

lemma plannerDiscreteOutput_eq_of_no_rounding_events {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (N : ℕ) (hN : 0 < N) (seed : PlannerUniformSeed n)
    (h0 : seed ∉ plannerChoiceRoundingEvent A p hA N hN)
    (h1 : seed ∉ plannerCoinRoundingEvent p N hN)
    (h2 : seed ∉ plannerIdentityRoundingEvent A p N hN)
    (h3 : seed ∉ plannerTailRoundingEvent A p N hN) :
    plannerDiscreteOutput (plannerUniformTransition A p seed) =
      plannerDiscreteOutput (plannerRoundedTransition A p N hN seed) := by
  let D := plannerFirstSuccessUniform A p hA seed.1
  have hD : D.Nonempty := plannerFirstSuccessUniform_nonempty A p hA seed.1
  have hDEq := plannerRecordedSubset_eq_of_no_rounding_events A p hA N hN seed h0 h1
  have hDR : plannerFirstSuccessUniform A p hA (plannerRoundSeed N hN seed).1 = D := by
    simpa only [plannerRecordedSubset, dif_pos hA] using hDEq.symm
  have hIdNo : ¬plannerTotalIdentity D seed.2.1 ≠
      plannerTotalIdentity D (uniformGridRound N hN seed.2.1) := by
    simpa only [plannerIdentityRoundingEvent, Set.mem_setOf_eq, plannerRecordedSubset, dif_pos hA] using h2
  have hId := not_ne_iff.mp hIdNo
  simp only [plannerTotalIdentity, dif_pos hD, Option.some.injEq] at hId
  have hD' : (plannerFirstSuccessUniform A p hA seed.1).Nonempty := hD
  have hTailNo : ¬∃ i : Fin n,
      decide (seed.2.2.2 i ≤ plannerUnitFraction D hD seed.2.2.1) ≠
        decide (uniformGridRound N hN (seed.2.2.2 i) ≤
          plannerUnitFraction D hD (plannerRoundVector N hN seed.2.2.1)) := by
    simpa only [plannerTailRoundingEvent, Set.mem_setOf_eq, plannerRecordedSubset, dif_pos hA,
      plannerTotalFraction, dif_pos hD'] using h3
  have hB : bernoulliSubset (A \ D) (fun _ => plannerUnitFraction D hD seed.2.2.1) seed.2.2.2 =
      bernoulliSubset (A \ D) (fun _ => plannerUnitFraction D hD (plannerRoundVector N hN seed.2.2.1))
        (plannerRoundVector N hN seed.2.2.2) := by
    ext i
    have hc : decide (seed.2.2.2 i ≤ plannerUnitFraction D hD seed.2.2.1) =
        decide (uniformGridRound N hN (seed.2.2.2 i) ≤
          plannerUnitFraction D hD (plannerRoundVector N hN seed.2.2.1)) := by
      by_contra hc
      exact hTailNo ⟨i, hc⟩
    simp only [bernoulliSubset, Finset.mem_filter, plannerRoundVector]
    exact and_congr Iff.rfl (decide_eq_decide.mp hc)
  unfold plannerRoundedTransition
  simp only [plannerUniformTransition, dif_pos hA]
  rw [hDR]
  change plannerDiscreteOutput (plannerUniformAfterSubset A D seed.2) = _
  simp only [plannerUniformAfterSubset, dif_pos hD, plannerUniformIdentityTransition,
    plannerMaskedTransition, plannerSomeTransition, plannerDiscreteOutput, plannerTailSet,
    plannerRoundSeed]
  rw [hId, hB]

noncomputable def plannerAugmentedDiscreteOutput {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (seed : PlannerUniformSeed n) : Finset (Fin n) × (Option (Fin n) × Finset (Fin n)) :=
  (plannerRecordedSubset A p seed.1, plannerDiscreteOutput (plannerUniformTransition A p seed))

lemma plannerAugmentedDiscreteOutput_measurable {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ) :
    Measurable (plannerAugmentedDiscreteOutput A p) := by
  have hd : Measurable (fun o : PlannerUniformOutput n => plannerDiscreteOutput o) :=
    measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  exact ((measurable_plannerRecordedSubset A p).comp measurable_fst).prodMk
    (hd.comp (measurable_plannerUniformTransition A p))

lemma plannerTotalFraction_mem_unit {n : ℕ} (D : Finset (Fin n)) (u : Fin n → ℝ) :
    plannerTotalFraction D u ∈ Icc (0 : ℝ) 1 := by
  unfold plannerTotalFraction
  split_ifs with hD
  · exact plannerUnitFraction_mem_unit D hD u
  · exact ⟨le_rfl, zero_le_one⟩

lemma plannerUniformTransition_fraction_eq_total {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (seed : PlannerUniformSeed n) :
    (plannerUniformTransition A p seed).2.1 =
      plannerTotalFraction (plannerRecordedSubset A p seed.1) seed.2.2.1 := by
  by_cases hA : A.Nonempty
  · have hD := plannerFirstSuccessUniform_nonempty A p hA seed.1
    simp only [plannerUniformTransition, dif_pos hA, plannerRecordedSubset,
      plannerUniformAfterSubset, dif_pos hD, plannerSomeTransition, plannerUniformIdentityTransition,
      plannerMaskedTransition, plannerTotalFraction]
  · simp [plannerUniformTransition, plannerRecordedSubset, hA, plannerTotalFraction]

lemma plannerUniformTransition_fraction_mem_unit {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (seed : PlannerUniformSeed n) : (plannerUniformTransition A p seed).2.1 ∈ Icc (0 : ℝ) 1 := by
  rw [plannerUniformTransition_fraction_eq_total]
  exact plannerTotalFraction_mem_unit _ _

lemma plannerUniformTransition_has_identity_of_nonempty {n : ℕ} (A : Finset (Fin n))
    (p : Fin n → ℝ) (hA : A.Nonempty) (seed : PlannerUniformSeed n) :
    ∃ i : Fin n, (plannerUniformTransition A p seed).1 = some i := by
  let D := plannerFirstSuccessUniform A p hA seed.1
  have hD : D.Nonempty := plannerFirstSuccessUniform_nonempty A p hA seed.1
  refine ⟨plannerUniformIdentity D hD seed.2.1, ?_⟩
  rw [plannerUniformTransition, dif_pos hA]
  change (plannerUniformAfterSubset A D seed.2).1 = _
  rw [plannerUniformAfterSubset, dif_pos hD]
  rfl

lemma plannerRoundedTransition_child_card_lt {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (N : ℕ) (hN : 0 < N) (seed : PlannerUniformSeed n) :
    (plannerRoundedTransition A p N hN seed).2.2.card < A.card := by
  obtain ⟨i, hi⟩ := plannerUniformTransition_has_identity_of_nonempty A p hA (plannerRoundSeed N hN seed)
  exact plannerUniformTransition_child_card_lt A p (plannerRoundSeed N hN seed) hi

/-- Matching intermediate subsets imply the same maximum reservoir is used.
Its unit support follows from the actual product marginal, independently of
how the first subset was selected. -/
theorem plannerRoundedTransition_fraction_error_on_matching_subset {n : ℕ}
    (A : Finset (Fin n)) (p : Fin n → ℝ) (N : ℕ) (hN : 0 < N) :
    ∀ᵐ seed ∂plannerUniformSeedLaw n,
      plannerRecordedSubset A p seed.1 = plannerRecordedSubset A p (plannerRoundSeed N hN seed).1 →
      |(plannerUniformTransition A p seed).2.1 - (plannerRoundedTransition A p N hN seed).2.1| ≤
        1 / (N : ℝ) := by
  have hp : MeasurePreserving (fun seed : PlannerUniformSeed n => seed.2.2.1)
      (plannerUniformSeedLaw n) (Instance.clocksLaw n) :=
    (measurePreserving_fst.comp measurePreserving_snd).comp measurePreserving_snd
  filter_upwards [hp.quasiMeasurePreserving.ae (Instance.clocks_mem_unitInterval (n := n))] with seed hu
  intro hD
  rw [plannerRoundedTransition, plannerUniformTransition_fraction_eq_total,
    plannerUniformTransition_fraction_eq_total]
  change |plannerTotalFraction (plannerRecordedSubset A p seed.1) seed.2.2.1 -
    plannerTotalFraction (plannerRecordedSubset A p (plannerRoundFirstSeed N hN seed.1))
      (plannerRoundVector N hN seed.2.2.1)| ≤ _
  change plannerRecordedSubset A p seed.1 =
    plannerRecordedSubset A p (plannerRoundFirstSeed N hN seed.1) at hD
  rw [← hD]
  exact plannerTotalFraction_round_error _ N hN seed.2.2.1 hu

/-- Intermediate subset, identity and child-set mismatch have one uniform
bound. This bound does not require positive probabilities in inactive rows. -/
theorem plannerAugmentedDiscreteOutput_rounded_probability {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (N : ℕ) (hN : 0 < N) :
    (plannerUniformSeedLaw n).real {seed | plannerAugmentedDiscreteOutput A p seed ≠
      plannerAugmentedDiscreteOutput A p (plannerRoundSeed N hN seed)} ≤ 10 * (n : ℝ) / N := by
  by_cases hA : A.Nonempty
  · let E0 := plannerChoiceRoundingEvent A p hA N hN
    let E1 := plannerCoinRoundingEvent p N hN
    let E2 := plannerIdentityRoundingEvent A p N hN
    let E3 := plannerTailRoundingEvent A p N hN
    have hsub : {seed | plannerAugmentedDiscreteOutput A p seed ≠
        plannerAugmentedDiscreteOutput A p (plannerRoundSeed N hN seed)} ⊆ E0 ∪ (E1 ∪ (E2 ∪ E3)) := by
      intro seed hbad
      by_cases h0 : seed ∈ E0
      · exact Or.inl h0
      · by_cases h1 : seed ∈ E1
        · exact Or.inr (Or.inl h1)
        · by_cases h2 : seed ∈ E2
          · exact Or.inr (Or.inr (Or.inl h2))
          · by_cases h3 : seed ∈ E3
            · exact Or.inr (Or.inr (Or.inr h3))
            · exact False.elim (hbad (Prod.ext
                (plannerRecordedSubset_eq_of_no_rounding_events A p hA N hN seed h0 h1)
                (plannerDiscreteOutput_eq_of_no_rounding_events A p hA N hN seed h0 h1 h2 h3)))
    have h0 := plannerChoiceRoundingEvent_probability A p hA N hN
    have h1 := plannerCoinRoundingEvent_probability p N hN
    have h2 := plannerIdentityRoundingEvent_probability A p N hN
    have h3 := plannerTailRoundingEvent_probability A p N hN
    have h23 : (plannerUniformSeedLaw n).real (E2 ∪ E3) ≤
        (plannerUniformSeedLaw n).real E2 + (plannerUniformSeedLaw n).real E3 := measureReal_union_le _ _
    have h123 : (plannerUniformSeedLaw n).real (E1 ∪ (E2 ∪ E3)) ≤
        (plannerUniformSeedLaw n).real E1 +
          ((plannerUniformSeedLaw n).real E2 + (plannerUniformSeedLaw n).real E3) :=
      (measureReal_union_le _ _).trans (add_le_add le_rfl h23)
    calc
      _ ≤ (plannerUniformSeedLaw n).real (E0 ∪ (E1 ∪ (E2 ∪ E3))) := measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ (plannerUniformSeedLaw n).real E0 + ((plannerUniformSeedLaw n).real E1 +
          ((plannerUniformSeedLaw n).real E2 + (plannerUniformSeedLaw n).real E3)) :=
        (measureReal_union_le _ _).trans (add_le_add le_rfl h123)
      _ ≤ (n : ℝ) / N + ((n : ℝ) / N + ((n : ℝ) / N + 4 * (n : ℝ) / N)) :=
        add_le_add h0 (add_le_add h1 (add_le_add h2 h3))
      _ ≤ _ := by
        simp only [div_eq_mul_inv]
        nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ n)
          (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹)]
  · have he : {seed | plannerAugmentedDiscreteOutput A p seed ≠
        plannerAugmentedDiscreteOutput A p (plannerRoundSeed N hN seed)} = ∅ := by
      ext seed
      simp [plannerAugmentedDiscreteOutput, plannerRecordedSubset, plannerUniformTransition, hA]
    rw [he, measureReal_empty]
    positivity

theorem plannerDiscreteOutput_rounded_probability {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (N : ℕ) (hN : 0 < N) :
    (plannerUniformSeedLaw n).real {seed | plannerDiscreteOutput (plannerUniformTransition A p seed) ≠
      plannerDiscreteOutput (plannerRoundedTransition A p N hN seed)} ≤ 10 * (n : ℝ) / N := by
  have hsub : {seed | plannerDiscreteOutput (plannerUniformTransition A p seed) ≠
      plannerDiscreteOutput (plannerRoundedTransition A p N hN seed)} ⊆
      {seed | plannerAugmentedDiscreteOutput A p seed ≠
        plannerAugmentedDiscreteOutput A p (plannerRoundSeed N hN seed)} := by
    intro seed hbad hEq
    exact hbad (congrArg Prod.snd hEq)
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (plannerAugmentedDiscreteOutput_rounded_probability A p N hN)

end ProphetSecretary.Statistics
