import ProphetSecretary.Statistics.PlannerRoundedComparisons

/-!
# Coupling the ideal and rounded planner executions

All uniforms belong to the fixed product seed already used by the ideal
sampler. Rounding is componentwise. Intermediate subsets are retained in the
coupling so that agreement of the recorded discrete data also controls the
maximum-derived time fraction.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability

noncomputable def plannerRoundVector {n : ℕ} (N : ℕ) (hN : 0 < N) (u : Fin n → ℝ) : Fin n → ℝ :=
  fun i => uniformGridRound N hN (u i)

lemma measurable_plannerRoundVector (n N : ℕ) (hN : 0 < N) :
    Measurable (@plannerRoundVector n N hN) :=
  measurable_pi_iff.mpr (fun i => (measurable_uniformGridRound N hN).comp (measurable_pi_apply i))

noncomputable def plannerRoundFirstSeed {n : ℕ} (N : ℕ) (hN : 0 < N)
    (seed : ℝ × (Fin n → ℝ)) : ℝ × (Fin n → ℝ) :=
  (uniformGridRound N hN seed.1, plannerRoundVector N hN seed.2)

lemma measurable_plannerRoundFirstSeed (n N : ℕ) (hN : 0 < N) :
    Measurable (@plannerRoundFirstSeed n N hN) :=
  ((measurable_uniformGridRound N hN).comp measurable_fst).prodMk
    ((measurable_plannerRoundVector n N hN).comp measurable_snd)

noncomputable def plannerRoundSeed {n : ℕ} (N : ℕ) (hN : 0 < N)
    (seed : PlannerUniformSeed n) : PlannerUniformSeed n :=
  (plannerRoundFirstSeed N hN seed.1,
    (uniformGridRound N hN seed.2.1,
      (plannerRoundVector N hN seed.2.2.1, plannerRoundVector N hN seed.2.2.2)))

lemma measurable_plannerRoundSeed (n N : ℕ) (hN : 0 < N) :
    Measurable (@plannerRoundSeed n N hN) := by
  exact ((measurable_plannerRoundFirstSeed n N hN).comp measurable_fst).prodMk
    (((measurable_uniformGridRound N hN).comp (measurable_fst.comp measurable_snd)).prodMk
      (((measurable_plannerRoundVector n N hN).comp (measurable_fst.comp
        (measurable_snd.comp measurable_snd))).prodMk
        ((measurable_plannerRoundVector n N hN).comp (measurable_snd.comp
          (measurable_snd.comp measurable_snd)))))

/-- Empty subsets have no identity to select. -/
noncomputable def plannerTotalIdentity {n : ℕ} (D : Finset (Fin n)) (u : ℝ) : Option (Fin n) :=
  if hD : D.Nonempty then some (plannerUniformIdentity D hD u) else none

lemma measurable_plannerTotalIdentity {n : ℕ} (D : Finset (Fin n)) : Measurable (plannerTotalIdentity D) := by
  unfold plannerTotalIdentity
  split_ifs with hD
  · exact (measurable_of_countable (some : Fin n → Option (Fin n))).comp
      (measurable_plannerUniformIdentity D hD)
  · exact measurable_const

lemma measurable_plannerTotalIdentity_joint (n : ℕ) :
    Measurable (fun z : Finset (Fin n) × ℝ => plannerTotalIdentity z.1 z.2) :=
  measurable_from_prod_countable_right (fun D => measurable_plannerTotalIdentity D)

/-- Empty subsets have fraction zero; nonempty subsets use the clipped maximum. -/
noncomputable def plannerTotalFraction {n : ℕ} (D : Finset (Fin n)) (u : Fin n → ℝ) : ℝ :=
  if hD : D.Nonempty then plannerUnitFraction D hD u else 0

lemma measurable_plannerTotalFraction {n : ℕ} (D : Finset (Fin n)) : Measurable (plannerTotalFraction D) := by
  unfold plannerTotalFraction
  split_ifs with hD
  · exact measurable_plannerUnitFraction D hD
  · exact measurable_const

lemma measurable_plannerTotalFraction_joint (n : ℕ) :
    Measurable (fun z : Finset (Fin n) × (Fin n → ℝ) => plannerTotalFraction z.1 z.2) :=
  measurable_from_prod_countable_right (fun D => measurable_plannerTotalFraction D)

lemma plannerUnitFraction_eq_sup'_of_unit {n : ℕ} (D : Finset (Fin n)) (hD : D.Nonempty)
    (u : Fin n → ℝ) (hu : ∀ i ∈ D, u i ∈ Icc (0 : ℝ) 1) :
    plannerUnitFraction D hD u = D.sup' hD u := by
  let i := Classical.choose hD
  have hi : i ∈ D := Classical.choose_spec hD
  have h0 : 0 ≤ D.sup' hD u := (hu i hi).1.trans (Finset.le_sup' u hi)
  have h1 : D.sup' hD u ≤ 1 := Finset.sup'_le hD u (fun j hj => (hu j hj).2)
  unfold plannerUnitFraction uniformSubsetMaximum
  rw [min_eq_left h1, max_eq_right h0]

lemma plannerTotalFraction_round_error {n : ℕ} (D : Finset (Fin n)) (N : ℕ) (hN : 0 < N)
    (u : Fin n → ℝ) (hu : ∀ i, u i ∈ Icc (0 : ℝ) 1) :
    |plannerTotalFraction D u - plannerTotalFraction D (plannerRoundVector N hN u)| ≤ 1 / (N : ℝ) := by
  by_cases hD : D.Nonempty
  · have hur : ∀ i ∈ D, plannerRoundVector N hN u i ∈ Icc (0 : ℝ) 1 := by
      intro i _
      have hb := uniformGridRound_bounds N hN (hu i)
      exact ⟨hb.1, hb.2.1.trans (hu i).2⟩
    simp only [plannerTotalFraction, dif_pos hD]
    rw [plannerUnitFraction_eq_sup'_of_unit D hD u (fun i _ => hu i),
      plannerUnitFraction_eq_sup'_of_unit D hD _ hur]
    have hb := uniformGridRound_sup'_bounds N hN D hD u (fun i _ => hu i)
    change |D.sup' hD u - D.sup' hD (fun i => uniformGridRound N hN (u i))| ≤ _
    rw [abs_of_nonneg (sub_nonneg.mpr hb.1)]
    exact hb.2
  · simp only [plannerTotalFraction, dif_neg hD, sub_self, abs_zero]
    positivity

lemma plannerTotalIdentity_rounded_probability {n : ℕ} (D : Finset (Fin n)) (N : ℕ) (hN : 0 < N) :
    Instance.uniformClock.real {u | plannerTotalIdentity D u ≠
      plannerTotalIdentity D (uniformGridRound N hN u)} ≤ (n : ℝ) / N := by
  by_cases hD : D.Nonempty
  · simp only [plannerTotalIdentity, dif_pos hD, Option.some.injEq, ne_eq, plannerUniformIdentity]
    have hb := categoricalUniformSample_rounded_probability D hD (fun _ => 1 / (D.card : ℝ)) N hN
    have hcN : D.card ≤ n := by simpa only [Fintype.card_fin] using D.card_le_univ
    have hc : (D.card : ℝ) ≤ n := by exact_mod_cast hcN
    exact hb.trans (div_le_div_of_nonneg_right hc (Nat.cast_nonneg N))
  · simp only [plannerTotalIdentity, dif_neg hD, ne_eq, not_true_eq_false,
      Set.setOf_false, measureReal_empty]
    positivity

noncomputable def plannerRecordedSubset {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (seed : ℝ × (Fin n → ℝ)) : Finset (Fin n) :=
  if hA : A.Nonempty then plannerFirstSuccessUniform A p hA seed else ∅

lemma measurable_plannerRecordedSubset {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ) :
    Measurable (plannerRecordedSubset A p) := by
  unfold plannerRecordedSubset
  split_ifs with hA
  · exact measurable_plannerFirstSuccessUniform A p hA
  · exact measurable_const

def plannerDiscreteOutput {n : ℕ} (o : PlannerUniformOutput n) : Option (Fin n) × Finset (Fin n) :=
  (o.1, o.2.2)

noncomputable def plannerRoundedTransition {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (N : ℕ) (hN : 0 < N) (seed : PlannerUniformSeed n) : PlannerUniformOutput n :=
  plannerUniformTransition A p (plannerRoundSeed N hN seed)

lemma measurable_plannerRoundedTransition {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (N : ℕ) (hN : 0 < N) : Measurable (plannerRoundedTransition A p N hN) :=
  (measurable_plannerUniformTransition A p).comp (measurable_plannerRoundSeed n N hN)

end ProphetSecretary.Statistics
