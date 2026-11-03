import ProphetSecretary.Analysis.FiniteRankValue
import ProphetSecretary.Statistics.PlannerRoundedOperator

/-!
# The fixed point of the rounded scalar recursion

Every nonterminal transition removes at least one active identity, including
on boundary seeds. Thus the rounded recursion stabilizes after at most the
number of identities plus one expected updates.
-/

open MeasureTheory Set

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis

variable {n : ℕ} {k : Fin n → ℕ}

lemma scalarPlannerRoundedRecursion_child_rank_lt (y : (i : Fin n) → Fin (k i) → ℝ)
    (N : ℕ) (hN : 0 < N) (x : ScalarPlannerState n)
    (hx : (scalarPlannerRoundedRecursion y N hN).isEmpty x = false) (s : PlannerUniformSeed n) :
    let D := scalarPlannerRoundedRecursion y N hN
    (plannerActive y (D.child x (D.sample x s)).1).card < (plannerActive y x.1).card := by
  let A := plannerActive y x.1
  let p := plannerPositiveProbability y
  have hA : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr (of_decide_eq_false hx)
  let o := plannerRoundedTransition A p N hN s
  change (plannerActive y o.2.2).card < A.card
  exact lt_of_le_of_lt (Finset.card_le_card (plannerActive_subset y o.2.2))
    (plannerRoundedTransition_child_card_lt A p hA N hN s)

lemma scalarPlannerRecursion_empty_bounds (y : (i : Fin n) → Fin (k i) → ℝ)
    (x : ScalarPlannerState n) :
    0 ≤ (scalarPlannerRecursion y).emptyValue x ∧ (scalarPlannerRecursion y).emptyValue x ≤ 4 := by
  have hu : scalarPlannerTime x ∈ Icc (0 : ℝ) 1 := plannerUnit_mem _
  have hz := scalarPlannerDurationWeight_mem x
  exact ⟨mul_nonneg hz.1 hu.1, (mul_le_of_le_one_right hz.1 hu.2).trans hz.2⟩

lemma scalarPlannerRecursion_offset_bounds (y : (i : Fin n) → Fin (k i) → ℝ)
    (x : ScalarPlannerState n) :
    0 ≤ (scalarPlannerRecursion y).offset x ∧ (scalarPlannerRecursion y).offset x ≤ 4 := by
  have hb := scalarPlannerRecursion_empty_bounds y x
  have hβ := scalarPlannerWeight_pos y x.1
  change 0 ≤ (scalarPlannerRecursion y).emptyValue x / scalarPlannerWeight y x.1 ∧
    (scalarPlannerRecursion y).emptyValue x / scalarPlannerWeight y x.1 ≤ 4
  exact ⟨div_nonneg hb.1 hβ.le, (div_le_self hb.1 (scalarPlannerWeight_ge_one y x.1)).trans hb.2⟩

/-- The true normalized value for the rounded transition law. -/
noncomputable def scalarPlannerNormalizedRoundedValue (y : (i : Fin n) → Fin (k i) → ℝ)
    (N : ℕ) (hN : 0 < N) : ScalarPlannerState n → ℝ :=
  finiteRankValue (scalarPlannerRoundedRecursion y N hN) (plannerUniformSeedLaw n) (n+1)

lemma measurable_scalarPlannerNormalizedRoundedValue (y : (i : Fin n) → Fin (k i) → ℝ)
    (N : ℕ) (hN : 0 < N) : Measurable (scalarPlannerNormalizedRoundedValue y N hN) :=
  measurable_finiteRankValue _ (scalarPlannerRoundedRecursion_measurable y N hN) _ _

lemma scalarPlannerNormalizedRoundedValue_bounds (y : (i : Fin n) → Fin (k i) → ℝ)
    (hcap : ∀ i j, y i j ≤ 1) (N : ℕ) (hN : 0 < N) (x : ScalarPlannerState n) :
    0 ≤ scalarPlannerNormalizedRoundedValue y N hN x ∧ scalarPlannerNormalizedRoundedValue y N hN x ≤ 5 :=
  finiteRankValue_bounds _ (scalarPlannerRoundedRecursion_measurable y N hN) _
    (fun x _ => ⟨(scalarPlannerRecursion_empty_bounds y x).1,
      (scalarPlannerRecursion_empty_bounds y x).2.trans (by norm_num)⟩)
    (scalarPlannerRecursion_offset_bounds y) (scalarPlannerRecursion_coefficient_bounds y)
    (fun _ o _ hw _ => scalarPlannerPayoff_bounds y hcap o hw) _ x

lemma scalarPlannerNormalizedRoundedValue_fixed (y : (i : Fin n) → Fin (k i) → ℝ)
    (N : ℕ) (hN : 0 < N) (x : ScalarPlannerState n) :
    scalarPlannerNormalizedRoundedValue y N hN x = finiteRankStep
      (scalarPlannerRoundedRecursion y N hN) (plannerUniformSeedLaw n)
      (scalarPlannerNormalizedRoundedValue y N hN) x := by
  apply finiteRankValue_fixed _ _ (fun x => (plannerActive y x.1).card)
    (scalarPlannerRoundedRecursion_child_rank_lt y N hN)
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)

lemma scalarPlannerNormalizedRoundedValue_empty (y : (i : Fin n) → Fin (k i) → ℝ)
    (N : ℕ) (hN : 0 < N) (x : ScalarPlannerState n)
    (hx : (scalarPlannerRoundedRecursion y N hN).isEmpty x = true) :
    (scalarPlannerRoundedRecursion y N hN).emptyValue x = scalarPlannerNormalizedRoundedValue y N hN x := by
  rw [scalarPlannerNormalizedRoundedValue_fixed y N hN x, finiteRankStep, if_pos hx]

variable [∀ i, NeZero (k i)]

/-- Second inequality in `bits:operator-error`, uniform over empirical states. -/
theorem scalarPlannerNormalizedRoundedValue_error (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (hcap : ∀ i j, y i j ≤ 1) (N : ℕ) (hN : 0 < N)
    (x : ScalarPlannerState n) :
    |scalarPlannerNormalizedValue y hy x - scalarPlannerNormalizedRoundedValue y N hN x| ≤
      (10*(n:ℝ)+4)/(3*(N:ℝ)) := by
  let D := scalarPlannerRoundedRecursion y N hN
  let E := (10*(n:ℝ)+4)/(4*(N:ℝ))
  have hres (x' : ScalarPlannerState n) : |scalarPlannerNormalizedValue y hy x' -
      finiteRankStep D (plannerUniformSeedLaw n) (scalarPlannerNormalizedValue y hy) x'| ≤ E := by
    cases h : D.isEmpty x'
    · simpa only [finiteRankStep, h, Bool.false_eq_true, if_false] using
        scalarPlannerNormalizedValue_rounded_residual y hy hcap x' h N hN
    · rw [finiteRankStep, if_pos h]
      have he : D.emptyValue x' = scalarPlannerNormalizedValue y hy x' :=
        scalarPlannerNormalizedValue_empty y hy x' h
      rw [he, sub_self, abs_zero]
      dsimp [E]
      positivity
  have h := finiteRank_distance_le D (scalarPlannerRoundedRecursion_measurable y N hN)
    (plannerUniformSeedLaw n) (fun x' => (plannerActive y x'.1).card)
    (scalarPlannerRoundedRecursion_child_rank_lt y N hN) (scalarPlannerRecursion_coefficient_bounds y)
    (fun _ o _ hw _ => scalarPlannerPayoff_bounds y hcap o hw) (fun _ o => scalarPlannerPayoff_lipschitz y o)
    (scalarPlannerNormalizedValue y hy) (scalarPlannerNormalizedRoundedValue y N hN)
    (measurable_scalarPlannerNormalizedValue y hy) (measurable_scalarPlannerNormalizedRoundedValue y N hN)
    (scalarPlannerNormalizedValue_bounds y hy hcap) (scalarPlannerNormalizedRoundedValue_bounds y hcap N hN)
    (scalarPlannerNormalizedRoundedValue_fixed y N hN) E (by dsimp [E]; positivity) hres x
  exact h.trans_eq (by dsimp [E]; ring)

end ProphetSecretary.Statistics
