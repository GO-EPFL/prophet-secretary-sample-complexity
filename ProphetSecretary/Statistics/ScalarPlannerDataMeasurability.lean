import ProphetSecretary.Statistics.ScalarPlannerAccuracy

/-!
# Joint measurability of empirical planner queries

The stored rows are part of the state throughout the recursion. The sampler
reads their finite positive counts. A public level gives the query a fixed
seed space, independent of the observed training data.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability

abbrev ScalarPlannerRows (n : ℕ) (k : Fin n → ℕ) := (i : Fin n) → Fin (k i) → ℝ

abbrev ScalarPlannerDataState (n : ℕ) (k : Fin n → ℕ) :=
  ScalarPlannerRows n k × ScalarPlannerState n

abbrev ScalarPlannerMedianInput (n : ℕ) (k : Fin n → ℕ) (r copies : ℕ) :=
  ScalarPlannerDataState n k × (Fin copies → MultilevelTree (PlannerUniformSeed n) r)

private abbrev PlannerPayoffInput (n : ℕ) (k : Fin n → ℕ) :=
  ScalarPlannerRows n k × (Finset (Fin n) × ℝ)

variable {n : ℕ} {k : Fin n → ℕ}

lemma measurable_positiveObservations (m : ℕ) :
    Measurable (positiveObservations (Value := ℝ) (m := m)) := by
  rw [measurable_finset_iff]
  intro j
  simp only [positiveObservations, Finset.mem_filter, Finset.mem_univ, true_and]
  exact measurableSet_setOf.mp (measurableSet_lt measurable_const (measurable_pi_apply j))

lemma measurable_positiveObservationCount (m : ℕ) :
    Measurable (fun row : Fin m → ℝ => (positiveObservations row).card) :=
  (measurable_of_countable (fun s : Finset (Fin m) => s.card)).comp (measurable_positiveObservations m)

lemma measurable_plannerPositiveProbability_data (i : Fin n) :
    Measurable (fun y : ScalarPlannerRows n k => plannerPositiveProbability y i) :=
  (((measurable_of_countable (fun a : ℕ => (a : ℝ))).comp
    (measurable_positiveObservationCount (k i))).comp (measurable_pi_apply i)).div_const (k i : ℝ)

noncomputable def scalarPlannerPositiveCounts (y : ScalarPlannerRows n k) : (i : Fin n) → Fin (k i + 1) :=
  fun i => ⟨(positiveObservations (y i)).card,
    Nat.lt_succ_of_le ((positiveObservations (y i)).card_le_univ.trans_eq (Fintype.card_fin _))⟩

lemma measurable_scalarPlannerPositiveCounts :
    Measurable (scalarPlannerPositiveCounts (n := n) (k := k)) := by
  apply measurable_pi_iff.mpr
  intro i
  apply measurable_to_countable'
  intro j
  have he : (fun y : ScalarPlannerRows n k => scalarPlannerPositiveCounts y i) ⁻¹' {j} =
      (fun y : ScalarPlannerRows n k => (positiveObservations (y i)).card) ⁻¹' {j.val} := by
    ext y
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Fin.ext_iff, scalarPlannerPositiveCounts]
  rw [he]
  exact ((measurable_positiveObservationCount (k i)).comp (measurable_pi_apply i))
    (measurableSet_singleton j.val)

noncomputable def scalarPlannerCountProbability (a : (i : Fin n) → Fin (k i + 1)) (i : Fin n) : ℝ :=
  (a i).val / (k i : ℝ)

lemma scalarPlannerCountProbability_counts (y : ScalarPlannerRows n k) :
    scalarPlannerCountProbability (scalarPlannerPositiveCounts y) = plannerPositiveProbability y := rfl

lemma measurable_plannerActive_data :
    Measurable (fun q : ScalarPlannerRows n k × Finset (Fin n) => plannerActive q.1 q.2) := by
  rw [measurable_finset_iff]
  intro i
  simp only [plannerActive, Finset.mem_filter]
  exact ((measurable_finset_mem i).comp measurable_snd).and
    (measurableSet_setOf.mp (measurableSet_lt measurable_const
      ((measurable_plannerPositiveProbability_data (k := k) i).comp measurable_fst)))

lemma measurable_scalarPlannerWeight_data :
    Measurable (fun q : ScalarPlannerRows n k × Finset (Fin n) => scalarPlannerWeight q.1 q.2) := by
  have h : Measurable (fun q : Finset (Fin n) × ((i : Fin n) → Fin (k i + 1)) =>
      plannerWeight q.1 (scalarPlannerCountProbability q.2)) := measurable_of_countable _
  simpa only [Function.comp_def, scalarPlannerCountProbability_counts, scalarPlannerWeight] using
    h.comp (measurable_plannerActive_data.prodMk (measurable_scalarPlannerPositiveCounts.comp measurable_fst))

lemma measurable_empiricalConditionalExcess_data (m : ℕ) :
    Measurable (fun q : (Fin m → ℝ) × ℝ => empiricalConditionalExcess q.1 q.2) := by
  have hnum : Measurable (fun q : (Fin m → ℝ) × ℝ =>
      ∑ j : Fin m, if 0 < q.1 j then max 0 (q.1 j - q.2) else 0) := by
    apply Finset.measurable_sum
    intro j _
    have hj : Measurable (fun q : (Fin m → ℝ) × ℝ => q.1 j) := (measurable_pi_apply j).comp measurable_fst
    exact Measurable.ite (measurableSet_lt measurable_const hj)
      (measurable_const.max (hj.sub measurable_snd)) measurable_const
  have hden : Measurable (fun q : (Fin m → ℝ) × ℝ => ((positiveObservations q.1).card : ℝ)) :=
    ((measurable_of_countable (fun a : ℕ => (a : ℝ))).comp (measurable_positiveObservationCount m)).comp
      measurable_fst
  have he : (fun q : (Fin m → ℝ) × ℝ => empiricalConditionalExcess q.1 q.2) =
      ((fun q => ∑ j : Fin m, if 0 < q.1 j then max 0 (q.1 j - q.2) else 0) /
        fun q => ((positiveObservations q.1).card : ℝ)) := by
    funext q
    simp only [Pi.div_apply, empiricalConditionalExcess, positiveObservations, Finset.sum_filter]
  rw [he]
  exact hnum.div hden

lemma measurable_scalarPlannerPayoff_data :
    Measurable (fun q : (ScalarPlannerRows n k × PlannerUniformOutput n) × ℝ =>
      scalarPlannerPayoff q.1.1 q.1.2 q.2) := by
  have h : Measurable (fun q : Option (Fin n) × (ScalarPlannerRows n k × (Finset (Fin n) × ℝ)) =>
      match q.1 with
      | none => 0
      | some i => empiricalConditionalExcess (q.2.1 i)
          (scalarPlannerWeight q.2.1 q.2.2.1 * q.2.2.2) / scalarPlannerWeight q.2.1 q.2.2.1) := by
    apply measurable_from_prod_countable_right
    intro i
    cases i with
    | none => exact measurable_const
    | some i =>
      have hproj : Measurable (fun q : PlannerPayoffInput n k => (q.1,q.2.1)) := by fun_prop
      have hb := (measurable_scalarPlannerWeight_data (n := n) (k := k)).comp hproj
      have hy : Measurable (fun q : PlannerPayoffInput n k => q.1 i) := by fun_prop
      have hw : Measurable (fun q : PlannerPayoffInput n k => q.2.2) := by fun_prop
      exact ((measurable_empiricalConditionalExcess_data (k i)).comp
        (hy.prodMk (hb.mul hw))).div hb
  have hp : Measurable (fun q : (ScalarPlannerRows n k × PlannerUniformOutput n) × ℝ =>
      (q.1.2.1, (q.1.1, (q.1.2.2.2,q.2)))) := by fun_prop
  exact h.comp hp

noncomputable def scalarPlannerRecursionWithData (n : ℕ) (k : Fin n → ℕ) :
    MultilevelRecursion (ScalarPlannerDataState n k) (PlannerUniformSeed n) (PlannerUniformOutput n) ℝ where
  isEmpty q := (scalarPlannerRecursion q.1).isEmpty q.2
  emptyValue q := (scalarPlannerRecursion q.1).emptyValue q.2
  offset q := (scalarPlannerRecursion q.1).offset q.2
  coefficient q := (scalarPlannerRecursion q.1).coefficient q.2
  sample q := (scalarPlannerRecursion q.1).sample q.2
  child q o := (q.1, (scalarPlannerRecursion q.1).child q.2 o)
  payoff q := (scalarPlannerRecursion q.1).payoff q.2

theorem scalarPlannerRecursionWithData_measurable (n : ℕ) (k : Fin n → ℕ) :
    (scalarPlannerRecursionWithData n k).IsMeasurable := by
  have hproj : Measurable (fun q : ScalarPlannerDataState n k => (q.1,q.2.1)) := by fun_prop
  have ha := (measurable_plannerActive_data (n := n) (k := k)).comp hproj
  have hcounts : Measurable (fun q : ScalarPlannerDataState n k => scalarPlannerPositiveCounts q.1) :=
    (measurable_scalarPlannerPositiveCounts (n := n) (k := k)).comp measurable_fst
  have hβ := (measurable_scalarPlannerWeight_data (n := n) (k := k)).comp hproj
  have hz := (measurable_scalarPlannerDurationWeight n).comp
    (measurable_snd : Measurable (Prod.snd : ScalarPlannerDataState n k → ScalarPlannerState n))
  have hu := (measurable_scalarPlannerTime n).comp
    (measurable_snd : Measurable (Prod.snd : ScalarPlannerDataState n k → ScalarPlannerState n))
  have hκ : Measurable (fun q : ScalarPlannerDataState n k =>
      plannerContraction (plannerActive q.1 q.2.1) (plannerPositiveProbability q.1)) := by
    have h : Measurable (fun z : Finset (Fin n) × ((i : Fin n) → Fin (k i+1)) =>
        plannerContraction z.1 (scalarPlannerCountProbability z.2)) := measurable_of_countable _
    simpa only [Function.comp_def, scalarPlannerCountProbability_counts] using h.comp (ha.prodMk hcounts)
  have hsam : Measurable (fun z : (Finset (Fin n) × ((i : Fin n) → Fin (k i+1))) × PlannerUniformSeed n =>
      plannerUniformTransition z.1.1 (scalarPlannerCountProbability z.1.2) z.2) := by
    apply measurable_from_prod_countable_right
    intro q
    exact measurable_plannerUniformTransition q.1 (scalarPlannerCountProbability q.2)
  have hchildSet : Measurable (fun q : ScalarPlannerDataState n k × PlannerUniformOutput n => q.2.2.2) := by
    fun_prop
  have hchildFraction : Measurable (fun q : ScalarPlannerDataState n k × PlannerUniformOutput n => q.2.2.1) := by
    fun_prop
  refine ⟨?_, hz.mul hu, (hz.mul hu).div hβ, hκ, ?_, ?_, ?_⟩
  · exact (measurable_of_countable (fun A : Finset (Fin n) => decide (A = ∅))).comp ha
  · simpa only [Function.comp_def, scalarPlannerCountProbability_counts, scalarPlannerRecursionWithData,
      scalarPlannerRecursion] using hsam.comp (((ha.prodMk hcounts).comp measurable_fst).prodMk measurable_snd)
  · have hrows : Measurable (fun q : ScalarPlannerDataState n k × PlannerUniformOutput n => q.1.1) := by
      fun_prop
    exact hrows.prodMk
      (hchildSet.prodMk (((hu.comp measurable_fst).mul
        (continuous_plannerUnit.measurable.comp hchildFraction)).prodMk (hz.comp measurable_fst)))
  · have hp : Measurable (fun q : (ScalarPlannerDataState n k × PlannerUniformOutput n) × ℝ =>
        ((q.1.1.1,q.1.2),q.2)) := by fun_prop
    exact (measurable_scalarPlannerPayoff_data (n := n) (k := k)).comp hp

lemma multilevelEstimate_withData (y : ScalarPlannerRows n k) (r : ℕ) (x : ScalarPlannerState n)
    (t : MultilevelTree (PlannerUniformSeed n) r) :
    multilevelEstimate (scalarPlannerRecursionWithData n k) r (y,x) t =
      multilevelEstimate (scalarPlannerRecursion y) r x t := by
  induction r using Nat.strong_induction_on generalizing x with
  | h r ih =>
    cases t with
    | zero => simp [multilevelEstimate_zero]
    | @node d base tr up lo =>
      have hU (l : Fin d) (x' : ScalarPlannerState n) (t' : MultilevelTree (PlannerUniformSeed n) (l.val+1)) :=
        ih (l.val+1) (by have := l.isLt; omega) x' t'
      have hL (l : Fin d) (x' : ScalarPlannerState n) (t' : MultilevelTree (PlannerUniformSeed n) l.val) :=
        ih l.val (by have := l.isLt; omega) x' t'
      simp only [scalarPlannerRecursionWithData] at hU hL
      simp only [multilevelEstimate, scalarPlannerRecursionWithData, hU, hL]

lemma measurable_scalarPlannerSingle_data_value (r : ℕ) :
    Measurable (fun q : ScalarPlannerDataState n k × MultilevelTree (PlannerUniformSeed n) r =>
      (scalarPlannerSingle q.1.1 q.1.2 r q.2).1) := by
  have hp : Measurable (fun q : ScalarPlannerDataState n k × MultilevelTree (PlannerUniformSeed n) r =>
      (q.1.1,q.1.2.1)) := by fun_prop
  have hb := (measurable_scalarPlannerWeight_data (n := n) (k := k)).comp hp
  have he : (fun q : ScalarPlannerDataState n k × MultilevelTree (PlannerUniformSeed n) r =>
      multilevelEstimate (scalarPlannerRecursionWithData n k) r q.1 q.2) =
      fun q => multilevelEstimate (scalarPlannerRecursion q.1.1) r q.1.2 q.2 := by
    funext q
    exact multilevelEstimate_withData q.1.1 r q.1.2 q.2
  have hm := measurable_multilevelEstimate (scalarPlannerRecursionWithData n k)
    (scalarPlannerRecursionWithData_measurable n k) r
  rw [he] at hm
  exact hb.mul hm

private lemma measurable_confidenceMedian_data {Data Seed : Type*}
    [MeasurableSpace Data] [MeasurableSpace Seed] (p : ℝ) (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ p)
    (F : Data → Seed → ℝ × ℕ) (hF : Measurable (fun q : Data × Seed => (F q.1 q.2).1)) :
    Measurable (fun q : Data × (Fin (confidenceCopyCount p H) → Seed) =>
      (confidenceMedianCopies p H (F q.1) q.2).value) := by
  simp_rw [confidenceMedianCopies_value]
  apply (measurable_sortedMedian (countedConfidenceLevel p H).1).comp
  apply measurable_pi_iff.mpr
  intro j
  exact hF.comp (measurable_fst.prodMk ((measurable_pi_apply j).comp measurable_snd))

theorem measurable_scalarPlannerQueryAtLevel_data (r : ℕ) (p : ℝ) (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ p) :
    Measurable (fun q : ScalarPlannerMedianInput n k r (confidenceCopyCount p H) =>
      (scalarPlannerQueryAtLevel q.1.1 q.1.2 r p H q.2).value) := by
  have hm : Measurable (fun q : ScalarPlannerMedianInput n k r (confidenceCopyCount p H) =>
      (confidenceMedianCopies p H (scalarPlannerSingle q.1.1 q.1.2 r) q.2).value) :=
    measurable_confidenceMedian_data p H (fun q : ScalarPlannerDataState n k => scalarPlannerSingle q.1 q.2 r)
      (measurable_scalarPlannerSingle_data_value r)
  have hD := scalarPlannerRecursionWithData_measurable n k
  have hE : MeasurableSet {q : ScalarPlannerMedianInput n k r (confidenceCopyCount p H) |
      (scalarPlannerRecursion q.1.1).isEmpty q.1.2 = true} :=
    (hD.isEmpty.comp measurable_fst) (measurableSet_singleton true)
  have hc : Measurable (fun q : ScalarPlannerMedianInput n k r (confidenceCopyCount p H) => clipFive
      (confidenceMedianCopies p H (scalarPlannerSingle q.1.1 q.1.2 r) q.2).value) :=
    measurable_const.max (measurable_const.min hm)
  simp only [scalarPlannerQueryAtLevel, apply_ite]
  exact Measurable.ite hE (hD.emptyValue.comp measurable_fst) hc

def scalarPlannerClampRows (y : ScalarPlannerRows n k) : ScalarPlannerRows n k :=
  fun i j => plannerUnit (y i j)

lemma measurable_scalarPlannerClampRows : Measurable (scalarPlannerClampRows (n := n) (k := k)) :=
  measurable_pi_iff.mpr (fun i => measurable_pi_iff.mpr (fun j =>
    continuous_plannerUnit.measurable.comp ((measurable_pi_apply j).comp (measurable_pi_apply i))))

lemma scalarPlannerClampRows_eq (y : ScalarPlannerRows n k) (hy : ∀ i j, y i j ∈ Icc (0 : ℝ) 1) :
    scalarPlannerClampRows y = y := by
  funext i j
  exact plannerUnit_eq (hy i j)

lemma measurable_scalarPlannerClampInput (r copies : ℕ) :
    Measurable (fun q : ScalarPlannerMedianInput n k r copies =>
      ((scalarPlannerClampRows q.1.1,q.1.2),q.2)) := by
  have hrows : Measurable (fun q : ScalarPlannerMedianInput n k r copies => q.1.1) := by
    exact measurable_fst.comp measurable_fst
  have hx : Measurable (fun q : ScalarPlannerMedianInput n k r copies => q.1.2) := by
    exact measurable_snd.comp measurable_fst
  have hseed : Measurable (fun q : ScalarPlannerMedianInput n k r copies => q.2) := measurable_snd
  exact (((measurable_scalarPlannerClampRows (n := n) (k := k)).comp hrows).prodMk hx).prodMk hseed

theorem measurable_scalarPlannerQueryAtLevel_clamped_data (r : ℕ) (p : ℝ) (H : ∃ j : ℕ, (1/4 : ℝ)^j ≤ p) :
    Measurable (fun q : ScalarPlannerMedianInput n k r (confidenceCopyCount p H) =>
      (scalarPlannerQueryAtLevel (scalarPlannerClampRows q.1.1) q.1.2 r p H q.2).value) := by
  let f := fun q : ScalarPlannerMedianInput n k r (confidenceCopyCount p H) =>
    (scalarPlannerQueryAtLevel q.1.1 q.1.2 r p H q.2).value
  let g := fun q : ScalarPlannerMedianInput n k r (confidenceCopyCount p H) =>
    ((scalarPlannerClampRows q.1.1,q.1.2),q.2)
  change Measurable (f ∘ g)
  have hf : Measurable f := measurable_scalarPlannerQueryAtLevel_data r p H
  have hg : Measurable g := measurable_scalarPlannerClampInput r (confidenceCopyCount p H)
  exact hf.comp hg

end ProphetSecretary.Statistics
