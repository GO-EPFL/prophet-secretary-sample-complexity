import ProphetSecretary.Statistics.PlannerWeightedBellman
import ProphetSecretary.Statistics.PlannerUniformSampler
import ProphetSecretary.Analysis.MultilevelEstimatorMoments
import ProphetSecretary.Model.BellmanBase
import Mathlib.Probability.HasLaw

/-!
# The empirical scalar planner's weighted recursion

The computational fields read the stored empirical observations, the current
state, and a fresh fixed-law seed. The optimal continuation is a separate
reference function used to prove the fixed-point equation.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Analysis

abbrev ScalarPlannerState (n : ℕ) := Finset (Fin n) × (ℝ × ℝ)

def scalarPlannerTime {n : ℕ} (x : ScalarPlannerState n) : ℝ := plannerUnit x.2.1

def scalarPlannerDurationWeight {n : ℕ} (x : ScalarPlannerState n) : ℝ := max 0 (min 4 x.2.2)

lemma scalarPlannerDurationWeight_mem {n : ℕ} (x : ScalarPlannerState n) :
    scalarPlannerDurationWeight x ∈ Icc (0 : ℝ) 4 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma scalarPlannerDurationWeight_eq {n : ℕ} {x : ScalarPlannerState n}
    (hx : x.2.2 ∈ Icc (0 : ℝ) 4) : scalarPlannerDurationWeight x = x.2.2 := by
  simp only [scalarPlannerDurationWeight, min_eq_right hx.2, max_eq_right hx.1]

lemma measurable_scalarPlannerTime (n : ℕ) : Measurable (@scalarPlannerTime n) :=
  continuous_plannerUnit.measurable.comp (measurable_fst.comp measurable_snd)

lemma measurable_scalarPlannerDurationWeight (n : ℕ) : Measurable (@scalarPlannerDurationWeight n) :=
  measurable_const.max (measurable_const.min (measurable_snd.comp measurable_snd))

variable {n : ℕ} {k : Fin n → ℕ}

noncomputable def scalarPlannerWeight (y : (i : Fin n) → Fin (k i) → ℝ)
    (A : Finset (Fin n)) : ℝ := plannerWeight (plannerActive y A) (plannerPositiveProbability y)

lemma scalarPlannerWeight_ge_one (y : (i : Fin n) → Fin (k i) → ℝ) (A : Finset (Fin n)) :
    1 ≤ scalarPlannerWeight y A :=
  one_le_plannerWeight _ _ (fun i _ => plannerPositiveProbability_nonnegative y i)

lemma scalarPlannerWeight_pos (y : (i : Fin n) → Fin (k i) → ℝ) (A : Finset (Fin n)) :
    0 < scalarPlannerWeight y A := zero_lt_one.trans_le (scalarPlannerWeight_ge_one y A)

noncomputable def scalarPlannerPayoff (y : (i : Fin n) → Fin (k i) → ℝ)
    (o : PlannerUniformOutput n) (a : ℝ) : ℝ :=
  match o.1 with
  | none => 0
  | some i => empiricalConditionalExcess (y i) (scalarPlannerWeight y o.2.2 * a) /
      scalarPlannerWeight y o.2.2

noncomputable def scalarPlannerRecursion (y : (i : Fin n) → Fin (k i) → ℝ) :
    MultilevelRecursion (ScalarPlannerState n) (PlannerUniformSeed n) (PlannerUniformOutput n) ℝ where
  isEmpty x := decide (plannerActive y x.1 = ∅)
  emptyValue x := scalarPlannerDurationWeight x * scalarPlannerTime x
  offset x := scalarPlannerDurationWeight x * scalarPlannerTime x / scalarPlannerWeight y x.1
  coefficient x := plannerContraction (plannerActive y x.1) (plannerPositiveProbability y)
  sample x := plannerUniformTransition (plannerActive y x.1) (plannerPositiveProbability y)
  child x o := (o.2.2, (scalarPlannerTime x * plannerUnit o.2.1, scalarPlannerDurationWeight x))
  payoff _ := scalarPlannerPayoff y

lemma measurable_scalarPlannerPayoff (y : (i : Fin n) → Fin (k i) → ℝ) :
    Measurable (fun q : PlannerUniformOutput n × ℝ => scalarPlannerPayoff y q.1 q.2) := by
  have hcore : Measurable (fun q : Option (Fin n) × (Finset (Fin n) × ℝ) =>
      match q.1 with
      | none => 0
      | some i => empiricalConditionalExcess (y i) (scalarPlannerWeight y q.2.1 * q.2.2) /
          scalarPlannerWeight y q.2.1) := by
    apply measurable_from_prod_countable_right
    intro o
    cases o with
    | none => exact measurable_const
    | some i =>
      have hβ : Measurable (fun q : Finset (Fin n) × ℝ => scalarPlannerWeight y q.1) :=
        (measurable_of_countable (scalarPlannerWeight y)).comp measurable_fst
      exact ((empiricalConditionalExcess_continuous (y i)).measurable.comp
        (hβ.mul measurable_snd)).div hβ
  have hp : Measurable (fun q : PlannerUniformOutput n × ℝ => (q.1.1, (q.1.2.2, q.2))) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp (measurable_snd.comp measurable_fst)).prodMk measurable_snd)
  exact hcore.comp hp

theorem scalarPlannerRecursion_measurable (y : (i : Fin n) → Fin (k i) → ℝ) :
    (scalarPlannerRecursion y).IsMeasurable := by
  have htime := measurable_scalarPlannerTime n
  have hz := measurable_scalarPlannerDurationWeight n
  have hβ : Measurable (fun x : ScalarPlannerState n => scalarPlannerWeight y x.1) :=
    (measurable_of_countable (scalarPlannerWeight y)).comp measurable_fst
  have hsam : Measurable (fun q : Finset (Fin n) × PlannerUniformSeed n =>
      plannerUniformTransition (plannerActive y q.1) (plannerPositiveProbability y) q.2) := by
    apply measurable_from_prod_countable_right
    intro A
    exact measurable_plannerUniformTransition (plannerActive y A) (plannerPositiveProbability y)
  have hchildSet : Measurable (fun q : ScalarPlannerState n × PlannerUniformOutput n => q.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hchildFraction : Measurable (fun q : ScalarPlannerState n × PlannerUniformOutput n => q.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  refine ⟨?_, hz.mul htime, (hz.mul htime).div hβ, ?_, ?_, ?_, ?_⟩
  · exact (measurable_of_countable (fun A : Finset (Fin n) => decide (plannerActive y A = ∅))).comp measurable_fst
  · exact (measurable_of_countable (fun A : Finset (Fin n) =>
      plannerContraction (plannerActive y A) (plannerPositiveProbability y))).comp measurable_fst
  · exact hsam.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  · exact hchildSet.prodMk (((htime.comp measurable_fst).mul
      (continuous_plannerUnit.measurable.comp hchildFraction)).prodMk (hz.comp measurable_fst))
  · exact (measurable_scalarPlannerPayoff y).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

lemma scalarPlannerRecursion_coefficient_bounds (y : (i : Fin n) → Fin (k i) → ℝ)
    (x : ScalarPlannerState n) :
    0 ≤ (scalarPlannerRecursion y).coefficient x ∧ (scalarPlannerRecursion y).coefficient x ≤ 1/4 := by
  exact ⟨plannerContraction_nonneg _ _ (fun i _ => plannerPositiveProbability_nonnegative y i),
    plannerContraction_le_quarter _ _ (fun i _ => plannerPositiveProbability_nonnegative y i)⟩

lemma scalarPlannerPayoff_bounds (y : (i : Fin n) → Fin (k i) → ℝ)
    (hcap : ∀ i j, y i j ≤ 1) (o : PlannerUniformOutput n) {a : ℝ} (ha : 0 ≤ a) :
    0 ≤ scalarPlannerPayoff y o a ∧ scalarPlannerPayoff y o a ≤ 1 := by
  cases h : o.1 with
  | none => simp [scalarPlannerPayoff, h]
  | some i =>
    have hβ := scalarPlannerWeight_pos y o.2.2
    have hl := empiricalConditionalExcess_nonnegative (y i) (scalarPlannerWeight y o.2.2 * a)
    have hu := empiricalConditionalExcess_le_one (y i) (hcap i) (mul_nonneg hβ.le ha)
    simp only [scalarPlannerPayoff, h]
    exact ⟨div_nonneg hl hβ.le, (div_le_one hβ).2 (hu.trans (scalarPlannerWeight_ge_one y o.2.2))⟩

lemma scalarPlannerPayoff_lipschitz (y : (i : Fin n) → Fin (k i) → ℝ)
    (o : PlannerUniformOutput n) : LipschitzWith 1 (scalarPlannerPayoff y o) := by
  rw [lipschitzWith_iff_dist_le_mul]
  intro a b
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  cases h : o.1 with
  | none => simp [scalarPlannerPayoff, h]
  | some i =>
    let β := scalarPlannerWeight y o.2.2
    have hβ := scalarPlannerWeight_pos y o.2.2
    simp only [scalarPlannerPayoff, h]
    rw [← sub_div, abs_div, abs_of_pos hβ]
    apply (div_le_iff₀ hβ).2
    calc
      _ ≤ |β * a - β * b| := empiricalConditionalExcess_lipschitz (y i) _ _
      _ = _ := by rw [← mul_sub, abs_mul, abs_of_pos hβ]; ring

lemma scalarPlannerTime_child (y : (i : Fin n) → Fin (k i) → ℝ)
    (x : ScalarPlannerState n) (o : PlannerUniformOutput n) :
    scalarPlannerTime ((scalarPlannerRecursion y).child x o) = scalarPlannerTime x * plannerUnit o.2.1 := by
  apply plannerUnit_eq
  have hu := plannerUnit_mem x.2.1
  have hs := plannerUnit_mem o.2.1
  exact ⟨mul_nonneg hu.1 hs.1, (mul_le_of_le_one_right hu.1 hs.2).trans hu.2⟩

lemma scalarPlannerDurationWeight_child (y : (i : Fin n) → Fin (k i) → ℝ)
    (x : ScalarPlannerState n) (o : PlannerUniformOutput n) :
    scalarPlannerDurationWeight ((scalarPlannerRecursion y).child x o) = scalarPlannerDurationWeight x :=
  scalarPlannerDurationWeight_eq (scalarPlannerDurationWeight_mem x)

variable [∀ i, NeZero (k i)]

noncomputable def scalarPlannerValue (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (x : ScalarPlannerState n) : ℝ :=
  (empiricalPlannerInstance y hy).continuationValue (plannerActive y x.1)
    (scalarPlannerTime x) 1 (scalarPlannerDurationWeight x)

noncomputable def scalarPlannerNormalizedValue (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (x : ScalarPlannerState n) : ℝ :=
  scalarPlannerValue y hy x / scalarPlannerWeight y x.1

lemma scalarPlannerValue_eq_continuation (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (A : Finset (Fin n)) {u z : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hz : z ∈ Icc (0 : ℝ) 4) :
    scalarPlannerValue y hy (A,(u,z)) = (empiricalPlannerInstance y hy).continuationValue A u 1 z := by
  rw [scalarPlannerValue, scalarPlannerTime, plannerUnit_eq hu, scalarPlannerDurationWeight_eq hz]
  exact (empiricalPlannerInstance_active_value y hy A hu.1 hz.1).symm

lemma measurable_scalarPlannerValue (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) : Measurable (scalarPlannerValue y hy) := by
  apply measurable_from_prod_countable_right
  intro A
  let Q := empiricalPlannerInstance y hy
  let B := plannerActive y A
  have hQ := empiricalPlannerInstance_integrable y hy
  have hu : Measurable (fun q : ℝ × ℝ => plannerUnit q.1) := continuous_plannerUnit.measurable.comp measurable_fst
  have hz : Measurable (fun q : ℝ × ℝ => max 0 (min 4 q.2)) :=
    measurable_const.max (measurable_const.min measurable_snd)
  exact (Q.restrictTo B).measurable_scalarValue_coefficients (Q.restrictTo_integrable_maximum B hQ)
    measurable_const (hz.mul hu) (fun _ => zero_le_one)
    (fun q => mul_nonneg (le_max_left _ _) (plannerUnit_mem q.1).1)

lemma measurable_scalarPlannerNormalizedValue (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) : Measurable (scalarPlannerNormalizedValue y hy) :=
  (measurable_scalarPlannerValue y hy).div
    ((measurable_of_countable (scalarPlannerWeight y)).comp measurable_fst)

lemma scalarPlannerValue_bounds (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (hcap : ∀ i j, y i j ≤ 1) (x : ScalarPlannerState n) :
    0 ≤ scalarPlannerValue y hy x ∧ scalarPlannerValue y hy x ≤ 5 := by
  let Q := empiricalPlannerInstance y hy
  let A := plannerActive y x.1
  let u := scalarPlannerTime x
  let z := scalarPlannerDurationWeight x
  have hQ := empiricalPlannerInstance_integrable y hy
  have hu : u ∈ Icc (0 : ℝ) 1 := plannerUnit_mem _
  have hz : z ∈ Icc (0 : ℝ) 4 := scalarPlannerDurationWeight_mem x
  have hzu0 : 0 ≤ z*u := mul_nonneg hz.1 hu.1
  have hzu1 : z*u ≤ 4 := (mul_le_of_le_one_right hz.1 hu.2).trans hz.2
  have hM : (Q.restrictTo A).expectedMaximum ≤ 1 :=
    (Q.restrictTo A).expectedMaximum_le_of_bounded zero_le_one
      (fun i => empiricalPlannerInstance_bounded y hy hcap (stateEmbedding A i))
  refine ⟨Q.continuationValue_nonnegative hQ A hu.1 zero_le_one hz.1, ?_⟩
  have hV := optimalScalarValue_le_benchmark (Q.restrictTo A)
    (Q.restrictTo_integrable_maximum A hQ) zero_le_one hzu0
  change optimalScalarValue (Q.restrictTo A) 1 (z*u) ≤ 5
  linarith

lemma scalarPlannerNormalizedValue_bounds (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (hcap : ∀ i j, y i j ≤ 1) (x : ScalarPlannerState n) :
    0 ≤ scalarPlannerNormalizedValue y hy x ∧ scalarPlannerNormalizedValue y hy x ≤ 5 := by
  have hv := scalarPlannerValue_bounds y hy hcap x
  have hb := scalarPlannerWeight_ge_one y x.1
  have hb' := scalarPlannerWeight_pos y x.1
  exact ⟨div_nonneg hv.1 hb'.le, (div_le_iff₀ hb').2 (by nlinarith [hv.2])⟩

lemma scalarPlannerNormalizedValue_empty (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (x : ScalarPlannerState n) (hx : (scalarPlannerRecursion y).isEmpty x = true) :
    (scalarPlannerRecursion y).emptyValue x = scalarPlannerNormalizedValue y hy x := by
  have he : plannerActive y x.1 = ∅ := of_decide_eq_true hx
  simp [scalarPlannerRecursion, scalarPlannerNormalizedValue, scalarPlannerValue, scalarPlannerWeight,
    he, Instance.continuationValue_empty]

noncomputable def scalarPlannerReferenceIntegrand (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (x : ScalarPlannerState n) (o : PlannerUniformOutput n) : ℝ :=
  match o.1 with
  | none => 0
  | some i => weightedContinuationIntegrand y hy (scalarPlannerTime x)
      (scalarPlannerDurationWeight x) (i,o.2)

lemma measurable_scalarPlannerReferenceIntegrand (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (x : ScalarPlannerState n) :
    Measurable (scalarPlannerReferenceIntegrand y hy x) := by
  apply measurable_from_prod_countable_right
  intro i
  cases i with
  | none => exact measurable_const
  | some i =>
    exact (measurable_weightedContinuationIntegrand y hy (plannerUnit_mem x.2.1).1
      (scalarPlannerDurationWeight_mem x).1).comp (measurable_const.prodMk measurable_id)

lemma scalarPlannerPayoff_at_normalizedChild (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (x : ScalarPlannerState n) (o : PlannerUniformOutput n) :
    (scalarPlannerRecursion y).payoff x o
      (scalarPlannerNormalizedValue y hy ((scalarPlannerRecursion y).child x o)) =
        scalarPlannerReferenceIntegrand y hy x o := by
  have hcancel : scalarPlannerWeight y o.2.2 *
      scalarPlannerNormalizedValue y hy ((scalarPlannerRecursion y).child x o) =
      (empiricalPlannerInstance y hy).continuationValue (plannerActive y o.2.2)
        (scalarPlannerTime x * plannerUnit o.2.1) 1 (scalarPlannerDurationWeight x) := by
    unfold scalarPlannerNormalizedValue scalarPlannerValue
    rw [scalarPlannerTime_child, scalarPlannerDurationWeight_child]
    change scalarPlannerWeight y o.2.2 * (_ / scalarPlannerWeight y o.2.2) = _
    field_simp [(scalarPlannerWeight_pos y o.2.2).ne']
    rfl
  change scalarPlannerPayoff y o _ = _
  cases h : o.1 with
  | none => simp [scalarPlannerPayoff, scalarPlannerReferenceIntegrand, h]
  | some i =>
    simp only [scalarPlannerPayoff, scalarPlannerReferenceIntegrand, h]
    rw [hcancel]
    rfl

/-- The true normalized continuation is a fixed point of the actual sampler
recursion. The distributional bridge is the proved fixed-seed kernel law. -/
theorem scalarPlannerNormalizedValue_fixed (y : (i : Fin n) → Fin (k i) → ℝ)
    (hy : ∀ i j, 0 ≤ y i j) (hcap : ∀ i j, y i j ≤ 1) (x : ScalarPlannerState n)
    (hx : (scalarPlannerRecursion y).isEmpty x = false) :
    scalarPlannerNormalizedValue y hy x = (scalarPlannerRecursion y).offset x +
      (scalarPlannerRecursion y).coefficient x *
        ∫ seed, (let o := (scalarPlannerRecursion y).sample x seed
          (scalarPlannerRecursion y).payoff x o
            (scalarPlannerNormalizedValue y hy ((scalarPlannerRecursion y).child x o)))
          ∂plannerUniformSeedLaw n := by
  let D := scalarPlannerRecursion y
  let A := plannerActive y x.1
  let p := plannerPositiveProbability y
  let F := scalarPlannerReferenceIntegrand y hy x
  let μ := plannerUniformSeedLaw n
  have hA : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr (of_decide_eq_false hx)
  have hpos : ∀ i ∈ A, 0 < p i := fun i hi => plannerActive_positive y x.1 hi
  have hmap : μ.map (D.sample x) = (plannerKernelLaw A p).map plannerSomeTransition :=
    map_plannerUniformTransition_of_nonempty A p hA hpos
  have hs : Measurable (D.sample x) := measurable_plannerUniformTransition A p
  have hF : Measurable F := measurable_scalarPlannerReferenceIntegrand y hy x
  have hI : (∫ seed, (let o := D.sample x seed
      D.payoff x o (scalarPlannerNormalizedValue y hy (D.child x o))) ∂μ) =
      ∫ o, weightedContinuationIntegrand y hy (scalarPlannerTime x)
        (scalarPlannerDurationWeight x) o ∂plannerKernelLaw A p := by
    calc
      _ = ∫ seed, F (D.sample x seed) ∂μ := integral_congr_ae
        (ae_of_all _ (fun seed => scalarPlannerPayoff_at_normalizedChild y hy x (D.sample x seed)))
      _ = ∫ o, F o ∂(plannerKernelLaw A p).map plannerSomeTransition := by
        rw [← hmap]
        exact (integral_map hs.aemeasurable hF.aestronglyMeasurable).symm
      _ = ∫ o, F (plannerSomeTransition o) ∂plannerKernelLaw A p :=
        integral_map (measurable_plannerSomeTransition n).aemeasurable hF.aestronglyMeasurable
      _ = _ := rfl
  change scalarPlannerNormalizedValue y hy x = D.offset x + D.coefficient x * _
  rw [hI]
  exact empiricalPlanner_weightedBellman y hy hcap A hA hpos
    (plannerUnit_mem x.2.1).1 (scalarPlannerDurationWeight_mem x).1

end ProphetSecretary.Statistics
