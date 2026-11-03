import ProphetSecretary.Statistics.EmpiricalPlannerInstance
import ProphetSecretary.Statistics.PlannerBellmanRestriction
import ProphetSecretary.Statistics.PlannerKernelExpectation
import ProphetSecretary.Statistics.PlannerKernelNormalization

/-!
# The weighted empirical Bellman fixed point

Normalizing the actual continuation value by the product weight gives the
fixed point used by the multilevel algorithm. Child values in the integrand
are mathematical reference values, not quantities supplied to the algorithm.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

/-- Clamping only totalizes arguments outside the unit fraction interval. -/
def plannerUnit (s : ℝ) : ℝ := max 0 (min 1 s)

lemma plannerUnit_mem (s : ℝ) : plannerUnit s ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma plannerUnit_eq {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : plannerUnit s = s := by
  simp only [plannerUnit, min_eq_right hs.2, max_eq_right hs.1]

@[fun_prop] lemma continuous_plannerUnit : Continuous plannerUnit := by unfold plannerUnit; fun_prop

lemma empiricalConditionalExcess_continuous {r : ℕ} (y : Fin r → ℝ) :
    Continuous (empiricalConditionalExcess y) := by
  have hL : LipschitzWith 1 (empiricalConditionalExcess y) := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro a b
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using empiricalConditionalExcess_lipschitz y a b
  exact hL.continuous

variable {n : ℕ} {k : Fin n → ℕ} [∀ i, NeZero (k i)]

lemma empiricalPlannerValue_fraction_continuous
    (y : (i : Fin n) → Fin (k i) → ℝ) (hy : ∀ i j, 0 ≤ y i j)
    (B : Finset (Fin n)) {u z : ℝ} (hu : 0 ≤ u) (hz : 0 ≤ z) :
    Continuous (fun s => (empiricalPlannerInstance y hy).continuationValue B (u*plannerUnit s) 1 z) := by
  let Q := empiricalPlannerInstance y hy
  have hQ := empiricalPlannerInstance_integrable y hy
  exact (optimalScalarValue_durationWeight_continuousOn (Q.restrictTo B)
    (Q.restrictTo_integrable_maximum B hQ) zero_le_one).comp_continuous
      (by fun_prop) (fun s => mul_nonneg hz (mul_nonneg hu (plannerUnit_mem s).1))

noncomputable def weightedContinuationIntegrand
    (y : (i : Fin n) → Fin (k i) → ℝ) (hy : ∀ i j, 0 ≤ y i j) (u z : ℝ)
    (x : Fin n × ℝ × Finset (Fin n)) : ℝ :=
  empiricalConditionalExcess (y x.1)
    ((empiricalPlannerInstance y hy).continuationValue (plannerActive y x.2.2)
      (u*plannerUnit x.2.1) 1 z) /
    plannerWeight (plannerActive y x.2.2) (plannerPositiveProbability y)

lemma measurable_weightedContinuationIntegrand
    (y : (i : Fin n) → Fin (k i) → ℝ) (hy : ∀ i j, 0 ≤ y i j)
    {u z : ℝ} (hu : 0 ≤ u) (hz : 0 ≤ z) : Measurable (weightedContinuationIntegrand y hy u z) := by
  apply measurable_from_prod_countable_right
  intro i
  apply measurable_from_prod_countable_left
  intro B
  change Measurable (fun s : ℝ => empiricalConditionalExcess (y i)
    ((empiricalPlannerInstance y hy).continuationValue (plannerActive y B) (u*plannerUnit s) 1 z) /
      plannerWeight (plannerActive y B) (plannerPositiveProbability y))
  exact (((empiricalConditionalExcess_continuous (y i)).comp
    (empiricalPlannerValue_fraction_continuous y hy (plannerActive y B) hu hz)).div_const
      (plannerWeight (plannerActive y B) (plannerPositiveProbability y))).measurable

lemma weightedContinuationIntegrand_abs_le_one
    (y : (i : Fin n) → Fin (k i) → ℝ) (hy : ∀ i j, 0 ≤ y i j)
    (hcap : ∀ i j, y i j ≤ 1) {u z : ℝ} (hu : 0 ≤ u) (hz : 0 ≤ z)
    (x : Fin n × ℝ × Finset (Fin n)) : |weightedContinuationIntegrand y hy u z x| ≤ 1 := by
  let Q := empiricalPlannerInstance y hy
  let B := plannerActive y x.2.2
  let β := plannerWeight B (plannerPositiveProbability y)
  have hβ : 1 ≤ β := one_le_plannerWeight B _ (fun i _ => plannerPositiveProbability_nonnegative y i)
  have hβpos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  have hv : 0 ≤ Q.continuationValue B (u*plannerUnit x.2.1) 1 z :=
    Q.continuationValue_nonnegative (empiricalPlannerInstance_integrable y hy) B
      (mul_nonneg hu (plannerUnit_mem _).1) zero_le_one hz
  have h0 := empiricalConditionalExcess_nonnegative (y x.1) (Q.continuationValue B (u*plannerUnit x.2.1) 1 z)
  have h1 := empiricalConditionalExcess_le_one (y x.1) (hcap x.1) hv
  change |empiricalConditionalExcess (y x.1) (Q.continuationValue B (u*plannerUnit x.2.1) 1 z)/β| ≤ 1
  rw [abs_of_nonneg (div_nonneg h0 hβpos.le)]
  exact (div_le_one hβpos).mpr (h1.trans hβ)

lemma weightedContinuationIntegrand_cancel
    (y : (i : Fin n) → Fin (k i) → ℝ) (hy : ∀ i j, 0 ≤ y i j)
    (A : Finset (Fin n)) (hA : A.Nonempty)
    (hpos : ∀ i ∈ A, 0 < plannerPositiveProbability y i)
    {u z s : ℝ} (hu : 0 ≤ u) (hz : 0 ≤ z) (hs : s ∈ Icc (0 : ℝ) 1)
    (i : Fin n) (_hi : i ∈ A) (B : Finset (Fin n)) (hB : B ⊆ A.erase i) :
    plannerContraction A (plannerPositiveProbability y) *
      plannerKernelDensity A (plannerPositiveProbability y) i B s *
        weightedContinuationIntegrand y hy u z (i,s,B) =
      (s^B.card * (1-s)^((A.erase i).card-B.card) *
        positivePremium ((empiricalPlannerInstance y hy).law i) 1
          ((empiricalPlannerInstance y hy).continuationValue B (u*s) 1 z)) /
      plannerWeight A (plannerPositiveProbability y) := by
  have hBA : B ⊆ A := hB.trans (Finset.erase_subset _ _)
  have hactive : plannerActive y B = B := plannerActive_of_positive y B (fun j hj => hpos j (hBA hj))
  unfold weightedContinuationIntegrand
  rw [hactive, plannerUnit_eq hs,
    plannerKernelWeight_cancel_gain A _ hA hpos i B hBA s]
  have hv := (empiricalPlannerInstance y hy).continuationValue_nonnegative
    (empiricalPlannerInstance_integrable y hy) B (mul_nonneg hu hs.1) zero_le_one hz
  have hfactor := positivePremium_empiricalLaw_factor (y i) hv
  change positivePremium ((empiricalPlannerInstance y hy).law i) 1
      ((empiricalPlannerInstance y hy).continuationValue B (u*s) 1 z) =
    plannerPositiveProbability y i * empiricalConditionalExcess (y i)
      ((empiricalPlannerInstance y hy).continuationValue B (u*s) 1 z) at hfactor
  rw [hfactor]
  ring

/-- The actual normalized empirical continuation satisfies the weighted equation. -/
theorem empiricalPlanner_weightedBellman
    (y : (i : Fin n) → Fin (k i) → ℝ) (hy : ∀ i j, 0 ≤ y i j)
    (hcap : ∀ i j, y i j ≤ 1) (A : Finset (Fin n)) (hA : A.Nonempty)
    (hpos : ∀ i ∈ A, 0 < plannerPositiveProbability y i)
    {u z : ℝ} (hu : 0 ≤ u) (hz : 0 ≤ z) :
    (empiricalPlannerInstance y hy).continuationValue A u 1 z /
        plannerWeight A (plannerPositiveProbability y) =
      z*u/plannerWeight A (plannerPositiveProbability y) +
        plannerContraction A (plannerPositiveProbability y) *
          ∫ x, weightedContinuationIntegrand y hy u z x
            ∂plannerKernelLaw A (plannerPositiveProbability y) := by
  let Q := empiricalPlannerInstance y hy
  let p := plannerPositiveProbability y
  let β := plannerWeight A p
  let κ := plannerContraction A p
  let F := weightedContinuationIntegrand y hy u z
  let G : Fin n → Finset (Fin n) → ℝ → ℝ := fun i B s =>
    s^B.card * (1-s)^((A.erase i).card-B.card) *
      positivePremium (Q.law i) 1 (Q.continuationValue B (u*plannerUnit s) 1 z)
  have hQ := empiricalPlannerInstance_integrable y hy
  have hGcont (i : Fin n) (B : Finset (Fin n)) : Continuous (G i B) := by
    have hv := empiricalPlannerValue_fraction_continuous y hy B hu hz
    have hprem := (positivePremium_continuous (Q.law i) (Q.integrable_maximum_iff.mp hQ i) 1).comp hv
    exact ((continuous_id.pow _).mul ((continuous_const.sub continuous_id).pow _)).mul hprem
  have hGI (i : Fin n) (B : Finset (Fin n)) : Integrable (G i B) Instance.uniformClock :=
    (hGcont i B).integrableOn_Icc
  have hcore : Q.continuationValue A u 1 z = z*u + ∑ i ∈ A,
      ∫ s, (∑ B ∈ (A.erase i).powerset, G i B s) ∂Instance.uniformClock := by
    rw [Q.continuationValue_allArrivals A hQ hu hz]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    have hsupp : ∀ᵐ s ∂Instance.uniformClock, s ∈ Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
    filter_upwards [hsupp] with s hs
    simp only [G, plannerUnit_eq hs]
  have hkernel := integral_plannerKernelLaw A p hA hpos F
    (measurable_weightedContinuationIntegrand y hy hu hz)
    (weightedContinuationIntegrand_abs_le_one y hy hcap hu hz)
  have he : κ*(∫ x, F x ∂plannerKernelLaw A p) =
      (∑ i ∈ A, ∫ s, (∑ B ∈ (A.erase i).powerset, G i B s) ∂Instance.uniformClock)/β := by
    calc
      κ*(∫ x, F x ∂plannerKernelLaw A p) =
          ∑ i ∈ A, ∑ B ∈ (A.erase i).powerset,
            ∫ s, κ*plannerKernelDensity A p i B s*F (i,s,B) ∂Instance.uniformClock := by
        rw [hkernel]
        simp only [Finset.mul_sum, integral_const_mul, mul_assoc]
      _ = ∑ i ∈ A, ∑ B ∈ (A.erase i).powerset,
          ∫ s, G i B s/β ∂Instance.uniformClock := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro B hB
        apply integral_congr_ae
        have hsupp : ∀ᵐ s ∂Instance.uniformClock, s ∈ Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
        filter_upwards [hsupp] with s hs
        simpa only [G, plannerUnit_eq hs] using
          weightedContinuationIntegrand_cancel y hy A hA hpos hu hz hs i hi B (Finset.mem_powerset.mp hB)
      _ = _ := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        rw [integral_finsetSum _ (fun B _ => hGI i B), Finset.sum_div]
        simp only [integral_div]
  change Q.continuationValue A u 1 z/β = z*u/β+κ*(∫ x, F x ∂plannerKernelLaw A p)
  rw [he, hcore, add_div]

end ProphetSecretary.Statistics
