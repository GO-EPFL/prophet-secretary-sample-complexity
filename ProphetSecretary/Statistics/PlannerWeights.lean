import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Product weights for the scalar planner

The weights in `alg:weighted-recursion` turn the sum of continuation errors
into a contraction with coefficient at most one quarter. Their normalization
is the integral of the derivative of a finite product.
-/

open MeasureTheory
open scoped BigOperators

namespace ProphetSecretary.Statistics

variable {ι : Type*}

/-- Product weight of a set of active identities. -/
noncomputable def plannerWeight (A : Finset ι) (p : ι → ℝ) : ℝ :=
  ∏ i ∈ A, (1 + 4 * p i)

/-- The same product with its positive probabilities multiplied by `s`. -/
noncomputable def plannerWeightAt (A : Finset ι) (p : ι → ℝ) (s : ℝ) : ℝ :=
  ∏ i ∈ A, (1 + 4 * p i * s)

/-- Coefficient of the normalized continuation expectation. -/
noncomputable def plannerContraction (A : Finset ι) (p : ι → ℝ) : ℝ :=
  (plannerWeight A p - 1) / (4 * plannerWeight A p)

@[simp] lemma plannerWeight_empty (p : ι → ℝ) : plannerWeight ∅ p = 1 := by
  simp [plannerWeight]

@[simp] lemma plannerWeightAt_zero (A : Finset ι) (p : ι → ℝ) :
    plannerWeightAt A p 0 = 1 := by
  simp [plannerWeightAt]

@[simp] lemma plannerWeightAt_one (A : Finset ι) (p : ι → ℝ) :
    plannerWeightAt A p 1 = plannerWeight A p := by
  simp [plannerWeightAt, plannerWeight]

lemma one_le_plannerWeight (A : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i) : 1 ≤ plannerWeight A p := by
  apply Finset.one_le_prod
  intro i hi
  linarith [hp i hi]

lemma plannerWeight_pos (A : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i) : 0 < plannerWeight A p :=
  lt_of_lt_of_le zero_lt_one (one_le_plannerWeight A p hp)

lemma one_lt_plannerWeight (A : Finset ι) (p : ι → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) : 1 < plannerWeight A p := by
  have h := Finset.prod_lt_prod_of_nonempty (s := A) (f := fun _ => (1 : ℝ))
    (g := fun i => 1 + 4 * p i) (fun _ _ => zero_lt_one)
    (fun i hi => by linarith [hp i hi]) hA
  simpa [plannerWeight] using h

/-- `alg:weight-size`: the weight depends exponentially on the positive count. -/
lemma plannerWeight_le_exp (A : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i) :
    plannerWeight A p ≤ Real.exp (4 * ∑ i ∈ A, p i) := by
  unfold plannerWeight
  calc
    ∏ i ∈ A, (1 + 4 * p i) ≤ ∏ i ∈ A, Real.exp (4 * p i) := by
      apply Finset.prod_le_prod
      · intro i hi
        linarith [hp i hi]
      · intro i _
        simpa only [add_comm] using Real.add_one_le_exp (4 * p i)
    _ = Real.exp (4 * ∑ i ∈ A, p i) := by
      rw [← Real.exp_sum, Finset.mul_sum]

@[simp] lemma plannerContraction_empty (p : ι → ℝ) :
    plannerContraction ∅ p = 0 := by
  simp [plannerContraction]

lemma plannerContraction_nonneg (A : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i) : 0 ≤ plannerContraction A p := by
  unfold plannerContraction
  exact div_nonneg (sub_nonneg.mpr (one_le_plannerWeight A p hp))
    (mul_nonneg (by norm_num) (plannerWeight_pos A p hp).le)

lemma plannerContraction_le_quarter (A : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i) : plannerContraction A p ≤ 1 / 4 := by
  have hβ := plannerWeight_pos A p hp
  unfold plannerContraction
  apply (div_le_iff₀ (by positivity : 0 < 4 * plannerWeight A p)).mpr
  linarith

/-- The expectation of the product weight under independent Bernoulli subsets.
The powerset sum spells out the finite Bernoulli law. -/
lemma bernoulli_plannerWeight_sum [DecidableEq ι] (A : Finset ι) (p : ι → ℝ) (s : ℝ) :
    (∑ B ∈ A.powerset, plannerWeight B p * s ^ B.card *
      (1 - s) ^ (A.card - B.card)) = plannerWeightAt A p s := by
  calc
    (∑ B ∈ A.powerset, plannerWeight B p * s ^ B.card *
      (1 - s) ^ (A.card - B.card)) =
      ∑ B ∈ A.powerset, (∏ i ∈ B, s * (1 + 4 * p i)) *
        ∏ i ∈ A \ B, (1 - s) := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
        Finset.card_sdiff_of_subset (Finset.mem_powerset.mp hB)]
      unfold plannerWeight
      ring
    _ = ∏ i ∈ A, (s * (1 + 4 * p i) + (1 - s)) :=
      (Finset.prod_add (fun i => s * (1 + 4 * p i)) (fun _ => 1 - s) A).symm
    _ = plannerWeightAt A p s := by
      unfold plannerWeightAt
      apply Finset.prod_congr rfl
      intro i _
      ring

lemma hasDerivAt_plannerWeightAt [DecidableEq ι] (A : Finset ι) (p : ι → ℝ) (s : ℝ) :
    HasDerivAt (plannerWeightAt A p)
      (4 * ∑ i ∈ A, p i * plannerWeightAt (A.erase i) p s) s := by
  have hf (i : ι) (_hi : i ∈ A) :
      HasDerivAt (fun t : ℝ => 1 + 4 * p i * t) (4 * p i) s := by
    simpa only [mul_one, id_eq] using ((hasDerivAt_id s).const_mul (4 * p i)).const_add 1
  have hDer := HasDerivAt.fun_finsetProd hf
  change HasDerivAt (plannerWeightAt A p)
    (∑ i ∈ A, plannerWeightAt (A.erase i) p s * (4 * p i)) s at hDer
  convert hDer using 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The normalization identity preceding `alg:weighted-recursion`. -/
lemma integral_plannerWeightAt_erase [DecidableEq ι] (A : Finset ι) (p : ι → ℝ) :
    ∑ i ∈ A, p i * (∫ s in (0 : ℝ)..1, plannerWeightAt (A.erase i) p s) =
      (plannerWeight A p - 1) / 4 := by
  have hcont : Continuous (fun s : ℝ =>
      4 * ∑ i ∈ A, p i * plannerWeightAt (A.erase i) p s) := by
    unfold plannerWeightAt
    fun_prop
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_plannerWeightAt A p s) (hcont.intervalIntegrable 0 1)
  rw [plannerWeightAt_one, plannerWeightAt_zero,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum] at hInt
  · simp_rw [intervalIntegral.integral_const_mul] at hInt
    linarith
  · intro i _
    have hc : Continuous (fun s : ℝ => p i * plannerWeightAt (A.erase i) p s) := by
      unfold plannerWeightAt
      fun_prop
    exact hc.intervalIntegrable 0 1

/-- Density of the planner transition, with respect to Lebesgue measure in
`s` and counting measure on the identity and subset coordinates. -/
noncomputable def plannerKernelDensity [DecidableEq ι] (A : Finset ι) (p : ι → ℝ)
    (i : ι) (B : Finset ι) (s : ℝ) : ℝ :=
  (4 * p i / (plannerWeight A p - 1)) *
    (plannerWeight B p * s ^ B.card * (1 - s) ^ ((A.erase i).card - B.card))

lemma plannerKernelDensity_nonneg [DecidableEq ι] (A : Finset ι) (p : ι → ℝ)
    (hp : ∀ j ∈ A, 0 ≤ p j) {i : ι} (hi : i ∈ A)
    {B : Finset ι} (hB : B ⊆ A.erase i) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ plannerKernelDensity A p i B s := by
  have hβ := one_le_plannerWeight A p hp
  have hβB := plannerWeight_pos B p (fun j hj => hp j (Finset.mem_erase.mp (hB hj)).2)
  have hpi := hp i hi
  unfold plannerKernelDensity
  exact mul_nonneg
    (div_nonneg (mul_nonneg (by norm_num) hpi) (sub_nonneg.mpr hβ))
    (mul_nonneg (mul_nonneg hβB.le (pow_nonneg hs.1 _))
      (pow_nonneg (sub_nonneg.mpr hs.2) _))

/-- The explicit finite-subset transition density has total mass one. -/
lemma plannerKernel_mass [DecidableEq ι] (A : Finset ι) (p : ι → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) :
    (∑ i ∈ A, ∫ s in (0 : ℝ)..1,
      ∑ B ∈ (A.erase i).powerset, plannerKernelDensity A p i B s) = 1 := by
  have hβ : plannerWeight A p - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (one_lt_plannerWeight A p hA hp))
  simp_rw [plannerKernelDensity, ← Finset.mul_sum, bernoulli_plannerWeight_sum,
    intervalIntegral.integral_const_mul]
  calc
    (∑ i ∈ A, 4 * p i / (plannerWeight A p - 1) *
      (∫ s in (0 : ℝ)..1, plannerWeightAt (A.erase i) p s)) =
      (4 / (plannerWeight A p - 1)) *
        ∑ i ∈ A, p i * (∫ s in (0 : ℝ)..1, plannerWeightAt (A.erase i) p s) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = (4 / (plannerWeight A p - 1)) * ((plannerWeight A p - 1) / 4) := by
      rw [integral_plannerWeightAt_erase]
    _ = 1 := by field_simp

/-- Normalizing both argument and value preserves a one-Lipschitz bound. -/
lemma normalized_excess_abs_sub_le {h : ℝ → ℝ} {β : ℝ} (hβ : 0 < β)
    (hLip : ∀ x y : ℝ, |h x - h y| ≤ |x - y|) (x y : ℝ) :
    |h (β * x) / β - h (β * y) / β| ≤ |x - y| := by
  calc
    |h (β * x) / β - h (β * y) / β| = |h (β * x) - h (β * y)| / β := by
      rw [← sub_div, abs_div, abs_of_pos hβ]
    _ ≤ |β * x - β * y| / β := div_le_div_of_nonneg_right (hLip _ _) hβ.le
    _ = |x - y| := by
      rw [← mul_sub, abs_mul, abs_of_pos hβ]
      field_simp

/-- A bounded nonnegative excess remains in the unit interval after normalization. -/
lemma normalized_excess_mem_unitInterval {h : ℝ → ℝ} {β y : ℝ}
    (hβ : 1 ≤ β) (hy : 0 ≤ y)
    (hRange : ∀ x : ℝ, 0 ≤ x → h x ∈ Set.Icc (0 : ℝ) 1) :
    h (β * y) / β ∈ Set.Icc (0 : ℝ) 1 := by
  have hβpos : 0 < β := lt_of_lt_of_le zero_lt_one hβ
  have h := hRange (β * y) (mul_nonneg hβpos.le hy)
  constructor
  · exact div_nonneg h.1 hβpos.le
  · apply (div_le_iff₀ hβpos).mpr
    simpa only [one_mul] using h.2.trans hβ

end ProphetSecretary.Statistics
