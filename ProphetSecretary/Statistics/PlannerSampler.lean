import ProphetSecretary.Statistics.PlannerWeights
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Data.ENNReal.BigOperators

/-!
# Subset distribution of the scalar-planner transition

The nonempty subset in `lem:planner-sampler` has product weights. This
finite probability mass function is the law of independent Bernoulli
variables with odds `4 * p i`, conditional on a nonempty outcome.
-/

open scoped BigOperators ENNReal

namespace ProphetSecretary.Statistics

variable {ι : Type*} [DecidableEq ι]

omit [DecidableEq ι] in
lemma plannerWeight_eq_sum_subsets (A : Finset ι) (p : ι → ℝ) :
    plannerWeight A p = ∑ D ∈ A.powerset, ∏ i ∈ D, (4 * p i) := by
  exact Finset.prod_one_add A

lemma plannerNonemptySubset_numerator_sum (A : Finset ι) (p : ι → ℝ) :
    (∑ D ∈ A.powerset.erase ∅, ∏ i ∈ D, (4 * p i)) = plannerWeight A p - 1 := by
  have h := Finset.sum_erase_add A.powerset (fun D => ∏ i ∈ D, (4 * p i))
    (Finset.empty_mem_powerset A)
  rw [← plannerWeight_eq_sum_subsets] at h
  simpa using eq_sub_of_add_eq h

omit [DecidableEq ι] in
lemma plannerNonemptySubset_weight_nonneg (A : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i) {D : Finset ι} (hD : D ⊆ A) :
    0 ≤ (∏ i ∈ D, (4 * p i)) / (plannerWeight A p - 1) := by
  exact div_nonneg (Finset.prod_nonneg (fun i hi => mul_nonneg (by norm_num) (hp i (hD hi))))
    (sub_nonneg.mpr (one_le_plannerWeight A p hp))

lemma plannerNonemptySubset_weight_sum (A : Finset ι) (p : ι → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) :
    (∑ D ∈ A.powerset.erase ∅,
      (∏ i ∈ D, (4 * p i)) / (plannerWeight A p - 1)) = 1 := by
  rw [← Finset.sum_div, plannerNonemptySubset_numerator_sum]
  exact div_self (ne_of_gt (sub_pos.mpr (one_lt_plannerWeight A p hA hp)))

/-- The actual finite probability law of the sampler's first subset. -/
noncomputable def plannerNonemptySubsetPMF (A : Finset ι) (p : ι → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) : PMF (Finset ι) := by
  let w : Finset ι → ℝ≥0∞ := fun D => if D ∈ A.powerset.erase ∅ then
    ENNReal.ofReal ((∏ i ∈ D, (4 * p i)) / (plannerWeight A p - 1)) else 0
  refine PMF.ofFinset w (A.powerset.erase ∅) ?_ ?_
  · change (∑ D ∈ A.powerset.erase ∅, w D) = 1
    simp only [w, Finset.sum_ite_mem, Finset.inter_self]
    rw [← ENNReal.ofReal_sum_of_nonneg]
    · rw [plannerNonemptySubset_weight_sum A p hA hp, ENNReal.ofReal_one]
    · intro D hD
      exact plannerNonemptySubset_weight_nonneg A p (fun i hi => (hp i hi).le)
        (Finset.mem_powerset.mp (Finset.mem_erase.mp hD).2)
  · intro D hD
    simp only [w, if_neg hD]

lemma plannerNonemptySubsetPMF_apply (A : Finset ι) (p : ι → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) (D : Finset ι) :
    plannerNonemptySubsetPMF A p hA hp D =
      if D ∈ A.powerset.erase ∅ then
        ENNReal.ofReal ((∏ i ∈ D, (4 * p i)) / (plannerWeight A p - 1)) else 0 := rfl

omit [DecidableEq ι] in
lemma plannerSubset_numerator_eq (p : ι → ℝ) (D : Finset ι) :
    (∏ i ∈ D, (4 * p i)) = 4 ^ D.card * ∏ i ∈ D, p i := by
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- Bernoulli probability whose odds are `4 * p`. -/
noncomputable def plannerBernoulliProbability (p : ℝ) : ℝ := 4 * p / (1 + 4 * p)

lemma plannerBernoulliProbability_mem_unitInterval {p : ℝ} (hp : 0 ≤ p) :
    plannerBernoulliProbability p ∈ Set.Icc (0 : ℝ) 1 := by
  have hd : 0 < 1 + 4 * p := by positivity
  constructor
  · exact div_nonneg (by positivity) hd.le
  · exact (div_le_iff₀ hd).mpr (by linarith)

lemma one_sub_plannerBernoulliProbability {p : ℝ} (hp : 0 ≤ p) :
    1 - plannerBernoulliProbability p = 1 / (1 + 4 * p) := by
  have hd : 1 + 4 * p ≠ 0 := ne_of_gt (by positivity)
  unfold plannerBernoulliProbability
  field_simp
  ring

omit [DecidableEq ι] in
lemma plannerBernoulliFailure_prod (A : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i) :
    (∏ i ∈ A, (1 - plannerBernoulliProbability (p i))) = 1 / plannerWeight A p := by
  calc
    (∏ i ∈ A, (1 - plannerBernoulliProbability (p i))) =
        ∏ i ∈ A, (1 / (1 + 4 * p i)) := by
      apply Finset.prod_congr rfl
      intro i hi
      exact one_sub_plannerBernoulliProbability (hp i hi)
    _ = 1 / plannerWeight A p := by
      rw [Finset.prod_div_distrib]
      simp [plannerWeight]

lemma plannerBernoulliSubset_mass (A : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i) {D : Finset ι} (hD : D ⊆ A) :
    (∏ i ∈ D, plannerBernoulliProbability (p i)) *
      (∏ i ∈ A \ D, (1 - plannerBernoulliProbability (p i))) =
        (∏ i ∈ D, (4 * p i)) / plannerWeight A p := by
  have hTail : ∀ i ∈ A \ D,
      1 - plannerBernoulliProbability (p i) = 1 / (1 + 4 * p i) := by
    intro i hi
    exact one_sub_plannerBernoulliProbability (hp i (Finset.mem_sdiff.mp hi).1)
  rw [Finset.prod_congr rfl hTail]
  simp only [plannerBernoulliProbability]
  rw [Finset.prod_div_distrib, Finset.prod_div_distrib, Finset.prod_const_one,
    div_mul_div_comm, mul_one]
  rw [mul_comm (∏ i ∈ D, (1 + 4 * p i)), Finset.prod_sdiff hD]
  rfl

/-- Conditioning the product Bernoulli masses on a nonempty subset gives
the sampler's prescribed law. -/
lemma plannerBernoulliSubset_conditional_mass (A : Finset ι) (p : ι → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) {D : Finset ι} (hD : D ⊆ A) :
    ((∏ i ∈ D, plannerBernoulliProbability (p i)) *
      (∏ i ∈ A \ D, (1 - plannerBernoulliProbability (p i)))) /
      (1 - ∏ i ∈ A, (1 - plannerBernoulliProbability (p i))) =
        (∏ i ∈ D, (4 * p i)) / (plannerWeight A p - 1) := by
  rw [plannerBernoulliSubset_mass A p (fun i hi => (hp i hi).le) hD,
    plannerBernoulliFailure_prod A p (fun i hi => (hp i hi).le)]
  have hβ : plannerWeight A p ≠ 0 := ne_of_gt
    (plannerWeight_pos A p (fun i hi => (hp i hi).le))
  have hβ1 : plannerWeight A p - 1 ≠ 0 :=
    ne_of_gt (sub_pos.mpr (one_lt_plannerWeight A p hA hp))
  field_simp

/-- The mass of an independent Bernoulli sequence whose first success is
at index `i`, before conditioning on at least one success. -/
noncomputable def plannerFirstSuccessMass (r : ℕ → ℝ) (i : ℕ) : ℝ :=
  r i * ∏ j ∈ Finset.range i, (1 - r j)

lemma plannerFirstSuccessMass_sum (r : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, plannerFirstSuccessMass r i) =
      1 - ∏ i ∈ Finset.range n, (1 - r i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.prod_range_succ]
    unfold plannerFirstSuccessMass
    ring

lemma plannerFirstSuccessMass_nonneg (r : ℕ → ℝ) (n : ℕ)
    (hr : ∀ i < n, r i ∈ Set.Icc (0 : ℝ) 1) {i : ℕ} (hi : i < n) :
    0 ≤ plannerFirstSuccessMass r i := by
  unfold plannerFirstSuccessMass
  exact mul_nonneg (hr i hi).1 (Finset.prod_nonneg (fun j hj =>
    sub_nonneg.mpr (hr j (lt_trans (Finset.mem_range.mp hj) hi)).2))

/-- The first-success categorical probabilities sum to one. -/
lemma plannerFirstSuccess_probability_sum (r : ℕ → ℝ) (n : ℕ)
    (h : 0 < 1 - ∏ i ∈ Finset.range n, (1 - r i)) :
    (∑ i ∈ Finset.range n, plannerFirstSuccessMass r i /
      (1 - ∏ j ∈ Finset.range n, (1 - r j))) = 1 := by
  rw [← Finset.sum_div, plannerFirstSuccessMass_sum]
  exact div_self (ne_of_gt h)

lemma plannerBernoulli_nonempty_probability_pos (n : ℕ) (p : ℕ → ℝ)
    (hn : 0 < n) (hp : ∀ i < n, 0 < p i) :
    0 < 1 - ∏ i ∈ Finset.range n, (1 - plannerBernoulliProbability (p i)) := by
  have hβ : 1 < plannerWeight (Finset.range n) p :=
    one_lt_plannerWeight _ _ (Finset.nonempty_range_iff.mpr hn.ne')
      (fun i hi => hp i (Finset.mem_range.mp hi))
  rw [plannerBernoulliFailure_prod _ _ (fun i hi => (hp i (Finset.mem_range.mp hi)).le)]
  apply sub_pos.mpr
  exact (div_lt_iff₀ (by linarith : 0 < plannerWeight (Finset.range n) p)).mpr
    (by simpa using hβ)

/-- Summing the sampler's contributions indexed by `D \ {i} ⊆ B` gives
the planner density after cancellation of the maximum-density and
uniform-identity factors. -/
lemma plannerKernelDensity_expansion (A : Finset ι) (p : ι → ℝ)
    (i : ι) (B : Finset ι) (s : ℝ) :
    (∑ C ∈ B.powerset, (4 * p i / (plannerWeight A p - 1)) *
      ((∏ j ∈ C, (4 * p j)) * s ^ B.card *
        (1 - s) ^ ((A.erase i).card - B.card))) =
      plannerKernelDensity A p i B s := by
  rw [plannerKernelDensity, plannerWeight_eq_sum_subsets B p]
  simp only [Finset.mul_sum, Finset.sum_mul]

end ProphetSecretary.Statistics
