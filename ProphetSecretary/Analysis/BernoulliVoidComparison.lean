import ProphetSecretary.Analysis.LocalExpQuadratic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite Bernoulli and Poisson void probabilities

For arbitrary probabilities, the Poisson void probability exceeds the
Bernoulli void probability by at most the sum of squared probabilities.
The bound includes empty families and has coefficient one independent of size.
-/

open scoped BigOperators

namespace ProphetSecretary.Analysis

lemma product_difference_le_sum {ι : Type*} (s : Finset ι) (f g c : ι → ℝ)
    (hg0 : ∀ i, 0 ≤ g i) (hgf : ∀ i, g i ≤ f i) (hf1 : ∀ i, f i ≤ 1)
    (hGap : ∀ i, f i-g i ≤ c i) :
    (∏ i ∈ s, f i)-(∏ i ∈ s, g i) ≤ ∑ i ∈ s, c i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hProd : (∏ j ∈ s, g j) ≤ ∏ j ∈ s, f j :=
      Finset.prod_le_prod (fun j _ => hg0 j) (fun j _ => hgf j)
    have hG1 : (∏ j ∈ s, g j) ≤ 1 :=
      Finset.prod_le_one (fun j _ => hg0 j) (fun j _ => (hgf j).trans (hf1 j))
    have hFirst : f i*((∏ j ∈ s, f j)-(∏ j ∈ s, g j)) ≤
        (∏ j ∈ s, f j)-(∏ j ∈ s, g j) :=
      mul_le_of_le_one_left (sub_nonneg.mpr hProd) (hf1 i)
    have hSecond : (f i-g i)*(∏ j ∈ s, g j) ≤ c i :=
      (mul_le_of_le_one_right (sub_nonneg.mpr (hgf i)) hG1).trans (hGap i)
    rw [Finset.prod_insert hi,Finset.prod_insert hi,Finset.sum_insert hi]
    nlinarith only [hFirst,hSecond,ih]

theorem bernoulli_void_comparison {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1) :
    0 ≤ Real.exp (-(∑ i, p i))-(∏ i, (1-p i)) ∧
      Real.exp (-(∑ i, p i))-(∏ i, (1-p i)) ≤ ∑ i, (p i)^2 := by
  classical
  have hgf (i : ι) : 1-p i ≤ Real.exp (-p i) := by
    linarith only [Real.add_one_le_exp (-p i)]
  have hExp (i : ι) : Real.exp (-p i) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hp0 i))
  have hGap (i : ι) : Real.exp (-p i)-(1-p i) ≤ (p i)^2 := by
    have hs : |-p i| ≤ 1 := by rw [abs_neg,abs_of_nonneg (hp0 i)]; exact hp1 i
    have h := exp_le_one_add_add_sq hs
    nlinarith only [h]
  have hEq : (∏ i, Real.exp (-p i)) = Real.exp (-(∑ i, p i)) := by
    rw [← Real.exp_sum,Finset.sum_neg_distrib]
  constructor
  · rw [← hEq]
    exact sub_nonneg.mpr (Finset.prod_le_prod (fun i _ => sub_nonneg.mpr (hp1 i)) (fun i _ => hgf i))
  · rw [← hEq]
    exact product_difference_le_sum Finset.univ (fun i => Real.exp (-p i)) (fun i => 1-p i)
      (fun i => (p i)^2) (fun i => sub_nonneg.mpr (hp1 i)) hgf hExp hGap

end ProphetSecretary.Analysis
