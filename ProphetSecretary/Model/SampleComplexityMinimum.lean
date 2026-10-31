import ProphetSecretary.Model.Learner
import Mathlib.Order.Lattice.Nat

/-!
# The least feasible hard sample budget is attained when finite

The extended-natural definition agrees with the natural minimum whenever
one feasible budget exists. Thus its natural value has the original
all-instance guarantee, rather than merely being an infimum of budgets.
-/

open Set
namespace ProphetSecretary.Model

lemma sampleComplexity_eq_nat_sInf {eps : ℝ} (h : ∃ k : ℕ, FeasibleBudget eps k) :
    sampleComplexity eps=((sInf {k : ℕ | FeasibleBudget eps k} : ℕ) : ℕ∞) := by
  have hMin : FeasibleBudget eps (sInf {k : ℕ | FeasibleBudget eps k}) := Nat.sInf_mem h
  apply le_antisymm
  · exact sInf_le ⟨_,hMin,rfl⟩
  · apply le_sInf
    rintro b ⟨k,hk,rfl⟩
    exact_mod_cast (Nat.sInf_le (s:={j : ℕ | FeasibleBudget eps j}) hk)

lemma sampleComplexity_ne_top {eps : ℝ} (h : ∃ k : ℕ, FeasibleBudget eps k) :
    sampleComplexity eps≠⊤ := by
  rw [sampleComplexity_eq_nat_sInf h]
  exact ENat.coe_ne_top _

lemma sampleComplexity_toNat_feasible {eps : ℝ} (h : ∃ k : ℕ, FeasibleBudget eps k) :
    FeasibleBudget eps (sampleComplexity eps).toNat := by
  rw [sampleComplexity_eq_nat_sInf h,ENat.toNat_coe]
  exact Nat.sInf_mem h

lemma sampleComplexity_toNat_le {eps : ℝ} {k : ℕ} (h : FeasibleBudget eps k) :
    (sampleComplexity eps).toNat≤k := by
  rw [sampleComplexity_eq_nat_sInf ⟨k,h⟩,ENat.toNat_coe]
  exact Nat.sInf_le (s:={j : ℕ | FeasibleBudget eps j}) h

end ProphetSecretary.Model
