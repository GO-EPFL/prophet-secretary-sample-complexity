import ProphetSecretary.Limiting.HybridCompensator
import ProphetSecretary.Limiting.HybridOutcomes
import ProphetSecretary.Model.TruncatedReward

/-!
# Pathwise hybrid reward bound by reached positive-tail occurrences

The terminal reward is at most the cutoff. Every larger selected offer is
bounded by the cap and supplies one reached occurrence in the corresponding
retained or anonymous count. This is valid for arbitrary causal hybrid rules.
-/
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*}

noncomputable def HybridRule.retainedTailReachIndicator (π : HybridRule n Seed) (i : Fin n) (b : ℝ)
    (v : HybridWorld n Seed) : ℝ :=
  if π.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i ∧ b < v.2.1 i then 1 else 0

lemma HybridRule.reachedPoissonBandCount_Ioi_toReal (π : HybridRule n Seed) (b : ℝ)
    (v : HybridWorld n Seed) :
    (π.reachedPoissonBandCount (Ioi b) v).toReal =
      ∑ j : Fin v.1.1, if π.ReachesPoisson v.2.2.2 v.2.1 v.2.2.1 v.1 j ∧ b < (v.1.2 j).2 then (1 : ℝ) else 0 := by
  unfold HybridRule.reachedPoissonBandCount
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro j _
    simp only [mem_Ioi,and_comm]
    split_ifs <;> simp
  · intro j _
    split_ifs <;> simp

lemma HybridRule.reward_le_cutoff_add_reached_tails (π : HybridRule n Seed) (a b H : ℝ)
    (ha : a ≤ b) (hb : 0 ≤ b) (hH : 0 ≤ H) (v : HybridWorld n Seed)
    (hv : ∀ k, combinedValues v.2.1 v.1.2 k ≤ H) :
    π.realizedReward a v ≤ b+H*((∑ i, π.retainedTailReachIndicator i b v)+
      (π.reachedPoissonBandCount (Ioi b) v).toReal) := by
  have hsum : (∑ k : Fin (n+v.1.1), if (π.asFinitePolicy v.1.1).Reaches v.2.2.2
      (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) k ∧ b < combinedValues v.2.1 v.1.2 k
      then (1 : ℝ) else 0) =
      (∑ i, π.retainedTailReachIndicator i b v)+(π.reachedPoissonBandCount (Ioi b) v).toReal := by
    rw [Fin.sum_univ_add,π.reachedPoissonBandCount_Ioi_toReal]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      simp only [HybridRule.retainedTailReachIndicator,HybridRule.ReachesIndividual,combinedValues,Fin.addCases_left]
      rfl
    · apply Finset.sum_congr rfl
      intro j _
      simp only [HybridRule.ReachesPoisson,combinedValues,Fin.addCases_right]
      rfl
  have hcount : 0 ≤ (∑ i, π.retainedTailReachIndicator i b v)+(π.reachedPoissonBandCount (Ioi b) v).toReal :=
    add_nonneg (Finset.sum_nonneg fun _ _ => by unfold HybridRule.retainedTailReachIndicator; split_ifs <;> norm_num) ENNReal.toReal_nonneg
  change π.reward a v.2.2.2 v.2.1 v.2.2.1 v.1 ≤ _
  by_cases hs : π.HasSelection v.2.2.2 v.2.1 v.2.2.1 v.1
  · rw [HybridRule.reward,if_pos hs]
    have h := (π.asFinitePolicy v.1.1).reward_le_cutoff_add_reached_tail v.2.2.2
      (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) hb hH hv
    rw [hsum] at h
    exact h
  · rw [π.reward_eq_terminal_of_no_selection _ _ _ _ _ hs]
    exact ha.trans (le_add_of_nonneg_right (mul_nonneg hH hcount))

end ProphetSecretary.Limiting
