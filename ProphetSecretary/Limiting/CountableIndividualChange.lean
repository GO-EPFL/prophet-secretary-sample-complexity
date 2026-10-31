import ProphetSecretary.Limiting.CountableRemainingState
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Changing one individual law in a full limiting instance

The original identity and independent clock remain present. A bounded
replacement probability law adds at most one to every positive-level tail
mass, so all countable-instance support and local-finiteness obligations hold.
-/

open MeasureTheory Set
open scoped Classical ENNReal

namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def updateIndividual (B : CountableInstance) (i : ℕ) (q : ProbabilityMeasure ℝ)
    (hq : ∀ᵐ x ∂(q : Measure ℝ), x ∈ Icc (0 : ℝ) B.cap) : CountableInstance where
  cap := B.cap
  terminal := B.terminal
  terminal_le_cap := B.terminal_le_cap
  individuals := Function.update B.individuals i q
  individual_supported k := by
    by_cases hki : k=i
    · subst k
      simpa only [Function.update_self] using hq
    · simpa only [Function.update_of_ne hki] using B.individual_supported k
  intensity := B.intensity
  intensity_supported := B.intensity_supported
  individual_tail_finite b hb := by
    have hPoint (k : ℕ) : ((Function.update B.individuals i q) k : Measure ℝ) (Ioi b) ≤
        (B.individuals k : Measure ℝ) (Ioi b)+(if k=i then (1 : ℝ≥0∞) else 0) := by
      by_cases hki : k=i
      · subst k
        rw [Function.update_self,if_pos rfl]
        exact (prob_le_one : (q : Measure ℝ) (Ioi b) ≤ 1).trans (le_add_of_nonneg_left bot_le)
      · simpa only [Function.update_of_ne hki,if_neg hki,add_zero] using
          (le_refl ((B.individuals k : Measure ℝ) (Ioi b)))
    calc
      _ ≤ ∑' k, ((B.individuals k : Measure ℝ) (Ioi b)+(if k=i then (1 : ℝ≥0∞) else 0)) :=
        ENNReal.tsum_le_tsum hPoint
      _ = (∑' k, (B.individuals k : Measure ℝ) (Ioi b))+1 := by
        rw [ENNReal.tsum_add]
        simp only [tsum_ite_eq]
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨B.individual_tail_finite b hb,by norm_num⟩
  intensity_tail_finite := B.intensity_tail_finite

lemma updateIndividual_same (B : CountableInstance) (i : ℕ) :
    B.updateIndividual i (B.individuals i) (B.individual_supported i)=B := by
  apply CountableInstance.ext_data
  · rfl
  · rfl
  · funext k
    change Function.update B.individuals i (B.individuals i) k=B.individuals k
    by_cases hki : k=i
    · subst k
      simp only [Function.update_self]
    · simp only [Function.update_of_ne hki]
  · rfl

end ProphetSecretary.Limiting.CountableInstance
