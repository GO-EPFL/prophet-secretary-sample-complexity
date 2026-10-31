import ProphetSecretary.Model.OuterRetention
import ProphetSecretary.Analysis.BernoulliVoidComparison
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Fixed-cutoff tail count and the tagged void probability

The probability that no tagged offer exceeds the cutoff is an actual product
of marginal failure probabilities. Positive retained offers form a subset of
those exceedances. This yields the logarithmic comparison in `upouter:tailcount`,
including zero atoms and the empty family.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Model.Instance
variable {n : ℕ}

noncomputable def taggedExceedanceProbability (P : Instance n) (t : ℝ × ℝ) (i : Fin n) : ℝ :=
  ((P.law i).prod uniformClock).real {z | taggedAbove t z}

noncomputable def taggedVoidProbability (P : Instance n) (t : ℝ × ℝ) : ℝ :=
  ∏ i : Fin n, (1-P.taggedExceedanceProbability t i)

lemma taggedExceedanceProbability_mem_unit (P : Instance n) (t : ℝ × ℝ) (i : Fin n) :
    P.taggedExceedanceProbability t i∈Icc (0:ℝ) 1 := ⟨measureReal_nonneg,measureReal_le_one⟩

lemma taggedVoidProbability_mem_unit (P : Instance n) (t : ℝ × ℝ) :
    P.taggedVoidProbability t∈Icc (0:ℝ) 1 := by
  refine ⟨Finset.prod_nonneg (fun i _ => sub_nonneg.mpr (P.taggedExceedanceProbability_mem_unit t i).2),?_⟩
  exact Finset.prod_le_one (fun i _ => sub_nonneg.mpr (P.taggedExceedanceProbability_mem_unit t i).2)
    (fun i _ => sub_le_self 1 (P.taggedExceedanceProbability_mem_unit t i).1)

lemma retainedAtTag_positiveCount_le_exceedances (P : Instance n) (t : ℝ × ℝ) :
    (P.retainedAtTag t).positiveCount≤∑ i, P.taggedExceedanceProbability t i := by
  unfold positiveCount tailCount
  apply Finset.sum_le_sum
  intro i _
  change (((P.law i).prod uniformClock).map (retainAboveTag t)).real (Ioi 0)≤_
  rw [map_measureReal_apply (measurable_retainAboveTag_fixed t) measurableSet_Ioi]
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro z hz
  by_contra hNot
  change ¬taggedAbove t z at hNot
  simp only [Set.mem_preimage,Set.mem_Ioi,retainAboveTag,if_neg hNot] at hz
  exact (lt_irrefl (0:ℝ)) hz

/-- Fixed-cutoff logarithmic comparison in `upouter:tailcount`. -/
theorem retainedAtTag_positiveCount_le_neg_log (P : Instance n) (t : ℝ × ℝ)
    (hQ : 0<P.taggedVoidProbability t) :
    (P.retainedAtTag t).positiveCount≤-Real.log (P.taggedVoidProbability t) := by
  have hVoid := (ProphetSecretary.Analysis.bernoulli_void_comparison (P.taggedExceedanceProbability t)
    (fun i => (P.taggedExceedanceProbability_mem_unit t i).1)
    (fun i => (P.taggedExceedanceProbability_mem_unit t i).2)).1
  have hExp : P.taggedVoidProbability t≤Real.exp (-(∑ i, P.taggedExceedanceProbability t i)) := by
    unfold taggedVoidProbability
    linarith only [hVoid]
  have hLog := (Real.log_le_iff_le_exp hQ).mpr hExp
  have hRet := P.retainedAtTag_positiveCount_le_exceedances t
  linarith only [hLog,hRet]

lemma retainedAtTag_positiveCount_le_two_log (P : Instance n) (t : ℝ × ℝ) {m : ℕ} (hm : 1≤m)
    (hQ : 1/(m:ℝ)^2≤P.taggedVoidProbability t) :
    (P.retainedAtTag t).positiveCount≤2*Real.log (m:ℝ) := by
  have hmR : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hSmall : (0:ℝ)<1/(m:ℝ)^2 := by positivity
  have hLog := Real.log_le_log hSmall hQ
  rw [one_div,Real.log_inv,Real.log_pow] at hLog
  norm_num only [Nat.cast_ofNat] at hLog
  exact (P.retainedAtTag_positiveCount_le_neg_log t (hSmall.trans_le hQ)).trans (by linarith only [hLog])

end ProphetSecretary.Model.Instance
