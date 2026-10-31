import ProphetSecretary.Model.InfiniteMeanLearner
import ProphetSecretary.Model.LearnerMixtureExpectations

open MeasureTheory
open scoped ENNReal

namespace ProphetSecretary.Model.Learner

variable {n k : ℕ}

/-- The finite-mean reward of the actual hard-budget mixture. -/
theorem infiniteMeanRepair_expectedReward (L : Learner n k) (hn : 0 < n) (hk : 1 ≤ k)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) :
    (L.infiniteMeanRepair hn hk).expectedReward P =
      (1 - 1 / (k : ℝ)) * L.expectedReward P +
        (1 / (k : ℝ)) * (RandomizedPolicy.uniformIdentity hn).expectedReward P := by
  change (L.mix (noTraining (RandomizedPolicy.uniformIdentity hn))
    (retainedWeight k) (reciprocalWeight k)
    (retainedWeight_add_reciprocalWeight hk)).expectedReward P = _
  rw [mix_expectedReward L _ _ _ _ P hP, retainedWeight_toReal hk,
    reciprocalWeight_toReal hk, noTraining_expectedReward]

/-- The repair loses at most `M/k` on every integrable nonnegative instance,
including the zero benchmark. -/
theorem infiniteMeanRepair_deficit (L : Learner n k) (hn : 0 < n) (hk : 1 ≤ k)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) :
    L.expectedReward P - (L.infiniteMeanRepair hn hk).expectedReward P ≤
      P.expectedMaximum / k := by
  rw [infiniteMeanRepair_expectedReward L hn hk P hP]
  exact finite_mixture_deficit hk
    ((L.randomizedPolicy P).expectedReward_le_maximum P hP)
    ((RandomizedPolicy.uniformIdentity hn).expectedReward_nonnegative P)

/-- A guarantee for the original learner degrades by at most `1/k`. -/
theorem infiniteMeanRepair_guarantees (L : Learner n k) (hn : 0 < n) (hk : 1 ≤ k)
    {rho : ℝ} (hL : L.Guarantees rho) :
    (L.infiniteMeanRepair hn hk).Guarantees (rho - 1 / (k : ℝ)) := by
  intro P hP
  have h := infiniteMeanRepair_deficit L hn hk P hP.1
  have hg := hL P hP
  have he : P.expectedMaximum / k = (1 / (k : ℝ)) * P.expectedMaximum := by ring
  rw [he] at h
  nlinarith

/-- A positive-probability uniform identity branch gives infinite expected
reward whenever the nonnegative prophet benchmark has infinite expectation. -/
theorem infiniteMeanRepair_extendedExpectedReward_eq_top (L : Learner n k) (hn : 0 < n)
    (hk : 1 ≤ k) (P : Instance n) (hP : P.extendedExpectedMaximum = ⊤) :
    (L.infiniteMeanRepair hn hk).extendedExpectedReward P = ⊤ := by
  change (L.mix (noTraining (RandomizedPolicy.uniformIdentity hn))
    (retainedWeight k) (reciprocalWeight k)
    (retainedWeight_add_reciprocalWeight hk)).extendedExpectedReward P = ⊤
  rw [mix_extendedExpectedReward]
  have hu : (noTraining (k := k) (RandomizedPolicy.uniformIdentity hn)).extendedExpectedReward P = ⊤ :=
    noTraining_uniform_extendedExpectedReward_eq_top P hn hP
  rw [hu]
  simp [ne_of_gt (reciprocalWeight_pos hk)]

/-- At `k=1`, the mixture has the same expected reward as the strategy that
performs no training at all. -/
theorem infiniteMeanRepair_one_expectedReward (L : Learner n 1) (hn : 0 < n)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) :
    (L.infiniteMeanRepair hn (by omega)).expectedReward P =
      (noTraining (k := 1) (RandomizedPolicy.uniformIdentity hn)).expectedReward P := by
  rw [infiniteMeanRepair_expectedReward L hn (by omega) P hP, noTraining_expectedReward]
  norm_num

theorem infiniteMeanRepair_one_extendedExpectedReward (L : Learner n 1) (hn : 0 < n)
    (P : Instance n) :
    (L.infiniteMeanRepair hn (by omega)).extendedExpectedReward P =
      (noTraining (k := 1) (RandomizedPolicy.uniformIdentity hn)).extendedExpectedReward P := by
  change (L.mix (noTraining (RandomizedPolicy.uniformIdentity hn))
    (retainedWeight 1) (reciprocalWeight 1)
    (retainedWeight_add_reciprocalWeight (by omega))).extendedExpectedReward P = _
  rw [mix_extendedExpectedReward]
  norm_num [retainedWeight, reciprocalWeight]

/-- One instance-independent lawful learner handles both finite and infinite
means using the original hard budget, on every raw training outcome. -/
theorem exists_infiniteMeanRepair (L : Learner n k) (hn : 0 < n) (hk : 1 ≤ k) :
    ∃ R : Learner n k,
      R.policy.IsMeasurable ∧
      (∀ (r : R.Seed) (y : Reservoir n k) (i : Fin n),
        requests (trainingTranscript R.request r y) i ≤ k) ∧
      (∀ P : Instance n, Integrable Instance.maximum P.valuesLaw →
        L.expectedReward P - R.expectedReward P ≤ P.expectedMaximum / k) ∧
      (∀ P : Instance n, P.extendedExpectedMaximum = ⊤ →
        R.extendedExpectedReward P = ⊤) := by
  exact ⟨L.infiniteMeanRepair hn hk, (L.infiniteMeanRepair hn hk).policy_isMeasurable,
    infiniteMeanRepair_hardBudget L hn hk, infiniteMeanRepair_deficit L hn hk,
    fun P hP => infiniteMeanRepair_extendedExpectedReward_eq_top L hn hk P hP⟩

/-- The endpoint budget can avoid the original learner's training entirely,
including on seeds of probability zero. -/
theorem exists_budgetOne_noTraining_repair (L : Learner n 1) (hn : 0 < n) :
    ∃ R : Learner n 1,
      (∀ (r : R.Seed) (y : Reservoir n 1) (i : Fin n),
        requests (trainingTranscript R.request r y) i = 0) ∧
      (∀ P : Instance n, Integrable Instance.maximum P.valuesLaw →
        L.expectedReward P - R.expectedReward P ≤ P.expectedMaximum) ∧
      (∀ P : Instance n, P.extendedExpectedMaximum = ⊤ →
        R.extendedExpectedReward P = ⊤) := by
  refine ⟨noTraining (RandomizedPolicy.uniformIdentity hn),
    noTraining_requests (RandomizedPolicy.uniformIdentity hn), ?_, ?_⟩
  · intro P hP
    rw [noTraining_expectedReward]
    have hL := (L.randomizedPolicy P).expectedReward_le_maximum P hP
    have hU := (RandomizedPolicy.uniformIdentity hn).expectedReward_nonnegative P
    change L.expectedReward P ≤ P.expectedMaximum at hL
    linarith
  · intro P hP
    exact noTraining_uniform_extendedExpectedReward_eq_top P hn hP

/-- The repair extends to all finite dimensions, retaining the original
learner when the identity set is empty. -/
theorem exists_infiniteMeanRepair_any_size (L : Learner n k) (hk : 1 ≤ k) :
    ∃ R : Learner n k,
      R.policy.IsMeasurable ∧
      (∀ (r : R.Seed) (y : Reservoir n k) (i : Fin n),
        requests (trainingTranscript R.request r y) i ≤ k) ∧
      (∀ P : Instance n, Integrable Instance.maximum P.valuesLaw →
        L.expectedReward P - R.expectedReward P ≤ P.expectedMaximum / k) ∧
      (∀ P : Instance n, P.extendedExpectedMaximum = ⊤ →
        R.extendedExpectedReward P = ⊤) := by
  by_cases hn : 0 < n
  · exact exists_infiniteMeanRepair L hn hk
  · refine ⟨L, L.policy_isMeasurable, L.hard_budget, ?_, ?_⟩
    · intro P _
      rw [sub_self]
      exact div_nonneg P.expectedMaximum_nonnegative (Nat.cast_nonneg k)
    · intro P hP
      exact (hn (P.size_pos_of_extendedExpectedMaximum_eq_top hP)).elim

/-- The zero-training endpoint also covers the empty identity set. -/
theorem exists_budgetOne_noTraining_repair_any_size (L : Learner n 1) :
    ∃ R : Learner n 1,
      (∀ (r : R.Seed) (y : Reservoir n 1) (i : Fin n),
        requests (trainingTranscript R.request r y) i = 0) ∧
      (∀ P : Instance n, Integrable Instance.maximum P.valuesLaw →
        L.expectedReward P - R.expectedReward P ≤ P.expectedMaximum) ∧
      (∀ P : Instance n, P.extendedExpectedMaximum = ⊤ →
        R.extendedExpectedReward P = ⊤) := by
  by_cases hn : 0 < n
  · exact exists_budgetOne_noTraining_repair L hn
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    refine ⟨L, ?_, ?_, ?_⟩
    · intro _ _ i
      exact Fin.elim0 i
    · intro P _
      rw [sub_self]
      exact P.expectedMaximum_nonnegative
    · intro P hP
      exact (hn (P.size_pos_of_extendedExpectedMaximum_eq_top hP)).elim

end ProphetSecretary.Model.Learner
