import ProphetSecretary.Model.LearnerMixture
import ProphetSecretary.Model.UniformIdentity

open MeasureTheory
open scoped ENNReal

namespace ProphetSecretary.Model.Learner

variable {n k : ℕ}

theorem noTraining_extendedExpectedReward (π : RandomizedPolicy n) (P : Instance n) :
    ((noTraining (k := k) π).randomizedPolicy P).extendedExpectedReward P =
      π.extendedExpectedReward P := by
  exact (noTrainingWorldMap_measurePreserving (k := k) π P).lintegral_comp
    π.measurable_realizedReward.ennreal_ofReal

noncomputable def reciprocalWeight (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal (1 / (k : ℝ))

noncomputable def retainedWeight (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 - 1 / (k : ℝ))

theorem reciprocalWeight_pos (hk : 1 ≤ k) : 0 < reciprocalWeight k := by
  unfold reciprocalWeight
  apply ENNReal.ofReal_pos.mpr
  exact one_div_pos.mpr (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk))

theorem retainedWeight_add_reciprocalWeight (hk : 1 ≤ k) :
    retainedWeight k + reciprocalWeight k = 1 := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hkle : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hdiv : 1 / (k : ℝ) ≤ 1 := (div_le_one hkpos).mpr hkle
  rw [retainedWeight, reciprocalWeight, ← ENNReal.ofReal_add (sub_nonneg.mpr hdiv)
    (le_of_lt (one_div_pos.mpr hkpos))]
  norm_num

theorem reciprocalWeight_toReal (hk : 1 ≤ k) :
    (reciprocalWeight k).toReal = 1 / (k : ℝ) := by
  apply ENNReal.toReal_ofReal
  exact div_nonneg zero_le_one
    (by exact_mod_cast (Nat.zero_le 1 |>.trans hk))

theorem retainedWeight_toReal (hk : 1 ≤ k) :
    (retainedWeight k).toReal = 1 - 1 / (k : ℝ) := by
  apply ENNReal.toReal_ofReal
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  exact sub_nonneg.mpr ((div_le_one hkpos).mpr (by exact_mod_cast hk))

/-- Preserve the original learner's hard budget and add a positive-probability
uniform identity branch that never requests a training sample. -/
noncomputable def infiniteMeanRepair (L : Learner n k) (hn : 0 < n) (hk : 1 ≤ k) :
    Learner n k :=
  L.mix (noTraining (RandomizedPolicy.uniformIdentity hn))
    (retainedWeight k) (reciprocalWeight k) (retainedWeight_add_reciprocalWeight hk)

theorem infiniteMeanRepair_hardBudget (L : Learner n k) (hn : 0 < n) (hk : 1 ≤ k)
    (r : (L.infiniteMeanRepair hn hk).Seed) (y : Reservoir n k) (i : Fin n) :
    requests (trainingTranscript (L.infiniteMeanRepair hn hk).request r y) i ≤ k :=
  (L.infiniteMeanRepair hn hk).hard_budget r y i

theorem infiniteMeanRepair_uniformBranch_requests (L : Learner n k) (hn : 0 < n)
    (hk : 1 ≤ k) (r : Fin n) (y : Reservoir n k) (i : Fin n) :
    requests (trainingTranscript (L.infiniteMeanRepair hn hk).request (.inr r) y) i = 0 := by
  change requests (trainingTranscript
    (L.mix (noTraining (RandomizedPolicy.uniformIdentity hn))
      (retainedWeight k) (reciprocalWeight k)
      (retainedWeight_add_reciprocalWeight hk)).request (.inr r) y) i = 0
  rw [mix_transcript_inr, noTraining_transcript]
  rfl

/-- At budget one the uniform identity strategy alone is a lawful choice and
uses zero samples on every raw outcome. -/
theorem budgetOne_noTraining (hn : 0 < n) (r : Fin n) (y : Reservoir n 1)
    (i : Fin n) :
    requests (trainingTranscript (noTraining (k := 1)
      (RandomizedPolicy.uniformIdentity hn)).request r y) i = 0 :=
  noTraining_requests (RandomizedPolicy.uniformIdentity hn) r y i

theorem noTraining_uniform_extendedExpectedReward_eq_top (P : Instance n) (hn : 0 < n)
    (hP : P.extendedExpectedMaximum = ⊤) :
    ((noTraining (k := k) (RandomizedPolicy.uniformIdentity hn)).randomizedPolicy P).extendedExpectedReward
      P = ⊤ := by
  rw [noTraining_extendedExpectedReward]
  exact RandomizedPolicy.uniformIdentity_extendedExpectedReward_eq_top P hn hP

theorem finite_mixture_deficit {A B M : ℝ} (hk : 1 ≤ k) (hA : A ≤ M) (hB : 0 ≤ B) :
    A - ((1 - 1 / (k : ℝ)) * A + (1 / (k : ℝ)) * B) ≤ M / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk)
  have hp : 0 ≤ 1 / (k : ℝ) := div_nonneg zero_le_one hk0.le
  have h := mul_le_mul_of_nonneg_left hA hp
  have hb := mul_nonneg hp hB
  calc
    _ ≤ (1 / (k : ℝ)) * M := by nlinarith
    _ = M / k := by ring

end ProphetSecretary.Model.Learner
