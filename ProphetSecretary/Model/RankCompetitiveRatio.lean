import ProphetSecretary.Model.ClockToRankLaw
import ProphetSecretary.Model.RankToClockLaw
import ProphetSecretary.Model.CompetitiveBasic

/-!
# The competitive benchmark is the same for rank and clock observations

Both directions are actual causal policy constructions with independent
auxiliary randomness. Consequently the per-instance optimal reward, and then
the global infimum over all finite positive finite-mean instances, agree.
This justifies the random-order representation in the paper's preliminaries.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def optimalRankReward (P : Instance n) : ℝ :=
  sSup {v : ℝ | ∃ π : RandomizedRankPolicy n, v = π.expectedReward P}

theorem clock_rank_reward_values_eq (P : Instance n) :
    {v : ℝ | ∃ π : RandomizedPolicy n, v = π.expectedReward P} =
      {v : ℝ | ∃ π : RandomizedRankPolicy n, v = π.expectedReward P} := by
  ext v
  constructor
  · rintro ⟨π,hv⟩
    exact ⟨π.clockToRank,hv.trans (π.clockToRank_expectedReward P).symm⟩
  · rintro ⟨π,hv⟩
    exact ⟨π.rankToClock,hv.trans (π.rankToClock_expectedReward P).symm⟩

theorem optimalRankReward_eq (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) :
    optimalRankReward P = optimalScalarValue P 1 0 := by
  have hSet : {v : ℝ | ∃ π : RandomizedPolicy n, v = π.scalarObjective P 1 0} =
      {v : ℝ | ∃ π : RandomizedPolicy n, v = π.expectedReward P} := by
    ext v
    simp only [RandomizedPolicy.scalarObjective_eq _ P hP,one_mul,zero_mul,add_zero]
  rw [optimalRankReward,optimalScalarValue,hSet,clock_rank_reward_values_eq P]

noncomputable def optimalRankCompetitiveRatio : ℝ :=
  sInf {r : ℝ | ∃ (n : ℕ) (P : Instance n), P.HasPositiveFiniteMaximum ∧
    r = optimalRankReward P/P.expectedMaximum}

theorem optimalRankCompetitiveRatio_eq : optimalRankCompetitiveRatio = optimalCompetitiveRatio := by
  unfold optimalRankCompetitiveRatio optimalCompetitiveRatio
  congr 1
  ext r
  constructor
  · rintro ⟨n,P,hP,hr⟩
    exact ⟨n,P,hP,by simpa only [optimalRankReward_eq P hP.1] using hr⟩
  · rintro ⟨n,P,hP,hr⟩
    exact ⟨n,P,hP,by simpa only [optimalRankReward_eq P hP.1] using hr⟩

end ProphetSecretary.Model
