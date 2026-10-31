import ProphetSecretary.Limiting.BoundarySingleExcessContradiction
import ProphetSecretary.Limiting.CountableExcessConcentration

/-!
# No bounded countable reward-critical instance with normalized maximum

Actual clipping forces equality of total and maximum excess. Independence and
Poisson count moments concentrate all excess on one individual and remove the
anonymous upper tail. The constructed cap-policy lift and strict reach then
contradict the actual unrestricted reward-only supremum.
-/

open MeasureTheory Set
open scoped NNReal Classical
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

theorem not_normalized_reward_critical (B : CountableInstance) (hM : B.expectedMaximum=1) :
    B.optimalScalarValue 1 0≠optimalCompetitiveRatio := by
  intro hV
  have hGap : B.scalarGap 1 0=0 := by
    simp only [scalarGap,hM,hV,add_zero,mul_one,sub_self]
  have hZero := B.terminal_eq_zero_of_gap_nonpositive zero_lt_one le_rfl hGap.le
  let K : ℝ≥0 := ⟨optimalCompetitiveRatio,optimalCompetitiveRatio_nonnegative⟩
  have hK : 0<K := (by norm_num : (0:ℝ)<1/2).trans_le half_le_optimalCompetitiveRatio
  rcases B.boundary_clipped_identities hZero hM hV K hK rfl with ⟨_hBounds,he,_hNew,_hSum,hEq⟩
  obtain ⟨hCloud,j,_hOthers,hSingle,_hIndividualPositive⟩ :=
    B.single_individual_capExcess_of_prophet_equality hZero K hK he hEq
  exact B.reward_critical_singleExcess_contradiction hZero hM hV K hK rfl j hCloud hSingle

end ProphetSecretary.Limiting.CountableInstance
