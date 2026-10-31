import ProphetSecretary.Probability.ScoreArrayMask
import ProphetSecretary.Probability.NormalizedScoreResponse
import ProphetSecretary.Model.UnitCanonicalPolicy

/-!
# Removing exceptional initial scalar weights from score limits

At every exceptional index the perturbation is zero. Eventually the weights
agree, so both canonical policies and their complete-score products agree.
The construction preserves the full canonical policy class and its actual
independent seed law.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting
open ProphetSecretary.Model ProphetSecretary.Probability

theorem masked_finiteCanonical_score_limits
    (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {H δ : ℝ}
    (hδ : 0<δ) (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H)
    (ls lams : ℕ → ℝ) (hLs : ∀ m, ls m∈Icc δ (1-δ)) (hLams : ∀ m, lams m∈Icc (0:ℝ) 1)
    (hEq : ls=ᶠ[atTop] lams) (score : ∀ m, Fin (sizes m) → ℝ → ℝ) {targetR targetT : ℝ}
    (hCore :
      let ρ := fun m => (P m).valuePolicy ((P m).integrable_maximum_of_bounded (hCap m))
        (hδ.le.trans (hLs m).1) (show 0≤1-ls m from by linarith only [(hLs m).2,hδ.le])
      Tendsto (fun m => (ρ m).expectedRewardScore (P m) (score m)) atTop (𝓝 targetR) ∧
      Tendsto (fun m => (ρ m).expectedDurationScore (P m) (score m)) atTop (𝓝 targetT)) :
    let masked := maskedArrayScore (fun m => ls m=lams m) score
    let ρ := fun m => (P m).unitCanonicalPolicy ((P m).integrable_maximum_of_bounded (hCap m))
      (lams m) (hLams m)
    Tendsto (fun m => (ρ m).expectedRewardScore (P m) (masked m)) atTop (𝓝 targetR) ∧
    Tendsto (fun m => (ρ m).expectedDurationScore (P m) (masked m)) atTop (𝓝 targetT) := by
  have hPolicy (m) (he : ls m=lams m) :
      (P m).valuePolicy ((P m).integrable_maximum_of_bounded (hCap m))
        (hδ.le.trans (hLs m).1) (show 0≤1-ls m from by linarith only [(hLs m).2,hδ.le])=
      (P m).unitCanonicalPolicy ((P m).integrable_maximum_of_bounded (hCap m))
        (lams m) (hLams m) := by
    have hPos : 0<lams m := (hδ.trans_le (hLs m).1).trans_eq he
    apply Eq.trans ?_ ((P m).unitCanonicalPolicy_eq_valuePolicy
      ((P m).integrable_maximum_of_bounded (hCap m)) (hLams m) hPos).symm
    simp only [he]
  have hMask (m) (he : ls m=lams m) : maskedArrayScore (fun m => ls m=lams m) score m=score m := by
    funext i x
    exact if_pos he
  constructor
  · apply hCore.1.congr'
    filter_upwards [hEq] with m hm
    exact congrArg₂ (fun π h => π.expectedRewardScore (P m) h) (hPolicy m hm) (hMask m hm).symm
  · apply hCore.2.congr'
    filter_upwards [hEq] with m hm
    exact congrArg₂ (fun π h => π.expectedDurationScore (P m) h) (hPolicy m hm) (hMask m hm).symm
end ProphetSecretary.Limiting
