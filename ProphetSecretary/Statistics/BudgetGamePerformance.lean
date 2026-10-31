import ProphetSecretary.Model.BudgetPadding
import ProphetSecretary.Statistics.FiniteResponseGame

/-!
# Reward and reach under an enlarged training budget

Only the original reservoir prefix reaches the old callback. The exact
prefix law preserves the actual reward-or-reach game for every instance;
the enlarged hard budget holds on every raw training outcome.
-/

open MeasureTheory
namespace ProphetSecretary.Model
variable {n k l : ℕ}

lemma Learner.padBudget_reachProbability (L : Learner n k) (h : k≤l) (P : Instance n) (i : Fin n) :
    (L.padBudget h).reachProbability P i=L.reachProbability P i := by
  let ν := (P.reservoirLaw l).prod L.seedLaw
  let f : Reservoir n l × L.Seed → Reservoir n k × L.Seed := fun p => (reservoirPrefix h p.1,p.2)
  have hf : Measurable f := ((measurable_reservoirPrefix h).comp measurable_fst).prodMk measurable_snd
  have hLaw : MeasurePreserving f ν (L.randomizedPolicy P).seedLaw :=
    (P.reservoirPrefix_measurePreserving h).prod (MeasurePreserving.id L.seedLaw)
  have hRule : (L.padBudget h).policy=L.policy.pullbackSeed f := by
    apply congrArg Policy.mk
    funext p t j x H
    exact L.padBudget_decide h p t j x H
  change (L.padBudget h).policy.reachProbability P ν i=_
  rw [hRule]
  exact (L.randomizedPolicy P).pullbackSeed_reachProbability ν f hf hLaw P i

lemma Learner.padBudget_targetGamePayoff (L : Learner n k) (h : k≤l) (P : Instance n)
    (J : Option (Fin n)) (C : ℝ) :
    (L.padBudget h).targetGamePayoff P J C=L.targetGamePayoff P J C := by
  cases J with
  | none => exact congrArg (fun r => r-C*P.expectedMaximum) (L.padBudget_expectedReward h P)
  | some i => exact congrArg (fun q => q-C) (L.padBudget_reachProbability h P i)

end ProphetSecretary.Model
