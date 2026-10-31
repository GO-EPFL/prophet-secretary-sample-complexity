import ProphetSecretary.Model.AllSamplesLearner
import ProphetSecretary.Model.TrainingCoordinates
import ProphetSecretary.Model.PolicySeedTransport
import ProphetSecretary.Probability.ProductCoordinates

/-!
# Increasing a learner's allowed sample budget

The padded full-sample program supplies only the original prefix to the original
learner. Its observed policy is unchanged; the prefix has the actual original
reservoir law. Sampling the unused suffix stays within the enlarged hard budget.
-/

open MeasureTheory
namespace ProphetSecretary.Model
variable {n k l : ℕ}

def reservoirPrefix (h : k≤l) (y : Reservoir n l) : Reservoir n k := fun i r => y i (Fin.castLE h r)

lemma measurable_reservoirPrefix (h : k≤l) : Measurable (reservoirPrefix (n:=n) h) :=
  measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun r =>
    (measurable_pi_apply (Fin.castLE h r)).comp (measurable_pi_apply i)

lemma Instance.reservoirPrefix_measurePreserving (P : Instance n) (h : k≤l) :
    MeasurePreserving (reservoirPrefix (n:=n) h) (P.reservoirLaw l) (P.reservoirLaw k) := by
  let e : (Fin n × Fin k) ↪ (Fin n × Fin l) :=
    ⟨fun q => (q.1,Fin.castLE h q.2),by
      intro a b hab
      refine Prod.ext ?_ ?_
      · exact congrArg (fun q : Fin n × Fin l => q.1) hab
      apply Fin.ext
      exact congrArg (fun q : Fin n × Fin l => q.2.val) hab⟩
  have hFlat := ProphetSecretary.Probability.productCoordinateProjection_measurePreserving
    (fun q : Fin n × Fin l => P.law q.1) e
  exact (P.reservoirCoordinates_symm_measurePreserving k).comp
    (hFlat.comp (P.reservoirCoordinates_measurePreserving l))

noncomputable def Learner.padBudget (L : Learner n k) (h : k≤l) : Learner n l :=
  Learner.ofSamplePolicy L.Seed L.seedLaw
    (L.policy.pullbackSeed (fun p : Reservoir n l × L.Seed => (reservoirPrefix h p.1,p.2)))
    (L.policy.pullbackSeed_measurable L.policy_isMeasurable
      ((measurable_reservoirPrefix h).comp measurable_fst |>.prodMk measurable_snd))

lemma Learner.padBudget_decide (L : Learner n k) (h : k≤l) (p : Reservoir n l × L.Seed)
    (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (L.padBudget h).policy.decide p t i x H=L.policy.decide (reservoirPrefix h p.1,p.2) t i x H :=
  Learner.ofSamplePolicy_decide _ _ _ _ p.1 p.2 t i x H

lemma Learner.padBudget_expectedReward (L : Learner n k) (h : k≤l) (P : Instance n) :
    (L.padBudget h).expectedReward P=L.expectedReward P := by
  let ν := (P.reservoirLaw l).prod L.seedLaw
  let f : Reservoir n l × L.Seed → Reservoir n k × L.Seed := fun p => (reservoirPrefix h p.1,p.2)
  have hf : Measurable f := ((measurable_reservoirPrefix h).comp measurable_fst).prodMk measurable_snd
  have hLaw : MeasurePreserving f ν (L.randomizedPolicy P).seedLaw :=
    (P.reservoirPrefix_measurePreserving h).prod (MeasurePreserving.id L.seedLaw)
  have hRule : (L.padBudget h).policy=L.policy.pullbackSeed f := by
    apply congrArg Policy.mk
    funext p t i x H
    exact L.padBudget_decide h p t i x H
  change (∫ ω : World n (Reservoir n l × L.Seed), (L.padBudget h).policy.reward ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw ν)=_
  rw [hRule]
  exact (L.randomizedPolicy P).pullbackSeed_expectedReward ν f hf hLaw P

lemma Learner.padBudget_guarantees (L : Learner n k) (h : k≤l) {rho : ℝ} (hG : L.Guarantees rho) :
    (L.padBudget h).Guarantees rho := by
  intro P hP
  rw [L.padBudget_expectedReward h P]
  exact hG P hP

noncomputable def Learner.rejecting (n k : ℕ) : Learner n k where
  Seed := Unit
  seedLaw := Measure.dirac ()
  request _ _ := none
  measurable_request := measurable_const
  decide _ _ _ _ _ _ := false
  measurable_decide := measurable_const

end ProphetSecretary.Model
