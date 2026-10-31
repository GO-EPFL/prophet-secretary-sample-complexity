import ProphetSecretary.Model.EmpiricalLearner
import ProphetSecretary.Model.TrainingCoordinates
import ProphetSecretary.Probability.ProductCoordinates

/-!
# Measurable patching of finitely many actual learners

A preliminary sample selects one of a fixed finite family of responses. Their
arbitrary independent seeds are sampled by a common finite product law. The
patched rule is implemented from a causal full-sample transcript, with hard
budget h+d on every outcome. No selection over all possible posterior priors is
assumed; only a given finite response family is used.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n h d : ℕ} {ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

def preliminaryTrainingArray (y : Reservoir n (h+d)) : (Fin n × Fin h) → ℝ :=
  fun q => y q.1 (Fin.castAdd d q.2)

def responseTrainingReservoir (y : Reservoir n (h+d)) : Reservoir n d :=
  fun i r => y i (Fin.natAdd h r)

lemma measurable_preliminaryTrainingArray : Measurable (preliminaryTrainingArray (n:=n) (h:=h) (d:=d)) :=
  measurable_pi_lambda _ (fun q => (measurable_pi_apply (Fin.castAdd d q.2)).comp (measurable_pi_apply q.1))

lemma measurable_responseTrainingReservoir : Measurable (responseTrainingReservoir (n:=n) (h:=h) (d:=d)) :=
  measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun r =>
    (measurable_pi_apply (Fin.natAdd h r)).comp (measurable_pi_apply i)))

abbrev FiniteResponseSeeds (L : ι → Learner n d) := (c : ι) → (L c).Seed

noncomputable def finiteResponseSeedLaw (L : ι → Learner n d) : Measure (FiniteResponseSeeds L) :=
  Measure.pi (fun c => (L c).seedLaw)

instance finiteResponseSeedLaw_probability (L : ι → Learner n d) : IsProbabilityMeasure (finiteResponseSeedLaw L) := by
  unfold finiteResponseSeedLaw
  infer_instance

noncomputable def finiteResponsePolicy (select : ((Fin n × Fin h) → ℝ) → ι) (L : ι → Learner n d) :
    Policy (Reservoir n (h+d) × FiniteResponseSeeds L) n where
  decide p t i x H := (L (select (preliminaryTrainingArray p.1))).policy.decide
    (responseTrainingReservoir p.1,p.2 (select (preliminaryTrainingArray p.1))) t i x H

lemma finiteResponsePolicy_isMeasurable {select : ((Fin n × Fin h) → ℝ) → ι}
    (hs : Measurable select) (L : ι → Learner n d) : (finiteResponsePolicy select L).IsMeasurable := by
  let Ω := (Reservoir n (h+d) × FiniteResponseSeeds L) × (ℝ × (Fin n × (ℝ × History n)))
  let s : Ω → ι := fun z => select (preliminaryTrainingArray z.1.1)
  have hsΩ : Measurable s := hs.comp (measurable_preliminaryTrainingArray.comp (measurable_fst.comp measurable_fst))
  have hFixed (c : ι) : Measurable (fun z : Ω => (L c).policy.decide
      (responseTrainingReservoir z.1.1,z.1.2 c) z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) := by
    have hp : Measurable (fun z : Ω => (responseTrainingReservoir (h:=h) (d:=d) z.1.1,z.1.2 c)) :=
      (measurable_responseTrainingReservoir.comp (measurable_fst.comp measurable_fst)).prodMk
        ((measurable_pi_apply c).comp (measurable_snd.comp measurable_fst))
    convert (L c).policy_isMeasurable.comp (hp.prodMk measurable_snd) using 1
    funext z
    rfl
  have hFamily : Measurable (fun p : ι × Ω => (L p.1).policy.decide
      (responseTrainingReservoir p.2.1.1,p.2.1.2 p.1) p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) :=
    measurable_from_prod_countable_right hFixed
  exact hFamily.comp (hsΩ.prodMk measurable_id)

/-- The family and selector are fixed before nature chooses an unknown instance. -/
noncomputable def finiteResponseLearner (select : ((Fin n × Fin h) → ℝ) → ι)
    (hs : Measurable select) (L : ι → Learner n d) : Learner n (h+d) :=
  Learner.ofSamplePolicy (FiniteResponseSeeds L) (finiteResponseSeedLaw L)
    (finiteResponsePolicy select L) (finiteResponsePolicy_isMeasurable hs L)

lemma finiteResponseLearner_decide (select : ((Fin n × Fin h) → ℝ) → ι)
    (hs : Measurable select) (L : ι → Learner n d) (y : Reservoir n (h+d)) (r : FiniteResponseSeeds L)
    (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (finiteResponseLearner select hs L).policy.decide (y,r) t i x H=
      (L (select (preliminaryTrainingArray y))).policy.decide
        (responseTrainingReservoir y,r (select (preliminaryTrainingArray y))) t i x H := by
  exact Learner.ofSamplePolicy_decide _ _ _ _ _ _ _ _ _ _

lemma finiteResponseLearner_hardBudget (select : ((Fin n × Fin h) → ℝ) → ι)
    (hs : Measurable select) (L : ι → Learner n d) (y : Reservoir n (h+d)) (r : FiniteResponseSeeds L) (i : Fin n) :
    requests (trainingTranscript (finiteResponseLearner select hs L).request r y) i≤h+d :=
  (finiteResponseLearner select hs L).hard_budget r y i

omit [MeasurableSpace ι] [MeasurableSingletonClass ι] in
/-- Every fixed response seed has its stated law, independent of the unknown law. -/
lemma finiteResponseSeed_eval_measurePreserving (L : ι → Learner n d) (c : ι) :
    MeasurePreserving (fun r : FiniteResponseSeeds L => r c) (finiteResponseSeedLaw L) (L c).seedLaw :=
  measurePreserving_eval (fun c => (L c).seedLaw) c

lemma finiteResponseLearner_frozen_eq (select : ((Fin n × Fin h) → ℝ) → ι)
    (hs : Measurable select) (L : ι → Learner n d) (y : Reservoir n (h+d)) (r : FiniteResponseSeeds L) :
    (finiteResponseLearner select hs L).frozenRule y r=
      (L (select (preliminaryTrainingArray y))).frozenRule
        (responseTrainingReservoir y) (r (select (preliminaryTrainingArray y))) := by
  apply congrArg Policy.mk
  funext s t i x H
  exact finiteResponseLearner_decide select hs L y r t i x H

def preliminaryTrainingIndex (n h d : ℕ) : (Fin n × Fin h) ↪ (Fin n × Fin (h+d)) where
  toFun q := (q.1,Fin.castAdd d q.2)
  inj' := by
    intro q r he
    exact Prod.ext (congrArg (fun p : Fin n × Fin (h+d) => p.1) he) (Fin.ext (congrArg (fun p : Fin n × Fin (h+d) => p.2.val) he))

lemma preliminaryTrainingArray_measurePreserving (P : Instance n) (h d : ℕ) :
    MeasurePreserving (preliminaryTrainingArray (n:=n) (h:=h) (d:=d))
      (P.reservoirLaw (h+d)) (P.trainingCoordinateLaw h) :=
  (ProphetSecretary.Probability.productCoordinateProjection_measurePreserving
    (fun q : Fin n × Fin (h+d) => P.law q.1) (preliminaryTrainingIndex n h d)).comp
      (P.reservoirCoordinates_measurePreserving (h+d))

end ProphetSecretary.Statistics
