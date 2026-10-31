import ProphetSecretary.Model.FiniteAlphabetInstance
import ProphetSecretary.Model.RankLearnerBounds
import ProphetSecretary.Probability.FiniteRoundingProduct

/-!
# Actual learner experiments on finite alphabets

One independent array contains every training coordinate and the online
values. Its transformation into the learner's reservoir and online world
preserves the full product law, with the permutation and policy seed sampled
independently. The learner still observes only its adaptive transcript and
causal online history.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model
open ProphetSecretary.Probability

variable {n k : ℕ} {Θ : Type*} [Fintype Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]

def alphabetLearnerWorld (L : RankLearner n k) (v : Θ → ℝ)
    (a : (LearningArrayIndex n k → Θ) × (Equiv.Perm (Fin n) × L.Seed)) :
    (Fin n → ℝ) × (Equiv.Perm (Fin n) × (Reservoir n k × L.Seed)) :=
  ((alphabetData v a.1).1,(a.2.1,((alphabetData v a.1).2,a.2.2)))

lemma alphabetLearnerWorld_measurePreserving (L : RankLearner n k) (v : Θ → ℝ) (hv : ∀ a, 0≤v a)
    (p : Fin n → Θ → ℝ) (hp : ∀ i, p i∈stdSimplex ℝ Θ) :
    MeasurePreserving (alphabetLearnerWorld L v)
      ((Measure.pi (fun q : LearningArrayIndex n k => finiteSimplexLaw (p q.variableIndex) (hp q.variableIndex))).prod
        ((Instance.uniformPermutationLaw n).prod L.seedLaw))
      ((L.randomizedPolicy (finiteAlphabetInstance v hv p hp)).worldLaw (finiteAlphabetInstance v hv p hp)) := by
  let P := finiteAlphabetInstance v hv p hp
  let ν := Instance.uniformPermutationLaw n
  have hSwap : MeasurePreserving (fun a : Reservoir n k × (Equiv.Perm (Fin n) × L.Seed) =>
      (a.2.1,(a.1,a.2.2))) ((P.reservoirLaw k).prod (ν.prod L.seedLaw))
      (ν.prod ((P.reservoirLaw k).prod L.seedLaw)) :=
    (measurePreserving_prodAssoc ν (P.reservoirLaw k) L.seedLaw).comp
      (((Measure.measurePreserving_swap (μ:=P.reservoirLaw k) (ν:=ν)).prod (MeasurePreserving.id L.seedLaw)).comp
        ((measurePreserving_prodAssoc (P.reservoirLaw k) ν L.seedLaw).symm MeasurableEquiv.prodAssoc))
  exact ((MeasurePreserving.id P.valuesLaw).prod hSwap).comp
    ((measurePreserving_prodAssoc P.valuesLaw (P.reservoirLaw k) (ν.prod L.seedLaw)).comp
      ((alphabetData_measurePreserving v hv p hp).prod (MeasurePreserving.id (ν.prod L.seedLaw))))

noncomputable def alphabetLearnerReward (L : RankLearner n k) (v : Θ → ℝ)
    (a : (LearningArrayIndex n k → Θ) × (Equiv.Perm (Fin n) × L.Seed)) : ℝ :=
  L.policy.reward ((alphabetLearnerWorld L v a).2.2) ((alphabetLearnerWorld L v a).2.1)
    ((alphabetLearnerWorld L v a).1)

noncomputable def alphabetLearnerReach (L : RankLearner n k) (v : Θ → ℝ) (i : Fin n)
    (a : (LearningArrayIndex n k → Θ) × (Equiv.Perm (Fin n) × L.Seed)) : ℝ :=
  if L.policy.Reaches ((alphabetLearnerWorld L v a).2.2) ((alphabetLearnerWorld L v a).2.1)
    ((alphabetLearnerWorld L v a).1) i then 1 else 0

lemma measurable_alphabetLearnerWorld (L : RankLearner n k) (v : Θ → ℝ) : Measurable (alphabetLearnerWorld L v) := by
  have hData : Measurable (alphabetData (n:=n) (k:=k) v) := measurable_of_finite _
  exact (hData.fst.comp measurable_fst).prodMk
    ((measurable_fst.comp measurable_snd).prodMk
      ((hData.snd.comp measurable_fst).prodMk (measurable_snd.comp measurable_snd)))

lemma measurable_alphabetLearnerReward (L : RankLearner n k) (v : Θ → ℝ) : Measurable (alphabetLearnerReward L v) :=
  L.policy.measurable_reward L.policy_isMeasurable
    ((measurable_snd.comp measurable_snd).comp (measurable_alphabetLearnerWorld L v))
    ((measurable_fst.comp measurable_snd).comp (measurable_alphabetLearnerWorld L v))
    (fun i => ((measurable_pi_apply i).comp measurable_fst).comp (measurable_alphabetLearnerWorld L v))

lemma measurable_alphabetLearnerReach (L : RankLearner n k) (v : Θ → ℝ) (i : Fin n) :
    Measurable (alphabetLearnerReach L v i) := by
  apply Measurable.ite _ measurable_const measurable_const
  exact L.policy.measurableSet_reaches L.policy_isMeasurable
    ((measurable_snd.comp measurable_snd).comp (measurable_alphabetLearnerWorld L v))
    ((measurable_fst.comp measurable_snd).comp (measurable_alphabetLearnerWorld L v))
    (fun j => ((measurable_pi_apply j).comp measurable_fst).comp (measurable_alphabetLearnerWorld L v)) i

omit [Fintype Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ] in
lemma alphabetLearnerReward_bounds (L : RankLearner n k) (v : Θ → ℝ)
    (hv : ∀ a, v a∈Icc (0 : ℝ) 1)
    (a : (LearningArrayIndex n k → Θ) × (Equiv.Perm (Fin n) × L.Seed)) :
    0≤alphabetLearnerReward L v a ∧ alphabetLearnerReward L v a≤1 := by
  constructor
  · exact L.policy.reward_nonnegative _ _ _ (fun i => (hv (a.1 (.inl i))).1)
  · exact (L.policy.reward_le_maximum _ _ _).trans
      (Instance.maximum_le _ (by norm_num) (fun i => (hv (a.1 (.inl i))).2))

omit [Fintype Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ] in
lemma alphabetLearnerReach_bounds (L : RankLearner n k) (v : Θ → ℝ) (i : Fin n)
    (a : (LearningArrayIndex n k → Θ) × (Equiv.Perm (Fin n) × L.Seed)) :
    0≤alphabetLearnerReach L v i a ∧ alphabetLearnerReach L v i a≤1 := by
  unfold alphabetLearnerReach
  split_ifs <;> norm_num

lemma integral_alphabetLearnerReward (L : RankLearner n k) (v : Θ → ℝ) (hv : ∀ a, 0≤v a)
    (p : Fin n → Θ → ℝ) (hp : ∀ i, p i∈stdSimplex ℝ Θ) :
    (∫ a, alphabetLearnerReward L v a
      ∂(Measure.pi (fun q : LearningArrayIndex n k => finiteSimplexLaw (p q.variableIndex) (hp q.variableIndex))).prod
        ((Instance.uniformPermutationLaw n).prod L.seedLaw)) = L.expectedReward (finiteAlphabetInstance v hv p hp) :=
  (alphabetLearnerWorld_measurePreserving L v hv p hp).hasLaw.integral_comp
    (L.randomizedPolicy (finiteAlphabetInstance v hv p hp)).measurable_realizedReward.aestronglyMeasurable

lemma integral_alphabetLearnerReach (L : RankLearner n k) (v : Θ → ℝ) (hv : ∀ a, 0≤v a)
    (p : Fin n → Θ → ℝ) (hp : ∀ i, p i∈stdSimplex ℝ Θ) (i : Fin n) :
    (∫ a, alphabetLearnerReach L v i a
      ∂(Measure.pi (fun q : LearningArrayIndex n k => finiteSimplexLaw (p q.variableIndex) (hp q.variableIndex))).prod
        ((Instance.uniformPermutationLaw n).prod L.seedLaw)) = L.reachProbability (finiteAlphabetInstance v hv p hp) i := by
  let P := finiteAlphabetInstance v hv p hp
  let E := {ω : (Fin n → ℝ) × (Equiv.Perm (Fin n) × (Reservoir n k × L.Seed)) |
    L.policy.Reaches ω.2.2 ω.2.1 ω.1 i}
  have hE : MeasurableSet E := L.policy.measurableSet_reaches L.policy_isMeasurable
    (measurable_snd.comp measurable_snd) (measurable_fst.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp measurable_fst) i
  have hMean := (alphabetLearnerWorld_measurePreserving L v hv p hp).hasLaw.integral_comp
    ((measurable_const : Measurable (fun _ => (1 : ℝ))).indicator hE).aestronglyMeasurable
  have hMass := integral_indicator_const (μ:=(L.randomizedPolicy P).worldLaw P) (1 : ℝ) hE
  rw [smul_eq_mul,mul_one] at hMass
  exact hMean.trans hMass

lemma sum_learningArrayIndex (f : Fin n → ℝ) :
    (∑ q : LearningArrayIndex n k, f q.variableIndex) = ((k : ℝ)+1)*∑ i, f i := by
  simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,LearningArrayIndex.variableIndex,
    Sum.elim_inl,Sum.elim_inr,id_eq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← Finset.mul_sum]
  ring

lemma RankLearner.rounding_reward_error [DecidableEq Θ] (L : RankLearner n k) (v : Θ → ℝ)
    (hv : ∀ a, v a∈Icc (0 : ℝ) 1) (p : Fin n → Θ → ℝ) (hp : ∀ i, p i∈stdSimplex ℝ Θ)
    (N : ℕ) (hN : 0<N) (z : Θ) :
    |L.expectedReward (finiteAlphabetInstance v (fun a => (hv a).1) p hp)-
      L.expectedReward (finiteAlphabetInstance v (fun a => (hv a).1)
        (fun i => roundedProbability (p i) N z) (fun i => roundedProbability_simplex (p i) (hp i) hN z))| ≤
      ((k : ℝ)+1)*∑ i, roundingLoss (p i) N z := by
  have h := roundingProductCoupling_observable_error ((Instance.uniformPermutationLaw n).prod L.seedLaw)
    (fun q : LearningArrayIndex n k => p q.variableIndex) (fun q => hp q.variableIndex) N hN z
    (alphabetLearnerReward L v) (measurable_alphabetLearnerReward L v) (by norm_num : (0 : ℝ)≤1)
    (alphabetLearnerReward_bounds L v hv)
  rw [integral_alphabetLearnerReward L v (fun a => (hv a).1) p hp,
    integral_alphabetLearnerReward L v (fun a => (hv a).1) (fun i => roundedProbability (p i) N z) (fun i => roundedProbability_simplex (p i) (hp i) hN z),one_mul,sum_learningArrayIndex (fun i => roundingLoss (p i) N z)] at h
  exact h

lemma RankLearner.rounding_reach_error [DecidableEq Θ] (L : RankLearner n k) (v : Θ → ℝ)
    (hv : ∀ a, 0≤v a) (p : Fin n → Θ → ℝ) (hp : ∀ i, p i∈stdSimplex ℝ Θ)
    (N : ℕ) (hN : 0<N) (z : Θ) (i : Fin n) :
    |L.reachProbability (finiteAlphabetInstance v hv p hp) i-
      L.reachProbability (finiteAlphabetInstance v hv
        (fun i => roundedProbability (p i) N z) (fun i => roundedProbability_simplex (p i) (hp i) hN z)) i| ≤
      ((k : ℝ)+1)*∑ j, roundingLoss (p j) N z := by
  have h := roundingProductCoupling_observable_error ((Instance.uniformPermutationLaw n).prod L.seedLaw)
    (fun q : LearningArrayIndex n k => p q.variableIndex) (fun q => hp q.variableIndex) N hN z
    (alphabetLearnerReach L v i) (measurable_alphabetLearnerReach L v i) (by norm_num : (0 : ℝ)≤1)
    (alphabetLearnerReach_bounds L v i)
  rw [integral_alphabetLearnerReach L v hv p hp i,
    integral_alphabetLearnerReach L v hv (fun i => roundedProbability (p i) N z) (fun i => roundedProbability_simplex (p i) (hp i) hN z) i,one_mul,sum_learningArrayIndex (fun i => roundingLoss (p i) N z)] at h
  exact h

end ProphetSecretary.Model
