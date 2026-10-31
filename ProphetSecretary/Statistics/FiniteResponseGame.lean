import ProphetSecretary.Statistics.FiniteResponseReach

/-!
# The finite reward-or-reach game and actual response patching

Nature's hidden target is reward or an identity whose reach is tested. The
reward benchmark is the instance expected maximum; the reach benchmark is one.
The exact mixture identity is for the actual implemented learners. It supplies
no unproved Bayes-response guarantee or finite minimax conclusion.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Model
variable {n d : ℕ}

noncomputable def Learner.targetGamePayoff (L : Learner n d) (P : Instance n) (J : Option (Fin n)) (C : ℝ) : ℝ :=
  match J with
  | none => L.expectedReward P-C*P.expectedMaximum
  | some i => L.reachProbability P i-C

end ProphetSecretary.Model

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n h d : ℕ} {ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma sum_selection_probabilities (P : Instance n) (h : ℕ)
    (s : ((Fin n × Fin h) → ℝ) → ι) (hs : Measurable s) :
    (∑ c : ι, (P.trainingCoordinateLaw h).real {a | s a=c})=1 := by
  have hSum := sum_measureReal_preimage_singleton (μ:=P.trainingCoordinateLaw h) Finset.univ
    (fun c _ => hs (measurableSet_singleton c))
  simpa only [Finset.coe_univ,Set.preimage_univ,probReal_univ,Set.preimage,Set.mem_singleton_iff,Set.mem_univ,Set.setOf_true] using hSum

/-- Exact finite-game performance after observable finite response selection. -/
theorem finiteResponseLearner_targetGamePayoff (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (s : ((Fin n × Fin h) → ℝ) → ι) (hs : Measurable s) (L : ι → Learner n d)
    (J : Option (Fin n)) (C : ℝ) :
    (finiteResponseLearner s hs L).targetGamePayoff P J C=
      ∑ c : ι, (P.trainingCoordinateLaw h).real {a | s a=c}*(L c).targetGamePayoff P J C := by
  have hMass := sum_selection_probabilities P h s hs
  cases J with
  | none =>
    simp only [Learner.targetGamePayoff]
    rw [finiteResponseLearner_expectedReward P hP s hs L]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,←Finset.sum_mul,hMass,one_mul]
  | some i =>
    simp only [Learner.targetGamePayoff]
    rw [finiteResponseLearner_reachProbability P s hs L i]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,←Finset.sum_mul,hMass,one_mul]

end ProphetSecretary.Statistics
