import ProphetSecretary.Statistics.FinitePriorSwap
import ProphetSecretary.Probability.ProductCoordinates
import ProphetSecretary.Model.EmpiricalLearner

/-!
# Actual training-prefix and online-value product law

An injective projection of the constructed iid matrix splits the first c≤N
training columns from the distinct ONLINE column N. Its law is exactly the
stated independent training/online product, conditional on each prior atom.
Current training data are functions of the visible prefix alone; the hypothetical
swap cannot change the actual adaptive transcript or its hard budget.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ}

def prefixColumn (N c : ℕ) (hc : c≤N) (r : Fin c) : Fin (N+1) := ⟨r.val,by omega⟩

def prefixOnlineIndex (n N c : ℕ) (hc : c≤N) : ((Fin n × Fin c) ⊕ Fin n) ↪ (Fin n × Fin (N+1)) where
  toFun := Sum.elim (fun q => (q.1,prefixColumn N c hc q.2)) (fun i => (i,Fin.last N))
  inj' := by
    intro x y he
    cases x with
    | inl q =>
      cases y with
      | inl r =>
        have h1 := congrArg Prod.fst he
        have h2 := congrArg (fun v : Fin n × Fin (N+1) => v.2.val) he
        exact congrArg Sum.inl (Prod.ext h1 (Fin.ext h2))
      | inr i =>
        have h2 := congrArg (fun v : Fin n × Fin (N+1) => v.2.val) he
        dsimp [prefixColumn] at h2
        have hq := q.2.is_lt
        omega
    | inr i =>
      cases y with
      | inl q =>
        have h2 := congrArg (fun v : Fin n × Fin (N+1) => v.2.val) he
        dsimp [prefixColumn] at h2
        have hq := q.2.is_lt
        omega
      | inr j => exact congrArg Sum.inr (congrArg Prod.fst he)

def prefixOnlineValues (n N c : ℕ) (hc : c≤N) (a : ValueArray n N) :
    (((Fin n × Fin c) → ℝ) × (Fin n → ℝ)) :=
  ((fun q => a (q.1,prefixColumn N c hc q.2)),fun i => a (i,Fin.last N))

lemma prefixOnlineValues_measurePreserving (P : Instance n) (N c : ℕ) (hc : c≤N) :
    MeasurePreserving (prefixOnlineValues n N c hc) (P.trainingCoordinateLaw (N+1))
      ((P.trainingCoordinateLaw c).prod P.valuesLaw) := by
  let e := prefixOnlineIndex n N c hc
  let μ := fun q : Fin n × Fin (N+1) => P.law q.1
  let μ' := fun q => μ (e q)
  haveI : ∀ q, IsProbabilityMeasure (μ' q) := fun q => P.probability (e q).1
  have h0 := ProphetSecretary.Probability.productCoordinateProjection_measurePreserving μ e
  have h1 := measurePreserving_sumPiEquivProdPi μ'
  exact h1.comp h0

def trainingLength (N b k : ℕ) : ℕ := min (b+k) N

lemma trainingLength_le (N b k : ℕ) : trainingLength N b k≤N := Nat.min_le_right _ _

def reservoirFromObservation (n N b k : ℕ) (d : ValueArray n N) : Reservoir n (trainingLength N b k) :=
  fun i r => d (i,prefixColumn N (trainingLength N b k) (trainingLength_le N b k) r)

lemma measurable_reservoirFromObservation (n N b k : ℕ) : Measurable (reservoirFromObservation n N b k) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_lambda _ (fun _ => measurable_pi_apply _))

def observedTraining (F : FinitePrior n) (N b k : ℕ) (ω : BaseWorld F N) : Reservoir n (trainingLength N b k) :=
  reservoirFromObservation n N b k (F.observe N b k ω)

lemma observedTraining_eq (F : FinitePrior n) (N b k : ℕ) (ω : BaseWorld F N) :
    F.observedTraining N b k ω=fun i r => ω.2 (i,prefixColumn N (trainingLength N b k) (trainingLength_le N b k) r) := by
  funext i r
  have hr : (i,prefixColumn N (trainingLength N b k) (trainingLength_le N b k) r)∈trainingCoordinates n N b k := by
    simp only [trainingCoordinates,Finset.mem_filter,Finset.mem_univ,true_and,prefixColumn]
    exact r.is_lt
  exact if_pos hr

lemma observedTraining_swap_next (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N) (ω : BaseWorld F N) :
    F.observedTraining N b k (F.swapBaseEquiv N (nextColumn N b k hk) ω)=F.observedTraining N b k ω :=
  congrArg (reservoirFromObservation n N b k) (F.observe_swap_next N b k hk ω)

/-- This is the actual hard budget for any implemented learner on the observed
prefix. The ONLINE vector is not an argument of the training protocol. -/
lemma observedTraining_hardBudget (F : FinitePrior n) (N b k : ℕ)
    (L : Learner n (trainingLength N b k)) (ω : BaseWorld F N) (r : L.Seed) (i : Fin n) :
    requests (trainingTranscript L.request r (F.observedTraining N b k ω)) i≤trainingLength N b k :=
  L.hard_budget r (F.observedTraining N b k ω) i

lemma actualTrainingTranscript_swap_next (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N)
    (L : Learner n (trainingLength N b k)) (ω : BaseWorld F N) (r : L.Seed) :
    trainingTranscript L.request r (F.observedTraining N b k (F.swapBaseEquiv N (nextColumn N b k hk) ω))=
      trainingTranscript L.request r (F.observedTraining N b k ω) := by
  rw [F.observedTraining_swap_next]

end ProphetSecretary.Statistics.FinitePrior
