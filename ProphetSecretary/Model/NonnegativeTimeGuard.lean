import ProphetSecretary.Model.Learner
import ProphetSecretary.Model.Independence
import ProphetSecretary.Model.Outcome

/-!
# Extending endpoint actions to raw negative times

Arrival clocks are nonnegative almost surely. Specifying endpoint decisions
also at negative raw times therefore changes neither reward nor reach. The
sample requests, transcript, and hard budget are unchanged on every outcome.
This supplies all-raw-input endpoint actions for the finite strategy encoding.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model
variable {n k : ℕ}

noncomputable def Learner.guardNegativeTimes (L : Learner n k) : Learner n k where
  Seed := L.Seed
  seedLaw := L.seedLaw
  request := L.request
  measurable_request := L.measurable_request
  decide r tr t i x H := if t<0 then Decidable.decide (x=1) else L.decide r tr t i x H
  measurable_decide := by
    let Ω := (L.Seed × Transcript n) × (ℝ × (Fin n × (ℝ × History n)))
    have ht : Measurable (fun z : Ω => z.2.1) := by fun_prop
    have hx : Measurable (fun z : Ω => z.2.2.2.1) := by fun_prop
    have hEndpoint : Measurable (fun z : Ω => Decidable.decide (z.2.2.2.1=1)) := by
      apply measurable_to_bool
      change MeasurableSet {z : Ω | Decidable.decide (z.2.2.2.1=1)=true}
      simpa only [decide_eq_true_eq] using (measurableSet_eq_fun hx (measurable_const : Measurable (fun _ : Ω => (1 : ℝ))))
    exact hEndpoint.ite (measurableSet_lt ht measurable_const) L.measurable_decide

lemma Learner.guardNegativeTimes_policy_decide (L : Learner n k) (p : Reservoir n k × L.Seed)
    (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    L.guardNegativeTimes.policy.decide p t i x H=
      if t<0 then Decidable.decide (x=1) else L.policy.decide p t i x H := rfl

lemma Learner.guardNegativeTimes_accepts_cap (L : Learner n k)
    (hCap : ∀ y r t, 0≤t → ∀ i H, L.policy.decide (y,r) t i 1 H=true)
    (y : Reservoir n k) (r : L.Seed) (t : ℝ) (i : Fin n) (H : History n) :
    L.guardNegativeTimes.policy.decide (y,r) t i 1 H=true := by
  rw [L.guardNegativeTimes_policy_decide]
  split_ifs with ht
  · simp
  · exact hCap y r t (not_lt.mp ht) i H

lemma Learner.guardNegativeTimes_rejects_zero (L : Learner n k)
    (hZero : ∀ y r t i H, L.policy.decide (y,r) t i 0 H=false)
    (y : Reservoir n k) (r : L.Seed) (t : ℝ) (i : Fin n) (H : History n) :
    L.guardNegativeTimes.policy.decide (y,r) t i 0 H=false := by
  rw [L.guardNegativeTimes_policy_decide]
  split_ifs
  · norm_num
  · exact hZero y r t i H

lemma Learner.guardNegativeTimes_accepted (L : Learner n k) (p : Reservoir n k × L.Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (hu : ∀ i, 0≤u i) :
    L.guardNegativeTimes.policy.accepted p D x u=L.policy.accepted p D x u := by
  unfold Policy.accepted
  apply Finset.filter_congr
  intro i _
  simp only [Policy.action,L.guardNegativeTimes_policy_decide,if_neg (not_lt.mpr (hu i))]

lemma Learner.guardNegativeTimes_stoppingTime (L : Learner n k) (p : Reservoir n k × L.Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (hu : ∀ i, 0≤u i) :
    L.guardNegativeTimes.policy.stoppingTime p D x u=L.policy.stoppingTime p D x u := by
  unfold Policy.stoppingTime Policy.stopTimes
  simp only [L.guardNegativeTimes_accepted p D x u hu]

lemma Learner.guardNegativeTimes_reward (L : Learner n k) (p : Reservoir n k × L.Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (hu : ∀ i, 0≤u i) :
    L.guardNegativeTimes.policy.reward p D x u=L.policy.reward p D x u := by
  unfold Policy.reward
  apply Finset.sum_congr rfl
  intro i _
  apply if_congr ?_ rfl rfl
  unfold Policy.ActualSelects Policy.Selects
  rw [L.guardNegativeTimes_accepted p D x u hu,L.guardNegativeTimes_stoppingTime p D x u hu]

lemma Learner.guardNegativeTimes_expectedReward (L : Learner n k) (P : Instance n) :
    L.guardNegativeTimes.expectedReward P=L.expectedReward P := by
  change (∫ ω : World n (Reservoir n k × L.Seed), L.guardNegativeTimes.policy.reward
      ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw ((P.reservoirLaw k).prod L.seedLaw))=_
  apply integral_congr_ae
  filter_upwards [P.world_clocks_mem_unitInterval ((P.reservoirLaw k).prod L.seedLaw)] with ω hω
  exact L.guardNegativeTimes_reward _ _ _ _ (fun i => (hω i).1)

lemma Learner.guardNegativeTimes_reachProbability (L : Learner n k) (P : Instance n) (i : Fin n) :
    L.guardNegativeTimes.reachProbability P i=L.reachProbability P i := by
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [P.world_clocks_mem_unitInterval ((P.reservoirLaw k).prod L.seedLaw)] with ω hω
  apply propext
  change L.guardNegativeTimes.policy.Reaches ω.2.2 ω.1 ω.2.1 i ↔ L.policy.Reaches ω.2.2 ω.1 ω.2.1 i
  unfold Policy.Reaches
  rw [L.guardNegativeTimes_stoppingTime _ _ _ _ (fun j => (hω j).1)]

end ProphetSecretary.Model
