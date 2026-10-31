import ProphetSecretary.Model.Learner
import ProphetSecretary.Model.ExecutionAgreement

open MeasureTheory
open scoped ENNReal

namespace ProphetSecretary.Model

namespace Learner

variable {n k : ℕ}

/-- An online strategy can be run with no training requests at any hard budget. -/
noncomputable def noTraining (π : RandomizedPolicy n) : Learner n k where
  Seed := π.Seed
  seedLaw := π.seedLaw
  request _ _ := none
  measurable_request := measurable_const
  decide r _ := π.rule.decide r
  measurable_decide := π.measurable_rule.comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

theorem noTraining_transcript (π : RandomizedPolicy n) (r : π.Seed)
    (y : Reservoir n k) :
    trainingTranscript (noTraining (k := k) π).request r y = [] := by
  unfold trainingTranscript
  cases n * k <;> rfl

theorem noTraining_requests (π : RandomizedPolicy n) (r : π.Seed)
    (y : Reservoir n k) (i : Fin n) :
    requests (trainingTranscript (noTraining (k := k) π).request r y) i = 0 := by
  rw [noTraining_transcript]
  rfl

theorem noTraining_decide (π : RandomizedPolicy n) (y : Reservoir n k) (r : π.Seed)
    (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (noTraining (k := k) π).policy.decide (y, r) t i x H =
      π.rule.decide r t i x H := rfl

theorem noTraining_reward (π : RandomizedPolicy n) (y : Reservoir n k) (r : π.Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    (noTraining (k := k) π).policy.reward (y, r) D x u =
      π.rule.reward r D x u :=
  (Policy.outcomes_eq_of_actions_eq _ _ _ _ D x u (fun _ => rfl)).1

def noTrainingWorldMap (π : RandomizedPolicy n)
    (ω : World n (Reservoir n k × π.Seed)) : World n π.Seed :=
  (ω.1, (ω.2.1, ω.2.2.2))

theorem noTrainingWorldMap_measurePreserving (π : RandomizedPolicy n) (P : Instance n) :
    MeasurePreserving (noTrainingWorldMap (k := k) π)
      (P.worldLaw ((P.reservoirLaw k).prod π.seedLaw)) (P.worldLaw π.seedLaw) :=
  (MeasurePreserving.id P.valuesLaw).prod
    ((MeasurePreserving.id (Instance.clocksLaw n)).prod measurePreserving_snd)

theorem noTraining_expectedReward (π : RandomizedPolicy n) (P : Instance n) :
    (noTraining (k := k) π).expectedReward P = π.expectedReward P := by
  have hmap := noTrainingWorldMap_measurePreserving (k := k) π P
  have hi := integral_map (μ := P.worldLaw ((P.reservoirLaw k).prod π.seedLaw))
    hmap.measurable.aemeasurable
    π.measurable_realizedReward.aestronglyMeasurable
  rw [hmap.map_eq] at hi
  exact hi.symm

/-- A branch chosen independently before training. Each branch retains its own
adaptive request rule and the same pathwise per-distribution budget. -/
noncomputable def mix (L R : Learner n k) (a b : ℝ≥0∞) (hab : a + b = 1) :
    Learner n k where
  Seed := L.Seed ⊕ R.Seed
  seedLaw := a • Measure.map Sum.inl L.seedLaw + b • Measure.map Sum.inr R.seedLaw
  probability := ⟨by simp [Measure.add_apply, Measure.smul_apply,
    Measure.map_apply measurable_inl MeasurableSet.univ,
    Measure.map_apply measurable_inr MeasurableSet.univ, hab]⟩
  request s := Sum.elim L.request R.request s
  measurable_request := by
    unfold MeasurableRequestRule
    convert (L.measurable_request.sumElim R.measurable_request).comp
      (MeasurableEquiv.sumProdDistrib L.Seed R.Seed (Transcript n)).measurable
      using 1
    funext z
    rcases z with ⟨s, H⟩
    cases s <;> rfl
  decide s := Sum.elim L.decide R.decide s
  measurable_decide := by
    let C := ℝ × (Fin n × (ℝ × History n))
    have h := (L.measurable_decide.sumElim R.measurable_decide).comp
      ((MeasurableEquiv.sumProdDistrib (L.Seed × Transcript n)
        (R.Seed × Transcript n) C).measurable.comp
        ((MeasurableEquiv.sumProdDistrib L.Seed R.Seed (Transcript n)).measurable.prodMap
          measurable_id))
    convert h using 1
    funext z
    rcases z with ⟨⟨s, H⟩, v⟩
    cases s <;> rfl

theorem mix_transcript_inl (L R : Learner n k) (a b : ℝ≥0∞) (hab : a + b = 1)
    (r : L.Seed) (y : Reservoir n k) :
    trainingTranscript (L.mix R a b hab).request (.inl r) y =
      trainingTranscript L.request r y := by
  have h (fuel : ℕ) (H : Transcript n) :
      train (L.mix R a b hab).request (.inl r) y fuel H =
        train L.request r y fuel H := by
    induction fuel generalizing H with
    | zero => rfl
    | succ fuel ih =>
      simp only [train]
      change (match L.request r H with
        | none => H
        | some i => if hi : requests H i < k then
            train (L.mix R a b hab).request (.inl r) y fuel
              ((i, y i ⟨requests H i, hi⟩) :: H) else H) = _
      split <;> simp_all
  exact h _ _

theorem mix_transcript_inr (L R : Learner n k) (a b : ℝ≥0∞) (hab : a + b = 1)
    (r : R.Seed) (y : Reservoir n k) :
    trainingTranscript (L.mix R a b hab).request (.inr r) y =
      trainingTranscript R.request r y := by
  have h (fuel : ℕ) (H : Transcript n) :
      train (L.mix R a b hab).request (.inr r) y fuel H =
        train R.request r y fuel H := by
    induction fuel generalizing H with
    | zero => rfl
    | succ fuel ih =>
      simp only [train]
      change (match R.request r H with
        | none => H
        | some i => if hi : requests H i < k then
            train (L.mix R a b hab).request (.inr r) y fuel
              ((i, y i ⟨requests H i, hi⟩) :: H) else H) = _
      split <;> simp_all
  exact h _ _

theorem mix_decide_inl (L R : Learner n k) (a b : ℝ≥0∞) (hab : a + b = 1)
    (y : Reservoir n k) (r : L.Seed) (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (L.mix R a b hab).policy.decide (y, .inl r) t i x H =
      L.policy.decide (y, r) t i x H := by
  change L.decide r (trainingTranscript (L.mix R a b hab).request (.inl r) y) t i x H = _
  rw [mix_transcript_inl]
  rfl

theorem mix_decide_inr (L R : Learner n k) (a b : ℝ≥0∞) (hab : a + b = 1)
    (y : Reservoir n k) (r : R.Seed) (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (L.mix R a b hab).policy.decide (y, .inr r) t i x H =
      R.policy.decide (y, r) t i x H := by
  change R.decide r (trainingTranscript (L.mix R a b hab).request (.inr r) y) t i x H = _
  rw [mix_transcript_inr]
  rfl

theorem mix_hardBudget (L R : Learner n k) (a b : ℝ≥0∞) (hab : a + b = 1)
    (r : (L.mix R a b hab).Seed) (y : Reservoir n k) (i : Fin n) :
    requests (trainingTranscript (L.mix R a b hab).request r y) i ≤ k :=
  (L.mix R a b hab).hard_budget r y i

theorem mix_reward_inl (L R : Learner n k) (a b : ℝ≥0∞) (hab : a + b = 1)
    (y : Reservoir n k) (r : L.Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    (L.mix R a b hab).policy.reward (y, .inl r) D x u =
      L.policy.reward (y, r) D x u :=
  (Policy.outcomes_eq_of_actions_eq _ _ _ _ D x u
    (fun _ => mix_decide_inl L R a b hab y r _ _ _ _)).1

theorem mix_reward_inr (L R : Learner n k) (a b : ℝ≥0∞) (hab : a + b = 1)
    (y : Reservoir n k) (r : R.Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    (L.mix R a b hab).policy.reward (y, .inr r) D x u =
      R.policy.reward (y, r) D x u :=
  (Policy.outcomes_eq_of_actions_eq _ _ _ _ D x u
    (fun _ => mix_decide_inr L R a b hab y r _ _ _ _)).1

end Learner
end ProphetSecretary.Model
