import ProphetSecretary.Limiting.CountableIndividualPayloadRule

/-!
# Exact execution of causally reconstructed payloads

Before the affected arrival, tag blindness justifies the default tag. At its
arrival and afterward, the current or observed value reconstructs the actual
payload. Thus every candidate action agrees with the reconstructed old world,
without evaluating a future displayed value inside a callback.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance

variable {Seed U T : Type*}

lemma payloadTagAtHistory_seen (i : ℕ) (F : ℝ × U → ℝ × T) (t0 : T) (u : U)
    (x clocks : ℕ → ℝ) {t : ℝ} (ht : clocks i<t) :
    payloadTagAtHistory i F t0 u (individualHistory x clocks t)=(F (x i,u)).2 := by
  simp only [payloadTagAtHistory,individualHistory,if_pos ht,reduceCtorEq,if_false,observedIndividualValue]

lemma payloadTagAtHistory_unseen (i : ℕ) (F : ℝ × U → ℝ × T) (t0 : T) (u : U)
    (x clocks : ℕ → ℝ) {t : ℝ} (ht : ¬clocks i<t) :
    payloadTagAtHistory i F t0 u (individualHistory x clocks t)=t0 := by
  simp only [payloadTagAtHistory,individualHistory,if_neg ht,if_true]

lemma CountableRule.pullbackIndividualPayload_candidateAction (π : CountableRule (Seed × T))
    (i : ℕ) (F : ℝ × U → ℝ × T) (t0 : T) (hBlind : π.TagBlindBefore i)
    (v : CompleteWorld (Seed × U)) (k : Candidate) :
    (π.pullbackIndividualPayload i F t0).candidateAction v k=
      π.candidateAction (recoverIndividualPayloadWorld i F v) k := by
  cases k with
  | inl j =>
    by_cases hji : j=i
    · subst j
      simp only [CountableRule.candidateAction,candidatePoint,CountableRule.pullbackIndividualPayload,
        recoverIndividualPayloadWorld,if_true,Function.update_self]
      rw [mapSingleIndividualHistory_actual]
    · simp only [CountableRule.candidateAction,candidatePoint,CountableRule.pullbackIndividualPayload,
        recoverIndividualPayloadWorld,if_neg hji]
      change π.individual (v.2.2.2.1,payloadTagAtHistory i F t0 v.2.2.2.2 (individualHistory v.2.1 v.2.2.1 (v.2.2.1 j)))
        (v.2.2.1 j) j (v.2.1 j)
        (mapSingleIndividualHistory i (fun y => (F (y,v.2.2.2.2)).1) (individualHistory v.2.1 v.2.2.1 (v.2.2.1 j)))
        (anonymousHistory v.1 (v.2.2.1 j))=
        π.individual (v.2.2.2.1,(F (v.2.1 i,v.2.2.2.2)).2) (v.2.2.1 j) j
          (Function.update v.2.1 i (F (v.2.1 i,v.2.2.2.2)).1 j)
          (individualHistory (Function.update v.2.1 i (F (v.2.1 i,v.2.2.2.2)).1) v.2.2.1 (v.2.2.1 j))
          (anonymousHistory v.1 (v.2.2.1 j))
      rw [mapSingleIndividualHistory_actual,Function.update_of_ne hji]
      by_cases ht : v.2.2.1 i<v.2.2.1 j
      · rw [payloadTagAtHistory_seen i F t0 _ _ _ ht]
      · rw [payloadTagAtHistory_unseen i F t0 _ _ _ ht]
        exact hBlind.1 _ _ _ _ _ _ _ _ hji (by simp only [individualHistory,if_neg ht])
  | inr kj =>
    let p := candidatePoint v (Sum.inr kj)
    change π.poisson (v.2.2.2.1,payloadTagAtHistory i F t0 v.2.2.2.2 (individualHistory v.2.1 v.2.2.1 p.1)) p.1 p.2
      (mapSingleIndividualHistory i (fun y => (F (y,v.2.2.2.2)).1) (individualHistory v.2.1 v.2.2.1 p.1))
      (anonymousHistory v.1 p.1)=
      π.poisson (v.2.2.2.1,(F (v.2.1 i,v.2.2.2.2)).2) p.1 p.2
        (individualHistory (Function.update v.2.1 i (F (v.2.1 i,v.2.2.2.2)).1) v.2.2.1 p.1) (anonymousHistory v.1 p.1)
    rw [mapSingleIndividualHistory_actual]
    by_cases ht : v.2.2.1 i<p.1
    · rw [payloadTagAtHistory_seen i F t0 _ _ _ ht]
    · rw [payloadTagAtHistory_unseen i F t0 _ _ _ ht]
      exact hBlind.2 _ _ _ _ _ _ _ (by simp only [individualHistory,if_neg ht])

end ProphetSecretary.Limiting.CountableInstance
