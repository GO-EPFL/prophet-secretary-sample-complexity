import ProphetSecretary.Limiting.CountablePendingDuration

/-!
# Exact prefixes of the kept-pending countable execution

Before the candidate clock, the auxiliary and actual callbacks receive exactly
the same histories. This is proved for the complete countable history,
including every zero-valued identity. The infimum comparison does not require
an attained first acceptance on the auxiliary terminal-clock slice.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

lemma individualHistory_pending_before (x u : ℕ → ℝ) (i : ℕ) {t : ℝ}
    (hti : t ≤ u i) (ht1 : t ≤ 1) :
    individualHistory (Function.update x i 0) (Function.update u i 1) t=individualHistory x u t := by
  funext j
  by_cases hji : j=i
  · subst j
    simp only [individualHistory,Function.update_self,if_neg (not_lt_of_ge hti),if_neg (not_lt_of_ge ht1)]
  · simp only [individualHistory,Function.update_of_ne hji]

lemma candidatePresent_keepIndividualPending (i : ℕ) (v : CompleteWorld Seed) (c : Candidate) :
    candidatePresent (keepIndividualPending i v) c ↔ candidatePresent v c := by
  cases c <;> rfl

lemma candidatePoint_keepIndividualPending_of_ne (i : ℕ) (v : CompleteWorld Seed) (c : Candidate)
    (hc : c ≠ Sum.inl i) : candidatePoint (keepIndividualPending i v) c=candidatePoint v c := by
  cases c with
  | inl j =>
    have hji : j ≠ i := fun h => hc (congrArg Sum.inl h)
    simp only [candidatePoint,keepIndividualPending,pendingIndividualWorld,Function.update_of_ne hji]
  | inr kj => rfl

lemma CountableRule.candidateAction_pending_before (π : CountableRule Seed) (i : ℕ)
    (v : CompleteWorld Seed) (c : Candidate) (hc : c ≠ Sum.inl i)
    (hti : (candidatePoint v c).1 ≤ v.2.2.1 i) (ht1 : (candidatePoint v c).1 ≤ 1) :
    π.candidateAction (keepIndividualPending i v) c=π.candidateAction v c := by
  have hPoint := candidatePoint_keepIndividualPending_of_ne i v c hc
  unfold CountableRule.candidateAction
  dsimp only [keepIndividualPending,pendingIndividualWorld] at hPoint ⊢
  rw [hPoint,individualHistory_pending_before v.2.1 v.2.2.1 i hti ht1]

lemma codeTime_pending_individual (i : ℕ) (v : CompleteWorld Seed) :
    codeTime (keepIndividualPending i v) (candidateEnumeration (Sum.inl i))=1 := by
  simp only [codeTime,codePoint,Equiv.symm_apply_apply,candidatePoint,keepIndividualPending,
    pendingIndividualWorld,Function.update_self]

lemma codeTime_individual (i : ℕ) (v : CompleteWorld Seed) :
    codeTime v (candidateEnumeration (Sum.inl i))=v.2.2.1 i := by
  simp only [codeTime,codePoint,Equiv.symm_apply_apply,candidatePoint]

lemma CountableRule.accepted_before_pending_iff (π : CountableRule Seed) (i : ℕ)
    (v : CompleteWorld Seed) {r : ℝ} (hr : r ≤ v.2.2.1 i) (hi1 : v.2.2.1 i ≤ 1) (k : ℕ) :
    (π.codeAccepted (keepIndividualPending i v) k ∧ codeTime (keepIndividualPending i v) k < r) ↔
      (π.codeAccepted v k ∧ codeTime v k < r) := by
  by_cases hc : candidateEnumeration.symm k=Sum.inl i
  · have hk : k=candidateEnumeration (Sum.inl i) := by
      simpa only [Equiv.apply_symm_apply] using congrArg candidateEnumeration hc
    subst k
    rw [codeTime_pending_individual,codeTime_individual]
    simp only [not_lt_of_ge hr,not_lt_of_ge (hr.trans hi1),and_false]
  · have hPoint := candidatePoint_keepIndividualPending_of_ne i v (candidateEnumeration.symm k) hc
    have hTime : codeTime (keepIndividualPending i v) k=codeTime v k := congrArg Prod.fst hPoint
    by_cases ht : codeTime v k < r
    · have hti : (candidatePoint v (candidateEnumeration.symm k)).1 ≤ v.2.2.1 i := ht.le.trans hr
      have ht1 : (candidatePoint v (candidateEnumeration.symm k)).1 ≤ 1 := hti.trans hi1
      have hAction := π.candidateAction_pending_before i v (candidateEnumeration.symm k) hc hti ht1
      have hPresent : codePresent (keepIndividualPending i v) k ↔ codePresent v k :=
        candidatePresent_keepIndividualPending i v _
      simp only [CountableRule.codeAccepted,hPresent,hTime,hAction]
    · rw [hTime]
      simp only [ht,and_false]

lemma CountableRule.le_pending_iff_le_infimum_before (π : CountableRule Seed) (i : ℕ)
    (v : CompleteWorld Seed) {r : ℝ} (hr : r ≤ v.2.2.1 i) (hi1 : v.2.2.1 i ≤ 1) :
    r ≤ π.pendingIndividualTime i v ↔ r ≤ π.infimumDuration v := by
  change r ≤ π.infimumDuration (keepIndividualPending i v) ↔ _
  rw [π.le_infimumDuration_iff,π.le_infimumDuration_iff]
  constructor
  · rintro ⟨h1,h⟩
    refine ⟨h1,?_⟩
    intro k hk
    by_contra hn
    have hp := (π.accepted_before_pending_iff i v hr hi1 k).mpr ⟨hk,lt_of_not_ge hn⟩
    exact (not_lt_of_ge (h k hp.1)) hp.2
  · rintro ⟨h1,h⟩
    refine ⟨h1,?_⟩
    intro k hk
    by_contra hn
    have hp := (π.accepted_before_pending_iff i v hr hi1 k).mp ⟨hk,lt_of_not_ge hn⟩
    exact (not_lt_of_ge (h k hp.1)) hp.2

lemma CountableRule.min_clock_pending_le_infimumDuration (π : CountableRule Seed) (i : ℕ)
    (v : CompleteWorld Seed) (hi1 : v.2.2.1 i ≤ 1) :
    min (v.2.2.1 i) (π.pendingIndividualTime i v) ≤ π.infimumDuration v :=
  (π.le_pending_iff_le_infimum_before i v (min_le_left _ _) hi1).mp (min_le_right _ _)

end ProphetSecretary.Limiting.CountableInstance
