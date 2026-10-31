import ProphetSecretary.Limiting.CountableTruncationSelectedTagLimit
import ProphetSecretary.Limiting.HybridObserverPayoff
import ProphetSecretary.Stability.SelectedOccurrence

/-!
# Anonymous selected tags as observer payoffs

At distinct arrival times, the selected offer is anonymous exactly when the
stopping time differs from every retained individual's arrival time. A tag
vanishing at zero also gives zero when there is no acceptance. Thus this
coefficient is a measurable function of reward, duration, and retained clocks.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting
open CountableInstance

lemma finite_anonymousSelectedTag_eq {n q : ℕ} {Seed : Type*}
    (π : Model.Policy Seed (n+q)) (r : Seed) (x u : Fin (n+q) → ℝ)
    (φ : ℝ → ℝ) (hφ0 : φ 0=0) (hu : Function.Injective u) :
    π.selectedTag r x u (Fin.addCases (fun _ : Fin n => 0)
      (fun j : Fin q => φ (x (j.natAdd n)))) =
      if ∀ i : Fin n, π.stoppingTime r Finset.univ x u ≠ u (i.castAdd q)
      then φ (π.reward r Finset.univ x u) else 0 := by
  by_cases h : ∃ j, π.ActualSelects r Finset.univ x u j
  · obtain ⟨j,hj⟩ := h
    rw [π.selectedTag_eq_of_actualSelects r x u _ hj,
      π.reward_eq_of_actualSelects r Finset.univ x u hj,←hj.1.2]
    induction j using Fin.addCases with
    | left j =>
      rw [Fin.addCases_left,if_neg (fun h => h j rfl)]
    | right j =>
      rw [Fin.addCases_right,if_pos]
      intro i he
      have hVal := congrArg Fin.val (hu he)
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hVal
      omega
  · have hn : ∀ j, ¬π.ActualSelects r Finset.univ x u j := by simpa using h
    rw [π.selectedTag_eq_zero_of_no_selection r x u _ hn,
      π.reward_eq_zero_of_no_actualSelection r Finset.univ x u hn,hφ0]
    split_ifs <;> rfl

noncomputable def HybridRule.anonymousSelectedTagObservable {n : ℕ} {Seed : Type*}
    (π : HybridRule n Seed) (φ : ℝ → ℝ) (v : FiniteObserverWorld n Seed) : ℝ :=
  if ∀ i : Fin n, π.observableDuration v ≠ v.2.2.1 i then φ (π.observableReward 0 v) else 0

lemma HybridRule.measurable_anonymousSelectedTagObservable {n : ℕ} {Seed : Type*}
    [MeasurableSpace Seed] (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    {φ : ℝ → ℝ} (hφ : Measurable φ) : Measurable (π.anonymousSelectedTagObservable φ) := by
  apply Measurable.ite _ (hφ.comp (π.measurable_observableReward hπ 0)) measurable_const
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_eq_fun (π.measurable_observableDuration hπ) (by fun_prop)).compl

lemma CountableRule.anonymousSelectedTag_eq {N : ℕ} {Seed : Type*}
    (π : CountableRule Seed) (v : CompleteWorld Seed) (φ : ℝ → ℝ) (hφ0 : φ 0=0)
    (hRet : ∀ i, π.codeAccepted v (candidateEnumeration (Sum.inl i)) → i<N)
    (hu : Set.InjOn (fun c : Candidate => (candidatePoint v c).1) {c | candidatePresent v c}) :
    π.selectedTag (anonymousPerturbationTag φ) v =
      if ∀ i : Fin N, π.realizedDuration v ≠ v.2.2.1 i.val
      then φ (π.realizedReward 0 v) else 0 := by
  cases hCode : FirstAcceptance.selectedCode π.codeAccepted codeTime v with
  | zero =>
    simp [CountableRule.selectedTag,CountableRule.realizedReward,FirstAcceptance.reward,hCode,hφ0]
  | succ k =>
    have hk := (FirstAcceptance.selectedCode_eq_succ_iff _ _ _ _).mp hCode
    have hT := FirstAcceptance.stoppingTime_of_earliest hk
    have hR := FirstAcceptance.reward_of_earliest 0 (x:=codeValue) hk
    have hTag := FirstAcceptance.reward_of_earliest 0 (x:=anonymousPerturbationTag φ) hk
    change FirstAcceptance.reward 0 π.codeAccepted codeTime (anonymousPerturbationTag φ) v = _
    rw [hTag]
    change _ = if ∀ i : Fin N, FirstAcceptance.stoppingTime π.codeAccepted codeTime v ≠ v.2.2.1 i.val
      then φ (FirstAcceptance.reward 0 π.codeAccepted codeTime codeValue v) else 0
    rw [hT,hR]
    cases he : candidateEnumeration.symm k with
    | inl j =>
      have hjCode : k=candidateEnumeration (Sum.inl j) := by
        simpa only [Equiv.apply_symm_apply] using congrArg candidateEnumeration he
      have hj := hRet j (by rw [←hjCode]; exact hk.1)
      have hTime : codeTime v k=v.2.2.1 j := by simp only [codeTime,codePoint,he,candidatePoint]
      simp only [anonymousPerturbationTag,he,hTime]
      rw [if_neg (fun h => h ⟨j,hj⟩ rfl)]
    | inr p =>
      simp only [anonymousPerturbationTag,he]
      rw [if_pos]
      intro i hTime
      have hPresent : candidatePresent v (candidateEnumeration.symm k) := hk.1.1
      have hTime' : (candidatePoint v (candidateEnumeration.symm k)).1 =
          (candidatePoint v (Sum.inl i.val)).1 := hTime
      have hEq := hu hPresent (show candidatePresent v (Sum.inl i.val) from trivial) hTime'
      rw [he] at hEq
      cases hEq

end ProphetSecretary.Limiting
