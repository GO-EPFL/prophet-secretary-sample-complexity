import ProphetSecretary.Limiting.CountablePendingPrefix
import ProphetSecretary.Limiting.CountableHistoryMask
import ProphetSecretary.Limiting.CountableMaskOrder

/-!
# Actual countable Markov rules and monotone thresholds

The callbacks read the unseen identity mask, elapsed time, current identity
or anonymous kind, current value and independent seed. They do not read past
values or anonymous construction labels. Deletion monotonicity is stated on
actual acceptance decisions and is derived from monotonicity of thresholds.
The pending-duration domination below is proved from these callbacks.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

noncomputable def countableMarkovRule
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool) : CountableRule Seed where
  individual r t i x H _ := accept r (unseenMask H) t (some i) x
  poisson r t x H _ := accept r (unseenMask H) t none x

def DeletionMonotoneCountableAcceptance
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool) : Prop :=
  ∀ r t, t ∈ Icc (0 : ℝ) 1 →
    (∀ i A D x, A i=true → MaskLe A D → accept r D t (some i) x=true → accept r A t (some i) x=true) ∧
    (∀ A D x, MaskLe A D → accept r D t none x=true → accept r A t none x=true)

noncomputable def countableThresholdRule
    (θ : Seed → IndividualMask → ℝ → Option ℕ → ℝ) : CountableRule Seed :=
  countableMarkovRule (fun r A t i x => decide (θ r A t i ≤ x))

def MonotoneCountableThresholds (θ : Seed → IndividualMask → ℝ → Option ℕ → ℝ) : Prop :=
  ∀ r t, t ∈ Icc (0 : ℝ) 1 →
    (∀ i A D, A i=true → MaskLe A D → θ r A t (some i) ≤ θ r D t (some i)) ∧
    (∀ A D, MaskLe A D → θ r A t none ≤ θ r D t none)

lemma thresholdAcceptance_deletionMonotone
    (θ : Seed → IndividualMask → ℝ → Option ℕ → ℝ) (hθ : MonotoneCountableThresholds θ) :
    DeletionMonotoneCountableAcceptance (fun r A t i x => decide (θ r A t i ≤ x)) := by
  intro r t ht
  constructor
  · intro i A D x hi hAD hAccept
    exact decide_eq_true ((hθ r t ht).1 i A D hi hAD |>.trans (of_decide_eq_true hAccept))
  · intro A D x hAD hAccept
    exact decide_eq_true ((hθ r t ht).2 A D hAD |>.trans (of_decide_eq_true hAccept))

lemma unseenMask_pending_mono (x u : ℕ → ℝ) (i : ℕ) {t : ℝ} (ht1 : t ≤ 1) :
    MaskLe (unseenMask (individualHistory x u t))
      (unseenMask (individualHistory (Function.update x i 0) (Function.update u i 1) t)) := by
  intro j hj
  rw [unseenMask_individualHistory] at hj ⊢
  simp only [decide_eq_true_eq] at hj ⊢
  by_cases hji : j=i
  · subst j
    simpa only [Function.update_self] using ht1
  · simpa only [Function.update_of_ne hji] using hj

lemma countableMarkovRule_accepts_pending_implies
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (hAccept : DeletionMonotoneCountableAcceptance accept) (i : ℕ) (v : CompleteWorld Seed)
    (c : Candidate) (hc : c ≠ Sum.inl i) (ht : (candidatePoint v c).1 ∈ Icc (0 : ℝ) 1)
    (hPending : (countableMarkovRule accept).candidateAction (keepIndividualPending i v) c=true) :
    (countableMarkovRule accept).candidateAction v c=true := by
  have hPoint := candidatePoint_keepIndividualPending_of_ne i v c hc
  have hMasks := unseenMask_pending_mono v.2.1 v.2.2.1 i ht.2
  unfold CountableRule.candidateAction at hPending ⊢
  dsimp only [keepIndividualPending,pendingIndividualWorld] at hPoint hPending
  rw [hPoint] at hPending
  cases c with
  | inl j =>
    apply (hAccept v.2.2.2 (v.2.2.1 j) ht).1 j _ _ (v.2.1 j) _ hMasks hPending
    rw [unseenMask_individualHistory]
    exact decide_eq_true le_rfl
  | inr kj =>
    exact (hAccept v.2.2.2 (candidatePoint v (Sum.inr kj)).1 ht).2 _ _ _ hMasks hPending

/-- This domination holds for the analytical infimum on every raw vector;
actual admissibility is needed only when converting its mean to policy duration. -/
theorem countableMarkovRule_infimum_le_pending
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool)
    (hAccept : DeletionMonotoneCountableAcceptance accept) (i : ℕ) (v : CompleteWorld Seed) :
    (countableMarkovRule accept).infimumDuration v ≤ (countableMarkovRule accept).pendingIndividualTime i v := by
  let π := countableMarkovRule accept
  apply (π.le_infimumDuration_iff (keepIndividualPending i v) (π.infimumDuration v)).mpr
  refine ⟨(π.infimumDuration_bounds v).2,?_⟩
  intro k hk
  by_cases hc : candidateEnumeration.symm k=Sum.inl i
  · have hkCode : k=candidateEnumeration (Sum.inl i) := by
      simpa only [Equiv.apply_symm_apply] using congrArg candidateEnumeration hc
    rw [hkCode,codeTime_pending_individual]
    exact (π.infimumDuration_bounds v).2
  · have hPoint := candidatePoint_keepIndividualPending_of_ne i v (candidateEnumeration.symm k) hc
    have hTime : codeTime (keepIndividualPending i v) k=codeTime v k := congrArg Prod.fst hPoint
    have hPresent : codePresent v k := (candidatePresent_keepIndividualPending i v _).mp hk.1
    have ht : (candidatePoint v (candidateEnumeration.symm k)).1 ∈ Icc (0 : ℝ) 1 := by
      change codeTime v k ∈ Icc (0 : ℝ) 1
      rw [← hTime]
      exact hk.2.1
    have hAction := countableMarkovRule_accepts_pending_implies accept hAccept i v _ hc ht hk.2.2
    have hActual : π.codeAccepted v k := ⟨hPresent,ht,hAction⟩
    rw [hTime]
    exact ((π.le_infimumDuration_iff v (π.infimumDuration v)).mp le_rfl).2 k hActual

end ProphetSecretary.Limiting.CountableInstance
