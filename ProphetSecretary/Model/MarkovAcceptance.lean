import ProphetSecretary.Reach.Pathwise
import Mathlib.Data.EReal.Basic

/-!
# Markov acceptance rules with deletion monotonicity

A Boolean acceptance rule permits rejection of every value, including the extended
threshold `+∞`, and acceptance of every value, including `−∞`. Deletion monotonicity
is required only for valid times, nonnegative offers, and unseen sets containing the
candidate. The pending-execution comparison is proved from the observed histories.
-/

open Set
open scoped Classical

namespace ProphetSecretary.Model

variable {Seed : Type*} {n : ℕ}

/-- A Markov rule reads the seed, unseen identities, elapsed time, current identity,
and current value. It does not read earlier values except through unseen identities. -/
noncomputable def markovPolicy
    (accept : Seed → Finset (Fin n) → ℝ → Fin n → ℝ → Bool) : Policy Seed n where
  decide r t i x h := accept r (unseen h) t i x

/-- Removing unseen alternatives can only increase acceptance, on the paper's valid
observation domain. No behavior outside the support of the online model is constrained. -/
def DeletionMonotoneAcceptance
    (accept : Seed → Finset (Fin n) → ℝ → Fin n → ℝ → Bool) : Prop :=
  ∀ r t, t ∈ Icc (0 : ℝ) 1 → ∀ i x, 0 ≤ x → ∀ A B,
    i ∈ A → A ⊆ B → accept r B t i x = true → accept r A t i x = true

lemma mem_unseen_at_own_clock (D : Finset (Fin n)) (x u : Fin n → ℝ) (i : Fin n) :
    i ∈ unseen (history D x u (u i)) := by
  simp [unseen, history]

lemma markovPolicy.accepted_pending_subset
    (accept : Seed → Finset (Fin n) → ℝ → Fin n → ℝ → Bool)
    (ha : DeletionMonotoneAcceptance accept) (r : Seed) (x u : Fin n → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hu : ∀ j, u j ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    (markovPolicy accept).accepted r (Finset.univ.erase i) x u ⊆
      (markovPolicy accept).accepted r Finset.univ x u := by
  intro j hj
  obtain ⟨_, hj⟩ := ((markovPolicy accept).mem_accepted r _ x u j).mp hj
  apply ((markovPolicy accept).mem_accepted r _ x u j).mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  exact ha r (u j) (hu j) j (x j) (hx j) _ _
    (mem_unseen_at_own_clock Finset.univ x u j)
    (unseen_subset_pending x u i (u j)) hj

/-- This is a consequence of the constructed pending execution, not an interface
assumption about the policy's stopping time. -/
lemma markovPolicy.stoppingTime_le_pendingTime
    (accept : Seed → Finset (Fin n) → ℝ → Fin n → ℝ → Bool)
    (ha : DeletionMonotoneAcceptance accept) (r : Seed) (x u : Fin n → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hu : ∀ j, u j ∈ Icc (0 : ℝ) 1) (i : Fin n) :
    (markovPolicy accept).stoppingTime r Finset.univ x u ≤
      (markovPolicy accept).pendingTime r x u i := by
  unfold Policy.pendingTime Policy.stoppingTime
  apply Finset.le_min'
  intro t ht
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact (markovPolicy accept).stoppingTime_le_one r Finset.univ x u
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ht
    exact (markovPolicy accept).stoppingTime_le_of_accepted r Finset.univ x u j
      (markovPolicy.accepted_pending_subset accept ha r x u hx hu i hj)

/-- Extended thresholds include rules which accept no finite offer or every offer. -/
noncomputable def extendedThresholdPolicy
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → EReal) : Policy Seed n :=
  markovPolicy (fun r A t i x => decide (θ r A t i ≤ (x : EReal)))

def MonotoneExtendedThresholds
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → EReal) : Prop :=
  ∀ r t, t ∈ Icc (0 : ℝ) 1 → ∀ i A B, i ∈ A → A ⊆ B → θ r A t i ≤ θ r B t i

lemma extendedThresholdPolicy.deletionMonotone
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → EReal) (hθ : MonotoneExtendedThresholds θ) :
    DeletionMonotoneAcceptance (fun r A t i x => decide (θ r A t i ≤ (x : EReal))) := by
  intro r t ht i x _hx A B hi hAB hacc
  simp only [decide_eq_true_eq] at hacc ⊢
  exact (hθ r t ht i A B hi hAB).trans hacc

lemma extendedThresholdPolicy.real_eq
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → ℝ) :
    extendedThresholdPolicy (fun r A t i => (θ r A t i : EReal)) = thresholdPolicy θ := by
  unfold extendedThresholdPolicy markovPolicy thresholdPolicy
  congr 1
  funext r t i x h
  simp only [EReal.coe_le_coe_iff]

lemma realThreshold_deletionMonotone
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → ℝ) (hθ : MonotoneThresholds θ) :
    DeletionMonotoneAcceptance (fun r A t i x => decide (θ r A t i ≤ x)) := by
  intro r t _ht i x _hx A B hi hAB hacc
  simp only [decide_eq_true_eq] at hacc ⊢
  exact (hθ r t i A B hi hAB).trans hacc

@[simp] lemma extendedThresholdPolicy_top :
    extendedThresholdPolicy (fun (_ : Seed) (_ : Finset (Fin n)) (_ : ℝ) (_ : Fin n) => (⊤ : EReal)) =
      (⟨fun _ _ _ _ _ => false⟩ : Policy Seed n) := by
  simp [extendedThresholdPolicy, markovPolicy]

@[simp] lemma extendedThresholdPolicy_bot :
    extendedThresholdPolicy (fun (_ : Seed) (_ : Finset (Fin n)) (_ : ℝ) (_ : Fin n) => (⊥ : EReal)) =
      (⟨fun _ _ _ _ _ => true⟩ : Policy Seed n) := by
  simp [extendedThresholdPolicy, markovPolicy]

end ProphetSecretary.Model
