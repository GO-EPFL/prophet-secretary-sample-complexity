import ProphetSecretary.Model.Policy

/-!
# Pending-variable executions

Pathwise part of `lem:monotone-reach` = `lem:strict-reach`. Keeping `i` pending means
running the same history-dependent decisions on all other offers, without ever revealing
`i`. In particular this auxiliary execution does not read either coordinate of `i`.
-/

namespace ProphetSecretary.Model

open scoped Classical

variable {Seed : Type*} {n : ℕ}

/-- The auxiliary execution suppresses `i` and keeps its identity unseen. -/
noncomputable def Policy.pendingTime (π : Policy Seed n) (r : Seed)
    (x u : Fin n → ℝ) (i : Fin n) : ℝ :=
  π.stoppingTime r (Finset.univ.erase i) x u

/-- Until `i` arrives, the ordinary and pending observers have identical histories. -/
theorem history_erase_of_le (x u : Fin n → ℝ) (i : Fin n) {t : ℝ} (ht : t ≤ u i) :
    history (Finset.univ.erase i) x u t = history Finset.univ x u t := by
  classical
  funext j
  by_cases hji : j = i
  · subst j
    simp [history, not_lt_of_ge ht]
  · simp [history, hji]

theorem Policy.action_pending_eq (π : Policy Seed n) (r : Seed)
    (x u : Fin n → ℝ) (i j : Fin n) (ht : u j ≤ u i) :
    π.action r (Finset.univ.erase i) x u j = π.action r Finset.univ x u j := by
  unfold Policy.action
  rw [history_erase_of_le x u i ht]

/-- Suppressing an identity removes all functional dependence on its value and clock.
This equality is proved from the execution, not imposed as an independence assumption. -/
theorem Policy.pendingTime_update (π : Policy Seed n) (r : Seed)
    (x u : Fin n → ℝ) (i : Fin n) (a b : ℝ) :
    π.pendingTime r (Function.update x i a) (Function.update u i b) i =
      π.pendingTime r x u i := by
  classical
  apply π.stoppingTime_congr
  · intro j hj
    exact Function.update_of_ne (Finset.mem_erase.mp hj).1 _ _
  · intro j hj
    exact Function.update_of_ne (Finset.mem_erase.mp hj).1 _ _

theorem Policy.reaches_iff_le_pendingTime (π : Policy Seed n) (r : Seed)
    (x u : Fin n → ℝ) (i : Fin n) (hi : u i ≤ 1) :
    π.Reaches r x u i ↔ u i ≤ π.pendingTime r x u i := by
  classical
  unfold Policy.Reaches Policy.pendingTime
  rw [π.le_stoppingTime_iff, π.le_stoppingTime_iff]
  constructor
  · rintro ⟨_, h⟩
    refine ⟨hi, ?_⟩
    intro j hj
    by_cases ht : u i ≤ u j
    · exact ht
    · apply h j
      obtain ⟨_, hj⟩ := (π.mem_accepted r _ x u j).mp hj
      exact (π.mem_accepted r _ x u j).mpr ⟨Finset.mem_univ _, by
        rw [← π.action_pending_eq r x u i j (le_of_lt (lt_of_not_ge ht))]
        exact hj⟩
  · rintro ⟨_, h⟩
    refine ⟨hi, ?_⟩
    intro j hj
    by_cases ht : u i ≤ u j
    · exact ht
    · apply h j
      obtain ⟨_, hj⟩ := (π.mem_accepted r _ x u j).mp hj
      have hji : j ≠ i := by intro e; subst j; exact ht le_rfl
      exact (π.mem_accepted r _ x u j).mpr ⟨Finset.mem_erase.mpr ⟨hji,
        Finset.mem_univ _⟩, by
          rw [π.action_pending_eq r x u i j (le_of_lt (lt_of_not_ge ht))]
          exact hj⟩

/-- The actual execution cannot stop before both the candidate and the pending run. -/
theorem Policy.min_le_stoppingTime (π : Policy Seed n) (r : Seed)
    (x u : Fin n → ℝ) (i : Fin n) (hi : u i ≤ 1) :
    min (u i) (π.pendingTime r x u i) ≤ π.stoppingTime r Finset.univ x u := by
  classical
  apply (π.le_stoppingTime_iff r Finset.univ x u _).mpr
  refine ⟨(min_le_left _ _).trans hi, ?_⟩
  intro j hj
  by_cases ht : u i ≤ u j
  · exact (min_le_left _ _).trans ht
  · apply (min_le_right _ _).trans
    apply π.stoppingTime_le_of_accepted
    obtain ⟨_, hj⟩ := (π.mem_accepted r _ x u j).mp hj
    have hji : j ≠ i := by intro e; subst j; exact ht le_rfl
    exact (π.mem_accepted r _ x u j).mpr ⟨Finset.mem_erase.mpr ⟨hji,
      Finset.mem_univ _⟩, by
        rw [π.action_pending_eq r x u i j (le_of_lt (lt_of_not_ge ht))]
        exact hj⟩

/-- The pending execution still considers every unobserved identity to be unseen. -/
noncomputable def unseen (h : History n) : Finset (Fin n) :=
  Finset.univ.filter fun j => h j = none

noncomputable def thresholdPolicy
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → ℝ) : Policy Seed n where
  decide r t j x h := decide (θ r (unseen h) t j ≤ x)

/-- The threshold at fixed time and candidate is nondecreasing under adding unseen
identities. This is exactly the extra hypothesis of `lem:strict-reach`. -/
def MonotoneThresholds (θ : Seed → Finset (Fin n) → ℝ → Fin n → ℝ) : Prop :=
  ∀ r t j A B, j ∈ A → A ⊆ B → θ r A t j ≤ θ r B t j

theorem unseen_subset_pending (x u : Fin n → ℝ) (i : Fin n) (t : ℝ) :
    unseen (history Finset.univ x u t) ⊆
      unseen (history (Finset.univ.erase i) x u t) := by
  classical
  intro j hj
  simp only [unseen, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
  by_cases hji : j = i
  · subst j
    simp [history]
  · simpa [history, hji] using hj

theorem thresholdPolicy.accepted_pending_subset
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → ℝ) (hθ : MonotoneThresholds θ)
    (r : Seed) (x u : Fin n → ℝ) (i : Fin n) :
    (thresholdPolicy θ).accepted r (Finset.univ.erase i) x u ⊆
      (thresholdPolicy θ).accepted r Finset.univ x u := by
  classical
  intro j hj
  obtain ⟨_, hj⟩ := ((thresholdPolicy θ).mem_accepted r _ x u j).mp hj
  apply ((thresholdPolicy θ).mem_accepted r _ x u j).mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  simp only [Policy.action, thresholdPolicy, decide_eq_true_eq] at hj ⊢
  exact (hθ r (u j) j _ _ (by simp [unseen, history])
    (unseen_subset_pending x u i (u j))).trans hj

/-- Deleting unseen options lowers monotone thresholds, hence can only hasten stopping. -/
theorem thresholdPolicy.stoppingTime_le_pendingTime
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → ℝ) (hθ : MonotoneThresholds θ)
    (r : Seed) (x u : Fin n → ℝ) (i : Fin n) :
    (thresholdPolicy θ).stoppingTime r Finset.univ x u ≤
      (thresholdPolicy θ).pendingTime r x u i := by
  classical
  unfold Policy.pendingTime Policy.stoppingTime
  apply Finset.le_min'
  intro y hy
  rcases Finset.mem_insert.mp hy with rfl | hy
  · exact (thresholdPolicy θ).stoppingTime_le_one r Finset.univ x u
  · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact (thresholdPolicy θ).stoppingTime_le_of_accepted r Finset.univ x u j
      (thresholdPolicy.accepted_pending_subset θ hθ r x u i hj)

/-- On selecting `i`, the improvement in stopping time is exactly `σ-Uᵢ`. Elsewhere
it is nonnegative. Integration yields the selection-weighted slack in the paper. -/
theorem thresholdPolicy.selection_slack
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → ℝ) (hθ : MonotoneThresholds θ)
    (r : Seed) (x u : Fin n → ℝ) (i : Fin n) :
    (if (thresholdPolicy θ).Selects r Finset.univ x u i then
        (thresholdPolicy θ).pendingTime r x u i - u i else 0) ≤
      (thresholdPolicy θ).pendingTime r x u i -
        (thresholdPolicy θ).stoppingTime r Finset.univ x u := by
  classical
  split_ifs with h
  · exact le_of_eq (congrArg ((thresholdPolicy θ).pendingTime r x u i - ·) h.2)
  · exact sub_nonneg.mpr (thresholdPolicy.stoppingTime_le_pendingTime θ hθ r x u i)

end ProphetSecretary.Model
