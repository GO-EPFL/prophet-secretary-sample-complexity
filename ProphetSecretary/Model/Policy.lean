import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Fin

/-!
# Finite online executions

The history records every previously observed identity, time, and value, including zero
values. A decision may depend on this entire history and on an independent random seed.
The declarations in this file are pathwise; probabilistic uses impose measurability on
the decision function and independence on the seed.
-/

namespace ProphetSecretary.Model

abbrev History (n : ℕ) := Fin n → Option (ℝ × ℝ)

/-- The action at a reached offer, before any offer has been accepted. Evaluating this
function also after the first acceptance is an analytical convention, not an observation
available to the executed policy. -/
structure Policy (Seed : Type*) (n : ℕ) where
  decide : Seed → ℝ → Fin n → ℝ → History n → Bool

variable {Seed : Type*} {n : ℕ}

/-- Restrict the observer to identities in `D`; an absent identity has not arrived.
The current candidate is supplied separately, and does not occur in its strict past. -/
noncomputable def history (D : Finset (Fin n)) (x u : Fin n → ℝ) (t : ℝ) : History n :=
  fun j => if j ∈ D ∧ u j < t then some (u j, x j) else none

noncomputable def Policy.action (π : Policy Seed n) (r : Seed) (D : Finset (Fin n))
    (x u : Fin n → ℝ) (j : Fin n) : Bool :=
  π.decide r (u j) j (x j) (history D x u (u j))

/-- Potential acceptances. The execution selects the earliest of these. -/
noncomputable def Policy.accepted (π : Policy Seed n) (r : Seed) (D : Finset (Fin n))
    (x u : Fin n → ℝ) : Finset (Fin n) :=
  D.filter fun j => π.action r D x u j = true

/-- Include the terminal convention `1` even when nothing is accepted. -/
noncomputable def Policy.stopTimes (π : Policy Seed n) (r : Seed) (D : Finset (Fin n))
    (x u : Fin n → ℝ) : Finset ℝ :=
  insert 1 ((π.accepted r D x u).image u)

noncomputable def Policy.stoppingTime (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) : ℝ :=
  (π.stopTimes r D x u).min' ⟨1, Finset.mem_insert_self _ _⟩

/-- At distinct arrival times there is at most one selected identity. -/
def Policy.Selects (π : Policy Seed n) (r : Seed) (D : Finset (Fin n))
    (x u : Fin n → ℝ) (i : Fin n) : Prop :=
  i ∈ π.accepted r D x u ∧ u i = π.stoppingTime r D x u

/-- No offer is accepted strictly before `i` arrives. -/
def Policy.Reaches (π : Policy Seed n) (r : Seed) (x u : Fin n → ℝ) (i : Fin n) : Prop :=
  u i ≤ π.stoppingTime r Finset.univ x u

@[simp] theorem Policy.mem_accepted (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (j : Fin n) :
    j ∈ π.accepted r D x u ↔ j ∈ D ∧ π.action r D x u j = true := by
  classical
  simp [Policy.accepted]

theorem Policy.stoppingTime_le_one (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) : π.stoppingTime r D x u ≤ 1 := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem Policy.stoppingTime_le_of_accepted (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (j : Fin n)
    (hj : j ∈ π.accepted r D x u) : π.stoppingTime r D x u ≤ u j := by
  classical
  exact Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨j, hj, rfl⟩))

theorem Policy.le_stoppingTime_iff (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (a : ℝ) :
    a ≤ π.stoppingTime r D x u ↔ a ≤ 1 ∧ ∀ j ∈ π.accepted r D x u, a ≤ u j := by
  classical
  constructor
  · intro h
    exact ⟨h.trans (π.stoppingTime_le_one r D x u), fun j hj =>
      h.trans (π.stoppingTime_le_of_accepted r D x u j hj)⟩
  · rintro ⟨h1, h⟩
    apply Finset.le_min'
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact h1
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      exact h j hj

theorem Policy.stoppingTime_nonneg (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (hu : ∀ j, 0 ≤ u j) :
    0 ≤ π.stoppingTime r D x u :=
  (π.le_stoppingTime_iff r D x u 0).mpr ⟨zero_le_one, fun j _ => hu j⟩

theorem Policy.selects_unique (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (hu : Function.Injective u)
    {i j : Fin n} (hi : π.Selects r D x u i) (hj : π.Selects r D x u j) : i = j :=
  hu (hi.2.trans hj.2.symm)

theorem history_congr {D : Finset (Fin n)} {x x' u u' : Fin n → ℝ}
    (hx : ∀ j ∈ D, x j = x' j) (hu : ∀ j ∈ D, u j = u' j) (t : ℝ) :
    history D x u t = history D x' u' t := by
  classical
  funext j
  by_cases hj : j ∈ D
  · simp only [history, hj, true_and, hx j hj, hu j hj]
  · simp [history, hj]

theorem Policy.action_congr (π : Policy Seed n) (r : Seed) {D : Finset (Fin n)}
    {x x' u u' : Fin n → ℝ} (hx : ∀ j ∈ D, x j = x' j)
    (hu : ∀ j ∈ D, u j = u' j) {j : Fin n} (hj : j ∈ D) :
    π.action r D x u j = π.action r D x' u' j := by
  simp only [Policy.action, hx j hj, hu j hj, history_congr hx hu]

theorem Policy.accepted_congr (π : Policy Seed n) (r : Seed) {D : Finset (Fin n)}
    {x x' u u' : Fin n → ℝ} (hx : ∀ j ∈ D, x j = x' j)
    (hu : ∀ j ∈ D, u j = u' j) :
    π.accepted r D x u = π.accepted r D x' u' := by
  classical
  ext j
  by_cases hj : j ∈ D
  · simp only [Policy.mem_accepted, hj, true_and, π.action_congr r hx hu hj]
  · simp [hj]

theorem Policy.stoppingTime_congr (π : Policy Seed n) (r : Seed) {D : Finset (Fin n)}
    {x x' u u' : Fin n → ℝ} (hx : ∀ j ∈ D, x j = x' j)
    (hu : ∀ j ∈ D, u j = u' j) :
    π.stoppingTime r D x u = π.stoppingTime r D x' u' := by
  classical
  have ha := π.accepted_congr r hx hu
  have ht : π.stopTimes r D x u = π.stopTimes r D x' u' := by
    simp only [Policy.stopTimes, ← ha]
    congr 1
    apply Finset.image_congr
    intro j hj
    exact hu j (π.mem_accepted r D x u j |>.mp hj).1
  unfold Policy.stoppingTime
  simp only [ht]

end ProphetSecretary.Model
