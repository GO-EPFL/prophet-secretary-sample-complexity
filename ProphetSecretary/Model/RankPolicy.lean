import ProphetSecretary.Model.Outcome
import ProphetSecretary.Model.ArrivalRepresentation

/-!
# Policies observing arrival ranks

A rank history records each previously observed identity, its arrival rank,
and its value, including zero values. The callback sees the current rank and
offer and the strict past; the future permutation is used only to define the
analytical execution. No Markov restriction is imposed.
-/

open Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

abbrev RankHistory (n : ℕ) := Fin n → Option (Fin n × ℝ)

structure RankPolicy (Seed : Type*) (n : ℕ) where
  decide : Seed → Fin n → Fin n → ℝ → RankHistory n → Bool

variable {n : ℕ} {Seed : Type*}

noncomputable def rankHistory (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (k : Fin n) : RankHistory n :=
  fun j => if p.symm j < k then some (p.symm j,x j) else none

noncomputable def RankPolicy.action (π : RankPolicy Seed n) (r : Seed) (p : Equiv.Perm (Fin n))
    (x : Fin n → ℝ) (i : Fin n) : Bool :=
  π.decide r (p.symm i) i (x i) (rankHistory p x (p.symm i))

noncomputable def RankPolicy.accepted (π : RankPolicy Seed n) (r : Seed)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => π.action r p x i = true)

def RankPolicy.Reaches (π : RankPolicy Seed n) (r : Seed)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (i : Fin n) : Prop :=
  ∀ j∈π.accepted r p x, p.symm i ≤ p.symm j

def RankPolicy.Selects (π : RankPolicy Seed n) (r : Seed)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (i : Fin n) : Prop :=
  i∈π.accepted r p x ∧ π.Reaches r p x i

noncomputable def RankPolicy.reward (π : RankPolicy Seed n) (r : Seed)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, if π.Selects r p x i then x i else 0

lemma RankPolicy.mem_accepted (π : RankPolicy Seed n) (r : Seed)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (i : Fin n) :
    i∈π.accepted r p x ↔ π.action r p x i = true := by simp [RankPolicy.accepted]

lemma RankPolicy.selects_unique (π : RankPolicy Seed n) (r : Seed)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) {i j : Fin n}
    (hi : π.Selects r p x i) (hj : π.Selects r p x j) : i = j :=
  p.symm.injective (le_antisymm (hi.2 j hj.1) (hj.2 i hi.1))

/-- The pre-drawn numerical times are independent auxiliary randomness of the
rank policy. Only their entries attached to the current and past ranks are
passed to the original callback. -/
def Policy.clockToRank (π : Policy Seed n) : RankPolicy ((Fin n → ℝ) × Seed) n where
  decide sr k i x H := π.decide sr.2 (sr.1 k) i x
    (fun j => (H j).map (fun z => (sr.1 z.1,z.2)))

lemma rankHistory_to_time (s : Fin n → ℝ) (hs : StrictMono s)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (k : Fin n) :
    (fun j => (rankHistory p x k j).map (fun z => (s z.1,z.2))) =
      history Finset.univ x (Instance.reconstructClocks (s,p)) (s k) := by
  funext j
  simp only [rankHistory,history,Finset.mem_univ,true_and,Instance.reconstructClocks,hs.lt_iff_lt]
  split <;> rfl

lemma Policy.clockToRank_action (π : Policy Seed n) (r : Seed) (s : Fin n → ℝ)
    (hs : StrictMono s) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (i : Fin n) :
    π.clockToRank.action (s,r) p x i =
      π.action r Finset.univ x (Instance.reconstructClocks (s,p)) i := by
  change π.decide r (s (p.symm i)) i (x i) _ = π.decide r (s (p.symm i)) i (x i) _
  rw [rankHistory_to_time s hs]
  rfl

lemma Policy.clockToRank_accepted (π : Policy Seed n) (r : Seed) (s : Fin n → ℝ)
    (hs : StrictMono s) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    π.clockToRank.accepted (s,r) p x = π.accepted r Finset.univ x (Instance.reconstructClocks (s,p)) := by
  ext i
  simp only [RankPolicy.mem_accepted,Policy.mem_accepted,Finset.mem_univ,true_and,π.clockToRank_action r s hs]

lemma Policy.clockToRank_reaches (π : Policy Seed n) (r : Seed) (s : Fin n → ℝ)
    (hs : StrictMono s) (hUnit : ∀ k, s k ≤ 1) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (i : Fin n) :
    π.clockToRank.Reaches (s,r) p x i ↔ π.Reaches r x (Instance.reconstructClocks (s,p)) i := by
  rw [RankPolicy.Reaches,Policy.Reaches,π.le_stoppingTime_iff]
  rw [π.clockToRank_accepted r s hs]
  simp only [Instance.reconstructClocks,hs.le_iff_le]
  exact ⟨fun h => ⟨hUnit _,h⟩,And.right⟩

lemma Policy.clockToRank_selects (π : Policy Seed n) (r : Seed) (s : Fin n → ℝ)
    (hs : StrictMono s) (hUnit : ∀ k, s k ≤ 1) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (i : Fin n) :
    π.clockToRank.Selects (s,r) p x i ↔ π.Selects r Finset.univ x (Instance.reconstructClocks (s,p)) i := by
  rw [RankPolicy.Selects,π.clockToRank_reaches r s hs hUnit,
    π.clockToRank_accepted r s hs]
  constructor
  · rintro ⟨hi,hReach⟩
    exact ⟨hi,le_antisymm hReach (π.stoppingTime_le_of_accepted r Finset.univ x _ i hi)⟩
  · intro hi
    exact ⟨hi.1,le_of_eq hi.2⟩

lemma Policy.clockToRank_reward (π : Policy Seed n) (r : Seed) (s : Fin n → ℝ)
    (hs : StrictMono s) (hUnit : ∀ k, s k ≤ 1) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    π.clockToRank.reward (s,r) p x = π.reward r Finset.univ x (Instance.reconstructClocks (s,p)) := by
  unfold RankPolicy.reward Policy.reward
  apply Finset.sum_congr rfl
  intro i _
  have hInj : Function.Injective (Instance.reconstructClocks (s,p)) := hs.injective.comp p.symm.injective
  rw [π.actualSelects_iff_selects r Finset.univ x _ hInj,
    π.clockToRank_selects r s hs hUnit]

end ProphetSecretary.Model
