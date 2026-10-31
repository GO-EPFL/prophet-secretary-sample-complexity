import ProphetSecretary.Model.RankPolicy
import Mathlib.Order.Interval.Finset.Fin

/-!
# From a rank-observing policy to a clock-observing policy

Only the current clock history is inspected. Present identities are counted
regardless of their values, and the rank of each past identity is recovered by
counting present entries at strictly earlier times. The current identity gives
a total fallback rank on malformed histories. No future permutation is supplied
to the callback.
-/

open Set
open scoped Classical
namespace ProphetSecretary.Model
variable {n : ℕ} {Seed : Type*}

noncomputable def clockHistoryPresent (H : History n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => H j≠none)

noncomputable def clockHistoryBefore (H : History n) (t : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => ∃ z : ℝ × ℝ, H j=some z ∧ z.1<t)

/-- The fallback is used only off the valid finite-history domain. -/
def clockHistoryRank (fallback : Fin n) (k : ℕ) : Fin n :=
  if hk : k<n then ⟨k,hk⟩ else fallback

lemma clockHistoryRank_of_fin (fallback k : Fin n) : clockHistoryRank fallback k.val=k := by
  rw [clockHistoryRank,dif_pos k.is_lt]

noncomputable def currentRankFromClock (fallback : Fin n) (H : History n) : Fin n :=
  clockHistoryRank fallback (clockHistoryPresent H).card

noncomputable def rankHistoryFromClock (fallback : Fin n) (H : History n) : RankHistory n :=
  fun j => (H j).map (fun z => (clockHistoryRank fallback (clockHistoryBefore H z.1).card,z.2))

noncomputable def RankPolicy.rankToClock (π : RankPolicy Seed n) : Policy Seed n where
  decide r _ i x H := π.decide r (currentRankFromClock i H) i x (rankHistoryFromClock i H)

lemma card_filter_permutation_lt (p : Equiv.Perm (Fin n)) (k : Fin n) :
    (Finset.univ.filter (fun j : Fin n => p.symm j<k)).card=k.val := by
  calc
    _=(Finset.Iio k).card := by
      apply Finset.card_bij (fun j _ => p.symm j)
      · intro j hj
        exact Finset.mem_Iio.mpr (Finset.mem_filter.mp hj).2
      · intro j _ l _ he
        exact p.symm.injective he
      · intro l hl
        refine ⟨p l,?_ ,by simp⟩
        simpa only [Finset.mem_filter,Finset.mem_univ,true_and,Equiv.symm_apply_apply] using Finset.mem_Iio.mp hl
    _=k.val := Fin.card_Iio k

lemma clockHistoryPresent_at_rank (s : Fin n → ℝ) (hs : StrictMono s)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (k : Fin n) :
    clockHistoryPresent (history Finset.univ x (Instance.reconstructClocks (s,p)) (s k))=
      Finset.univ.filter (fun j => p.symm j<k) := by
  ext j
  by_cases hj : p.symm j<k <;>
    simp [clockHistoryPresent,history,Instance.reconstructClocks,hs.lt_iff_lt,hj]

lemma clockHistoryBefore_at_rank (s : Fin n → ℝ) (hs : StrictMono s)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (k l : Fin n) (hlk : l≤k) :
    clockHistoryBefore (history Finset.univ x (Instance.reconstructClocks (s,p)) (s k)) (s l)=
      Finset.univ.filter (fun j => p.symm j<l) := by
  ext j
  by_cases hj : p.symm j<k
  · simp only [clockHistoryBefore,Finset.mem_filter,Finset.mem_univ,true_and,history,
      Instance.reconstructClocks,hs.lt_iff_lt,if_pos hj,Option.some.injEq,exists_eq_left']
  · have hjl : ¬p.symm j<l := fun h => hj (h.trans_le hlk)
    simp [clockHistoryBefore,history,Instance.reconstructClocks,hs.lt_iff_lt,hj,hjl]

lemma currentRankFromClock_at_rank (fallback : Fin n) (s : Fin n → ℝ) (hs : StrictMono s)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (k : Fin n) :
    currentRankFromClock fallback (history Finset.univ x (Instance.reconstructClocks (s,p)) (s k))=k := by
  rw [currentRankFromClock,clockHistoryPresent_at_rank s hs p x k,card_filter_permutation_lt,clockHistoryRank_of_fin]

lemma rankHistoryFromClock_at_rank (fallback : Fin n) (s : Fin n → ℝ) (hs : StrictMono s)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (k : Fin n) :
    rankHistoryFromClock fallback (history Finset.univ x (Instance.reconstructClocks (s,p)) (s k))=rankHistory p x k := by
  funext j
  by_cases hj : p.symm j<k
  · change (if _ then some _ else none).map _=if p.symm j<k then some _ else none
    rw [if_pos (by simpa only [Finset.mem_univ,true_and,Instance.reconstructClocks,hs.lt_iff_lt] using hj),if_pos hj,Option.map_some]
    change some (clockHistoryRank fallback (clockHistoryBefore
      (history Finset.univ x (Instance.reconstructClocks (s,p)) (s k)) (s (p.symm j))).card,x j)=some (p.symm j,x j)
    rw [clockHistoryBefore_at_rank s hs p x k (p.symm j) hj.le,card_filter_permutation_lt,clockHistoryRank_of_fin]
  · simp [rankHistoryFromClock,history,rankHistory,Instance.reconstructClocks,hs.lt_iff_lt,hj]

lemma RankPolicy.rankToClock_action (π : RankPolicy Seed n) (r : Seed) (s : Fin n → ℝ)
    (hs : StrictMono s) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (i : Fin n) :
    π.rankToClock.action r Finset.univ x (Instance.reconstructClocks (s,p)) i=π.action r p x i := by
  change π.decide r (currentRankFromClock i (history Finset.univ x (Instance.reconstructClocks (s,p)) (s (p.symm i))))
    i (x i) (rankHistoryFromClock i (history Finset.univ x (Instance.reconstructClocks (s,p)) (s (p.symm i))))=_
  rw [currentRankFromClock_at_rank i s hs p x (p.symm i),rankHistoryFromClock_at_rank i s hs p x (p.symm i)]
  rfl

lemma RankPolicy.rankToClock_accepted (π : RankPolicy Seed n) (r : Seed) (s : Fin n → ℝ)
    (hs : StrictMono s) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    π.rankToClock.accepted r Finset.univ x (Instance.reconstructClocks (s,p))=π.accepted r p x := by
  ext i
  simp only [Policy.mem_accepted,Finset.mem_univ,true_and,π.rankToClock_action r s hs,RankPolicy.mem_accepted]

lemma RankPolicy.rankToClock_reaches (π : RankPolicy Seed n) (r : Seed) (s : Fin n → ℝ)
    (hs : StrictMono s) (hUnit : ∀ k, s k≤1) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (i : Fin n) :
    π.rankToClock.Reaches r x (Instance.reconstructClocks (s,p)) i ↔ π.Reaches r p x i := by
  rw [Policy.Reaches,π.rankToClock.le_stoppingTime_iff,π.rankToClock_accepted r s hs]
  simp only [Instance.reconstructClocks,hs.le_iff_le,RankPolicy.Reaches]
  exact ⟨And.right,fun h => ⟨hUnit _,h⟩⟩

lemma RankPolicy.rankToClock_selects (π : RankPolicy Seed n) (r : Seed) (s : Fin n → ℝ)
    (hs : StrictMono s) (hUnit : ∀ k, s k≤1) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (i : Fin n) :
    π.rankToClock.Selects r Finset.univ x (Instance.reconstructClocks (s,p)) i ↔ π.Selects r p x i := by
  rw [RankPolicy.Selects,←π.rankToClock_reaches r s hs hUnit]
  constructor
  · intro h
    exact ⟨by rw [←π.rankToClock_accepted r s hs];exact h.1,le_of_eq h.2⟩
  · rintro ⟨hi,hReach⟩
    have hi' := hi
    rw [←π.rankToClock_accepted r s hs] at hi'
    exact ⟨hi',le_antisymm hReach (π.rankToClock.stoppingTime_le_of_accepted r Finset.univ x _ i hi')⟩

lemma RankPolicy.rankToClock_reward (π : RankPolicy Seed n) (r : Seed) (s : Fin n → ℝ)
    (hs : StrictMono s) (hUnit : ∀ k, s k≤1) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    π.rankToClock.reward r Finset.univ x (Instance.reconstructClocks (s,p))=π.reward r p x := by
  unfold Policy.reward RankPolicy.reward
  apply Finset.sum_congr rfl
  intro i _
  have hInj : Function.Injective (Instance.reconstructClocks (s,p)) := hs.injective.comp p.symm.injective
  rw [π.rankToClock.actualSelects_iff_selects r Finset.univ x _ hInj,π.rankToClock_selects r s hs hUnit]

end ProphetSecretary.Model
