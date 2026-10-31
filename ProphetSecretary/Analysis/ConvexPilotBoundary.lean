import Mathlib.Analysis.Convex.Jensen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Normed.Field.Basic

/-!
# Two deterministic level points for a convex empirical minimizer

A continuous convex true objective has at most two relevant level locations,
one on each side of a reference point. They are chosen from the true objective
before the empirical objective is seen. Convexity of the latter then transfers
its reference-point bound to a selected true-level point.
-/

open Set

namespace ProphetSecretary.Analysis

/-- The finite set depends only on F, its interval, the reference point and s.
In particular, it is independent of the empirical convex function G and its
chosen minimizer b. This is the two-location step preceding `eq:bayes-pilot`. -/
theorem exists_two_pilot_level_points {F : ℝ → ℝ} {lo hi a s : ℝ}
    (hF : ConvexOn ℝ (Icc lo hi) F) (hFc : ContinuousOn F (Icc lo hi))
    (ha : a ∈ Icc lo hi) (hFa : F a ≤ s) :
    ∃ D : Finset ℝ, D.card ≤ 2 ∧ (∀ x ∈ D, x ∈ Icc lo hi ∧ F x = s) ∧
      ∀ (G : ℝ → ℝ), ConvexOn ℝ (Icc lo hi) G → ∀ b ∈ Icc lo hi,
        s < F b → G b ≤ G a → ∃ x ∈ D, G x ≤ G a := by
  classical
  let L : Prop := ∃ x ∈ Icc lo hi, x ≤ a ∧ F x = s
  let R : Prop := ∃ x ∈ Icc lo hi, a ≤ x ∧ F x = s
  let DL : Finset ℝ := if h : L then {h.choose} else ∅
  let DR : Finset ℝ := if h : R then {h.choose} else ∅
  have hDL : DL.card ≤ 1 := by dsimp only [DL]; split <;> simp
  have hDR : DR.card ≤ 1 := by dsimp only [DR]; split <;> simp
  have hLeft : ∀ x ∈ DL, x ∈ Icc lo hi ∧ F x = s := by
    intro x hx
    dsimp only [DL] at hx
    split at hx
    · rename_i h
      have he : x = h.choose := Finset.mem_singleton.mp hx
      subst x
      exact ⟨h.choose_spec.1,h.choose_spec.2.2⟩
    · exact False.elim (Finset.notMem_empty _ hx)
  have hRight : ∀ x ∈ DR, x ∈ Icc lo hi ∧ F x = s := by
    intro x hx
    dsimp only [DR] at hx
    split at hx
    · rename_i h
      have he : x = h.choose := Finset.mem_singleton.mp hx
      subst x
      exact ⟨h.choose_spec.1,h.choose_spec.2.2⟩
    · exact False.elim (Finset.notMem_empty _ hx)
  refine ⟨DL ∪ DR,?_,?_,?_⟩
  · have h := Finset.card_union_le DL DR
    omega
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hLeft x hx
    · exact hRight x hx
  · intro G hG b hb hFb hGb
    rcases le_total b a with hba | hab
    · have hLocal : ContinuousOn F (Icc b a) := hFc.mono
        (Icc_subset_Icc hb.1 ha.2)
      obtain ⟨r,hr,hFr⟩ := intermediate_value_Icc' hba hLocal ⟨hFa,hFb.le⟩
      have hL : L := ⟨r,⟨hb.1.trans hr.1,hr.2.trans ha.2⟩,hr.2,hFr⟩
      have hx : hL.choose ∈ Icc lo hi := hL.choose_spec.1
      have hxa : hL.choose ≤ a := hL.choose_spec.2.1
      have hxF : F hL.choose = s := hL.choose_spec.2.2
      have hbx : b ≤ hL.choose := by
        by_contra hn
        have hxb : hL.choose ≤ b := (lt_of_not_ge hn).le
        have h := hF.le_max_of_mem_Icc hx ha ⟨hxb,hba⟩
        rw [hxF,max_eq_left hFa] at h
        exact hFb.not_ge h
      refine ⟨hL.choose,Finset.mem_union_left _ ?_,?_⟩
      · simp only [DL,dif_pos hL,Finset.mem_singleton]
      · exact (hG.le_max_of_mem_Icc hb ha ⟨hbx,hxa⟩).trans (max_le hGb le_rfl)
    · have hLocal : ContinuousOn F (Icc a b) := hFc.mono
        (Icc_subset_Icc ha.1 hb.2)
      obtain ⟨r,hr,hFr⟩ := intermediate_value_Icc hab hLocal ⟨hFa,hFb.le⟩
      have hR : R := ⟨r,⟨ha.1.trans hr.1,hr.2.trans hb.2⟩,hr.1,hFr⟩
      have hx : hR.choose ∈ Icc lo hi := hR.choose_spec.1
      have hax : a ≤ hR.choose := hR.choose_spec.2.1
      have hxF : F hR.choose = s := hR.choose_spec.2.2
      have hxb : hR.choose ≤ b := by
        by_contra hn
        have hbx : b ≤ hR.choose := (lt_of_not_ge hn).le
        have h := hF.le_max_of_mem_Icc ha hx ⟨hab,hbx⟩
        rw [hxF,max_eq_right hFa] at h
        exact hFb.not_ge h
      refine ⟨hR.choose,Finset.mem_union_right _ ?_,?_⟩
      · simp only [DR,dif_pos hR,Finset.mem_singleton]
      · exact (hG.le_max_of_mem_Icc ha hb ⟨hax,hxb⟩).trans (max_le le_rfl hGb)

end ProphetSecretary.Analysis
