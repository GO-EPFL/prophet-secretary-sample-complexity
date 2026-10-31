import ProphetSecretary.Limiting.FirstAcceptanceOutcomeLimit

/-!
# Bounded selected tags in a countable execution

Different tags force a discrepancy of reward or physical stopping time, or
a close pair of distinct positive occurrences. The argument does not require
finitely many candidates and never supplies analytical tags to a callback.
-/

open Set
open scoped Classical

namespace ProphetSecretary.Limiting.FirstAcceptance

variable {Ω : Type*}

def ClosePositivePair (present : ℕ → Prop) (b η : ℝ) (x u : ℕ → ℝ) : Prop :=
  ∃ i j, i ≠ j ∧ present i ∧ present j ∧ b < x i ∧ b < x j ∧ |u i-u j| ≤ η

lemma reward_abs_le (A : Ω → ℕ → Prop) (u a : Ω → ℕ → ℝ) (ω : Ω)
    {D : ℝ} (hD : 0 ≤ D) (ha : ∀ i, |a ω i| ≤ D) : |reward 0 A u a ω| ≤ D := by
  by_cases h : selectedCode A u ω=0
  · simpa only [reward,h,if_pos,abs_zero] using hD
  · simpa only [reward,if_neg h] using ha (selectedCode A u ω-1)

lemma selectedTag_ne_implies (A B : Ω → ℕ → Prop) (u x a : Ω → ℕ → ℝ) (ω : Ω)
    (present : ℕ → Prop) (hA : ∀ i, A ω i → present i) (hB : ∀ i, B ω i → present i)
    {b η : ℝ} (hb : 0 < b) (hzero : ∀ i, x ω i < b → a ω i=0)
    (hne : reward 0 A u a ω ≠ reward 0 B u a ω) :
    b/2 ≤ |reward 0 A u x ω-reward 0 B u x ω| ∨
      η ≤ |stoppingTime A u ω-stoppingTime B u ω| ∨
      ClosePositivePair present (b/2) η (x ω) (u ω) := by
  by_cases hPa : ∃ i, Earliest A u ω i
  · obtain ⟨i,hi⟩ := hPa
    by_cases hPb : ∃ j, Earliest B u ω j
    · obtain ⟨j,hj⟩ := hPb
      have hneTag : a ω i ≠ a ω j := by
        simpa only [reward_of_earliest 0 hi,reward_of_earliest 0 hj] using hne
      have hij : i ≠ j := fun he => hneTag (congrArg (a ω) he)
      have hHigh : b ≤ x ω i ∨ b ≤ x ω j := by
        by_cases hxi : x ω i < b
        · exact Or.inr (le_of_not_gt (fun hxj => hneTag ((hzero i hxi).trans (hzero j hxj).symm)))
        · exact Or.inl (le_of_not_gt hxi)
      by_cases hR : b/2 ≤ |reward 0 A u x ω-reward 0 B u x ω|
      · exact Or.inl hR
      by_cases hT : η ≤ |stoppingTime A u ω-stoppingTime B u ω|
      · exact Or.inr (Or.inl hT)
      apply Or.inr ∘ Or.inr
      rw [reward_of_earliest 0 hi,reward_of_earliest 0 hj] at hR
      have habs := abs_lt.mp (lt_of_not_ge hR)
      have hix : b/2 < x ω i := by rcases hHigh with h | h <;> linarith
      have hjx : b/2 < x ω j := by rcases hHigh with h | h <;> linarith
      refine ⟨i,j,hij,hA i hi.1,hB j hj.1,hix,hjx,?_⟩
      rw [stoppingTime_of_earliest hi,stoppingTime_of_earliest hj] at hT
      exact (lt_of_not_ge hT).le
    · have hneTag : a ω i ≠ 0 := by
        simpa only [reward_of_earliest 0 hi,reward_of_no_first 0 hPb] using hne
      have hix : b ≤ x ω i := le_of_not_gt (fun h => hneTag (hzero i h))
      apply Or.inl
      rw [reward_of_earliest 0 hi,reward_of_no_first 0 hPb,sub_zero,abs_of_pos (hb.trans_le hix)]
      linarith only [hix,hb]
  · by_cases hPb : ∃ j, Earliest B u ω j
    · obtain ⟨j,hj⟩ := hPb
      have hneTag : a ω j ≠ 0 := by
        intro he
        apply hne
        rw [reward_of_no_first 0 hPa,reward_of_earliest 0 hj,he]
      have hjx : b ≤ x ω j := le_of_not_gt (fun h => hneTag (hzero j h))
      apply Or.inl
      rw [reward_of_no_first 0 hPa,reward_of_earliest 0 hj,zero_sub,abs_neg,abs_of_pos (hb.trans_le hjx)]
      linarith only [hjx,hb]
    · apply False.elim
      apply hne
      rw [reward_of_no_first 0 hPa,reward_of_no_first 0 hPb]

lemma selectedTag_difference_le (A B : Ω → ℕ → Prop) (u x a : Ω → ℕ → ℝ) (ω : Ω)
    (present : ℕ → Prop) (hA : ∀ i, A ω i → present i) (hB : ∀ i, B ω i → present i)
    {D b η : ℝ} (hD : 0 ≤ D) (hb : 0 < b) (hη : 0 < η)
    (ha : ∀ i, |a ω i| ≤ D) (hzero : ∀ i, x ω i < b → a ω i=0) :
    |reward 0 A u a ω-reward 0 B u a ω| ≤
      2*D*(2*|reward 0 A u x ω-reward 0 B u x ω|/b+
        |stoppingTime A u ω-stoppingTime B u ω|/η+
        if ClosePositivePair present (b/2) η (x ω) (u ω) then 1 else 0) := by
  have hR : 0 ≤ 2*|reward 0 A u x ω-reward 0 B u x ω|/b := by positivity
  have hT : 0 ≤ |stoppingTime A u ω-stoppingTime B u ω|/η := by positivity
  have hI : (0 : ℝ) ≤ if ClosePositivePair present (b/2) η (x ω) (u ω) then 1 else 0 := by
    split_ifs <;> norm_num
  by_cases hEq : reward 0 A u a ω=reward 0 B u a ω
  · rw [hEq,sub_self,abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) hD) (add_nonneg (add_nonneg hR hT) hI)
  have hTag : |reward 0 A u a ω-reward 0 B u a ω| ≤ 2*D := by
    have h := abs_sub_le (reward 0 A u a ω) 0 (reward 0 B u a ω)
    have hA' := reward_abs_le A u a ω hD ha
    have hB' := reward_abs_le B u a ω hD ha
    rw [sub_zero,zero_sub,abs_neg] at h
    linarith only [h,hA',hB']
  have hOne : 1 ≤ 2*|reward 0 A u x ω-reward 0 B u x ω|/b+
      |stoppingTime A u ω-stoppingTime B u ω|/η+
      if ClosePositivePair present (b/2) η (x ω) (u ω) then 1 else 0 := by
    rcases selectedTag_ne_implies A B u x a ω present hA hB hb hzero hEq with h | h | h
    · have hR1 : 1 ≤ 2*|reward 0 A u x ω-reward 0 B u x ω|/b := (le_div_iff₀ hb).mpr (by linarith only [h])
      linarith only [hR1,hT,hI]
    · have hT1 : 1 ≤ |stoppingTime A u ω-stoppingTime B u ω|/η := (le_div_iff₀ hη).mpr (by linarith only [h])
      linarith only [hR,hT1,hI]
    · rw [if_pos h]
      linarith only [hR,hT]
  exact hTag.trans (by simpa only [mul_one] using
    mul_le_mul_of_nonneg_left hOne (show 0 ≤ 2*D by positivity))

end ProphetSecretary.Limiting.FirstAcceptance
