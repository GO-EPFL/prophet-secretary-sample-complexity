import ProphetSecretary.Limiting.CountableFirstAcceptance
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Outcome convergence from actual countable acceptance decisions

Pointwise eventual action agreement becomes agreement on each early time
window because a common positive linear acceptance floor leaves only finitely
many relevant candidates there. This proves reward/duration convergence as an
execution statement, separately from convergence of optimized scalar values.
-/

open Set Filter
open scoped Topology Classical

namespace ProphetSecretary.Limiting.FirstAcceptance

variable {Ω : Type*}

lemma reward_of_no_first (a : ℝ) {A : Ω → ℕ → Prop} {u x : Ω → ℕ → ℝ} {ω : Ω}
    (h : ¬∃ i, Earliest A u ω i) : reward a A u x ω = a := by
  rw [reward,(selectedCode_eq_zero_iff _ _ _).mpr h,if_pos rfl]

lemma earliest_of_prefix_agreement {A D : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω}
    {i : ℕ} {q : ℝ} (hi : Earliest A u ω i) (hiq : u ω i ≤ q)
    (hAgree : ∀ j, u ω j ≤ q → (D ω j ↔ A ω j)) : Earliest D u ω i := by
  refine ⟨(hAgree i hiq).mpr hi.1,?_⟩
  intro j hj
  by_cases hjq : u ω j ≤ q
  · exact hi.2 j ((hAgree j hjq).mp hj)
  · have hlt : u ω i < u ω j := hiq.trans_lt (not_le.mp hjq)
    exact ⟨hlt.le,fun he => False.elim ((ne_of_lt hlt) he)⟩

lemma prefix_agreement_eventually_of_linear_floor
    (A : Ω → ℕ → Prop) (As : ℕ → Ω → ℕ → Prop) (present : Ω → ℕ → Prop)
    (u x : Ω → ℕ → ℝ) (ω : Ω) {γ : ℝ} (hγ : 0 < γ)
    (hLocal : ∀ d > (0 : ℝ), {i | present ω i ∧ d < x ω i}.Finite)
    (hPresent : ∀ i, A ω i → present ω i) (hPresents : ∀ n i, As n ω i → present ω i)
    (hFloor : ∀ i, A ω i → γ*(1-u ω i) ≤ x ω i)
    (hFloors : ∀ n i, As n ω i → γ*(1-u ω i) ≤ x ω i)
    (hPoint : ∀ i, present ω i → ∀ᶠ n in atTop, As n ω i ↔ A ω i) :
    ∀ q < (1 : ℝ), ∀ᶠ n in atTop, ∀ i, u ω i ≤ q → (As n ω i ↔ A ω i) := by
  intro q hq
  let d := γ*(1-q)/2
  have hd : 0 < d := div_pos (mul_pos hγ (sub_pos.mpr hq)) (by norm_num)
  let S : Set ℕ := {i | present ω i ∧ d < x ω i}
  have hS : S.Finite := hLocal d hd
  have hAll : ∀ᶠ n in atTop, ∀ i ∈ S, As n ω i ↔ A ω i :=
    hS.eventually_all.mpr (fun i hi => hPoint i hi.1)
  filter_upwards [hAll] with n hn
  intro i hiq
  by_cases hiS : i ∈ S
  · exact hn i hiS
  have hSmall (hF : γ*(1-u ω i) ≤ x ω i) : d < x ω i := by
    have hMono := mul_le_mul_of_nonneg_left (sub_le_sub_left hiq 1) hγ.le
    have hPos := mul_pos hγ (sub_pos.mpr hq)
    dsimp only [d]
    linarith only [hF,hMono,hPos]
  constructor
  · intro hi
    exact False.elim (hiS ⟨hPresents n i hi,hSmall (hFloors n i hi)⟩)
  · intro hi
    exact False.elim (hiS ⟨hPresent i hi,hSmall (hFloor i hi)⟩)

/-- A pointwise execution lemma. Every accepted point is an actual present
candidate; high-valued candidates are locally finite and actual clocks are
strictly preterminal. The target has an attained first point if it accepts. -/
theorem outcomes_tendsto_of_pointwise_actions
    (A : Ω → ℕ → Prop) (As : ℕ → Ω → ℕ → Prop) (present : Ω → ℕ → Prop)
    (u x : Ω → ℕ → ℝ) (ω : Ω) {γ H : ℝ} (hγ : 0 < γ) (hH : 0 ≤ H)
    (hLocal : ∀ d > (0 : ℝ), {i | present ω i ∧ d < x ω i}.Finite)
    (hTimes : ∀ i, present ω i → u ω i ∈ Ioo (0 : ℝ) 1)
    (hValues : ∀ i, present ω i → x ω i ∈ Icc (0 : ℝ) H)
    (hPresent : ∀ i, A ω i → present ω i) (hPresents : ∀ n i, As n ω i → present ω i)
    (hFloor : ∀ i, A ω i → γ*(1-u ω i) ≤ x ω i)
    (hFloors : ∀ n i, As n ω i → γ*(1-u ω i) ≤ x ω i)
    (hFirst : HasFirstIfAccepted A u ω)
    (hPoint : ∀ i, present ω i → ∀ᶠ n in atTop, As n ω i ↔ A ω i) :
    Tendsto (fun n => reward 0 (As n) u x ω) atTop (𝓝 (reward 0 A u x ω)) ∧
      Tendsto (fun n => stoppingTime (As n) u ω) atTop (𝓝 (stoppingTime A u ω)) := by
  have hPrefix := prefix_agreement_eventually_of_linear_floor A As present u x ω hγ hLocal
    hPresent hPresents hFloor hFloors hPoint
  by_cases hAny : ∃ i, A ω i
  · obtain ⟨i,hi⟩ := hFirst hAny
    have hTime : u ω i < 1 := (hTimes i (hPresent i hi.1)).2
    have hEarliest : ∀ᶠ n in atTop, Earliest (As n) u ω i :=
      (hPrefix (u ω i) hTime).mono (fun _ hn => earliest_of_prefix_agreement hi le_rfl hn)
    have hReward : ∀ᶠ n in atTop, reward 0 (As n) u x ω = reward 0 A u x ω :=
      hEarliest.mono (fun _ hn => (reward_of_earliest 0 hn).trans (reward_of_earliest 0 hi).symm)
    have hDuration : ∀ᶠ n in atTop, stoppingTime (As n) u ω = stoppingTime A u ω :=
      hEarliest.mono (fun _ hn => (stoppingTime_of_earliest hn).trans (stoppingTime_of_earliest hi).symm)
    exact ⟨Tendsto.congr' (hReward.mono (fun _ he => he.symm)) tendsto_const_nhds,Tendsto.congr' (hDuration.mono (fun _ he => he.symm)) tendsto_const_nhds⟩
  have hNoFirst : ¬∃ i, Earliest A u ω i := by rintro ⟨i,hi⟩; exact hAny ⟨i,hi.1⟩
  rw [reward_of_no_first 0 hNoFirst,stoppingTime_of_no_first hNoFirst]
  constructor
  · apply tendsto_order.mpr
    constructor
    · intro l hl
      exact Eventually.of_forall (fun n => hl.trans_le
        (reward_bounded (a := 0) ⟨le_rfl,hH⟩ (fun i hi => hValues i (hPresents n i hi))).1)
    · intro r hr
      let d := r/2
      have hd : 0 < d := by dsimp only [d]; positivity
      let S : Set ℕ := {i | present ω i ∧ d < x ω i}
      have hS : S.Finite := hLocal d hd
      have hAvoid : ∀ᶠ n in atTop, ∀ i ∈ S, ¬As n ω i := by
        apply hS.eventually_all.mpr
        intro i hi
        filter_upwards [hPoint i hi.1] with n hn
        intro hAi
        exact hAny ⟨i,hn.mp hAi⟩
      filter_upwards [hAvoid] with n hn
      have hBound : reward 0 (As n) u x ω ≤ d := by
        by_cases hEarliest : ∃ i, Earliest (As n) u ω i
        · obtain ⟨i,hi⟩ := hEarliest
          rw [reward_of_earliest 0 hi]
          apply le_of_not_gt
          intro hHigh
          exact hn i ⟨hPresents n i hi.1,hHigh⟩ hi.1
        · rw [reward_of_no_first 0 hEarliest]
          exact hd.le
      exact hBound.trans_lt (by dsimp only [d]; linarith only [hr])
  · apply tendsto_order.mpr
    constructor
    · intro l hl
      filter_upwards [hPrefix l hl] with n hn
      by_cases hEarliest : ∃ i, Earliest (As n) u ω i
      · obtain ⟨i,hi⟩ := hEarliest
        rw [stoppingTime_of_earliest hi]
        apply lt_of_not_ge
        intro hIl
        exact hAny ⟨i,(hn i hIl).mp hi.1⟩
      · rw [stoppingTime_of_no_first hEarliest]
        exact hl
    · intro r hr
      exact Eventually.of_forall (fun n => (stoppingTime_le_one
        (fun i hi => (hTimes i (hPresents n i hi)).2.le)).trans_lt hr)

end ProphetSecretary.Limiting.FirstAcceptance
