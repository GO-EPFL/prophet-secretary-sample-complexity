import ProphetSecretary.Model.TerminalFallbackPolicy
import ProphetSecretary.Model.TerminalWindowProbabilities
import ProphetSecretary.Model.TerminalReward
import ProphetSecretary.Model.ConstantThreshold

/-!
# Terminal-window reward and duration comparison

A terminal payoff is implemented approximately by an actual causal policy that
uses the dense supply in the final window. The failure event is unconditional.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

lemma Policy.fallbackAfter_reward_ge_level (π : Policy Seed n) (s ℓ b : ℝ)
    (hℓb : ℓ ≤ b) (hπ : ∀ r t i x H, π.decide r t i x H = true → b < x)
    (r : Seed) (x u : Fin n → ℝ) (hu : ∀ i, u i ≤ 1)
    (hLate : lateExceedance x u s ℓ) :
    ℓ ≤ (π.fallbackAfter s ℓ).reward r Finset.univ x u := by
  let σ := π.fallbackAfter s ℓ
  obtain ⟨i,hit,hix⟩ := hLate
  have hai : i ∈ σ.accepted r Finset.univ x u := by
    apply (σ.mem_accepted r Finset.univ x u i).mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [π.fallbackAfter_action_after s ℓ r Finset.univ x u i hit]
    exact decide_eq_true hix
  obtain ⟨j,hj⟩ := σ.exists_actualSelects_of_accepted r Finset.univ x u hu ⟨i,hai⟩
  rw [σ.reward_eq_of_actualSelects r Finset.univ x u hj]
  have hact := ((σ.mem_accepted r Finset.univ x u j).mp hj.1.1).2
  exact (π.fallbackAfter_acceptsAbove s ℓ b hℓb hπ r (u j) j (x j)
    (history Finset.univ x u (u j)) hact).le

lemma Policy.terminalReward_le_fallbackAfter_add (π : Policy Seed n) (s ℓ b H : ℝ)
    (hℓ : 0 ≤ ℓ) (hℓb : ℓ ≤ b) (hbH : b ≤ H)
    (hπ : ∀ r t i y G, π.decide r t i y G = true → b < y)
    (r : Seed) (x u : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i ∧ x i ≤ H)
    (hu : ∀ i, u i ≤ 1) (hDistinct : Function.Injective u) :
    (if ∃ i, π.ActualSelects r Finset.univ x u i then π.reward r Finset.univ x u else b)
      ≤ (π.fallbackAfter s ℓ).reward r Finset.univ x u + (b-ℓ) +
        H*(if lateExceedance x u s b then 1 else 0) +
        H*(if ¬lateExceedance x u s ℓ then 1 else 0) := by
  let σ := π.fallbackAfter s ℓ
  have hb : 0 ≤ b := hℓ.trans hℓb
  have hH : 0 ≤ H := hb.trans hbH
  have hR0 : 0 ≤ σ.reward r Finset.univ x u := σ.reward_nonnegative _ _ _ _ (fun i => (hx i).1)
  have hHigh : 0 ≤ H*(if lateExceedance x u s b then 1 else 0) := by positivity
  have hFail : 0 ≤ H*(if ¬lateExceedance x u s ℓ then 1 else 0) := by positivity
  by_cases hEarly : ∃ i, π.ActualSelects r Finset.univ x u i ∧ u i < s
  · obtain ⟨i,hi,hit⟩ := hEarly
    rw [if_pos ⟨i,hi⟩]
    have he := π.fallbackAfter_reward_eq_of_early_selection s ℓ r Finset.univ x u hDistinct hi hit
    change σ.reward r Finset.univ x u = π.reward r Finset.univ x u at he
    linarith only [he,hHigh,hFail,hℓb]
  · have hOld : (if ∃ i, π.ActualSelects r Finset.univ x u i then π.reward r Finset.univ x u else b)
        ≤ b + H*(if lateExceedance x u s b then 1 else 0) := by
      by_cases hs : ∃ i, π.ActualSelects r Finset.univ x u i
      · obtain ⟨i,hi⟩ := hs
        have ht : s ≤ u i := le_of_not_gt (fun h => hEarly ⟨i,hi,h⟩)
        have ha := ((π.mem_accepted r Finset.univ x u i).mp hi.1.1).2
        have hv := hπ r (u i) i (x i) (history Finset.univ x u (u i)) ha
        rw [if_pos ⟨i,hi⟩,if_pos (show lateExceedance x u s b from ⟨i,ht,hv⟩),
          π.reward_eq_of_actualSelects r Finset.univ x u hi]
        linarith [(hx i).2]
      · rw [if_neg hs]
        exact le_add_of_nonneg_right hHigh
    have hNew : ℓ ≤ σ.reward r Finset.univ x u + H*(if ¬lateExceedance x u s ℓ then 1 else 0) := by
      by_cases hl : lateExceedance x u s ℓ
      · rw [if_neg (not_not.mpr hl),mul_zero,add_zero]
        exact π.fallbackAfter_reward_ge_level s ℓ b hℓb hπ r x u hu hl
      · rw [if_pos hl,mul_one]
        linarith only [hR0,hℓb,hbH]
    linarith only [hOld,hNew]

end ProphetSecretary.Model
