import ProphetSecretary.Model.Outcome

/-!
# A causal terminal-window fallback policy

Before a fixed cutoff the original callback is unchanged. Afterwards the policy
accepts the first offer strictly above a fixed level. Identities, zero-valued
arrivals, and the original strict history remain available as in the finite model.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

noncomputable def Policy.fallbackAfter (π : Policy Seed n) (s ℓ : ℝ) : Policy Seed n where
  decide r t i x H := if t < s then π.decide r t i x H else _root_.Decidable.decide (ℓ < x)

lemma Policy.fallbackAfter_action_before (π : Policy Seed n) (s ℓ : ℝ) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (i : Fin n) (hi : u i < s) :
    (π.fallbackAfter s ℓ).action r D x u i = π.action r D x u i := by
  change (if u i < s then π.action r D x u i else _root_.Decidable.decide (ℓ < x i)) = _
  exact if_pos hi

lemma Policy.fallbackAfter_action_after (π : Policy Seed n) (s ℓ : ℝ) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (i : Fin n) (hi : s ≤ u i) :
    (π.fallbackAfter s ℓ).action r D x u i = _root_.Decidable.decide (ℓ < x i) := by
  change (if u i < s then π.action r D x u i else _root_.Decidable.decide (ℓ < x i)) = _
  exact if_neg (not_lt_of_ge hi)

lemma Policy.stoppingTime_le_fallbackAfter_add (π : Policy Seed n) {s : ℝ} (hs : s ≤ 1) (ℓ : ℝ)
    (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    π.stoppingTime r D x u ≤ (π.fallbackAfter s ℓ).stoppingTime r D x u + (1-s) := by
  have hOld := π.stoppingTime_le_one r D x u
  have h : π.stoppingTime r D x u-(1-s) ≤ (π.fallbackAfter s ℓ).stoppingTime r D x u := by
    apply ((π.fallbackAfter s ℓ).le_stoppingTime_iff r D x u _).mpr
    refine ⟨by linarith only [hOld,hs],?_⟩
    intro j hj
    have hmem := ((π.fallbackAfter s ℓ).mem_accepted r D x u j).mp hj
    by_cases ht : u j < s
    · have hact := hmem.2
      rw [π.fallbackAfter_action_before s ℓ r D x u j ht] at hact
      have hjOld : j ∈ π.accepted r D x u := (π.mem_accepted r D x u j).mpr ⟨hmem.1,hact⟩
      have hle := π.stoppingTime_le_of_accepted r D x u j hjOld
      linarith only [hle,hs]
    · have hge : s ≤ u j := not_lt.mp ht
      linarith only [hOld,hge]
  linarith only [h]

lemma Policy.fallbackAfter_acceptsAbove (π : Policy Seed n) (s ℓ b : ℝ) (hℓ : ℓ ≤ b)
    (hπ : ∀ r t i x H, π.decide r t i x H = true → b < x) :
    ∀ r t i x H, (π.fallbackAfter s ℓ).decide r t i x H = true → ℓ < x := by
  intro r t i x H h
  simp only [Policy.fallbackAfter] at h
  split_ifs at h with ht
  · exact hℓ.trans_lt (hπ r t i x H h)
  · exact of_decide_eq_true h

lemma Policy.fallbackAfter_reward_eq_of_early_selection (π : Policy Seed n) (s ℓ : ℝ)
    (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) (hu : Function.Injective u)
    {i : Fin n} (hi : π.ActualSelects r D x u i) (ht : u i < s) :
    (π.fallbackAfter s ℓ).reward r D x u = π.reward r D x u := by
  let σ := π.fallbackAfter s ℓ
  have hmemOld := (π.mem_accepted r D x u i).mp hi.1.1
  have hactNew : σ.action r D x u i = true := by
    rw [π.fallbackAfter_action_before s ℓ r D x u i ht]
    exact hmemOld.2
  have hmemNew := (σ.mem_accepted r D x u i).mpr ⟨hmemOld.1,hactNew⟩
  have hupper := σ.stoppingTime_le_of_accepted r D x u i hmemNew
  have hlower : u i ≤ σ.stoppingTime r D x u := by
    apply (σ.le_stoppingTime_iff r D x u _).mpr
    refine ⟨hi.1.2.trans_le (π.stoppingTime_le_one r D x u),?_⟩
    intro j hj
    by_cases hjs : u j < s
    · have hm := (σ.mem_accepted r D x u j).mp hj
      have ha := hm.2
      rw [π.fallbackAfter_action_before s ℓ r D x u j hjs] at ha
      exact hi.1.2.trans_le (π.stoppingTime_le_of_accepted r D x u j ((π.mem_accepted r D x u j).mpr ⟨hm.1,ha⟩))
    · exact (ht.trans_le (not_lt.mp hjs)).le
  have hs : σ.Selects r D x u i := ⟨hmemNew,le_antisymm hlower hupper⟩
  rw [σ.reward_eq_of_selects r D x u hu hs,π.reward_eq_of_actualSelects r D x u hi]

variable [MeasurableSpace Seed]

lemma Policy.fallbackAfter_isMeasurable (π : Policy Seed n) (hπ : π.IsMeasurable) (s ℓ : ℝ) :
    (π.fallbackAfter s ℓ).IsMeasurable := by
  have ht : Measurable (fun q : Seed × (ℝ × (Fin n × (ℝ × History n))) => q.2.1) := by fun_prop
  have hx : Measurable (fun q : Seed × (ℝ × (Fin n × (ℝ × History n))) => q.2.2.2.1) := by fun_prop
  have hDec : Measurable (fun q : Seed × (ℝ × (Fin n × (ℝ × History n))) => _root_.Decidable.decide (ℓ < q.2.2.2.1)) := by
    apply measurable_to_bool
    change MeasurableSet {q : Seed × (ℝ × (Fin n × (ℝ × History n))) | _root_.Decidable.decide (ℓ < q.2.2.2.1) = true}
    simp only [decide_eq_true_eq]
    exact measurableSet_lt measurable_const hx
  exact Measurable.ite (measurableSet_lt ht measurable_const) hπ hDec

end ProphetSecretary.Model
