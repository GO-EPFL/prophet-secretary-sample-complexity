import ProphetSecretary.Model.ClockOrderContinuity

/-!
# Continuity of actual finite Markov threshold executions

At distinct clocks and away from value-threshold ties, all actual candidate
actions and the accepted identity set are locally constant. Avoiding terminal
clock 1 also makes the actual selected identity locally constant. The realized
reward and stopping time are then continuous functions of values and clocks.
Only the fixed-seed Markov threshold class is used here.
-/
open Set Filter
open scoped Topology Classical BigOperators
namespace ProphetSecretary.Model
variable {n : ℕ} {Seed : Type*}

lemma Policy.selects_iff_accepted_time_le (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (i : Fin n) :
    π.Selects r D x u i ↔ i ∈ π.accepted r D x u ∧ u i ≤ 1 ∧ ∀ j ∈ π.accepted r D x u, u i ≤ u j := by
  constructor
  · rintro ⟨hi,ht⟩
    refine ⟨hi,?_,?_⟩
    · rw [ht]
      exact π.stoppingTime_le_one r D x u
    · intro j hj
      rw [ht]
      exact π.stoppingTime_le_of_accepted r D x u j hj
  · rintro ⟨hi,ht,hmin⟩
    exact ⟨hi,le_antisymm ((π.le_stoppingTime_iff r D x u (u i)).mpr ⟨ht,hmin⟩)
      (π.stoppingTime_le_of_accepted r D x u i hi)⟩

lemma Policy.selects_iff_of_accepted_clock_order (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x y u v : Fin n → ℝ)
    (hacc : π.accepted r D y v = π.accepted r D x u)
    (horder : ∀ i j, (v i < v j ↔ u i < u j)) (hterm : ∀ i, (v i ≤ 1 ↔ u i ≤ 1)) (i : Fin n) :
    π.Selects r D y v i ↔ π.Selects r D x u i := by
  rw [π.selects_iff_accepted_time_le,π.selects_iff_accepted_time_le,hacc]
  constructor
  · rintro ⟨hi,ht,hmin⟩
    exact ⟨hi,(hterm i).mp ht,fun j hj => (clock_le_order_fixed horder i j).mp (hmin j hj)⟩
  · rintro ⟨hi,ht,hmin⟩
    exact ⟨hi,(hterm i).mpr ht,fun j hj => (clock_le_order_fixed horder i j).mpr (hmin j hj)⟩

lemma Policy.actualSelects_iff_of_accepted_clock_order (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x y u v : Fin n → ℝ)
    (hacc : π.accepted r D y v = π.accepted r D x u)
    (horder : ∀ i j, (v i < v j ↔ u i < u j)) (hterm : ∀ i, (v i ≤ 1 ↔ u i ≤ 1)) (i : Fin n) :
    π.ActualSelects r D y v i ↔ π.ActualSelects r D x u i := by
  simp only [Policy.ActualSelects,π.selects_iff_of_accepted_clock_order r D x y u v hacc horder hterm]

lemma thresholdPolicy.action_eventually_fixed
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → ℝ) (r : Seed)
    (hθ : ∀ A i, Continuous (fun t => θ r A t i)) (D : Finset (Fin n)) (x u : Fin n → ℝ)
    (hu : Function.Injective u)
    (htie : ∀ i, x i ≠ θ r (unseen (history D x u (u i))) (u i) i) :
    ∀ᶠ z : (Fin n → ℝ) × (Fin n → ℝ) in 𝓝 (x,u), ∀ i,
      (thresholdPolicy θ).action r D z.1 z.2 i = (thresholdPolicy θ).action r D x u i := by
  apply eventually_all.mpr
  intro i
  have hθAt : ContinuousAt (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      θ r (unseen (history D x u (u i))) (z.2 i) i) (x,u) :=
    ((hθ (unseen (history D x u (u i))) i).comp ((continuous_apply i).comp continuous_snd)).continuousAt
  have hxAt : ContinuousAt (fun z : (Fin n → ℝ) × (Fin n → ℝ) => z.1 i) (x,u) :=
    ((continuous_apply i).comp continuous_fst).continuousAt
  have hComp := eventually_le_iff_of_continuousAt_ne hθAt hxAt (htie i).symm
  filter_upwards [unseen_at_arrival_eventually_fixed D x u hu,hComp] with z hz hc
  simp only [Policy.action,thresholdPolicy,hz i]
  exact congrArg (fun p : Prop => decide p) (propext hc)

lemma thresholdPolicy.accepted_eventually_fixed
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → ℝ) (r : Seed)
    (hθ : ∀ A i, Continuous (fun t => θ r A t i)) (D : Finset (Fin n)) (x u : Fin n → ℝ)
    (hu : Function.Injective u)
    (htie : ∀ i, x i ≠ θ r (unseen (history D x u (u i))) (u i) i) :
    ∀ᶠ z : (Fin n → ℝ) × (Fin n → ℝ) in 𝓝 (x,u),
      (thresholdPolicy θ).accepted r D z.1 z.2 = (thresholdPolicy θ).accepted r D x u := by
  filter_upwards [thresholdPolicy.action_eventually_fixed θ r hθ D x u hu htie] with z hz
  ext i
  simp only [Policy.mem_accepted,hz i]

lemma thresholdPolicy.actualSelects_eventually_fixed
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → ℝ) (r : Seed)
    (hθ : ∀ A i, Continuous (fun t => θ r A t i)) (D : Finset (Fin n)) (x u : Fin n → ℝ)
    (hu : Function.Injective u) (hterm : ∀ i, u i ≠ 1)
    (htie : ∀ i, x i ≠ θ r (unseen (history D x u (u i))) (u i) i) :
    ∀ᶠ z : (Fin n → ℝ) × (Fin n → ℝ) in 𝓝 (x,u), ∀ i,
      ((thresholdPolicy θ).ActualSelects r D z.1 z.2 i ↔ (thresholdPolicy θ).ActualSelects r D x u i) := by
  filter_upwards [thresholdPolicy.accepted_eventually_fixed θ r hθ D x u hu htie,
    continuous_snd.continuousAt.eventually (clock_order_eventually_fixed u hu),
    continuous_snd.continuousAt.eventually (clocks_terminal_comparison_eventually_fixed u hterm)] with z hz ho ht
  exact fun i => (thresholdPolicy θ).actualSelects_iff_of_accepted_clock_order r D x z.1 u z.2 hz ho ht i

private lemma Policy.reward_continuousAt_of_locally_fixed_selection (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ)
    (hsel : ∀ᶠ z : (Fin n → ℝ) × (Fin n → ℝ) in 𝓝 (x,u), ∀ i,
      (π.ActualSelects r D z.1 z.2 i ↔ π.ActualSelects r D x u i)) :
    ContinuousAt (fun z : (Fin n → ℝ) × (Fin n → ℝ) => π.reward r D z.1 z.2) (x,u) := by
  have hc : Continuous (fun z : (Fin n → ℝ) × (Fin n → ℝ) =>
      ∑ i : Fin n, if π.ActualSelects r D x u i then z.1 i else 0) := by
    apply continuous_finsetSum
    intro i _
    by_cases hi : π.ActualSelects r D x u i
    · simpa only [if_pos hi,Function.comp_def] using (continuous_apply i).comp continuous_fst
    · simp only [if_neg hi]
      exact continuous_const
  apply hc.continuousAt.congr_of_eventuallyEq
  filter_upwards [hsel] with z hz
  simp only [Policy.reward,hz]

private lemma Policy.stoppingTime_continuousAt_of_locally_fixed_selection (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ)
    (hsel : ∀ᶠ z : (Fin n → ℝ) × (Fin n → ℝ) in 𝓝 (x,u), ∀ i,
      (π.ActualSelects r D z.1 z.2 i ↔ π.ActualSelects r D x u i)) :
    ContinuousAt (fun z : (Fin n → ℝ) × (Fin n → ℝ) => π.stoppingTime r D z.1 z.2) (x,u) := by
  by_cases hs : ∃ i, π.ActualSelects r D x u i
  · obtain ⟨i,hi⟩ := hs
    apply ((continuous_apply i).comp continuous_snd).continuousAt.congr_of_eventuallyEq
    filter_upwards [hsel] with z hz
    exact ((hz i).mpr hi).1.2.symm
  · apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [hsel] with z hz
    exact π.stoppingTime_eq_one_of_no_actualSelection r D z.1 z.2 (fun i hi => hs ⟨i,(hz i).mp hi⟩)

/-- Actual reward and duration are continuous at a regular finite execution. -/
theorem thresholdPolicy.outcomes_continuousAt
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → ℝ) (r : Seed)
    (hθ : ∀ A i, Continuous (fun t => θ r A t i)) (D : Finset (Fin n)) (x u : Fin n → ℝ)
    (hu : Function.Injective u) (hterm : ∀ i, u i ≠ 1)
    (htie : ∀ i, x i ≠ θ r (unseen (history D x u (u i))) (u i) i) :
    ContinuousAt (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (thresholdPolicy θ).reward r D z.1 z.2) (x,u) ∧
    ContinuousAt (fun z : (Fin n → ℝ) × (Fin n → ℝ) => (thresholdPolicy θ).stoppingTime r D z.1 z.2) (x,u) := by
  have hsel := thresholdPolicy.actualSelects_eventually_fixed θ r hθ D x u hu hterm htie
  exact ⟨(thresholdPolicy θ).reward_continuousAt_of_locally_fixed_selection r D x u hsel,
    (thresholdPolicy θ).stoppingTime_continuousAt_of_locally_fixed_selection r D x u hsel⟩

end ProphetSecretary.Model
