import ProphetSecretary.Model.Measurability
import ProphetSecretary.Model.Outcome

/-!
# Ordered capped threshold families

The numerical policies in `con:calibrated-learner` reject zero and accept
the cap on every input. Their continuation estimates may depend on the full
observed history and an independent seed. Ordering those estimates orders
actual stopping durations on a common trajectory.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {Seed : Type*} {n : ℕ}

/-- A capped threshold callback retains the complete observed history. -/
noncomputable def cappedHistoryThresholdPolicy
    (θ : Seed → ℝ → Fin n → History n → ℝ) : Policy Seed n where
  decide r t i x H := decide (x = 1 ∨ (0 < x ∧ θ r t i H ≤ x))

@[simp] lemma cappedHistoryThresholdPolicy_accepts_cap
    (θ : Seed → ℝ → Fin n → History n → ℝ) (r : Seed) (t : ℝ)
    (i : Fin n) (H : History n) :
    (cappedHistoryThresholdPolicy θ).decide r t i 1 H = true := by
  simp [cappedHistoryThresholdPolicy]

@[simp] lemma cappedHistoryThresholdPolicy_rejects_zero
    (θ : Seed → ℝ → Fin n → History n → ℝ) (r : Seed) (t : ℝ)
    (i : Fin n) (H : History n) :
    (cappedHistoryThresholdPolicy θ).decide r t i 0 H = false := by
  norm_num [cappedHistoryThresholdPolicy]

lemma cappedHistoryThresholdPolicy_isMeasurable [MeasurableSpace Seed]
    (θ : Seed → ℝ → Fin n → History n → ℝ)
    (hθ : Measurable (fun z : Seed × (ℝ × (Fin n × (ℝ × History n))) =>
      θ z.1 z.2.1 z.2.2.1 z.2.2.2.2)) :
    (cappedHistoryThresholdPolicy θ).IsMeasurable := by
  let Ω := Seed × (ℝ × (Fin n × (ℝ × History n)))
  have hx : Measurable (fun z : Ω => z.2.2.2.1) := by fun_prop
  apply measurable_to_bool
  change MeasurableSet {z : Ω | decide (z.2.2.2.1 = 1 ∨
    (0 < z.2.2.2.1 ∧ θ z.1 z.2.1 z.2.2.1 z.2.2.2.2 ≤ z.2.2.2.1)) = true}
  simp only [decide_eq_true_eq]
  exact (measurableSet_eq_fun hx measurable_const).union
    ((measurableSet_lt measurable_const hx).inter (measurableSet_le hθ hx))

/-- Inclusion of all potential acceptances compares the actual executions. -/
theorem Policy.stoppingTime_le_of_action_imp (π σ : Policy Seed n)
    (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ)
    (ha : ∀ i ∈ D, σ.action r D x u i = true → π.action r D x u i = true) :
    π.stoppingTime r D x u ≤ σ.stoppingTime r D x u := by
  apply (σ.le_stoppingTime_iff r D x u _).mpr
  refine ⟨π.stoppingTime_le_one r D x u, ?_⟩
  intro i hi
  obtain ⟨hiD, hact⟩ := (σ.mem_accepted r D x u i).mp hi
  exact π.stoppingTime_le_of_accepted r D x u i
    ((π.mem_accepted r D x u i).mpr ⟨hiD, ha i hiD hact⟩)

/-- No Markov assumption is needed for ordering a common seeded family. -/
theorem cappedHistoryThresholdPolicy_stoppingTime_mono
    (θ ψ : Seed → ℝ → Fin n → History n → ℝ)
    (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ)
    (hθψ : ∀ i ∈ D, θ r (u i) i (history D x u (u i)) ≤
      ψ r (u i) i (history D x u (u i))) :
    (cappedHistoryThresholdPolicy θ).stoppingTime r D x u ≤
      (cappedHistoryThresholdPolicy ψ).stoppingTime r D x u := by
  apply Policy.stoppingTime_le_of_action_imp
  intro i hi ha
  simp only [Policy.action, cappedHistoryThresholdPolicy, decide_eq_true_eq] at ha ⊢
  exact ha.imp_right (fun h => ⟨h.1, (hθψ i hi).trans h.2⟩)

/-- The duration floor forces a pathwise reward bound, including no selection. -/
theorem cappedHistoryThresholdPolicy_reward_ge_duration_floor
    (θ : Seed → ℝ → Fin n → History n → ℝ) (r : Seed) (x u : Fin n → ℝ)
    {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1) (hx : ∀ i, 0 ≤ x i)
    (hu : ∀ i, u i ∈ Icc (0 : ℝ) 1)
    (hfloor : ∀ i, z * (1 - u i) ≤ θ r (u i) i (history Finset.univ x u (u i))) :
    z * (1 - (cappedHistoryThresholdPolicy θ).stoppingTime r Finset.univ x u) ≤
      (cappedHistoryThresholdPolicy θ).reward r Finset.univ x u := by
  let π := cappedHistoryThresholdPolicy θ
  rcases π.stoppingTime_eq_one_or_actualSelects r Finset.univ x u with ht | ⟨i, hi⟩
  · rw [ht, sub_self, mul_zero]
    exact π.reward_nonnegative r Finset.univ x u hx
  · rw [π.reward_eq_of_actualSelects r Finset.univ x u hi, ← hi.1.2]
    have ha := ((π.mem_accepted r Finset.univ x u i).mp hi.1.1).2
    change decide (x i = 1 ∨ (0 < x i ∧ θ r (u i) i (history Finset.univ x u (u i)) ≤ x i)) = true at ha
    rcases (of_decide_eq_true ha) with hcap | hth
    · rw [hcap]
      nlinarith [mul_nonneg hz0 (hu i).1]
    · exact (hfloor i).trans hth.2

end ProphetSecretary.Model
