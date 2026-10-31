import ProphetSecretary.Model.SaturatedDurationValue
import ProphetSecretary.Analysis.MovingThreshold
import ProphetSecretary.Reach.SelectionCharge

/-!
# Finite continuation branches at a regular crossing

With all other arrival clocks fixed, the unseen set and the pending-run survival
indicator are locally constant away from those clocks and the terminal time.
This permits the exact moving-root integral to be used for each finite state.
-/

open MeasureTheory Set Filter
open scoped Topology Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

lemma eventually_le_iff_at_ne {r a : ℝ} (h : r ≠ a) :
    ∀ᶠ t : ℝ in 𝓝 r, (t ≤ a ↔ r ≤ a) := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · filter_upwards [eventually_lt_nhds hlt] with t ht
    exact iff_of_true ht.le hlt.le
  · filter_upwards [eventually_gt_nhds hgt] with t ht
    exact iff_of_false (not_le.mpr ht) (not_le.mpr hgt)

lemma otherUnseen_eventually_eq (u : Fin n → ℝ) (i : Fin n) {r : ℝ}
    (hr : ∀ j, j ≠ i → r ≠ u j) :
    ∀ᶠ t : ℝ in 𝓝 r, otherUnseen u i t = otherUnseen u i r := by
  have he : ∀ j : Fin n, ∀ᶠ t : ℝ in 𝓝 r,
      (j ∈ otherUnseen u i t ↔ j ∈ otherUnseen u i r) := by
    intro j
    by_cases hji : j = i
    · subst j
      exact Filter.Eventually.of_forall (fun _ ↦ by simp [otherUnseen])
    · filter_upwards [eventually_le_iff_at_ne (hr j hji)] with t ht
      simpa only [otherUnseen, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
        and_true, ne_eq, hji, not_false_eq_true, true_and] using ht
  filter_upwards [Filter.eventually_all.mpr he] with t ht
  exact Finset.ext (ht ·)

lemma Policy.pendingTime_ne_of_ne_clocks (π : Policy Seed n) (r : Seed)
    (x u : Fin n → ℝ) (i : Fin n) {t : ℝ} (ht : t ≠ 1)
    (hu : ∀ j, j ≠ i → t ≠ u j) : t ≠ π.pendingTime r x u i := by
  intro he
  rcases π.stoppingTime_eq_one_or_selects r (Finset.univ.erase i) x u with h | ⟨j, hj⟩
  · exact ht (he.trans h)
  · exact hu j (Finset.mem_erase.mp ((π.mem_accepted r _ x u j).mp hj.1).1).1
      (he.trans hj.2.symm)

/-- The multiplier records the unit interval, actual unseen state, and survival
of the old pending execution. It is only an analytical complete-vector function. -/
noncomputable def Policy.branchMultiplier (π : Policy Seed n) (r : Seed)
    (x u : Fin n → ℝ) (i : Fin n) (A : Finset (Fin n)) (t : ℝ) : ℝ :=
  if t ∈ Icc (0 : ℝ) 1 ∧ otherUnseen u i t = A ∧ t ≤ π.pendingTime r x u i then 1 else 0

lemma Policy.branchMultiplier_eventually_eq (π : Policy Seed n) (r : Seed)
    (x u : Fin n → ℝ) (i : Fin n) (A : Finset (Fin n)) {s : ℝ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hsu : ∀ j, j ≠ i → s ≠ u j) :
    ∀ᶠ t : ℝ in 𝓝 s, π.branchMultiplier r x u i A t = π.branchMultiplier r x u i A s := by
  have h0 : ∀ᶠ t : ℝ in 𝓝 s, (0 ≤ t ↔ 0 ≤ s) := by
    rcases lt_or_gt_of_ne hs0 with hn | hp
    · filter_upwards [eventually_lt_nhds hn] with t ht
      exact iff_of_false (not_le.mpr ht) (not_le.mpr hn)
    · filter_upwards [eventually_gt_nhds hp] with t ht
      exact iff_of_true ht.le hp.le
  filter_upwards [h0, eventually_le_iff_at_ne hs1, otherUnseen_eventually_eq u i hsu,
    eventually_le_iff_at_ne (π.pendingTime_ne_of_ne_clocks r x u i hs1 hsu)] with t ht0 ht1 htA htσ
  simp only [Policy.branchMultiplier, mem_Icc, ht0, ht1, htA, htσ]

/-- The exact second-order limit for one finite continuation state. The policy
inside the multiplier remains fixed at the base coefficient. -/
theorem Instance.branch_regret_limit (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (π : Policy Seed n) (r : Seed)
    (x u : Fin n → ℝ) (i : Fin n) (A : Finset (Fin n)) {z : ℝ} (hz : 0 < z)
    (hx : optimalScalarValue (P.restrictTo A) 1 0 < x i)
    (hr0 : (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z (x i) ≠ 0)
    (hru : ∀ j, j ≠ i →
      (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z (x i) ≠ u j) :
    let Q := P.restrictTo A
    let hQ := P.restrictTo_integrable_maximum A hP
    let d := Q.durationRoot hQ (x i)
    let root := Q.crossingTime hQ z (x i)
    Tendsto (fun h : ℝ ↦ (∫ t : ℝ, π.branchMultiplier r x u i A t *
      ProphetSecretary.Analysis.branchThresholdLoss Q.saturatedDurationValue d z (z + h) t) / h ^ 2)
      (𝓝[≠] 0) (𝓝 (π.branchMultiplier r x u i A root * d ^ 2 *
        Q.rootDuration hQ (x i) / (2 * z ^ 3))) := by
  let Q := P.restrictTo A
  have hQ := P.restrictTo_integrable_maximum A hP
  have hd := Q.durationRoot_positive hQ hx
  have hr1 : Q.crossingTime hQ z (x i) ≠ 1 := by
    unfold Instance.crossingTime
    have hp := div_pos hd hz
    linarith
  have hm := π.branchMultiplier_eventually_eq r x u i A hr0 hr1 hru
  have hD := Q.saturatedDurationValue_hasDerivAt hQ hd
  rw [← Q.rootDuration_eq_canonical hQ hd] at hD
  exact ProphetSecretary.Analysis.tendsto_weighted_branch_regret (Q.saturatedDurationValue_continuous hQ)
    (Q.saturatedDurationValue_level_iff hQ hd) hz hD hm

end ProphetSecretary.Model
