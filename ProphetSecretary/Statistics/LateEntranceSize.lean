import ProphetSecretary.Model.PendingFirstMoment

/-!
# The size of a late continuation state

A state with remaining horizon at most `h` occurs after time `max 0 (1-h)`.
Pending marginal means decrease pathwise, so their expectation is at most `h S`.
This deterministic domination supplies the finite entrance-size bound in
`upstat:entrance`; construction and restart at a value-defined entrance are separate.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.pendingFirstMoment_antitone (P : Instance n) (i : Fin n) (u : Fin n → ℝ) :
    Antitone (fun t => P.pendingFirstMoment i t u) := by
  intro s t hst
  apply Finset.sum_le_sum
  intro j _
  split_ifs with ht hs hs
  · exact le_rfl
  · exact False.elim (hs (hst.trans ht))
  · exact integral_nonneg_of_ae (P.nonnegative j)
  · exact le_rfl

lemma Instance.pendingFirstMoment_le_total (P : Instance n) (i : Fin n) (t : ℝ) (u : Fin n → ℝ) :
    P.pendingFirstMoment i t u ≤ P.totalFirstMoment := by
  calc
    _ ≤ ∑ j ∈ Finset.univ.erase i, (∫ x, x ∂P.law j) := by
      apply Finset.sum_le_sum
      intro j _
      split_ifs
      · exact le_rfl
      · exact integral_nonneg_of_ae (P.nonnegative j)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset i Finset.univ)
      (fun j _ _ => integral_nonneg_of_ae (P.nonnegative j))

lemma Instance.measurable_pendingFirstMoment_at_time (P : Instance n) (i : Fin n)
    {σ : (Fin n → ℝ) → ℝ} (hσ : Measurable σ) :
    Measurable (fun u => P.pendingFirstMoment i (σ u) u) := by
  apply Finset.measurable_sum
  intro j _
  exact Measurable.ite (measurableSet_le hσ (measurable_pi_apply j)) measurable_const measurable_const

lemma Instance.integrable_pendingFirstMoment_at_time (P : Instance n) (i : Fin n)
    {σ : (Fin n → ℝ) → ℝ} (hσ : Measurable σ) :
    Integrable (fun u => P.pendingFirstMoment i (σ u) u) (Instance.clocksLaw n) := by
  apply Integrable.of_bound (P.measurable_pendingFirstMoment_at_time i hσ).aestronglyMeasurable P.totalFirstMoment
  filter_upwards [] with u
  simpa only [Real.norm_eq_abs, abs_of_nonneg (P.pendingFirstMoment_nonnegative i (σ u) u)] using
    P.pendingFirstMoment_le_total i (σ u) u

/-- A late random time, even if chosen with full knowledge of all clocks, leaves
at most `h S` expected pending first moment. No optional-stopping premise is needed. -/
theorem Instance.integral_pendingFirstMoment_at_late_time_le (P : Instance n) (i : Fin n)
    {σ : (Fin n → ℝ) → ℝ} (hσ : Measurable σ) {h : ℝ} (hh : 0 ≤ h)
    (hσ0 : ∀ u, 0 ≤ σ u) (hLate : ∀ u, 1 - σ u ≤ h) :
    (∫ u, P.pendingFirstMoment i (σ u) u ∂Instance.clocksLaw n) ≤ h * P.totalFirstMoment := by
  let t := max 0 (1 - h)
  have ht0 : 0 ≤ t := le_max_left _ _
  have ht1 : t ≤ 1 := max_le (by norm_num) (by linarith)
  have hts (u : Fin n → ℝ) : t ≤ σ u := max_le (hσ0 u) (by linarith [hLate u])
  calc
    _ ≤ ∫ u, P.pendingFirstMoment i t u ∂Instance.clocksLaw n :=
      integral_mono (P.integrable_pendingFirstMoment_at_time i hσ) (P.integrable_pendingFirstMoment i t)
        (fun u => P.pendingFirstMoment_antitone i u (hts u))
    _ ≤ (1 - t) * P.totalFirstMoment := P.integral_pendingFirstMoment_le i ht0 ht1
    _ ≤ h * P.totalFirstMoment := mul_le_mul_of_nonneg_right
      (by dsimp [t]; linarith [le_max_right (0 : ℝ) (1 - h)]) P.totalFirstMoment_nonnegative

/-- Expected pending first moment plus remaining horizon at any such late state. -/
theorem Instance.integral_late_state_size_le (P : Instance n) (i : Fin n)
    {σ : (Fin n → ℝ) → ℝ} (hσ : Measurable σ) {h : ℝ} (hh : 0 ≤ h)
    (hσ0 : ∀ u, 0 ≤ σ u) (hσ1 : ∀ u, σ u ≤ 1) (hLate : ∀ u, 1 - σ u ≤ h) :
    (∫ u, P.pendingFirstMoment i (σ u) u + (1 - σ u) ∂Instance.clocksLaw n) ≤
      h * (1 + P.totalFirstMoment) := by
  have hU : Integrable (fun u : Fin n → ℝ => 1 - σ u) (Instance.clocksLaw n) := by
    apply Integrable.of_bound (measurable_const.sub hσ).aestronglyMeasurable 1
    filter_upwards [] with u
    change ‖(1 : ℝ) - σ u‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hσ1 u])]
    linarith [hσ0 u]
  rw [integral_add (P.integrable_pendingFirstMoment_at_time i hσ) hU]
  have hs := P.integral_pendingFirstMoment_at_late_time_le i hσ hh hσ0 hLate
  have hu := integral_mono hU (integrable_const h) hLate
  simp only [integral_const, probReal_univ, one_smul] at hu
  nlinarith

end ProphetSecretary.Model
