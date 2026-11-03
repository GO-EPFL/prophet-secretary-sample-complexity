import ProphetSecretary.Probability.DyadicUniformCoupling

/-!
# One finite-bit mixture coin

A threshold on the same grid makes a strict comparison with a rounded
uniform draw identical to comparison with the underlying uniform draw.
Rounding the mixing probability down therefore costs at most one grid
cell.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Probability
open ProphetSecretary.Model

lemma uniformGridRound_lt_gridPoint (N : ℕ) (hN : 0<N) {u : ℝ}
    (hu : u∈Ico (0 : ℝ) 1) (j : Fin N) :
    uniformGridRound N hN u<(gridPoint N j : ℝ) ↔ u<(gridPoint N j : ℝ) := by
  have hNR : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  have hnu : 0≤(N : ℝ)*u := mul_nonneg hNR.le hu.1
  unfold uniformGridRound gridPoint
  rw [div_lt_div_iff_of_pos_right hNR,uniformGridIndex_of_lt_one N hN hu.1 hu.2,
    Nat.cast_lt,Nat.floor_lt hnu,lt_div_iff₀ hNR,mul_comm u]

theorem roundedMixtureCoin_disagreement_probability (N : ℕ) (hN : 0<N) {α : ℝ}
    (hα : α∈Icc (0 : ℝ) 1) :
    Instance.uniformClock.real {u | decide (u<α)≠
      decide (uniformGridRound N hN u<uniformGridRound N hN α)}≤1/(N : ℝ) := by
  let b := uniformGridRound N hN α
  have hB := uniformGridRound_bounds N hN hα
  have hInc : {u | decide (u<α)≠decide (uniformGridRound N hN u<b)}
      ≤ᵐ[Instance.uniformClock] Icc b α := by
    filter_upwards [uniformClock_mem_open_unit] with u hu h
    have hI : uniformGridRound N hN u<b ↔ u<b :=
      uniformGridRound_lt_gridPoint N hN ⟨hu.1.le,hu.2⟩ (uniformGridIndex N hN α)
    change decide (u<α)≠decide (uniformGridRound N hN u<b) at h
    by_cases h1 : u<α
    · have h2 : ¬u<b := by
        intro h2
        have h3 := hI.mpr h2
        simp [h1,h3] at h
      exact ⟨le_of_not_gt h2,h1.le⟩
    · have h2 : ¬u<b := fun hh => h1 (hh.trans_le hB.2.1)
      have h3 : ¬uniformGridRound N hN u<b := fun hh => h2 (hI.mp hh)
      simp [h1,h3] at h
  have h1 : Instance.uniformClock.real
      {u | decide (u<α)≠decide (uniformGridRound N hN u<b)}≤Instance.uniformClock.real (Icc b α) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hInc)
  exact h1.trans ((uniformClock_interval_le_length b α hB.2.1).trans hB.2.2)

end ProphetSecretary.Probability
