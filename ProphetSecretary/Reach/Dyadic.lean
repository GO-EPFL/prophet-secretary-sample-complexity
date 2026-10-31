import ProphetSecretary.Reach.EmpiricalChaining
import Mathlib.Algebra.Order.Floor.Semiring
import Lean.Elab.Tactic.Omega

/-!
# Dyadic grid chaining

A grid deviation is obtained from a parent grid deviation by adding at most one centered
half-cell increment. Thus the maximal grid deviation is bounded by a sum of maximal
increments over the levels. Monotonicity of the empirical CDF controls the final cell.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Reach.EmpiricalChaining


variable {Ω : Type*}

noncomputable def gridPoint (j k : ℕ) : ℝ := (k : ℝ) / (2 : ℝ) ^ j

noncomputable def gridDeviation (F : Ω → ℝ → ℝ) (j k : ℕ) (ω : Ω) : ℝ :=
  F ω (gridPoint j k) - gridPoint j k

noncomputable def levelIncrement (F : Ω → ℝ → ℝ) (j k : ℕ) (ω : Ω) : ℝ :=
  gridDeviation F (j + 1) (2 * k + 1) ω - gridDeviation F j k ω

noncomputable def gridMaximum (F : Ω → ℝ → ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  maxAbs (fun k : Fin (2 ^ j + 1) => gridDeviation F j k) ω

noncomputable def levelMaximum (F : Ω → ℝ → ℝ) (j : ℕ) (ω : Ω) : ℝ :=
  maxAbs (fun k : Fin (2 ^ j) => levelIncrement F j k) ω

theorem gridPoint_even (j k : ℕ) : gridPoint (j + 1) (2 * k) = gridPoint j k := by
  unfold gridPoint
  simp only [Nat.cast_mul, Nat.cast_ofNat, pow_succ]
  field_simp

theorem gridPoint_odd_gap (j k : ℕ) :
    gridPoint (j + 1) (2 * k + 1) - gridPoint j k = 1 / (2 : ℝ) ^ (j + 1) := by
  unfold gridPoint
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, pow_succ]
  field_simp
  ring

theorem levelIncrement_eq (F : Ω → ℝ → ℝ) (j k : ℕ) (ω : Ω) :
    levelIncrement F j k ω = F ω (gridPoint (j + 1) (2 * k + 1)) - F ω (gridPoint j k) -
      1 / (2 : ℝ) ^ (j + 1) := by
  unfold levelIncrement gridDeviation
  rw [← gridPoint_odd_gap j k]
  ring

theorem gridMaximum_succ_le (F : Ω → ℝ → ℝ) (j : ℕ) (ω : Ω) :
    gridMaximum F (j + 1) ω ≤ gridMaximum F j ω + levelMaximum F j ω := by
  apply maxAbs_le
  · exact add_nonneg (maxAbs_nonnegative _ _) (maxAbs_nonnegative _ _)
  · intro k
    have hk : k.val ≤ 2 * 2 ^ j := by
      have := Nat.le_of_lt_succ k.isLt
      simpa [pow_succ, mul_comm] using this
    let l := k.val / 2
    have hl : l ≤ 2 ^ j := by dsimp [l]; omega
    let i : Fin (2 ^ j + 1) := ⟨l, Nat.lt_succ_of_le hl⟩
    by_cases hp : k.val % 2 = 0
    · have he : k.val = 2 * l := by dsimp [l]; omega
      have hg : gridDeviation F (j + 1) k ω = gridDeviation F j i ω := by
        simp only [gridDeviation, he, gridPoint_even, i]
      rw [hg]
      exact (le_maxAbs (fun k : Fin (2 ^ j + 1) => gridDeviation F j k) ω i).trans
        (le_add_of_nonneg_right (maxAbs_nonnegative (fun k : Fin (2 ^ j) => levelIncrement F j k) ω))
    · have hp' : k.val % 2 = 1 := by omega
      have he : k.val = 2 * l + 1 := by dsimp [l]; omega
      have hl' : l < 2 ^ j := by omega
      let i' : Fin (2 ^ j) := ⟨l, hl'⟩
      have hg : gridDeviation F (j + 1) k ω =
          gridDeviation F j i ω + levelIncrement F j i' ω := by
        simp only [levelIncrement, i, i', he]
        ring
      rw [hg]
      exact (abs_add_le _ _).trans (add_le_add
        (le_maxAbs (fun k : Fin (2 ^ j + 1) => gridDeviation F j k) ω i)
        (le_maxAbs (fun k : Fin (2 ^ j) => levelIncrement F j k) ω i'))

theorem gridMaximum_zero (F : Ω → ℝ → ℝ) (ω : Ω) (h0 : F ω 0 = 0) (h1 : F ω 1 = 1) :
    gridMaximum F 0 ω = 0 := by
  apply le_antisymm
  · apply maxAbs_le le_rfl
    intro k
    have hk : k.val = 0 ∨ k.val = 1 := by have := k.isLt; norm_num at this; omega
    rcases hk with hk | hk
    · simp [gridDeviation, gridPoint, hk, h0]
    · simp [gridDeviation, gridPoint, hk, h1]
  · exact maxAbs_nonnegative _ _

theorem gridMaximum_le_sum (F : Ω → ℝ → ℝ) (J : ℕ) (ω : Ω)
    (h0 : F ω 0 = 0) (h1 : F ω 1 = 1) :
    gridMaximum F J ω ≤ ∑ j ∈ Finset.range J, levelMaximum F j ω := by
  induction J with
  | zero => simp [gridMaximum_zero F ω h0 h1]
  | succ J ih =>
    calc
      gridMaximum F (J + 1) ω ≤ gridMaximum F J ω + levelMaximum F J ω :=
        gridMaximum_succ_le F J ω
      _ ≤ (∑ j ∈ Finset.range J, levelMaximum F j ω) + levelMaximum F J ω := add_le_add ih le_rfl
      _ = ∑ j ∈ Finset.range (J + 1), levelMaximum F j ω := (Finset.sum_range_succ _ _).symm

/-- Every positive point of the unit interval lies in a grid cell that is open on the
left and closed on the right. This convention also controls empirical left limits. -/
theorem exists_grid_cell (D : ℕ) (hD : 0 < D) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    ∃ k : Fin D, (k.val : ℝ) / D < t ∧ t ≤ ((k.val : ℝ) + 1) / D := by
  have hd : (0 : ℝ) < D := by exact_mod_cast hD
  let c := Nat.ceil ((D : ℝ) * t)
  have hc0 : 1 ≤ c := Nat.one_le_ceil_iff.mpr (mul_pos hd ht)
  have hcD : c ≤ D := Nat.ceil_le.mpr (by nlinarith)
  have he : c - 1 + 1 = c := Nat.sub_add_cancel hc0
  have hkc : c - 1 < c := by omega
  refine ⟨⟨c - 1, hkc.trans_le hcD⟩, ?_, ?_⟩
  · apply (div_lt_iff₀ hd).mpr
    have h := Nat.lt_ceil.mp hkc
    simpa [c, mul_comm] using h
  · apply (le_div_iff₀ hd).mpr
    have h := Nat.le_ceil ((D : ℝ) * t)
    have he' : ((c - 1 : ℕ) : ℝ) + 1 = c := by exact_mod_cast he
    rw [he']
    simpa [c, mul_comm] using h

open ProphetSecretary.Reach.ZeroReach

theorem empiricalCDF_monotone {N : ℕ} (z : Fin N → ℝ) : Monotone (empiricalCDF z) := by
  intro a b hab
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : z i ≤ a
  · simp [hi, hi.trans hab]
  · simp only [if_neg hi]
    split_ifs <;> norm_num

theorem empiricalCDF_le_left {N : ℕ} (z : Fin N → ℝ) {a b : ℝ} (hab : a < b) :
    empiricalCDF z a ≤ empiricalCDFLeft z b := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : z i ≤ a
  · simp [hi, hi.trans_lt hab]
  · simp only [if_neg hi]
    split_ifs <;> norm_num

theorem empiricalCDFLeft_nonnegative {N : ℕ} (z : Fin N → ℝ) (t : ℝ) :
    0 ≤ empiricalCDFLeft z t := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  exact Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num

/-- The finite grid controls both empirical-CDF sides at any point of the unit interval.
The statement includes clocks exactly at grid boundaries. -/
theorem discrepancy_le_grid {N : ℕ} (z : Ω → Fin N → ℝ) (J : ℕ) (ω : Ω)
    (hz : ∀ i, 0 ≤ z ω i ∧ z ω i ≤ 1) :
    discrepancy (z ω) ≤ gridMaximum (fun ω => empiricalCDF (z ω)) J ω + 1 / (2 : ℝ) ^ J := by
  let F := fun ω => empiricalCDF (z ω)
  let B := gridMaximum F J ω + 1 / (2 : ℝ) ^ J
  have hb : 0 ≤ B := add_nonneg (maxAbs_nonnegative _ _) (by positivity)
  have hg : ∀ k : Fin (2 ^ J + 1), |empiricalCDF (z ω) (gridPoint J k) - gridPoint J k| ≤
      gridMaximum F J ω := fun k => le_maxAbs (fun k : Fin (2 ^ J + 1) => gridDeviation F J k) ω k
  have herr : ∀ i : Fin N,
      empiricalCDF (z ω) (z ω i) - z ω i ≤ B ∧
        z ω i - empiricalCDFLeft (z ω) (z ω i) ≤ B := by
    intro i
    by_cases hi : 0 < z ω i
    · obtain ⟨k, hk0, hk1⟩ := exists_grid_cell (2 ^ J) (by positivity) hi (hz i).2
      have hk0' : gridPoint J k < z ω i := by
        simpa only [gridPoint, Nat.cast_pow, Nat.cast_ofNat] using hk0
      have hk1' : z ω i ≤ gridPoint J (k.val + 1) := by
        simpa only [gridPoint, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using hk1
      let l : Fin (2 ^ J + 1) := ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
      let r : Fin (2 ^ J + 1) := ⟨k.val + 1, Nat.succ_lt_succ k.isLt⟩
      have hl := hg l
      have hr := hg r
      have hright := empiricalCDF_monotone (z ω) hk1'
      have hleft := empiricalCDF_le_left (z ω) hk0'
      have hgap : gridPoint J (k.val + 1) - gridPoint J k = 1 / (2 : ℝ) ^ J := by
        simp only [gridPoint, Nat.cast_add, Nat.cast_one]
        ring
      constructor
      · have hr' := le_abs_self (empiricalCDF (z ω) (gridPoint J r) - gridPoint J r)
        dsimp [l, r, B] at hl hr ⊢
        linarith
      · have hl' := neg_le_abs (empiricalCDF (z ω) (gridPoint J l) - gridPoint J l)
        dsimp [l, r, B] at hl hr ⊢
        linarith
    · have hi0 : z ω i = 0 := le_antisymm (le_of_not_gt hi) (hz i).1
      have hg0 := hg ⟨0, Nat.zero_lt_succ _⟩
      simp only [gridPoint, Nat.cast_zero, zero_div] at hg0
      constructor
      · rw [hi0]
        exact (le_abs_self _).trans (hg0.trans (le_add_of_nonneg_right (by positivity)))
      · rw [hi0]
        exact (sub_nonpos.mpr (empiricalCDFLeft_nonnegative _ _)).trans hb
  calc
    discrepancy (z ω) ≤ rawDiscrepancy (z ω) := min_le_right _ _
    _ ≤ B := by
      apply Finset.sup'_le
      intro c _
      cases c with
      | none => exact hb
      | some c =>
        rcases c with ⟨i, b⟩
        cases b with
        | false => exact (herr i).1
        | true => exact (herr i).2

/-- The discrepancy is bounded by the complete finite dyadic chain plus its final mesh. -/
theorem discrepancy_le_sum_levels {N : ℕ} (hN : 0 < N) (z : Ω → Fin N → ℝ)
    (J : ℕ) (ω : Ω) (hz : ∀ i, 0 < z ω i ∧ z ω i ≤ 1) :
    discrepancy (z ω) ≤ (∑ j ∈ Finset.range J,
      levelMaximum (fun ω => empiricalCDF (z ω)) j ω) + 1 / (2 : ℝ) ^ J := by
  have h0 : empiricalCDF (z ω) 0 = 0 :=
    empiricalCDF_eq_zero _ _ (fun i => not_le_of_gt (hz i).1)
  have h1 : empiricalCDF (z ω) 1 = 1 := empiricalCDF_eq_one hN _ _ (fun i => (hz i).2)
  exact (discrepancy_le_grid z J ω (fun i => ⟨(hz i).1.le, (hz i).2⟩)).trans
    (add_le_add (gridMaximum_le_sum _ J ω h0 h1) le_rfl)

/-- A CDF increment is exactly the empirical mass of the corresponding half-open cell. -/
theorem empiricalCDF_difference_eq_interval {N : ℕ} (z : Fin N → ℝ) {a b : ℝ} (hab : a ≤ b) :
    empiricalCDF z b - empiricalCDF z a =
      (∑ i : Fin N, if a < z i ∧ z i ≤ b then (1 : ℝ) else 0) / N := by
  unfold empiricalCDF
  rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases ha : z i ≤ a
  · simp [ha, ha.trans hab, not_lt_of_ge ha]
  · by_cases hb : z i ≤ b
    · simp [ha, hb, lt_of_not_ge ha]
    · simp [ha, hb]

theorem gridPoint_nonnegative (j k : ℕ) : 0 ≤ gridPoint j k :=
  div_nonneg (Nat.cast_nonneg _) (by positivity)

theorem gridPoint_odd_le_one (j : ℕ) (k : Fin (2 ^ j)) :
    gridPoint (j + 1) (2 * k.val + 1) ≤ 1 := by
  apply (div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ (j + 1))).mpr
  have hnat : 2 * k.val + 1 ≤ 2 ^ (j + 1) := by
    have hk := k.isLt
    rw [pow_succ]
    omega
  exact_mod_cast hnat

theorem gridPoint_le_odd (j k : ℕ) : gridPoint j k ≤ gridPoint (j + 1) (2 * k + 1) := by
  have h := gridPoint_odd_gap j k
  have hp : 0 ≤ 1 / (2 : ℝ) ^ (j + 1) := by positivity
  linarith

/-- Centered half-cell empirical masses are bounded in absolute value by one, for every
clock vector; the random clocks need not be independent for this deterministic bound. -/
theorem abs_empirical_levelIncrement_le_one {N : ℕ} (hN : 0 < N)
    (z : Ω → Fin N → ℝ) (j : ℕ) (k : Fin (2 ^ j)) (ω : Ω) :
    |levelIncrement (fun ω => empiricalCDF (z ω)) j k ω| ≤ 1 := by
  let a := gridPoint j k
  let b := gridPoint (j + 1) (2 * k.val + 1)
  have ha : 0 ≤ a := div_nonneg (Nat.cast_nonneg _) (by positivity)
  have hb : b ≤ 1 := by
    apply (div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ (j + 1))).mpr
    have hnat : 2 * k.val + 1 ≤ 2 ^ (j + 1) := by
      have hk := k.isLt
      rw [pow_succ]
      omega
    exact_mod_cast hnat
  have hgap : b - a = 1 / (2 : ℝ) ^ (j + 1) := gridPoint_odd_gap j k
  have hp : 0 ≤ 1 / (2 : ℝ) ^ (j + 1) := by positivity
  have hp1 : 1 / (2 : ℝ) ^ (j + 1) ≤ 1 := by linarith
  have hab : a ≤ b := by linarith
  have h0 : 0 ≤ empiricalCDF (z ω) b - empiricalCDF (z ω) a :=
    sub_nonneg.mpr (empiricalCDF_monotone _ hab)
  have h1 : empiricalCDF (z ω) b - empiricalCDF (z ω) a ≤ 1 := by
    linarith [empiricalCDF_nonnegative (z ω) a, empiricalCDF_le_one hN (z ω) b]
  rw [levelIncrement_eq]
  apply abs_le.mpr
  constructor <;> linarith

variable [MeasurableSpace Ω]

theorem measurable_gridDeviation {F : Ω → ℝ → ℝ}
    (hF : ∀ t, Measurable fun ω => F ω t) (j k : ℕ) :
    Measurable (gridDeviation F j k) := (hF _).sub measurable_const

theorem measurable_levelIncrement {F : Ω → ℝ → ℝ}
    (hF : ∀ t, Measurable fun ω => F ω t) (j k : ℕ) :
    Measurable (levelIncrement F j k) :=
  (measurable_gridDeviation hF _ _).sub (measurable_gridDeviation hF _ _)

theorem measurable_levelMaximum {F : Ω → ℝ → ℝ}
    (hF : ∀ t, Measurable fun ω => F ω t) (j : ℕ) :
    Measurable (levelMaximum F j) :=
  measurable_maxAbs fun _ => measurable_levelIncrement hF _ _

theorem integrable_empirical_levelMaximum {N : ℕ} (hN : 0 < N) (μ : Measure Ω)
    [IsFiniteMeasure μ] {z : Ω → Fin N → ℝ} (hz : ∀ i, Measurable fun ω => z ω i) (j : ℕ) :
    Integrable (levelMaximum (fun ω => empiricalCDF (z ω)) j) μ := by
  apply Integrable.of_bound (measurable_levelMaximum
    (fun _ => measurable_empiricalCDF hz measurable_const) j).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs]
  change |maxAbs (fun k : Fin (2 ^ j) => levelIncrement (fun ω => empiricalCDF (z ω)) j k) ω| ≤ 1
  rw [abs_of_nonneg (maxAbs_nonnegative _ _)]
  exact maxAbs_le zero_le_one (fun k => abs_empirical_levelIncrement_le_one hN z j k ω)

/-- Exact expectation reduction to finite dyadic half-cell maxima. All distributional
work is left in those explicit maxima; no empirical-process inequality is assumed. -/
theorem integral_discrepancy_le_sum_levels {N : ℕ} (hN : 0 < N) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {z : Ω → Fin N → ℝ}
    (hz : ∀ i, Measurable fun ω => z ω i)
    (hunit : ∀ᵐ ω ∂μ, ∀ i, 0 < z ω i ∧ z ω i ≤ 1) (J : ℕ) :
    (∫ ω, discrepancy (z ω) ∂μ) ≤
      (∑ j ∈ Finset.range J, ∫ ω, levelMaximum (fun ω => empiricalCDF (z ω)) j ω ∂μ) +
        1 / (2 : ℝ) ^ J := by
  have hi := integrable_finsetSum (Finset.range J) (fun j _ => integrable_empirical_levelMaximum hN μ hz j)
  have hbound := integral_mono_ae (integrable_discrepancy μ hz)
    (hi.add (integrable_const (1 / (2 : ℝ) ^ J))) (by
      filter_upwards [hunit] with ω hω
      exact discrepancy_le_sum_levels hN z J ω hω)
  change (∫ ω, discrepancy (z ω) ∂μ) ≤
    ∫ ω, (∑ j ∈ Finset.range J, levelMaximum (fun ω => empiricalCDF (z ω)) j ω) +
      1 / (2 : ℝ) ^ J ∂μ at hbound
  rw [integral_add hi (integrable_const _), integral_finsetSum _
    (fun j _ => integrable_empirical_levelMaximum hN μ hz j)] at hbound
  simpa using hbound

end ProphetSecretary.Reach.EmpiricalChaining
