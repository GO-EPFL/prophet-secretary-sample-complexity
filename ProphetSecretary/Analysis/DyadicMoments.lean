import ProphetSecretary.Analysis.DyadicPath
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Dyadic level moments of bounded continuous-parameter processes
The bound on the whole process is used only for integrability. The quantitative
level estimates use the supplied increment moments.
-/
open MeasureTheory Set
open scoped BigOperators Classical
namespace ProphetSecretary.Analysis
open ProphetSecretary.Reach.EmpiricalChaining
variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
lemma maxAbs_pow_le_sum {K : ℕ} (X : Fin K → Ω → ℝ) (ω : Ω) (p : ℕ) (hp : 0 < p) :
    maxAbs X ω ^ p ≤ ∑ k : Fin K, |X k ω| ^ p := by
  let Y : Option (Fin K) → ℝ := fun i ↦ i.elim 0 (fun k ↦ |X k ω|)
  obtain ⟨i, _, hMax⟩ := Finset.exists_max_image (Finset.univ : Finset (Option (Fin K))) Y ⟨none, Finset.mem_univ _⟩
  have he : maxAbs X ω = Y i := le_antisymm
    (Finset.sup'_le _ _ (fun j hj ↦ hMax j hj)) (Finset.le_sup' _ (Finset.mem_univ i))
  rw [he]
  cases i with
  | none => simpa only [Y, Option.elim_none, zero_pow hp.ne'] using
      Finset.sum_nonneg (fun k (_ : k ∈ (Finset.univ : Finset (Fin K))) ↦ pow_nonneg (abs_nonneg (X k ω)) p)
  | some i => exact Finset.single_le_sum (fun k _ ↦ pow_nonneg (abs_nonneg (X k ω)) p) (Finset.mem_univ i)

lemma lifted_gridMaximum_measurable {f : Ω → ℝ → ℝ} (hf : ∀ t, Measurable (fun ω ↦ f ω t)) (j : ℕ) :
    Measurable (gridMaximum (liftProcess f) j) := by
  apply measurable_maxAbs
  intro k
  convert hf (gridPoint j k) using 1
  funext ω
  exact lifted_gridDeviation f j k ω

lemma lifted_levelMaximum_measurable {f : Ω → ℝ → ℝ} (hf : ∀ t, Measurable (fun ω ↦ f ω t)) (j : ℕ) :
    Measurable (levelMaximum (liftProcess f) j) :=
  measurable_levelMaximum (fun t ↦ measurable_const.add (hf t)) j

omit [MeasurableSpace Ω] in
lemma lifted_gridMaximum_bound {f : Ω → ℝ → ℝ} {D : ℝ} (hD : 0 ≤ D) (ω : Ω)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, |f ω t| ≤ D) (j : ℕ) : gridMaximum (liftProcess f) j ω ≤ D := by
  apply maxAbs_le hD
  intro k
  rw [lifted_gridDeviation]
  exact hf _ (gridPoint_mem_unitInterval j k)

omit [MeasurableSpace Ω] in
lemma lifted_levelMaximum_bound {f : Ω → ℝ → ℝ} {D : ℝ} (hD : 0 ≤ D) (ω : Ω)
    (hf : ∀ t ∈ Icc (0 : ℝ) 1, |f ω t| ≤ D) (j : ℕ) : levelMaximum (liftProcess f) j ω ≤ 2 * D := by
  apply maxAbs_le (by positivity)
  intro k
  have hParent : gridPoint j k ∈ Icc (0 : ℝ) 1 :=
    gridPoint_mem_unitInterval j ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
  have hChild : gridPoint (j + 1) (2 * k.val + 1) ∈ Icc (0 : ℝ) 1 :=
    ⟨gridPoint_nonnegative _ _, gridPoint_odd_le_one j k⟩
  change |gridDeviation (liftProcess f) (j + 1) (2 * k.val + 1) ω - gridDeviation (liftProcess f) j k ω| ≤ _
  rw [lifted_gridDeviation, lifted_gridDeviation]
  exact (abs_sub _ _).trans ((add_le_add (hf _ hChild) (hf _ hParent)).trans_eq (by ring))

lemma integrable_nonnegative_pow_of_bound (μ : Measure Ω) [IsFiniteMeasure μ] {Y : Ω → ℝ} {D : ℝ}
    (hY : Measurable Y) (hY0 : ∀ ω, 0 ≤ Y ω) (hBound : ∀ᵐ ω ∂μ, Y ω ≤ D) (p : ℕ) :
    Integrable (fun ω ↦ Y ω ^ p) μ := by
  apply Integrable.of_bound (hY.pow_const p).aestronglyMeasurable (D ^ p)
  filter_upwards [hBound] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hY0 ω) p)]
  exact pow_le_pow_left₀ (hY0 ω) hω p

lemma integrable_lifted_gridMaximum_pow (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ → ℝ} (hf : ∀ t, Measurable (fun ω ↦ f ω t)) {D : ℝ} (hD : 0 ≤ D)
    (hBound : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) 1, |f ω t| ≤ D) (j p : ℕ) :
    Integrable (fun ω ↦ gridMaximum (liftProcess f) j ω ^ p) μ :=
  integrable_nonnegative_pow_of_bound μ (lifted_gridMaximum_measurable hf j) (fun _ ↦ maxAbs_nonnegative _ _)
    (hBound.mono (fun ω hω ↦ lifted_gridMaximum_bound hD ω hω j)) p

lemma integrable_lifted_levelMaximum_pow (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ → ℝ} (hf : ∀ t, Measurable (fun ω ↦ f ω t)) {D : ℝ} (hD : 0 ≤ D)
    (hBound : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) 1, |f ω t| ≤ D) (j p : ℕ) :
    Integrable (fun ω ↦ levelMaximum (liftProcess f) j ω ^ p) μ :=
  integrable_nonnegative_pow_of_bound μ (lifted_levelMaximum_measurable hf j) (fun _ ↦ maxAbs_nonnegative _ _)
    (hBound.mono (fun ω hω ↦ lifted_levelMaximum_bound hD ω hω j)) p

lemma integrable_increment_pow (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ → ℝ} (hf : ∀ t, Measurable (fun ω ↦ f ω t)) {D : ℝ} (_hD : 0 ≤ D)
    (hBound : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) 1, |f ω t| ≤ D) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (p : ℕ) :
    Integrable (fun ω ↦ |f ω s - f ω t| ^ p) μ := by
  apply integrable_nonnegative_pow_of_bound μ ((hf s).sub (hf t) |>.norm) (fun _ ↦ abs_nonneg _)
    (D := 2 * D) _ p
  filter_upwards [hBound] with ω hω
  exact (abs_sub _ _).trans ((add_le_add (hω s hs) (hω t ht)).trans_eq (by ring))

/-- The maximum over a level costs its number of half-cells, rather than the
number of points on all preceding grids. -/
theorem integral_lifted_levelMaximum_pow_le (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ → ℝ} (hf : ∀ t, Measurable (fun ω ↦ f ω t)) {D B : ℝ} (hD : 0 ≤ D)
    (hBound : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) 1, |f ω t| ≤ D)
    (p : ℕ) (hp : 0 < p)
    (hMoment : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (∫ ω, |f ω s - f ω t| ^ p ∂μ) ≤ B * |s - t| ^ p) (j : ℕ) :
    (∫ ω, levelMaximum (liftProcess f) j ω ^ p ∂μ) ≤
      B * (2 : ℝ) ^ j * (1 / (2 : ℝ) ^ (j + 1)) ^ p := by
  have hParent (k : Fin (2 ^ j)) : gridPoint j k ∈ Icc (0 : ℝ) 1 :=
    gridPoint_mem_unitInterval j ⟨k.val, Nat.lt_succ_of_lt k.isLt⟩
  have hChild (k : Fin (2 ^ j)) : gridPoint (j + 1) (2 * k.val + 1) ∈ Icc (0 : ℝ) 1 :=
    ⟨gridPoint_nonnegative _ _, gridPoint_odd_le_one j k⟩
  have hInt (k : Fin (2 ^ j)) : Integrable (fun ω ↦ |levelIncrement (liftProcess f) j k ω| ^ p) μ := by
    simpa only [levelIncrement, lifted_gridDeviation] using integrable_increment_pow μ hf hD hBound (hChild k) (hParent k) p
  calc
    _ ≤ ∫ ω, ∑ k : Fin (2 ^ j), |levelIncrement (liftProcess f) j k ω| ^ p ∂μ :=
      integral_mono (integrable_lifted_levelMaximum_pow μ hf hD hBound j p)
        (integrable_finsetSum _ (fun k _ ↦ hInt k)) (fun ω ↦ maxAbs_pow_le_sum _ ω p hp)
    _ = ∑ k : Fin (2 ^ j), ∫ ω, |levelIncrement (liftProcess f) j k ω| ^ p ∂μ :=
      integral_finsetSum _ (fun k _ ↦ hInt k)
    _ ≤ ∑ _k : Fin (2 ^ j), B * (1 / (2 : ℝ) ^ (j + 1)) ^ p := by
      apply Finset.sum_le_sum
      intro k _
      have h := hMoment _ (hChild k) _ (hParent k)
      simpa only [levelIncrement, lifted_gridDeviation, gridPoint_odd_gap,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ (j + 1))] using h
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]; ring

end ProphetSecretary.Analysis
