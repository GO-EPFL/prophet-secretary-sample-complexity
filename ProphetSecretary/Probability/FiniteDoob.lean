import Mathlib.Probability.Martingale.Basic
import ProphetSecretary.Probability.FourthMoment
import Mathlib.Tactic

/-!
# Finite second and sixth maximal estimates

Running maxima admit a deterministic summation-by-parts inequality. Applied to a
nonnegative bounded submartingale, its predictable drift has nonnegative expectation.
Polynomial Young inequalities then give explicit maximal-moment constants.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Probability

/-- Running maximum of a finite initial segment of a real sequence. -/
def runningMaximum (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => x 0
  | n + 1 => max (runningMaximum x n) (x (n + 1))

lemma runningMaximum_nonnegative {x : ℕ → ℝ} (hx : ∀ j, 0 ≤ x j) (n : ℕ) :
    0 ≤ runningMaximum x n := by
  induction n with
  | zero => exact hx 0
  | succ n ih => exact ih.trans (le_max_left _ _)

lemma le_runningMaximum (x : ℕ → ℝ) {j n : ℕ} (hjn : j ≤ n) : x j ≤ runningMaximum x n := by
  induction n with
  | zero =>
    have hj : j = 0 := Nat.eq_zero_of_le_zero hjn
    subst j
    exact le_rfl
  | succ n ih =>
    by_cases h : j ≤ n
    · exact (ih h).trans (le_max_left _ _)
    · have he : j = n + 1 := by omega
      subst j
      exact le_max_right _ _

lemma runningMaximum_le {x : ℕ → ℝ} {C : ℝ} (hC : ∀ j, x j ≤ C) (n : ℕ) :
    runningMaximum x n ≤ C := by
  induction n with
  | zero => exact hC 0
  | succ n ih => exact max_le ih (hC (n + 1))

/-- Deterministic quadratic maximal duality. -/
lemma runningMaximum_square_duality (x : ℕ → ℝ) (n : ℕ) :
    runningMaximum x n ^ 2 ≤ 2 * x n * runningMaximum x n -
      2 * ∑ j ∈ Finset.range n, runningMaximum x j * (x (j + 1) - x j) := by
  induction n with
  | zero => simp only [runningMaximum, Finset.range_zero, Finset.sum_empty]; nlinarith [sq_nonneg (x 0)]
  | succ n ih =>
    rw [runningMaximum, Finset.sum_range_succ]
    by_cases h : x (n + 1) ≤ runningMaximum x n
    · rw [max_eq_left h]
      nlinarith
    · rw [max_eq_right (le_of_not_ge h)]
      nlinarith [sq_nonneg (x (n + 1) - runningMaximum x n)]

/-- A polynomial form of the sixth-power Young inequality. -/
lemma sixth_young {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    6 * a * b ^ 5 ≤ a ^ 6 + 5 * b ^ 6 := by
  have h : 0 ≤ (a - b) ^ 2 * (a ^ 4 + 2 * a ^ 3 * b + 3 * a ^ 2 * b ^ 2 +
      4 * a * b ^ 3 + 5 * b ^ 4) := mul_nonneg (sq_nonneg _) (by positivity)
  nlinarith

/-- Deterministic sixth-power maximal duality for nonnegative sequences. -/
lemma runningMaximum_sixth_duality {x : ℕ → ℝ} (hx : ∀ j, 0 ≤ x j) (n : ℕ) :
    5 * runningMaximum x n ^ 6 ≤ 6 * x n * runningMaximum x n ^ 5 -
      6 * ∑ j ∈ Finset.range n, runningMaximum x j ^ 5 * (x (j + 1) - x j) := by
  induction n with
  | zero =>
    simp only [runningMaximum, Finset.range_zero, Finset.sum_empty]
    nlinarith [pow_nonneg (hx 0) 6]
  | succ n ih =>
    rw [runningMaximum, Finset.sum_range_succ]
    by_cases h : x (n + 1) ≤ runningMaximum x n
    · rw [max_eq_left h]
      nlinarith
    · rw [max_eq_right (le_of_not_ge h)]
      have hy := sixth_young (hx (n + 1)) (runningMaximum_nonnegative hx n)
      nlinarith

variable {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}

lemma stronglyAdapted_runningMaximum (hX : StronglyAdapted ℱ X) :
    StronglyAdapted ℱ (fun n ω => runningMaximum (fun j => X j ω) n) := by
  intro n
  induction n with
  | zero => exact hX 0
  | succ n ih =>
    letI : MeasurableSpace Ω := ℱ (n + 1)
    exact (ih.mono (ℱ.mono (Nat.le_succ n))).sup (hX (n + 1))

lemma integrable_runningMaximum_pow (hX : StronglyAdapted ℱ X)
    (h0 : ∀ n ω, 0 ≤ X n ω) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ n, ∀ᵐ ω ∂μ, X n ω ≤ C) (p n : ℕ) :
    Integrable (fun ω => runningMaximum (fun j => X j ω) n ^ p) μ := by
  have hm := ((stronglyAdapted_runningMaximum hX n).mono (ℱ.le n)).pow p
  apply Integrable.of_bound hm.aestronglyMeasurable (C ^ p)
  have hall : ∀ᵐ ω ∂μ, ∀ j, X j ω ≤ C := ae_all_iff.mpr hb
  filter_upwards [hall] with ω hω
  rw [Real.norm_eq_abs]
  change |runningMaximum (fun j => X j ω) n ^ p| ≤ C ^ p
  rw [abs_of_nonneg (pow_nonneg (runningMaximum_nonnegative (fun j => h0 j ω) n) p)]
  exact pow_le_pow_left₀ (runningMaximum_nonnegative (fun j => h0 j ω) n) (runningMaximum_le hω n) p

/-- The predictable running-maximum drift has nonnegative expectation. Weights are
clipped outside the a.e. bound before applying the library's submartingale transform. -/
lemma integral_runningMaximum_drift_nonnegative (hX : Submartingale X ℱ μ)
    (h0 : ∀ n ω, 0 ≤ X n ω) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, ∀ᵐ ω ∂μ, X n ω ≤ C) (p N : ℕ) :
    Integrable (fun ω => ∑ j ∈ Finset.range N,
      runningMaximum (fun a => X a ω) j ^ p * (X (j + 1) ω - X j ω)) μ ∧
    0 ≤ ∫ ω, ∑ j ∈ Finset.range N,
      runningMaximum (fun a => X a ω) j ^ p * (X (j + 1) ω - X j ω) ∂μ := by
  let M : ℕ → Ω → ℝ := fun n ω => runningMaximum (fun j => X j ω) n
  let W : ℕ → Ω → ℝ := fun n ω => min (M n ω ^ p) (C ^ p)
  have hM : StronglyAdapted ℱ M := stronglyAdapted_runningMaximum hX.stronglyAdapted
  have hW : StronglyAdapted ℱ W := by
    intro n
    letI : MeasurableSpace Ω := ℱ n
    exact (hM n).pow p |>.inf stronglyMeasurable_const
  have hW0 (n : ℕ) (ω : Ω) : 0 ≤ W n ω :=
    le_min (pow_nonneg (runningMaximum_nonnegative (fun j => h0 j ω) n) p) (pow_nonneg hC p)
  have hWC (n : ℕ) (ω : Ω) : W n ω ≤ C ^ p := min_le_right _ _
  have hS := hX.sum_mul_sub hW hWC hW0
  have hSI : Integrable (fun ω => ∑ j ∈ Finset.range N, W j ω * (X (j + 1) ω - X j ω)) μ := by
    convert hS.integrable N using 1
    funext ω
    simp only [Finset.sum_apply, Pi.mul_apply, Pi.sub_apply]
  have hmean : 0 ≤ ∫ ω, ∑ j ∈ Finset.range N, W j ω * (X (j + 1) ω - X j ω) ∂μ := by
    have h := hS.setIntegral_le (Nat.zero_le N) (s := Set.univ) MeasurableSet.univ
    simpa only [Finset.range_zero, Finset.sum_empty, Pi.zero_apply, setIntegral_univ, integral_zero,
      Finset.sum_apply, Pi.mul_apply, Pi.sub_apply] using h
  have hall : ∀ᵐ ω ∂μ, ∀ j, X j ω ≤ C := ae_all_iff.mpr hb
  have heq : (fun ω => ∑ j ∈ Finset.range N, W j ω * (X (j + 1) ω - X j ω)) =ᵐ[μ]
      (fun ω => ∑ j ∈ Finset.range N, M j ω ^ p * (X (j + 1) ω - X j ω)) := by
    filter_upwards [hall] with ω hω
    apply Finset.sum_congr rfl
    intro j _
    have hj : M j ω ^ p ≤ C ^ p := pow_le_pow_left₀
      (runningMaximum_nonnegative (fun a => h0 a ω) j) (runningMaximum_le hω j) p
    dsimp [W]
    rw [min_eq_left hj]
  exact ⟨hSI.congr heq, (integral_congr_ae heq) ▸ hmean⟩

omit [IsProbabilityMeasure μ] in
lemma integrable_terminal_mul_runningMaximum_pow (hX : Submartingale X ℱ μ)
    (h0 : ∀ n ω, 0 ≤ X n ω) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ n, ∀ᵐ ω ∂μ, X n ω ≤ C) (p N : ℕ) :
    Integrable (fun ω => X N ω * runningMaximum (fun j => X j ω) N ^ p) μ := by
  have hm := ((stronglyAdapted_runningMaximum hX.stronglyAdapted N).mono (ℱ.le N)).pow p
  apply (hX.integrable N).mul_bdd hm.aestronglyMeasurable
  have hall : ∀ᵐ ω ∂μ, ∀ j, X j ω ≤ C := ae_all_iff.mpr hb
  filter_upwards [hall] with ω hω
  rw [Real.norm_eq_abs]
  change |runningMaximum (fun j => X j ω) N ^ p| ≤ C ^ p
  rw [abs_of_nonneg (pow_nonneg (runningMaximum_nonnegative (fun j => h0 j ω) N) p)]
  exact pow_le_pow_left₀ (runningMaximum_nonnegative (fun j => h0 j ω) N) (runningMaximum_le hω N) p

/-- Finite Doob second-moment estimate with its classical constant four. -/
theorem submartingale_runningMaximum_square_le (hX : Submartingale X ℱ μ)
    (h0 : ∀ n ω, 0 ≤ X n ω) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, ∀ᵐ ω ∂μ, X n ω ≤ C) (N : ℕ) :
    (∫ ω, runningMaximum (fun j => X j ω) N ^ 2 ∂μ) ≤ 4 * ∫ ω, X N ω ^ 2 ∂μ := by
  let M : Ω → ℝ := fun ω => runningMaximum (fun j => X j ω) N
  let D : Ω → ℝ := fun ω => ∑ j ∈ Finset.range N,
    runningMaximum (fun a => X a ω) j * (X (j + 1) ω - X j ω)
  have hM2 : Integrable (fun ω => M ω ^ 2) μ := integrable_runningMaximum_pow hX.stronglyAdapted h0 hC hb 2 N
  have hX2 : Integrable (fun ω => X N ω ^ 2) μ :=
    integrable_pow_of_bound ((hX.stronglyAdapted N).mono (ℱ.le N)).measurable hC
      ((hb N).mono (fun ω hω => by simpa only [abs_of_nonneg (h0 N ω)] using hω)) 2
  have hXM : Integrable (fun ω => X N ω * M ω) μ := by
    simpa only [pow_one] using integrable_terminal_mul_runningMaximum_pow hX h0 hC hb 1 N
  have hD : Integrable D μ ∧ 0 ≤ ∫ ω, D ω ∂μ := by
    simpa only [pow_one] using integral_runningMaximum_drift_nonnegative hX h0 hC hb 1 N
  have hdual : (∫ ω, M ω ^ 2 ∂μ) ≤ ∫ ω, 2 * (X N ω * M ω) - 2 * D ω ∂μ := by
    apply integral_mono hM2 ((hXM.const_mul 2).sub (hD.1.const_mul 2))
    intro ω
    change M ω ^ 2 ≤ 2 * (X N ω * M ω) - 2 * D ω
    simpa only [M, D, mul_assoc] using runningMaximum_square_duality (fun j => X j ω) N
  rw [integral_sub (f := fun ω => 2 * (X N ω * M ω)) (g := fun ω => 2 * D ω)
    (hXM.const_mul 2) (hD.1.const_mul 2), integral_const_mul, integral_const_mul] at hdual
  have hyoung : (∫ ω, 4 * (X N ω * M ω) ∂μ) ≤ ∫ ω, 4 * X N ω ^ 2 + M ω ^ 2 ∂μ := by
    apply integral_mono (hXM.const_mul 4) ((hX2.const_mul 4).add hM2)
    intro ω
    change 4 * (X N ω * M ω) ≤ 4 * X N ω ^ 2 + M ω ^ 2
    nlinarith [sq_nonneg (2 * X N ω - M ω)]
  rw [integral_const_mul,
    integral_add (f := fun ω => 4 * X N ω ^ 2) (g := fun ω => M ω ^ 2) (hX2.const_mul 4) hM2,
    integral_const_mul] at hyoung
  change (∫ ω, M ω ^ 2 ∂μ) ≤ 4 * ∫ ω, X N ω ^ 2 ∂μ
  linarith [hD.2]

/-- Finite sixth-moment maximal estimate with explicit universal constant thirteen.
This slightly larger constant avoids fractional-exponent manipulation. -/
theorem submartingale_runningMaximum_sixth_le (hX : Submartingale X ℱ μ)
    (h0 : ∀ n ω, 0 ≤ X n ω) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, ∀ᵐ ω ∂μ, X n ω ≤ C) (N : ℕ) :
    (∫ ω, runningMaximum (fun j => X j ω) N ^ 6 ∂μ) ≤ 13 * ∫ ω, X N ω ^ 6 ∂μ := by
  let M : Ω → ℝ := fun ω => runningMaximum (fun j => X j ω) N
  let D : Ω → ℝ := fun ω => ∑ j ∈ Finset.range N,
    runningMaximum (fun a => X a ω) j ^ 5 * (X (j + 1) ω - X j ω)
  have hM6 : Integrable (fun ω => M ω ^ 6) μ := integrable_runningMaximum_pow hX.stronglyAdapted h0 hC hb 6 N
  have hX6 : Integrable (fun ω => X N ω ^ 6) μ :=
    integrable_pow_of_bound ((hX.stronglyAdapted N).mono (ℱ.le N)).measurable hC
      ((hb N).mono (fun ω hω => by simpa only [abs_of_nonneg (h0 N ω)] using hω)) 6
  have hXM5 : Integrable (fun ω => X N ω * M ω ^ 5) μ :=
    integrable_terminal_mul_runningMaximum_pow hX h0 hC hb 5 N
  have hD : Integrable D μ ∧ 0 ≤ ∫ ω, D ω ∂μ :=
    integral_runningMaximum_drift_nonnegative hX h0 hC hb 5 N
  have hdual : (∫ ω, 5 * M ω ^ 6 ∂μ) ≤ ∫ ω, 6 * (X N ω * M ω ^ 5) - 6 * D ω ∂μ := by
    apply integral_mono (hM6.const_mul 5) ((hXM5.const_mul 6).sub (hD.1.const_mul 6))
    intro ω
    change 5 * M ω ^ 6 ≤ 6 * (X N ω * M ω ^ 5) - 6 * D ω
    simpa only [M, D, mul_assoc] using runningMaximum_sixth_duality (fun j => h0 j ω) N
  rw [integral_const_mul,
    integral_sub (f := fun ω => 6 * (X N ω * M ω ^ 5)) (g := fun ω => 6 * D ω)
      (hXM5.const_mul 6) (hD.1.const_mul 6), integral_const_mul, integral_const_mul] at hdual
  have hyoung : (∫ ω, 12 * (X N ω * M ω ^ 5) ∂μ) ≤
      ∫ ω, 64 * X N ω ^ 6 + 5 * M ω ^ 6 ∂μ := by
    apply integral_mono (hXM5.const_mul 12) ((hX6.const_mul 64).add (hM6.const_mul 5))
    intro ω
    change 12 * (X N ω * M ω ^ 5) ≤ 64 * X N ω ^ 6 + 5 * M ω ^ 6
    have h := sixth_young (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (h0 N ω))
      (runningMaximum_nonnegative (fun j => h0 j ω) N)
    dsimp [M]
    nlinarith
  rw [integral_const_mul,
    integral_add (f := fun ω => 64 * X N ω ^ 6) (g := fun ω => 5 * M ω ^ 6)
      (hX6.const_mul 64) (hM6.const_mul 5), integral_const_mul, integral_const_mul] at hyoung
  have hnonneg : 0 ≤ ∫ ω, X N ω ^ 6 ∂μ := integral_nonneg (fun ω => pow_nonneg (h0 N ω) 6)
  change (∫ ω, M ω ^ 6 ∂μ) ≤ 13 * ∫ ω, X N ω ^ 6 ∂μ
  linarith [hD.2]

end ProphetSecretary.Probability
