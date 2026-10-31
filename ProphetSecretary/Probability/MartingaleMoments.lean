import ProphetSecretary.Probability.FiniteDoob
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Polynomial martingale moment estimates

The sixth-power increment estimate cancels the linear martingale term after conditional
expectation. Its constants are universal and involve no instance-size parameter.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Probability

lemma sixth_increment_le (s d : ℝ) :
    (s + d) ^ 6 ≤ s ^ 6 + 6 * s ^ 5 * d + 39 * (s ^ 4 * d ^ 2 + d ^ 6) := by
  have h31 : 0 ≤ d ^ 2 * (s - d) ^ 2 * (2 * s ^ 2 + (s + d) ^ 2) := by positivity
  have h22 : 0 ≤ d ^ 2 * (s ^ 2 - d ^ 2) ^ 2 := by positivity
  have h13 : 0 ≤ d ^ 2 * (s - d) ^ 2 * ((s + d) ^ 2 + 2 * d ^ 2) := by positivity
  have hd6 : 0 ≤ d ^ 6 := by positivity
  nlinarith

lemma cubic_young {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    3 * a ^ 2 * b ≤ 2 * a ^ 3 + b ^ 3 := by
  have h : 0 ≤ (a - b) ^ 2 * (2 * a + b) := mul_nonneg (sq_nonneg _) (by positivity)
  nlinarith

variable {Ω : Type*} [m0 : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ m0} {S : ℕ → Ω → ℝ}

omit [IsProbabilityMeasure μ] in
lemma martingale_abs_submartingale (hS : Martingale S ℱ μ) :
    Submartingale (fun n ω => |S n ω|) ℱ μ := by
  have hadapt : StronglyAdapted ℱ (fun n ω => |S n ω|) := by
    intro n
    letI : MeasurableSpace Ω := ℱ n
    exact continuous_abs.comp_stronglyMeasurable (hS.stronglyAdapted n)
  refine ⟨hadapt, ?_, fun n => (hS.integrable n).abs⟩
  intro i j hij
  filter_upwards [hS.condExp_ae_eq hij, norm_condExp_le (μ := μ) (m := ℱ i) (S j)] with ω heq hle
  simpa only [Real.norm_eq_abs, heq] using hle

/-- The previously proved finite Doob estimate applies to the absolute process
of an actual martingale, with no separately assumed submartingale property. -/
theorem martingale_runningAbsMaximum_square_le (hS : Martingale S ℱ μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ ω ∂μ, |S n ω| ≤ C) (N : ℕ) :
    (∫ ω, runningMaximum (fun j => |S j ω|) N ^ 2 ∂μ) ≤ 4 * ∫ ω, S N ω ^ 2 ∂μ := by
  simpa only [sq_abs] using submartingale_runningMaximum_square_le
    (martingale_abs_submartingale hS) (fun _ _ => abs_nonneg _) hC hb N

theorem martingale_runningAbsMaximum_sixth_le (hS : Martingale S ℱ μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ ω ∂μ, |S n ω| ≤ C) (N : ℕ) :
    (∫ ω, runningMaximum (fun j => |S j ω|) N ^ 6 ∂μ) ≤ 13 * ∫ ω, S N ω ^ 6 ∂μ := by
  have h := submartingale_runningMaximum_sixth_le
    (martingale_abs_submartingale hS) (fun _ _ => abs_nonneg _) hC hb N
  apply h.trans_eq
  apply congrArg (13 * ·)
  apply integral_congr_ae
  filter_upwards [] with ω
  rw [← abs_pow, abs_of_nonneg (by positivity)]

lemma martingale_condExp_increment_zero (hS : Martingale S ℱ μ) (j : ℕ) :
    μ[S (j + 1) - S j | ℱ j] =ᵐ[μ] 0 := by
  have hd := condExp_sub (hS.integrable (j + 1)) (hS.integrable j) (ℱ j)
  rw [condExp_of_stronglyMeasurable (ℱ.le j) (hS.stronglyAdapted j) (hS.integrable j)] at hd
  filter_upwards [hd, hS.condExp_ae_eq (Nat.le_succ j)] with ω hdω hsω
  simpa only [Pi.sub_apply, Pi.zero_apply, hsω, sub_self] using hdω

/-- Cancellation of the linear predictable term in a moment expansion. -/
lemma integral_predictable_mul_increment_zero (hS : Martingale S ℱ μ) (j : ℕ)
    {g : Ω → ℝ} (hg : StronglyMeasurable[ℱ j] g)
    (hprod : Integrable (g * (S (j + 1) - S j)) μ) :
    (∫ ω, g ω * (S (j + 1) ω - S j ω) ∂μ) = 0 := by
  have hCE := condExp_mul_of_stronglyMeasurable_left (m := ℱ j) hg hprod
    ((hS.integrable (j + 1)).sub (hS.integrable j))
  have hzero : μ[g * (S (j + 1) - S j) | ℱ j] =ᵐ[μ] 0 := by
    filter_upwards [hCE, martingale_condExp_increment_zero hS j] with ω hω hz
    simpa only [Pi.mul_apply, Pi.zero_apply, hz, mul_zero] using hω
  change (∫ ω, (g * (S (j + 1) - S j)) ω ∂μ) = 0
  calc
    _ = ∫ ω, (μ[g * (S (j + 1) - S j) | ℱ j]) ω ∂μ := (integral_condExp (ℱ.le j)).symm
    _ = 0 := integral_eq_zero_of_ae hzero

/-- Pulling out a predictable factor gives an actual integral identity and proves
integrability of its product with the conditional expectation. -/
lemma predictable_mul_condExp_integral {j : ℕ} {g f : Ω → ℝ}
    (hg : StronglyMeasurable[ℱ j] g) (hf : Integrable f μ) (hprod : Integrable (g * f) μ) :
    Integrable (g * μ[f | ℱ j]) μ ∧
      (∫ ω, g ω * f ω ∂μ) = ∫ ω, g ω * (μ[f | ℱ j]) ω ∂μ := by
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := ℱ j) hg hprod hf
  refine ⟨integrable_condExp.congr hpull, ?_⟩
  change (∫ ω, (g * f) ω ∂μ) = ∫ ω, (g * μ[f | ℱ j]) ω ∂μ
  calc
    _ = ∫ ω, (μ[g * f | ℱ j]) ω ∂μ := (integral_condExp (ℱ.le j)).symm
    _ = _ := integral_congr_ae hpull

lemma integrable_martingale_monomial (hS : Martingale S ℱ μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ ω ∂μ, |S n ω| ≤ C)
    (j p q : ℕ) :
    Integrable (fun ω => S j ω ^ p * (S (j + 1) ω - S j ω) ^ q) μ := by
  have hSj : Measurable (S j) := ((hS.stronglyAdapted j).mono (ℱ.le j)).measurable
  have hSj1 : Measurable (S (j + 1)) := ((hS.stronglyAdapted (j + 1)).mono (ℱ.le (j + 1))).measurable
  apply Integrable.of_bound ((hSj.pow_const p).mul ((hSj1.sub hSj).pow_const q)).aestronglyMeasurable
    (C ^ p * (2 * C) ^ q)
  filter_upwards [hb j, hb (j + 1)] with ω hj hj1
  rw [Real.norm_eq_abs]
  change |S j ω ^ p * (S (j + 1) ω - S j ω) ^ q| ≤ C ^ p * (2 * C) ^ q
  rw [abs_mul, abs_pow, abs_pow]
  have hd : |S (j + 1) ω - S j ω| ≤ 2 * C := by
    calc
      _ ≤ |S (j + 1) ω| + |S j ω| := abs_sub _ _
      _ ≤ C + C := add_le_add hj1 hj
      _ = _ := by ring
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hj p)
    (pow_le_pow_left₀ (abs_nonneg _) hd q) (pow_nonneg (abs_nonneg _) q) (pow_nonneg hC p)

/-- The predictable quadratic variation is built from the actual conditional second
moments, rather than supplied as a moment-bound hypothesis. -/
noncomputable def predictableQuadraticVariation (ℱ : Filtration ℕ m0) (μ : Measure Ω)
    (S : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ j ∈ Finset.range N, (μ[(fun a => (S (j + 1) a - S j a) ^ 2) | ℱ j]) ω

omit [IsProbabilityMeasure μ] in
lemma measurable_predictableQuadraticVariation (N : ℕ) :
    Measurable (predictableQuadraticVariation ℱ μ S N) := by
  apply Finset.measurable_sum
  intro j _
  have hq : StronglyMeasurable[ℱ j] (μ[(fun a => (S (j + 1) a - S j a) ^ 2) | ℱ j]) :=
    stronglyMeasurable_condExp
  exact (hq.mono (ℱ.le j)).measurable

omit [IsProbabilityMeasure μ] in
lemma predictableQuadraticVariation_bounds {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, ∀ᵐ ω ∂μ, |S n ω| ≤ C) (N : ℕ) :
    ∀ᵐ ω ∂μ, 0 ≤ predictableQuadraticVariation ℱ μ S N ω ∧
      predictableQuadraticVariation ℱ μ S N ω ≤ (N : ℝ) * (2 * C) ^ 2 := by
  have hq (j : ℕ) : ∀ᵐ ω ∂μ,
      0 ≤ (μ[(fun a => (S (j + 1) a - S j a) ^ 2) | ℱ j]) ω ∧
        (μ[(fun a => (S (j + 1) a - S j a) ^ 2) | ℱ j]) ω ≤ (2 * C) ^ 2 := by
    have hdb : ∀ᵐ ω ∂μ, (S (j + 1) ω - S j ω) ^ 2 ≤ (2 * C) ^ 2 := by
      filter_upwards [hb j, hb (j + 1)] with ω hj hj1
      have hd : |S (j + 1) ω - S j ω| ≤ 2 * C := by
        calc
          _ ≤ |S (j + 1) ω| + |S j ω| := abs_sub _ _
          _ ≤ C + C := add_le_add hj1 hj
          _ = _ := by ring
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (show (0 : ℝ) ≤ 2 * C by positivity)).mpr hd
    filter_upwards [condExp_nonneg (Filter.Eventually.of_forall (fun ω => sq_nonneg (S (j + 1) ω - S j ω))),
      condExp_le_nonneg_const (m := ℱ j) (sq_nonneg (2 * C)) hdb] with ω h0 h1
    exact ⟨h0, h1⟩
  have hall : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ (μ[(fun a => (S (j + 1) a - S j a) ^ 2) | ℱ j]) ω ∧
      (μ[(fun a => (S (j + 1) a - S j a) ^ 2) | ℱ j]) ω ≤ (2 * C) ^ 2 := ae_all_iff.mpr hq
  filter_upwards [hall] with ω hω
  constructor
  · exact Finset.sum_nonneg (fun j _ => (hω j).1)
  · apply (Finset.sum_le_sum (fun j (_ : j ∈ Finset.range N) => (hω j).2)).trans_eq
    simp

lemma integrable_predictableQuadraticVariation_pow {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ n, ∀ᵐ ω ∂μ, |S n ω| ≤ C) (p N : ℕ) :
    Integrable (fun ω => predictableQuadraticVariation ℱ μ S N ω ^ p) μ := by
  apply integrable_pow_of_bound (C := (N : ℝ) * (2 * C) ^ 2)
    (measurable_predictableQuadraticVariation N) (by positivity)
  filter_upwards [predictableQuadraticVariation_bounds (ℱ := ℱ) hC hb N] with ω hω
  simpa only [abs_of_nonneg hω.1] using hω.2

/-- Summing the polynomial increment inequality along a finite path. -/
lemma sixth_process_bound (s : ℕ → ℝ) (N : ℕ) :
    s N ^ 6 ≤ s 0 ^ 6 + 6 * (∑ j ∈ Finset.range N, s j ^ 5 * (s (j + 1) - s j)) +
      39 * (∑ j ∈ Finset.range N, s j ^ 4 * (s (j + 1) - s j) ^ 2) +
      39 * (∑ j ∈ Finset.range N, (s (j + 1) - s j) ^ 6) := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    have h := sixth_increment_le (s N) (s (N + 1) - s N)
    rw [add_sub_cancel] at h
    linarith

lemma second_process_identity (s : ℕ → ℝ) (N : ℕ) :
    s N ^ 2 = s 0 ^ 2 + 2 * (∑ j ∈ Finset.range N, s j * (s (j + 1) - s j)) +
      ∑ j ∈ Finset.range N, (s (j + 1) - s j) ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    nlinarith

lemma integral_martingale_monomial_linear_zero (hS : Martingale S ℱ μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ ω ∂μ, |S n ω| ≤ C) (j p : ℕ) :
    (∫ ω, S j ω ^ p * (S (j + 1) ω - S j ω) ∂μ) = 0 := by
  have hg : StronglyMeasurable[ℱ j] (fun ω => S j ω ^ p) := by
    letI : MeasurableSpace Ω := ℱ j
    exact (hS.stronglyAdapted j).pow p
  have hprod : Integrable ((fun ω => S j ω ^ p) * (S (j + 1) - S j)) μ := by
    convert integrable_martingale_monomial hS hC hb j p 1 using 1
    funext ω
    simp only [Pi.mul_apply, Pi.sub_apply, pow_one]
  exact integral_predictable_mul_increment_zero hS j hg hprod

lemma integral_predictableQuadraticVariation (N : ℕ) :
    (∫ ω, predictableQuadraticVariation ℱ μ S N ω ∂μ) =
      ∑ j ∈ Finset.range N, ∫ ω, (S (j + 1) ω - S j ω) ^ 2 ∂μ := by
  unfold predictableQuadraticVariation
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    exact integral_condExp (ℱ.le j)
  · intro j _
    exact integrable_condExp

/-- Exact second-moment identity for a bounded martingale starting at zero. -/
theorem martingale_secondMoment_eq_quadraticVariation (hS : Martingale S ℱ μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ ω ∂μ, |S n ω| ≤ C)
    (hzero : ∀ ω, S 0 ω = 0) (N : ℕ) :
    (∫ ω, S N ω ^ 2 ∂μ) = ∫ ω, predictableQuadraticVariation ℱ μ S N ω ∂μ := by
  have hpow (j p : ℕ) : Integrable (fun ω => S j ω ^ p) μ :=
    integrable_pow_of_bound ((hS.stronglyAdapted j).mono (ℱ.le j)).measurable hC (hb j) p
  let D : Ω → ℝ := fun ω => ∑ j ∈ Finset.range N, S j ω * (S (j + 1) ω - S j ω)
  let J : Ω → ℝ := fun ω => ∑ j ∈ Finset.range N, (S (j + 1) ω - S j ω) ^ 2
  have hD : Integrable D μ := by
    apply integrable_finsetSum
    intro j _
    simpa only [pow_one] using integrable_martingale_monomial hS hC hb j 1 1
  have hJ : Integrable J μ := by
    apply integrable_finsetSum
    intro j _
    simpa only [pow_zero, one_mul] using integrable_martingale_monomial hS hC hb j 0 2
  have hDmean : (∫ ω, D ω ∂μ) = 0 := by
    rw [integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro j _
      simpa only [pow_one] using integral_martingale_monomial_linear_zero hS hC hb j 1
    · intro j _
      simpa only [pow_one] using integrable_martingale_monomial hS hC hb j 1 1
  have hI0 : (∫ ω, S 0 ω ^ 2 ∂μ) = 0 := by simp [hzero]
  have heq : (fun ω => S N ω ^ 2) = (fun ω => (S 0 ω ^ 2 + 2 * D ω) + J ω) := by
    funext ω
    exact second_process_identity (fun j => S j ω) N
  rw [heq,
    integral_add (f := fun ω => S 0 ω ^ 2 + 2 * D ω) (g := J)
      ((hpow 0 2).add (hD.const_mul 2)) hJ,
    integral_add (f := fun ω => S 0 ω ^ 2) (g := fun ω => 2 * D ω)
      (hpow 0 2) (hD.const_mul 2), integral_const_mul,
    hI0, hDmean, mul_zero, add_zero, zero_add, integral_predictableQuadraticVariation]
  exact integral_finsetSum _ (fun j _ => by
    simpa only [pow_zero, one_mul] using integrable_martingale_monomial hS hC hb j 0 2)

/-- Actual finite martingale maximal second moment in terms of its constructed
predictable quadratic variation. -/
theorem martingale_runningAbsMaximum_square_le_variation (hS : Martingale S ℱ μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ ω ∂μ, |S n ω| ≤ C)
    (hzero : ∀ ω, S 0 ω = 0) (N : ℕ) :
    (∫ ω, runningMaximum (fun j => |S j ω|) N ^ 2 ∂μ) ≤
      4 * ∫ ω, predictableQuadraticVariation ℱ μ S N ω ∂μ := by
  rw [← martingale_secondMoment_eq_quadraticVariation hS hC hb hzero N]
  exact martingale_runningAbsMaximum_square_le hS hC hb N

lemma integrable_runningAbsMaximum_pow_mul_variation (hS : Martingale S ℱ μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ ω ∂μ, |S n ω| ≤ C) (p N : ℕ) :
    Integrable (fun ω => runningMaximum (fun j => |S j ω|) N ^ p *
      predictableQuadraticVariation ℱ μ S N ω) μ := by
  have hM : Integrable (fun ω => runningMaximum (fun j => |S j ω|) N ^ p) μ :=
    integrable_runningMaximum_pow (martingale_abs_submartingale hS).stronglyAdapted
      (fun _ _ => abs_nonneg _) hC hb p N
  apply hM.mul_bdd (measurable_predictableQuadraticVariation N).aestronglyMeasurable
  filter_upwards [predictableQuadraticVariation_bounds (ℱ := ℱ) hC hb N] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
  exact hω.2

/-- Pulling the conditional second moment into each predictable monomial gives the
constructed quadratic variation; the running absolute maximum bounds every past factor. -/
lemma integral_fourth_times_increment_square_le (hS : Martingale S ℱ μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ ω ∂μ, |S n ω| ≤ C) (N : ℕ) :
    (∫ ω, ∑ j ∈ Finset.range N, S j ω ^ 4 * (S (j + 1) ω - S j ω) ^ 2 ∂μ) ≤
      ∫ ω, runningMaximum (fun j => |S j ω|) N ^ 4 * predictableQuadraticVariation ℱ μ S N ω ∂μ := by
  let q : ℕ → Ω → ℝ := fun j => μ[(fun a => (S (j + 1) a - S j a) ^ 2) | ℱ j]
  have hPJ (j : ℕ) : Integrable (fun ω => S j ω ^ 4 * q j ω) μ ∧
      (∫ ω, S j ω ^ 4 * (S (j + 1) ω - S j ω) ^ 2 ∂μ) =
        ∫ ω, S j ω ^ 4 * q j ω ∂μ := by
    have hg : StronglyMeasurable[ℱ j] (fun ω => S j ω ^ 4) := by
      letI : MeasurableSpace Ω := ℱ j
      exact (hS.stronglyAdapted j).pow 4
    have hf : Integrable (fun ω => (S (j + 1) ω - S j ω) ^ 2) μ := by
      simpa only [pow_zero, one_mul] using integrable_martingale_monomial hS hC hb j 0 2
    have hprod : Integrable ((fun ω => S j ω ^ 4) * (fun ω => (S (j + 1) ω - S j ω) ^ 2)) μ :=
      integrable_martingale_monomial hS hC hb j 4 2
    exact predictable_mul_condExp_integral hg hf hprod
  have hLI : Integrable (fun ω => ∑ j ∈ Finset.range N, S j ω ^ 4 * (S (j + 1) ω - S j ω) ^ 2) μ :=
    integrable_finsetSum _ (fun j _ => integrable_martingale_monomial hS hC hb j 4 2)
  have hRI : Integrable (fun ω => ∑ j ∈ Finset.range N, S j ω ^ 4 * q j ω) μ :=
    integrable_finsetSum _ (fun j _ => (hPJ j).1)
  have hq0 : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ q j ω := by
    apply ae_all_iff.mpr
    intro j
    exact condExp_nonneg (Filter.Eventually.of_forall (fun ω => sq_nonneg (S (j + 1) ω - S j ω)))
  calc
    _ = ∑ j ∈ Finset.range N, ∫ ω, S j ω ^ 4 * (S (j + 1) ω - S j ω) ^ 2 ∂μ :=
      integral_finsetSum _ (fun j _ => integrable_martingale_monomial hS hC hb j 4 2)
    _ = ∑ j ∈ Finset.range N, ∫ ω, S j ω ^ 4 * q j ω ∂μ := Finset.sum_congr rfl (fun j _ => (hPJ j).2)
    _ = ∫ ω, ∑ j ∈ Finset.range N, S j ω ^ 4 * q j ω ∂μ :=
      (integral_finsetSum _ (fun j _ => (hPJ j).1)).symm
    _ ≤ _ := by
      apply integral_mono_ae hRI (integrable_runningAbsMaximum_pow_mul_variation hS hC hb 4 N)
      filter_upwards [hq0] with ω hω
      change (∑ j ∈ Finset.range N, S j ω ^ 4 * q j ω) ≤
        runningMaximum (fun j => |S j ω|) N ^ 4 * (∑ j ∈ Finset.range N, q j ω)
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j hj
      have hle := le_runningMaximum (fun j => |S j ω|) (Nat.le_of_lt (Finset.mem_range.mp hj))
      have hpow := pow_le_pow_left₀ (abs_nonneg (S j ω)) hle 4
      have he : |S j ω| ^ 4 = S j ω ^ 4 := by rw [← abs_pow, abs_of_nonneg (by positivity)]
      rw [he] at hpow
      exact mul_le_mul_of_nonneg_right hpow (hω j)

/-- The terminal sixth moment is controlled by the actual quadratic variation and
sixth powers of jumps. Its predictable linear terms cancel by the martingale property. -/
theorem martingale_sixth_terminal_le (hS : Martingale S ℱ μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ ω ∂μ, |S n ω| ≤ C)
    (hzero : ∀ ω, S 0 ω = 0) (N : ℕ) :
    (∫ ω, S N ω ^ 6 ∂μ) ≤
      39 * (∫ ω, runningMaximum (fun j => |S j ω|) N ^ 4 * predictableQuadraticVariation ℱ μ S N ω ∂μ) +
      39 * (∑ j ∈ Finset.range N, ∫ ω, (S (j + 1) ω - S j ω) ^ 6 ∂μ) := by
  let L : Ω → ℝ := fun ω => ∑ j ∈ Finset.range N, S j ω ^ 5 * (S (j + 1) ω - S j ω)
  let V : Ω → ℝ := fun ω => ∑ j ∈ Finset.range N, S j ω ^ 4 * (S (j + 1) ω - S j ω) ^ 2
  let W : Ω → ℝ := fun ω => ∑ j ∈ Finset.range N, (S (j + 1) ω - S j ω) ^ 6
  have hpow (j p : ℕ) : Integrable (fun ω => S j ω ^ p) μ :=
    integrable_pow_of_bound ((hS.stronglyAdapted j).mono (ℱ.le j)).measurable hC (hb j) p
  have hL : Integrable L μ := by
    apply integrable_finsetSum
    intro j _
    simpa only [pow_one] using integrable_martingale_monomial hS hC hb j 5 1
  have hV : Integrable V μ := integrable_finsetSum _ (fun j _ => integrable_martingale_monomial hS hC hb j 4 2)
  have hW : Integrable W μ := by
    apply integrable_finsetSum
    intro j _
    simpa only [pow_zero, one_mul] using integrable_martingale_monomial hS hC hb j 0 6
  have hLmean : (∫ ω, L ω ∂μ) = 0 := by
    rw [integral_finsetSum]
    · exact Finset.sum_eq_zero (fun j _ => integral_martingale_monomial_linear_zero hS hC hb j 5)
    · intro j _
      simpa only [pow_one] using integrable_martingale_monomial hS hC hb j 5 1
  have hI0 : (∫ ω, S 0 ω ^ 6 ∂μ) = 0 := by simp [hzero]
  have hineq : (∫ ω, S N ω ^ 6 ∂μ) ≤
      ∫ ω, ((S 0 ω ^ 6 + 6 * L ω) + 39 * V ω) + 39 * W ω ∂μ := by
    apply integral_mono (hpow N 6) ((((hpow 0 6).add (hL.const_mul 6)).add (hV.const_mul 39)).add (hW.const_mul 39))
    intro ω
    change S N ω ^ 6 ≤ ((S 0 ω ^ 6 + 6 * L ω) + 39 * V ω) + 39 * W ω
    exact sixth_process_bound (fun j => S j ω) N
  rw [integral_add (f := fun ω => (S 0 ω ^ 6 + 6 * L ω) + 39 * V ω) (g := fun ω => 39 * W ω)
      (((hpow 0 6).add (hL.const_mul 6)).add (hV.const_mul 39)) (hW.const_mul 39),
    integral_add (f := fun ω => S 0 ω ^ 6 + 6 * L ω) (g := fun ω => 39 * V ω)
      ((hpow 0 6).add (hL.const_mul 6)) (hV.const_mul 39),
    integral_add (f := fun ω => S 0 ω ^ 6) (g := fun ω => 6 * L ω) (hpow 0 6) (hL.const_mul 6),
    integral_const_mul, integral_const_mul, integral_const_mul, hI0, hLmean] at hineq
  simp only [mul_zero, zero_add] at hineq
  have hWmean : (∫ ω, W ω ∂μ) = ∑ j ∈ Finset.range N, ∫ ω, (S (j + 1) ω - S j ω) ^ 6 ∂μ :=
    integral_finsetSum _ (fun j _ => by simpa only [pow_zero, one_mul] using integrable_martingale_monomial hS hC hb j 0 6)
  rw [hWmean] at hineq
  exact hineq.trans (add_le_add
    (mul_le_mul_of_nonneg_left (integral_fourth_times_increment_square_le hS hC hb N) (by norm_num)) le_rfl)

/-- A finite sixth-moment maximal inequality with an explicit universal constant.
Only the constructed predictable quadratic variation appears in the conclusion;
`C` justifies integrability and has no effect on the constant. -/
theorem martingale_runningAbsMaximum_sixth_le_variation (hS : Martingale S ℱ μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, ∀ᵐ ω ∂μ, |S n ω| ≤ C)
    (hzero : ∀ ω, S 0 ω = 0) (N : ℕ) :
    (∫ ω, runningMaximum (fun j => |S j ω|) N ^ 6 ∂μ) ≤
      2000000000 * ((∫ ω, predictableQuadraticVariation ℱ μ S N ω ^ 3 ∂μ) +
        ∑ j ∈ Finset.range N, ∫ ω, (S (j + 1) ω - S j ω) ^ 6 ∂μ) := by
  let M : Ω → ℝ := fun ω => runningMaximum (fun j => |S j ω|) N
  let Q : Ω → ℝ := predictableQuadraticVariation ℱ μ S N
  let A : ℝ := ∫ ω, M ω ^ 4 * Q ω ∂μ
  let B : ℝ := ∑ j ∈ Finset.range N, ∫ ω, (S (j + 1) ω - S j ω) ^ 6 ∂μ
  let X : ℝ := ∫ ω, M ω ^ 6 ∂μ
  let Y : ℝ := ∫ ω, Q ω ^ 3 ∂μ
  have hQbounds := predictableQuadraticVariation_bounds (ℱ := ℱ) hC hb N
  have hA0 : 0 ≤ A := by
    apply integral_nonneg_of_ae
    filter_upwards [hQbounds] with ω hω
    exact mul_nonneg (by positivity) hω.1
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun j _ => integral_nonneg (fun ω => by positivity))
  have hdoob := martingale_runningAbsMaximum_sixth_le hS hC hb N
  have hterm := martingale_sixth_terminal_le hS hC hb hzero N
  have hbound : X ≤ 1000 * (A + B) := by
    change X ≤ 13 * (∫ ω, S N ω ^ 6 ∂μ) at hdoob
    change (∫ ω, S N ω ^ 6 ∂μ) ≤ 39 * A + 39 * B at hterm
    nlinarith
  have hMI : Integrable (fun ω => M ω ^ 6) μ :=
    integrable_runningMaximum_pow (martingale_abs_submartingale hS).stronglyAdapted (fun _ _ => abs_nonneg _) hC hb 6 N
  have hQI : Integrable (fun ω => Q ω ^ 3) μ := integrable_predictableQuadraticVariation_pow hC hb 3 N
  have hAI : Integrable (fun ω => M ω ^ 4 * Q ω) μ := integrable_runningAbsMaximum_pow_mul_variation hS hC hb 4 N
  have hyoung : (∫ ω, 6000 * (M ω ^ 4 * Q ω) ∂μ) ≤
      ∫ ω, 2 * M ω ^ 6 + 8000000000 * Q ω ^ 3 ∂μ := by
    apply integral_mono_ae (hAI.const_mul 6000) ((hMI.const_mul 2).add (hQI.const_mul 8000000000))
    filter_upwards [hQbounds] with ω hω
    change 6000 * (M ω ^ 4 * Q ω) ≤ 2 * M ω ^ 6 + 8000000000 * Q ω ^ 3
    have h := cubic_young (sq_nonneg (M ω)) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2000) hω.1)
    nlinarith
  rw [integral_const_mul,
    integral_add (f := fun ω => 2 * M ω ^ 6) (g := fun ω => 8000000000 * Q ω ^ 3)
      (hMI.const_mul 2) (hQI.const_mul 8000000000), integral_const_mul, integral_const_mul] at hyoung
  change 6000 * A ≤ 2 * X + 8000000000 * Y at hyoung
  change X ≤ 2000000000 * (Y + B)
  nlinarith

end ProphetSecretary.Probability
