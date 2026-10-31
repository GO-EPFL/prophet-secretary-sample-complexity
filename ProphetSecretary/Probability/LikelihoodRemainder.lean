import ProphetSecretary.Probability.LikelihoodTilt
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Uniform Taylor remainders for fixed payoffs

Dimension-dependent pointwise bounds below justify differentiation under a finite
instance's integral. The resulting second-derivative and Taylor estimates use only
`I`, with constants independent of the number of variables. A payoff is held fixed
throughout differentiation, even if it was selected to examine a particular remainder.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology

namespace ProphetSecretary.Probability

variable {n : ℕ}

lemma tiltFactor_half_bounds {a t : ℝ} (ht : |t| ≤ 1 / 2) (ha : |a| ≤ 1) :
    1 / 2 ≤ 1 + t * a ∧ 1 + t * a ≤ 3 / 2 := by
  have hm : |t * a| ≤ 1 / 2 := by
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_left ha (abs_nonneg t)).trans (by simpa using ht))
  have h := abs_le.mp hm
  constructor <;> linarith

lemma tiltedScore_half_abs_le {a t : ℝ} (ht : |t| ≤ 1 / 2) (ha : |a| ≤ 1) :
    |a / (1 + t * a)| ≤ 2 := by
  have hl := (tiltFactor_half_bounds ht ha).1
  have hp : 0 < 1 + t * a := by linarith
  rw [abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  linarith

lemma likelihood_local_bounds (h : Fin n → ℝ → ℝ) (x : Fin n → ℝ)
    (hx : ∀ i, |h i (x i)| ≤ 1) {t : ℝ} (ht : |t| ≤ 1 / 2) :
    |likelihood h t x| ≤ (3 / 2 : ℝ) ^ n ∧
    |likelihoodFirst h t x| ≤ (3 / 2 : ℝ) ^ n * (2 * n) ∧
    |likelihoodSecond h t x| ≤ (3 / 2 : ℝ) ^ n * ((2 * (n : ℝ)) ^ 2 + 4 * n) := by
  let s : Fin n → ℝ := fun i => tiltedScore (h i) t (x i)
  have hs (i : Fin n) : |s i| ≤ 2 := tiltedScore_half_abs_le ht (hx i)
  have hL : |likelihood h t x| ≤ (3 / 2 : ℝ) ^ n := by
    unfold likelihood
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _i : Fin n, (3 / 2 : ℝ) := by
        apply Finset.prod_le_prod (fun _ _ => abs_nonneg _)
        intro i _
        have hi := tiltFactor_half_bounds ht (hx i)
        rw [abs_of_nonneg (by change 0 ≤ 1 + t * h i (x i); linarith)]
        exact hi.2
      _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hS : |∑ i, s i| ≤ 2 * n := by
    calc
      _ ≤ ∑ i, |s i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, (2 : ℝ) := Finset.sum_le_sum fun i _ => hs i
      _ = _ := by simp [nsmul_eq_mul, mul_comm]
  have hS2 : (∑ i, s i) ^ 2 ≤ (2 * (n : ℝ)) ^ 2 := by
    have hp := pow_le_pow_left₀ (abs_nonneg _) hS 2
    simpa only [sq_abs] using hp
  have hQ : ∑ i, s i ^ 2 ≤ 4 * n := by
    calc
      _ ≤ ∑ _i : Fin n, (4 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        have hp := pow_le_pow_left₀ (abs_nonneg (s i)) (hs i) 2
        norm_num only [sq_abs] at hp
        exact hp
      _ = _ := by simp [nsmul_eq_mul, mul_comm]
  have hCore : |secondLikelihoodCore h t x| ≤ (2 * (n : ℝ)) ^ 2 + 4 * n := by
    have hQ0 : 0 ≤ ∑ i, s i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    change |(∑ i, s i) ^ 2 - ∑ i, s i ^ 2| ≤ _
    apply abs_le.mpr
    constructor <;> nlinarith [sq_nonneg (∑ i, s i)]
  refine ⟨hL, ?_, ?_⟩
  · rw [likelihoodFirst, abs_mul]
    exact mul_le_mul hL hS (abs_nonneg _) (by positivity)
  · rw [likelihoodSecond, abs_mul]
    exact mul_le_mul hL hCore (abs_nonneg _) (by positivity)

lemma measurable_likelihoodFirst {h : Fin n → ℝ → ℝ} (hh : ∀ i, Measurable (h i)) (t : ℝ) :
    Measurable (likelihoodFirst h t) :=
  (measurable_likelihood hh t).mul (measurable_completeScore fun i => measurable_tiltedScore (hh i) t)

lemma measurable_likelihoodSecond {h : Fin n → ℝ → ℝ} (hh : ∀ i, Measurable (h i)) (t : ℝ) :
    Measurable (likelihoodSecond h t) := by
  apply (measurable_likelihood hh t).mul
  apply (measurable_completeScore (fun i => measurable_tiltedScore (hh i) t) |>.pow_const 2).sub
  exact Finset.measurable_sum _ (fun i _ => ((measurable_tiltedScore (hh i) t).comp (measurable_pi_apply i)).pow_const 2)

lemma measurable_likelihoodSecond_joint {h : Fin n → ℝ → ℝ} (hh : ∀ i, Measurable (h i)) :
    Measurable (fun z : ℝ × (Fin n → ℝ) => likelihoodSecond h z.1 z.2) := by
  unfold likelihoodSecond likelihood secondLikelihoodCore completeScore tiltedScore tiltFactor
  fun_prop

noncomputable def fixedPayoffMean (μ : Fin n → Measure ℝ) (h : Fin n → ℝ → ℝ)
    (F : (Fin n → ℝ) → ℝ) (t : ℝ) : ℝ := ∫ x, F x * likelihood h t x ∂Measure.pi μ

noncomputable def fixedPayoffFirst (μ : Fin n → Measure ℝ) (h : Fin n → ℝ → ℝ)
    (F : (Fin n → ℝ) → ℝ) (t : ℝ) : ℝ := ∫ x, F x * likelihoodFirst h t x ∂Measure.pi μ

noncomputable def fixedPayoffSecond (μ : Fin n → Measure ℝ) (h : Fin n → ℝ → ℝ)
    (F : (Fin n → ℝ) → ℝ) (t : ℝ) : ℝ := ∫ x, F x * likelihoodSecond h t x ∂Measure.pi μ

lemma ae_scores_unit (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) :
    ∀ᵐ x ∂Measure.pi μ, ∀ i, |h i (x i)| ≤ 1 := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval μ i).quasiMeasurePreserving.ae (hb i)

lemma fixedPayoff_integrable_local (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) (F : (Fin n → ℝ) → ℝ) (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hFb : ∀ᵐ x ∂Measure.pi μ, |F x| ≤ B)
    {t : ℝ} (ht : |t| ≤ 1 / 2) :
    Integrable (fun x => F x * likelihood h t x) (Measure.pi μ) ∧
    Integrable (fun x => F x * likelihoodFirst h t x) (Measure.pi μ) ∧
    Integrable (fun x => F x * likelihoodSecond h t x) (Measure.pi μ) := by
  have hgood := ae_scores_unit μ h hb
  refine ⟨?_, ?_, ?_⟩
  · apply Integrable.of_bound (hF.mul (measurable_likelihood hh t)).aestronglyMeasurable (B * (3 / 2 : ℝ) ^ n)
    filter_upwards [hgood, hFb] with x hx hFx
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hFx (likelihood_local_bounds h x hx ht).1 (abs_nonneg _) hB
  · apply Integrable.of_bound (hF.mul (measurable_likelihoodFirst hh t)).aestronglyMeasurable
      (B * ((3 / 2 : ℝ) ^ n * (2 * n)))
    filter_upwards [hgood, hFb] with x hx hFx
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hFx (likelihood_local_bounds h x hx ht).2.1 (abs_nonneg _) hB
  · apply Integrable.of_bound (hF.mul (measurable_likelihoodSecond hh t)).aestronglyMeasurable
      (B * ((3 / 2 : ℝ) ^ n * ((2 * (n : ℝ)) ^ 2 + 4 * n)))
    filter_upwards [hgood, hFb] with x hx hFx
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul hFx (likelihood_local_bounds h x hx ht).2.2 (abs_nonneg _) hB

/-- Differentiation of a fixed bounded payoff. In particular this does not differentiate
a reoptimized policy or a weight chosen again as the parameter changes. -/
lemma fixedPayoff_derivatives (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) (F : (Fin n → ℝ) → ℝ) (hF : Measurable F)
    {B : ℝ} (hB : 0 ≤ B) (hFb : ∀ᵐ x ∂Measure.pi μ, |F x| ≤ B)
    {t₀ : ℝ} (ht₀ : |t₀| ≤ 1 / 4) :
    HasDerivAt (fixedPayoffMean μ h F) (fixedPayoffFirst μ h F t₀) t₀ ∧
    HasDerivAt (fixedPayoffFirst μ h F) (fixedPayoffSecond μ h F t₀) t₀ := by
  have hhalf₀ : |t₀| ≤ 1 / 2 := ht₀.trans (by norm_num)
  have hi := fixedPayoff_integrable_local μ h hh hb F hF hB hFb hhalf₀
  have hs : Ioo (-(1 / 2 : ℝ)) (1 / 2) ∈ 𝓝 t₀ := by
    have h := abs_le.mp ht₀
    exact Ioo_mem_nhds (by linarith) (by linarith)
  have hhalf (t : ℝ) (ht : t ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) : |t| ≤ 1 / 2 := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
  have hgood := ae_scores_unit μ h hb
  have hne (x : Fin n → ℝ) (hx : ∀ i, |h i (x i)| ≤ 1) (t : ℝ)
      (ht : t ∈ Ioo (-(1 / 2 : ℝ)) (1 / 2)) (i : Fin n) : tiltFactor (h i) t (x i) ≠ 0 := by
    have hl : (1 / 2 : ℝ) ≤ tiltFactor (h i) t (x i) := (tiltFactor_half_bounds (hhalf t ht) (hx i)).1
    linarith
  constructor
  · have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := Measure.pi μ) (F := fun t x => F x * likelihood h t x)
      (F' := fun t x => F x * likelihoodFirst h t x)
      (bound := fun _ => B * ((3 / 2 : ℝ) ^ n * (2 * n))) hs
      (Filter.Eventually.of_forall fun t => (hF.mul (measurable_likelihood hh t)).aestronglyMeasurable)
      hi.1 (hF.mul (measurable_likelihoodFirst hh t₀)).aestronglyMeasurable
      (by
        filter_upwards [hgood, hFb] with x hx hFx
        intro t ht
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul hFx (likelihood_local_bounds h x hx (hhalf t ht)).2.1 (abs_nonneg _) hB)
      (integrable_const _) (by
        filter_upwards [hgood] with x hx
        intro t ht
        exact (hasDerivAt_likelihood h x t (hne x hx t ht)).const_mul (F x))
    exact hd.2
  · have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := Measure.pi μ) (F := fun t x => F x * likelihoodFirst h t x)
      (F' := fun t x => F x * likelihoodSecond h t x)
      (bound := fun _ => B * ((3 / 2 : ℝ) ^ n * ((2 * (n : ℝ)) ^ 2 + 4 * n))) hs
      (Filter.Eventually.of_forall fun t => (hF.mul (measurable_likelihoodFirst hh t)).aestronglyMeasurable)
      hi.2.1 (hF.mul (measurable_likelihoodSecond hh t₀)).aestronglyMeasurable
      (by
        filter_upwards [hgood, hFb] with x hx hFx
        intro t ht
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul hFx (likelihood_local_bounds h x hx (hhalf t ht)).2.2 (abs_nonneg _) hB)
      (integrable_const _) (by
        filter_upwards [hgood] with x hx
        intro t ht
        exact (hasDerivAt_likelihoodFirst h x t (hne x hx t ht)).const_mul (F x))
    exact hd.2

lemma measurable_fixedPayoffSecond (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i)) (F : (Fin n → ℝ) → ℝ) (hF : Measurable F) :
    Measurable (fixedPayoffSecond μ h F) := by
  have hj : Measurable (fun z : ℝ × (Fin n → ℝ) => F z.2 * likelihoodSecond h z.1 z.2) :=
    (hF.comp measurable_snd).mul (measurable_likelihoodSecond_joint hh)
  exact hj.stronglyMeasurable.integral_prod_right'.measurable

/-- Only this dimension-free bound enters the Taylor estimate. -/
lemma fixedPayoffSecond_abs_le (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂μ i = 0)
    (F : (Fin n → ℝ) → ℝ) (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hFb : ∀ᵐ x ∂Measure.pi μ, |F x| ≤ B) {t : ℝ} (ht : |t| ≤ 1 / 4) :
    |fixedPayoffSecond μ h F t| ≤ 4 * B * information μ h := by
  have hi := (fixedPayoff_integrable_local μ h hh hb F hF hB hFb (ht.trans (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2))).2.2
  have hs := likelihoodSecond_integrable_and_bound μ h hh hb hm ht
  calc
    _ ≤ ∫ x, |F x * likelihoodSecond h t x| ∂Measure.pi μ := by
      simpa only [fixedPayoffSecond, Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (μ := Measure.pi μ) (fun x => F x * likelihoodSecond h t x))
    _ ≤ ∫ x, B * |likelihoodSecond h t x| ∂Measure.pi μ := by
      apply integral_mono_ae hi.abs (hs.1.abs.const_mul B)
      exact hFb.mono fun x hx => by dsimp only; rw [abs_mul]; exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    _ = B * ∫ x, |likelihoodSecond h t x| ∂Measure.pi μ := integral_const_mul _ _
    _ ≤ B * (4 * information μ h) := mul_le_mul_of_nonneg_left hs.2 hB
    _ = _ := by ring

/-- A second-order scalar Taylor estimate using supplied derivatives, proved by
integration by parts. No continuity of the second derivative is required. -/
lemma unit_secondOrder_remainder_bound {f fd fdd : ℝ → ℝ}
    (hdf : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt f (fd t) t)
    (hdd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt fd (fdd t) t)
    (hmeas : Measurable fdd) {C : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1, |fdd t| ≤ C) :
    |f 1 - f 0 - fd 0| ≤ C / 2 := by
  have hfdcont : ContinuousOn fd (Set.uIcc (0 : ℝ) 1) := by
    simpa only [Set.uIcc_of_le zero_le_one] using HasDerivAt.continuousOn hdd
  have hiFd : IntervalIntegrable fd volume 0 1 := hfdcont.intervalIntegrable
  have hiFddR : IntegrableOn fdd (Icc (0 : ℝ) 1) volume := by
    apply Integrable.of_bound hmeas.aestronglyMeasurable C
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [Real.norm_eq_abs] using hbound t ht
  have hiFdd : IntervalIntegrable fdd volume 0 1 :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).mpr hiFddR
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (fun t ht => hdf t (by simpa only [Set.uIcc_of_le zero_le_one] using ht)) hiFd
  have hw : ContinuousOn (fun t : ℝ => 1 - t) (Set.uIcc (0 : ℝ) 1) := by fun_prop
  have hb := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (u := fun t => 1 - t) (u' := fun _ => -1)
    (v := fd) (v' := fdd) hw hfdcont
    (fun t _ => by convert! (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t) using 1; simp)
    (fun t ht => hdd t (by
      simp only [min_eq_left zero_le_one, max_eq_right zero_le_one, Set.mem_Ioo] at ht
      exact ⟨ht.1.le, ht.2.le⟩)) (intervalIntegrable_const) hiFdd
  simp only [sub_self, zero_mul, zero_sub, sub_zero, one_mul, neg_one_mul, intervalIntegral.integral_neg] at hb
  rw [hFTC] at hb
  have hrep : f 1 - f 0 - fd 0 = ∫ t in (0 : ℝ)..1, (1 - t) * fdd t := by linarith
  have hiW : IntervalIntegrable (fun t : ℝ => (1 - t) * fdd t) volume 0 1 := hiFdd.continuousOn_mul hw
  have hiAbs : IntervalIntegrable (fun t : ℝ => |(1 - t) * fdd t|) volume 0 1 := by
    simpa only [Real.norm_eq_abs] using hiW.norm
  have hiR : IntervalIntegrable (fun t : ℝ => (1 - t) * C) volume 0 1 :=
    (show ContinuousOn (fun t : ℝ => (1 - t) * C) (Set.uIcc (0 : ℝ) 1) by fun_prop).intervalIntegrable
  rw [hrep]
  calc
    _ ≤ ∫ t in (0 : ℝ)..1, |(1 - t) * fdd t| := by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm (f := fun t : ℝ => (1 - t) * fdd t) zero_le_one)
    _ ≤ ∫ t in (0 : ℝ)..1, (1 - t) * C :=
      intervalIntegral.integral_mono_on zero_le_one hiAbs hiR (fun t ht => by
        rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr ht.2)]
        exact mul_le_mul_of_nonneg_left (hbound t ht) (sub_nonneg.mpr ht.2))
    _ = C / 2 := by
      rw [intervalIntegral.integral_mul_const,
        intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => t)
          intervalIntegrable_const (continuous_id.intervalIntegrable 0 1),
        intervalIntegral.integral_const, integral_id]
      norm_num
      ring

/-- Explicit uniform Taylor remainder for a payoff fixed during the perturbation. -/
lemma fixedPayoff_taylor_bound (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂μ i = 0)
    (F : (Fin n → ℝ) → ℝ) (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hFb : ∀ᵐ x ∂Measure.pi μ, |F x| ≤ B) {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    |fixedPayoffMean μ h F θ - fixedPayoffMean μ h F 0 - θ * fixedPayoffFirst μ h F 0| ≤
      2 * B * θ ^ 2 * information μ h := by
  have ht (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : |θ * s| ≤ 1 / 4 := by
    rw [abs_mul, abs_of_nonneg hs.1]
    exact ((mul_le_mul_of_nonneg_left hs.2 (abs_nonneg θ)).trans (by simpa using hθ))
  let f := fun s : ℝ => fixedPayoffMean μ h F (θ * s)
  let fd := fun s : ℝ => θ * fixedPayoffFirst μ h F (θ * s)
  let fdd := fun s : ℝ => θ ^ 2 * fixedPayoffSecond μ h F (θ * s)
  have hd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : HasDerivAt f (fd s) s := by
    have h := (fixedPayoff_derivatives μ h hh hb F hF hB hFb (ht s hs)).1.comp s ((hasDerivAt_id s).const_mul θ)
    convert! h using 1
    simp [fd, mul_comm]
  have hdd (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : HasDerivAt fd (fdd s) s := by
    have h := ((fixedPayoff_derivatives μ h hh hb F hF hB hFb (ht s hs)).2.comp s
      ((hasDerivAt_id s).const_mul θ)).const_mul θ
    convert! h using 1
    dsimp [fd, fdd]
    ring
  have hmeas : Measurable fdd := measurable_const.mul
    ((measurable_fixedPayoffSecond μ h hh F hF).comp (measurable_const.mul measurable_id))
  have hbound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) : |fdd s| ≤ 4 * B * information μ h * θ ^ 2 := by
    dsimp [fdd]
    rw [abs_mul, abs_of_nonneg (sq_nonneg θ)]
    have h := mul_le_mul_of_nonneg_left (fixedPayoffSecond_abs_le μ h hh hb hm F hF hB hFb (ht s hs)) (sq_nonneg θ)
    nlinarith
  have hTaylor := unit_secondOrder_remainder_bound hd hdd hmeas hbound
  dsimp [f, fd] at hTaylor
  simpa only [mul_one, mul_zero, show (4 * B * information μ h * θ ^ 2) / 2 = 2 * B * θ ^ 2 * information μ h by ring] using hTaylor

lemma fixedPayoff_law_taylor_bound (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂μ i = 0)
    (F : (Fin n → ℝ) → ℝ) (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hFb : ∀ᵐ x ∂Measure.pi μ, |F x| ≤ B) {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    |(∫ x, F x ∂productTiltLaw μ h θ) - (∫ x, F x ∂Measure.pi μ) -
      θ * (∫ x, F x * completeScore h x ∂Measure.pi μ)| ≤ 2 * B * θ ^ 2 * information μ h := by
  have he : (∫ x, F x ∂productTiltLaw μ h θ) = fixedPayoffMean μ h F θ := by
    rw [integral_productTiltLaw μ h hh hb hm hθ F]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => mul_comm _ _
  rw [he]
  have hT := fixedPayoff_taylor_bound μ h hh hb hm F hF hB hFb hθ
  simpa only [fixedPayoffMean, fixedPayoffFirst, likelihood_zero, likelihoodFirst_zero, mul_one] using hT

lemma likelihood_remainder_integrable (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) (θ : ℝ) :
    Integrable (fun x => likelihood h θ x - 1 - θ * completeScore h x) (Measure.pi μ) := by
  have hZ : Integrable (completeScore h) (Measure.pi μ) := by
    simpa only [pow_one] using completeScore_integrable_pow μ h hh hb 1
  exact ((likelihood_integrable μ h hh hb θ).sub (integrable_const 1)).sub (hZ.const_mul θ)

/-- The L¹ Taylor remainder of the complete likelihood is at most `2θ²I`.
The bounded sign payoff used in the proof is fixed before differentiating its expectation. -/
lemma likelihood_L1_remainder_bound (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂μ i = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    (∫ x, |likelihood h θ x - 1 - θ * completeScore h x| ∂Measure.pi μ) ≤ 2 * θ ^ 2 * information μ h := by
  let R : (Fin n → ℝ) → ℝ := fun x => likelihood h θ x - 1 - θ * completeScore h x
  let F : (Fin n → ℝ) → ℝ := fun x => if 0 ≤ R x then 1 else -1
  have hRm : Measurable R := ((measurable_likelihood hh θ).sub measurable_const).sub
    (measurable_const.mul (measurable_completeScore hh))
  have hFm : Measurable F := Measurable.ite (measurableSet_le measurable_const hRm) measurable_const measurable_const
  have hFb : ∀ x, |F x| ≤ 1 := by intro x; dsimp [F]; split_ifs <;> norm_num
  have hFint : Integrable F (Measure.pi μ) := Integrable.of_bound hFm.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hFb x)
  have hZ : Integrable (completeScore h) (Measure.pi μ) := by
    simpa only [pow_one] using completeScore_integrable_pow μ h hh hb 1
  have hFZ : Integrable (fun x => F x * completeScore h x) (Measure.pi μ) := by
    apply hZ.abs.mono' (hFm.mul (measurable_completeScore hh)).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      simp only [Pi.mul_apply, abs_mul]
      exact (mul_le_mul_of_nonneg_right (hFb x) (abs_nonneg _)).trans_eq (one_mul _)
  have hFL := (fixedPayoff_integrable_local μ h hh hb F hFm zero_le_one
    (Filter.Eventually.of_forall hFb) (hθ.trans (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2))).1
  have hiDiff : Integrable (fun x => F x * likelihood h θ x - F x) (Measure.pi μ) := hFL.sub hFint
  have herror : fixedPayoffMean μ h F θ - fixedPayoffMean μ h F 0 - θ * fixedPayoffFirst μ h F 0 =
      ∫ x, |R x| ∂Measure.pi μ := by
    simp only [fixedPayoffMean, fixedPayoffFirst, likelihood_zero, likelihoodFirst_zero, mul_one]
    rw [← integral_const_mul, ← integral_sub hFL hFint, ← integral_sub hiDiff (hFZ.const_mul θ)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      have he : F x * likelihood h θ x - F x - θ * (F x * completeScore h x) = F x * R x := by dsimp [R]; ring
      change F x * likelihood h θ x - F x - θ * (F x * completeScore h x) = |R x|
      rw [he]
      dsimp [F]
      by_cases hx : 0 ≤ R x
      · rw [if_pos hx, one_mul, abs_of_nonneg hx]
      · rw [if_neg hx, neg_one_mul, abs_of_neg (lt_of_not_ge hx)]
  have hT := fixedPayoff_taylor_bound μ h hh hb hm F hFm zero_le_one (Filter.Eventually.of_forall hFb) hθ
  rw [herror, abs_of_nonneg (integral_nonneg fun x => abs_nonneg (R x))] at hT
  simpa only [one_mul, mul_one, R] using hT

/-- Fixed-policy payoffs may include arbitrary independent auxiliary randomness,
including arrival clocks. Its law is held fixed while the offer law is tilted. -/
lemma fixedPayoff_law_taylor_bound_prod {Aux : Type*} [MeasurableSpace Aux]
    (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (ν : Measure Aux) [IsProbabilityMeasure ν]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂μ i = 0)
    (G : (Fin n → ℝ) × Aux → ℝ) (hG : Measurable G) {B : ℝ} (hB : 0 ≤ B)
    (hGb : ∀ᵐ z ∂(Measure.pi μ).prod ν, |G z| ≤ B) {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    |(∫ z, G z ∂(productTiltLaw μ h θ).prod ν) - (∫ z, G z ∂(Measure.pi μ).prod ν) -
      θ * (∫ z, G z * completeScore h z.1 ∂(Measure.pi μ).prod ν)| ≤ 2 * B * θ ^ 2 * information μ h := by
  haveI := productTiltLaw_probability μ h hh hb hm hθ
  let F : (Fin n → ℝ) → ℝ := fun x => ∫ y, G (x, y) ∂ν
  have hFm : Measurable F := hG.stronglyMeasurable.integral_prod_right'.measurable
  have hFb : ∀ᵐ x ∂Measure.pi μ, |F x| ≤ B := by
    filter_upwards [Measure.ae_ae_of_ae_prod hGb] with x hx
    have h := norm_integral_le_of_norm_le_const (μ := ν)
      (f := fun y => G (x, y)) (hx.mono fun y hy => by simpa only [Real.norm_eq_abs] using hy)
    simpa only [F, Real.norm_eq_abs, probReal_univ, mul_one] using h
  have hGi : Integrable G ((Measure.pi μ).prod ν) := Integrable.of_bound hG.aestronglyMeasurable B
    (hGb.mono fun z hz => by simpa only [Real.norm_eq_abs] using hz)
  have hAC : (productTiltLaw μ h θ).prod ν ≪ (Measure.pi μ).prod ν := by
    rw [productTiltLaw_eq_withDensity μ h hh hb hm hθ,
      prod_withDensity_left (measurable_likelihood hh θ |>.ennreal_ofReal)]
    exact withDensity_absolutelyContinuous _ _
  have hGbTilt : ∀ᵐ z ∂(productTiltLaw μ h θ).prod ν, |G z| ≤ B := hAC.ae_le hGb
  have hGj : Integrable G ((productTiltLaw μ h θ).prod ν) := Integrable.of_bound hG.aestronglyMeasurable B
    (hGbTilt.mono fun z hz => by simpa only [Real.norm_eq_abs] using hz)
  have hbase := integral_prod G hGi
  have htilt := integral_prod G hGj
  have hZ : Integrable (completeScore h) (Measure.pi μ) := by
    simpa only [pow_one] using completeScore_integrable_pow μ h hh hb 1
  have hfst : MeasurePreserving (fun z : (Fin n → ℝ) × Aux => z.1) ((Measure.pi μ).prod ν) (Measure.pi μ) := measurePreserving_fst
  have hDom := (hfst.integrable_comp_of_integrable hZ.abs).const_mul B
  have hScore : Integrable (fun z : (Fin n → ℝ) × Aux => G z * completeScore h z.1) ((Measure.pi μ).prod ν) := by
    apply hDom.mono' (hG.mul ((measurable_completeScore hh).comp measurable_fst)).aestronglyMeasurable
    filter_upwards [hGb] with z hz
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right hz (abs_nonneg _)
  have hscore := integral_prod (fun z : (Fin n → ℝ) × Aux => G z * completeScore h z.1) hScore
  simp_rw [integral_mul_const] at hscore
  have hT := fixedPayoff_law_taylor_bound μ h hh hb hm F hFm hB hFb hθ
  rw [← hbase, ← htilt, ← hscore] at hT
  exact hT

/-- The score expectation is the derivative of the law's fixed-payoff expectation at
the base law. The payoff itself is not selected again during differentiation. -/
lemma hasDerivAt_fixedPayoff_law_zero (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂μ i = 0)
    (F : (Fin n → ℝ) → ℝ) (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (hFb : ∀ᵐ x ∂Measure.pi μ, |F x| ≤ B) :
    HasDerivAt (fun t => ∫ x, F x ∂productTiltLaw μ h t)
      (∫ x, F x * completeScore h x ∂Measure.pi μ) 0 := by
  have hd := (fixedPayoff_derivatives μ h hh hb F hF hB hFb (by norm_num : |(0 : ℝ)| ≤ 1 / 4)).1
  have he : (fun t => ∫ x, F x ∂productTiltLaw μ h t) =ᶠ[𝓝 (0 : ℝ)] fixedPayoffMean μ h F := by
    filter_upwards [Ioo_mem_nhds (by norm_num : (-(1 / 4 : ℝ)) < 0) (by norm_num : (0 : ℝ) < 1 / 4)] with t ht
    have hθ : |t| ≤ 1 / 4 := abs_le.mpr ⟨ht.1.le, ht.2.le⟩
    rw [integral_productTiltLaw μ h hh hb hm hθ F]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => mul_comm _ _
  simpa only [fixedPayoffFirst, likelihoodFirst_zero] using hd.congr_of_eventuallyEq he

end ProphetSecretary.Probability
