import ProphetSecretary.Model.Instance
import ProphetSecretary.Probability.FourthMoment
import Mathlib.Probability.Moments.Variance
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Centered likelihood tilts of independent marginals

The complete-vector score includes all offer coordinates, even those arriving after
an online policy stops. It is an analytical random variable, not policy information.
All first-order identities in this file keep the payoff fixed while the law changes.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace ProphetSecretary.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

def tiltFactor (h : Ω → ℝ) (θ : ℝ) (x : Ω) : ℝ := 1 + θ * h x

noncomputable def tiltLaw (μ : Measure Ω) (h : Ω → ℝ) (θ : ℝ) : Measure Ω :=
  μ.withDensity (fun x => ENNReal.ofReal (tiltFactor h θ x))

@[fun_prop] lemma measurable_tiltFactor {h : Ω → ℝ} (hh : Measurable h) (θ : ℝ) : Measurable (tiltFactor h θ) :=
  measurable_const.add (measurable_const.mul hh)

lemma tiltFactor_bounds {a θ : ℝ} (hθ : |θ| ≤ 1 / 4) (ha : |a| ≤ 1) :
    3 / 4 ≤ 1 + θ * a ∧ 1 + θ * a ≤ 5 / 4 := by
  have hmul : |θ * a| ≤ 1 / 4 := by
    rw [abs_mul]
    exact ((mul_le_mul_of_nonneg_left ha (abs_nonneg θ)).trans (by simpa using hθ))
  have h := abs_le.mp hmul
  constructor <;> linarith

lemma tiltLaw_absolutelyContinuous (μ : Measure Ω) (h : Ω → ℝ) (θ : ℝ) : tiltLaw μ h θ ≪ μ :=
  withDensity_absolutelyContinuous μ _

lemma probability_withDensity_ofReal {μ : Measure Ω} {f : Ω → ℝ}
    (hfi : Integrable f μ) (hf0 : ∀ᵐ x ∂μ, 0 ≤ f x) (hf1 : ∫ x, f x ∂μ = 1) :
    IsProbabilityMeasure (μ.withDensity (fun x => ENNReal.ofReal (f x))) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hfi hf0, hf1, ENNReal.ofReal_one]

lemma tiltLaw_probability {μ : Measure Ω} [IsProbabilityMeasure μ] {h : Ω → ℝ}
    (hh : Measurable h) (hbound : ∀ᵐ x ∂μ, |h x| ≤ 1) (hmean : ∫ x, h x ∂μ = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 4) : IsProbabilityMeasure (tiltLaw μ h θ) := by
  have hi : Integrable h μ := by
    apply Integrable.of_bound hh.aestronglyMeasurable 1
    simpa only [Real.norm_eq_abs] using hbound
  have hfi : Integrable (tiltFactor h θ) μ := (integrable_const 1).add (hi.const_mul θ)
  apply probability_withDensity_ofReal hfi
  · exact hbound.mono fun x hx => (by norm_num : (0 : ℝ) ≤ 3 / 4).trans (tiltFactor_bounds hθ hx).1
  · change (∫ x, 1 + θ * h x ∂μ) = 1
    rw [integral_add (integrable_const 1) (hi.const_mul θ), integral_const_mul, hmean]
    simp

lemma integral_tiltLaw {μ : Measure Ω} {h : Ω → ℝ} (hh : Measurable h) {θ : ℝ}
    (hnonneg : ∀ᵐ x ∂μ, 0 ≤ tiltFactor h θ x) (f : Ω → ℝ) :
    (∫ x, f x ∂tiltLaw μ h θ) = ∫ x, tiltFactor h θ x * f x ∂μ := by
  rw [tiltLaw, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [hnonneg] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul]

lemma tiltLaw_mutuallyAbsolutelyContinuous {μ : Measure Ω} {h : Ω → ℝ} (hh : Measurable h)
    (hbound : ∀ᵐ x ∂μ, |h x| ≤ 1) {θ : ℝ} (hθ : |θ| ≤ 1 / 4) : μ ≪ tiltLaw μ h θ := by
  apply withDensity_absolutelyContinuous' (by fun_prop)
  exact hbound.mono fun x hx => ENNReal.ofReal_ne_zero_iff.mpr (by
    have hlow := (tiltFactor_bounds hθ hx).1
    change 0 < 1 + θ * h x
    linarith)

variable {n : ℕ}

noncomputable def information (μ : Fin n → Measure ℝ) (h : Fin n → ℝ → ℝ) : ℝ :=
  ∑ i, ∫ x, h i x ^ 2 ∂μ i

def completeScore (h : Fin n → ℝ → ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, h i (x i)

def likelihood (h : Fin n → ℝ → ℝ) (θ : ℝ) (x : Fin n → ℝ) : ℝ := ∏ i, tiltFactor (h i) θ (x i)

lemma information_nonnegative (μ : Fin n → Measure ℝ) (h : Fin n → ℝ → ℝ) : 0 ≤ information μ h :=
  Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _

lemma measurable_completeScore {h : Fin n → ℝ → ℝ} (hh : ∀ i, Measurable (h i)) : Measurable (completeScore h) :=
  Finset.measurable_sum _ (fun i _ => (hh i).comp (measurable_pi_apply i))

lemma measurable_likelihood {h : Fin n → ℝ → ℝ} (hh : ∀ i, Measurable (h i)) (θ : ℝ) : Measurable (likelihood h θ) :=
  Finset.measurable_prod _ (fun i _ => (measurable_tiltFactor (hh i) θ).comp (measurable_pi_apply i))

lemma integral_coordinate_comp (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : ℝ → ℝ) (hf : Measurable f) (i : Fin n) :
    (∫ x : Fin n → ℝ, f (x i) ∂Measure.pi μ) = ∫ x, f x ∂μ i := by
  have he := integral_map (μ := Measure.pi μ) (measurable_pi_apply i).aemeasurable hf.aestronglyMeasurable
  rw [(measurePreserving_eval μ i).map_eq] at he
  exact he.symm

lemma completeScore_integrable_pow (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) (k : ℕ) :
    Integrable (fun x : Fin n → ℝ => completeScore h x ^ k) (Measure.pi μ) := by
  exact integrable_finsetSum_pow_of_bound Finset.univ (fun (i : Fin n) (x : Fin n → ℝ) => h i (x i))
    (fun i => (hh i).comp (measurable_pi_apply i))
    (fun i => (measurePreserving_eval μ i).quasiMeasurePreserving.ae (hb i)) k

lemma completeScore_mean (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂μ i = 0) :
    (∫ x, completeScore h x ∂Measure.pi μ) = 0 := by
  unfold completeScore
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _
    rw [integral_coordinate_comp μ (h i) (hh i) i, hm i]
  · intro i _
    apply (measurePreserving_eval μ i).integrable_comp_of_integrable
    exact Integrable.of_bound (hh i).aestronglyMeasurable 1 (by simpa only [Real.norm_eq_abs] using hb i)

/-- The complete score variance is the sum of marginal score variances, with no
number-of-variables relaxation. -/
lemma completeScore_secondMoment (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂μ i = 0) :
    (∫ x, completeScore h x ^ 2 ∂Measure.pi μ) = information μ h := by
  have hmem (i : Fin n) : MemLp (h i) 2 (μ i) :=
    MemLp.of_bound (hh i).aestronglyMeasurable 1 (by simpa only [Real.norm_eq_abs] using hb i)
  have hv := variance_sum_pi (μ := μ) hmem
  have he : (∑ i : Fin n, fun x : Fin n → ℝ => h i (x i)) = completeScore h := by
    funext x
    simp only [Finset.sum_apply, completeScore]
  rw [he, variance_eq_integral (measurable_completeScore hh).aemeasurable, completeScore_mean μ h hh hb hm] at hv
  simp only [sub_zero] at hv
  rw [hv]
  apply Finset.sum_congr rfl
  intro i _
  rw [variance_eq_integral (hh i).aemeasurable, hm i]
  simp

/-- The centered marginal score at the tilted law. -/
noncomputable def tiltedScore (h : Ω → ℝ) (θ : ℝ) (x : Ω) : ℝ := h x / tiltFactor h θ x

lemma measurable_tiltedScore {h : Ω → ℝ} (hh : Measurable h) (θ : ℝ) : Measurable (tiltedScore h θ) :=
  hh.div (measurable_tiltFactor hh θ)

lemma tiltedScore_abs_le {a θ : ℝ} (hθ : |θ| ≤ 1 / 4) (ha : |a| ≤ 1) :
    |a / (1 + θ * a)| ≤ 4 / 3 := by
  have hf := (tiltFactor_bounds hθ ha).1
  have hp : 0 < 1 + θ * a := by linarith
  rw [abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).mpr
  linarith

lemma tiltedScore_centered {μ : Measure Ω} {h : Ω → ℝ} (hh : Measurable h)
    (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) (hm : ∫ x, h x ∂μ = 0) {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    (∫ x, tiltedScore h θ x ∂tiltLaw μ h θ) = 0 := by
  have h0 : ∀ᵐ x ∂μ, 0 ≤ tiltFactor h θ x :=
    hb.mono fun x hx => (by norm_num : (0 : ℝ) ≤ 3 / 4).trans (tiltFactor_bounds hθ hx).1
  rw [integral_tiltLaw hh h0]
  calc
    _ = ∫ x, h x ∂μ := by
      apply integral_congr_ae
      filter_upwards [hb] with x hx
      have hp : 0 < tiltFactor h θ x := by
        have hh := (tiltFactor_bounds hθ hx).1
        change 0 < 1 + θ * h x
        linarith
      unfold tiltedScore
      field_simp
    _ = 0 := hm

lemma tiltedScore_secondMoment_le {μ : Measure Ω} [IsProbabilityMeasure μ] {h : Ω → ℝ}
    (hh : Measurable h) (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    (∫ x, tiltedScore h θ x ^ 2 ∂tiltLaw μ h θ) ≤ (4 / 3) * ∫ x, h x ^ 2 ∂μ := by
  have h0 : ∀ᵐ x ∂μ, 0 ≤ tiltFactor h θ x :=
    hb.mono fun x hx => (by norm_num : (0 : ℝ) ≤ 3 / 4).trans (tiltFactor_bounds hθ hx).1
  have hi2 : Integrable (fun x => h x ^ 2) μ := integrable_pow_of_bound hh zero_le_one hb 2
  have hdom : ∀ᵐ x ∂μ, 0 ≤ tiltFactor h θ x * tiltedScore h θ x ^ 2 ∧
      tiltFactor h θ x * tiltedScore h θ x ^ 2 ≤ (4 / 3) * h x ^ 2 := by
    filter_upwards [hb] with x hx
    have hlow : (3 / 4 : ℝ) ≤ tiltFactor h θ x := (tiltFactor_bounds hθ hx).1
    have hp : 0 < tiltFactor h θ x := by linarith
    refine ⟨mul_nonneg hp.le (sq_nonneg _), ?_⟩
    have he : tiltFactor h θ x * tiltedScore h θ x ^ 2 = h x ^ 2 / tiltFactor h θ x := by
      unfold tiltedScore
      field_simp
    rw [he]
    apply (div_le_iff₀ hp).mpr
    have hmul := mul_nonneg (sq_nonneg (h x)) (sub_nonneg.mpr hlow)
    nlinarith
  have hiL : Integrable (fun x => tiltFactor h θ x * tiltedScore h θ x ^ 2) μ := by
    apply (hi2.const_mul (4 / 3)).mono' ((measurable_tiltFactor hh θ).mul (measurable_tiltedScore hh θ |>.pow_const 2)).aestronglyMeasurable
    exact hdom.mono fun x hx => by simpa only [Pi.mul_apply, Real.norm_eq_abs, abs_of_nonneg hx.1] using hx.2
  rw [integral_tiltLaw hh h0]
  exact (integral_mono_ae hiL (hi2.const_mul _) (hdom.mono fun _ hx => hx.2)).trans_eq (integral_const_mul _ _)

lemma integrable_tiltFactor {μ : Measure Ω} [IsProbabilityMeasure μ] {h : Ω → ℝ}
    (hh : Measurable h) (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) (θ : ℝ) : Integrable (tiltFactor h θ) μ := by
  have hi : Integrable h μ := Integrable.of_bound hh.aestronglyMeasurable 1 (by simpa only [Real.norm_eq_abs] using hb)
  exact (integrable_const 1).add (hi.const_mul θ)

lemma tiltFactor_ae_nonnegative {μ : Measure Ω} {h : Ω → ℝ}
    (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) {θ : ℝ} (hθ : |θ| ≤ 1 / 4) : ∀ᵐ x ∂μ, 0 ≤ tiltFactor h θ x :=
  hb.mono fun x hx => (by norm_num : (0 : ℝ) ≤ 3 / 4).trans (tiltFactor_bounds hθ hx).1

lemma tiltLaw_apply_eq_indicator {μ : Measure Ω} [IsProbabilityMeasure μ] {h : Ω → ℝ}
    (hh : Measurable h) (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) {θ : ℝ} (hθ : |θ| ≤ 1 / 4)
    (s : Set Ω) (hs : MeasurableSet s) :
    tiltLaw μ h θ s = ENNReal.ofReal (∫ x, s.indicator (tiltFactor h θ) x ∂μ) := by
  rw [tiltLaw, withDensity_apply _ hs]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_tiltFactor hh hb θ).integrableOn
    (ae_restrict_of_ae (tiltFactor_ae_nonnegative hb hθ)), ← integral_indicator hs]

lemma likelihood_integrable (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) (θ : ℝ) :
    Integrable (likelihood h θ) (Measure.pi μ) :=
  Integrable.fintype_prod (fun i => integrable_tiltFactor (hh i) (hb i) θ)

lemma likelihood_ae_nonnegative (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    ∀ᵐ x ∂Measure.pi μ, 0 ≤ likelihood h θ x := by
  have hb' : ∀ᵐ x ∂Measure.pi μ, ∀ i, |h i (x i)| ≤ 1 := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval μ i).quasiMeasurePreserving.ae (hb i)
  exact hb'.mono fun x hx => Finset.prod_nonneg fun i _ =>
    (by norm_num : (0 : ℝ) ≤ 3 / 4).trans (tiltFactor_bounds hθ (hx i)).1

noncomputable def productTiltLaw (μ : Fin n → Measure ℝ) (h : Fin n → ℝ → ℝ) (θ : ℝ) :
    Measure (Fin n → ℝ) := Measure.pi (fun i => tiltLaw (μ i) (h i) θ)

/-- The finite tilted product has exactly the product likelihood density. -/
lemma productTiltLaw_eq_withDensity (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂μ i = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    productTiltLaw μ h θ = (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (likelihood h θ x)) := by
  haveI : ∀ i, IsProbabilityMeasure (tiltLaw (μ i) (h i) θ) := fun i => tiltLaw_probability (hh i) (hb i) (hm i) hθ
  change Measure.pi (fun i => tiltLaw (μ i) (h i) θ) = _
  apply Measure.pi_eq
  intro s hs
  have hrect := MeasurableSet.univ_pi hs
  have he (x : Fin n → ℝ) : (univ.pi s).indicator (likelihood h θ) x =
      ∏ i, (s i).indicator (tiltFactor (h i) θ) (x i) := by
    by_cases hx : x ∈ univ.pi s
    · have hx' : ∀ i, x i ∈ s i := fun i => hx i (Set.mem_univ i)
      simp only [Set.indicator_of_mem hx, likelihood]
      apply Finset.prod_congr rfl
      intro i _
      rw [Set.indicator_of_mem (hx' i)]
    · have hx' : ∃ i, x i ∉ s i := by simpa only [Set.mem_pi, Set.mem_univ, forall_true_left, not_forall] using hx
      obtain ⟨i, hi⟩ := hx'
      rw [Set.indicator_of_notMem hx]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact Set.indicator_of_notMem hi _
  have h0i (i : Fin n) : 0 ≤ ∫ x, (s i).indicator (tiltFactor (h i) θ) x ∂μ i := by
    apply integral_nonneg_of_ae
    exact (tiltFactor_ae_nonnegative (hb i) hθ).mono fun x hx => by
      unfold Set.indicator
      split_ifs <;> simp_all
  rw [withDensity_apply _ hrect]
  rw [← ofReal_integral_eq_lintegral_ofReal (likelihood_integrable μ h hh hb θ).integrableOn
    (ae_restrict_of_ae (likelihood_ae_nonnegative μ h hb hθ))]
  rw [← integral_indicator hrect]
  simp_rw [he]
  rw [integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg (fun i _ => h0i i)]
  apply Finset.prod_congr rfl
  intro i _
  exact (tiltLaw_apply_eq_indicator (hh i) (hb i) hθ (s i) (hs i)).symm

lemma productTiltLaw_probability (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂μ i = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 4) : IsProbabilityMeasure (productTiltLaw μ h θ) := by
  haveI : ∀ i, IsProbabilityMeasure (tiltLaw (μ i) (h i) θ) := fun i => tiltLaw_probability (hh i) (hb i) (hm i) hθ
  dsimp [productTiltLaw]
  infer_instance

lemma completeScore_secondMoment_of_memLp (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i)) (hmem : ∀ i, MemLp (h i) 2 (μ i))
    (hm : ∀ i, ∫ x, h i x ∂μ i = 0) :
    (∫ x, completeScore h x ^ 2 ∂Measure.pi μ) = information μ h := by
  have hmean : (∫ x, completeScore h x ∂Measure.pi μ) = 0 := by
    unfold completeScore
    rw [integral_finsetSum]
    · apply Finset.sum_eq_zero
      intro i _
      rw [integral_coordinate_comp μ (h i) (hh i) i, hm i]
    · intro i _
      exact (measurePreserving_eval μ i).integrable_comp_of_integrable ((hmem i).integrable (by norm_num))
  have hv := variance_sum_pi (μ := μ) hmem
  have he : (∑ i : Fin n, fun x : Fin n → ℝ => h i (x i)) = completeScore h := by
    funext x
    simp only [Finset.sum_apply, completeScore]
  rw [he, variance_eq_integral (measurable_completeScore hh).aemeasurable, hmean] at hv
  simp only [sub_zero] at hv
  rw [hv]
  exact Finset.sum_congr rfl fun i _ => by rw [variance_eq_integral (hh i).aemeasurable, hm i]; simp

/-- The second logarithmic derivative contributes a sum of squared tilted scores. -/
noncomputable def secondLikelihoodCore (h : Fin n → ℝ → ℝ) (θ : ℝ) (x : Fin n → ℝ) : ℝ :=
  completeScore (fun i => tiltedScore (h i) θ) x ^ 2 - ∑ i, tiltedScore (h i) θ (x i) ^ 2

lemma tiltedScore_memLp_two {μ : Measure Ω} [IsProbabilityMeasure μ] {h : Ω → ℝ}
    (hh : Measurable h) (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) (hm : ∫ x, h x ∂μ = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 4) : MemLp (tiltedScore h θ) 2 (tiltLaw μ h θ) := by
  haveI := tiltLaw_probability hh hb hm hθ
  apply MemLp.of_bound (measurable_tiltedScore hh θ).aestronglyMeasurable (4 / 3)
  apply (tiltLaw_absolutelyContinuous μ h θ).ae_le
  exact hb.mono fun x hx => by simpa only [Real.norm_eq_abs, tiltedScore, tiltFactor] using tiltedScore_abs_le hθ hx

/-- The L¹ second-likelihood core is bounded by `4I`, uniformly in the instance size. -/
lemma secondLikelihoodCore_integrable_and_bound (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂μ i = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    Integrable (secondLikelihoodCore h θ) (productTiltLaw μ h θ) ∧
      (∫ x, |secondLikelihoodCore h θ x| ∂productTiltLaw μ h θ) ≤ 4 * information μ h := by
  let ν : Fin n → Measure ℝ := fun i => tiltLaw (μ i) (h i) θ
  let s : Fin n → ℝ → ℝ := fun i => tiltedScore (h i) θ
  haveI : ∀ i, IsProbabilityMeasure (ν i) := fun i => tiltLaw_probability (hh i) (hb i) (hm i) hθ
  have hsM (i : Fin n) : Measurable (s i) := measurable_tiltedScore (hh i) θ
  have hsLp (i : Fin n) : MemLp (s i) 2 (ν i) := tiltedScore_memLp_two (hh i) (hb i) (hm i) hθ
  have hs0 (i : Fin n) : (∫ x, s i x ∂ν i) = 0 := tiltedScore_centered (hh i) (hb i) (hm i) hθ
  have hsBd (i : Fin n) : ∀ᵐ x ∂ν i, |s i x| ≤ 4 / 3 := by
    apply (tiltLaw_absolutelyContinuous (μ i) (h i) θ).ae_le
    exact (hb i).mono fun x hx => tiltedScore_abs_le hθ hx
  have hall : ∀ᵐ x ∂Measure.pi ν, ∀ i, |s i (x i)| ≤ 4 / 3 := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval ν i).quasiMeasurePreserving.ae (hsBd i)
  have hScoreBd : ∀ᵐ x ∂Measure.pi ν, |completeScore s x| ≤ (4 / 3) * (n : ℝ) := by
    filter_upwards [hall] with x hx
    calc
      |completeScore s x| ≤ ∑ i, |s i (x i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, (4 / 3 : ℝ) := Finset.sum_le_sum fun i _ => hx i
      _ = (4 / 3) * (n : ℝ) := by simp [nsmul_eq_mul, mul_comm]
  have hiScoreSq : Integrable (fun x : Fin n → ℝ => completeScore s x ^ 2) (Measure.pi ν) :=
    integrable_pow_of_bound (measurable_completeScore hsM) (by positivity) hScoreBd 2
  have hiSq (i : Fin n) : Integrable (fun x : Fin n → ℝ => s i (x i) ^ 2) (Measure.pi ν) :=
    ((hsLp i).comp_measurePreserving (measurePreserving_eval ν i)).integrable_sq
  have hiSumSq : Integrable (fun x : Fin n → ℝ => ∑ i, s i (x i) ^ 2) (Measure.pi ν) :=
    integrable_finsetSum _ (fun i _ => hiSq i)
  have hiCore : Integrable (fun x : Fin n → ℝ => |completeScore s x ^ 2 - ∑ i, s i (x i) ^ 2|) (Measure.pi ν) :=
    (hiScoreSq.sub hiSumSq).abs
  constructor
  · exact hiScoreSq.sub hiSumSq
  ·
    have hiAdd : Integrable (fun x : Fin n → ℝ => completeScore s x ^ 2 + ∑ i, s i (x i) ^ 2) (Measure.pi ν) :=
      hiScoreSq.add hiSumSq
    have hfirst := integral_mono hiCore hiAdd (fun x => by
      have hsq : 0 ≤ completeScore s x ^ 2 := sq_nonneg _
      have hsum : 0 ≤ ∑ i, s i (x i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      exact abs_le.mpr ⟨by linarith, by linarith⟩)
    change (∫ x : Fin n → ℝ, |completeScore s x ^ 2 - ∑ i, s i (x i) ^ 2| ∂Measure.pi ν) ≤ _
    rw [integral_add hiScoreSq hiSumSq,
      completeScore_secondMoment_of_memLp ν s hsM hsLp hs0,
      integral_finsetSum _ (fun i _ => hiSq i)] at hfirst
    simp_rw [integral_coordinate_comp ν _ ((hsM _).pow_const 2) _] at hfirst
    have hinfo : information ν s ≤ (4 / 3) * information μ h := by
      unfold information
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => tiltedScore_secondMoment_le (hh i) (hb i) hθ
    change (∫ x : Fin n → ℝ, |completeScore s x ^ 2 - ∑ i, s i (x i) ^ 2| ∂Measure.pi ν) ≤ information ν s + information ν s at hfirst
    nlinarith [information_nonnegative μ h]
  
lemma integral_abs_secondLikelihoodCore_le (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂μ i = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    (∫ x, |secondLikelihoodCore h θ x| ∂productTiltLaw μ h θ) ≤ 4 * information μ h :=
  (secondLikelihoodCore_integrable_and_bound μ h hh hb hm hθ).2

noncomputable def likelihoodFirst (h : Fin n → ℝ → ℝ) (θ : ℝ) (x : Fin n → ℝ) : ℝ :=
  likelihood h θ x * completeScore (fun i => tiltedScore (h i) θ) x

noncomputable def likelihoodSecond (h : Fin n → ℝ → ℝ) (θ : ℝ) (x : Fin n → ℝ) : ℝ :=
  likelihood h θ x * secondLikelihoodCore h θ x

lemma hasDerivAt_tiltFactor (h : ℝ → ℝ) (x θ : ℝ) :
    HasDerivAt (fun t => tiltFactor h t x) (h x) θ := by
  simpa only [tiltFactor, one_mul, id_eq] using ((hasDerivAt_id θ).mul_const (h x)).const_add 1

lemma hasDerivAt_likelihood (h : Fin n → ℝ → ℝ) (x : Fin n → ℝ) (θ : ℝ)
    (hne : ∀ i, tiltFactor (h i) θ (x i) ≠ 0) :
    HasDerivAt (fun t => likelihood h t x) (likelihoodFirst h θ x) θ := by
  have hp := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Fin n)))
    (fun i _ => hasDerivAt_tiltFactor (h i) (x i) θ)
  convert! hp using 1
  simp only [likelihoodFirst, completeScore, tiltedScore, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he := Finset.prod_erase_mul Finset.univ (fun j => tiltFactor (h j) θ (x j)) (Finset.mem_univ i)
  change (∏ j, tiltFactor (h j) θ (x j)) * (h i (x i) / tiltFactor (h i) θ (x i)) = _
  rw [← he]
  field_simp [hne i]

lemma hasDerivAt_tiltedScore (h : ℝ → ℝ) (x θ : ℝ) (hne : tiltFactor h θ x ≠ 0) :
    HasDerivAt (fun t => tiltedScore h t x) (-tiltedScore h θ x ^ 2) θ := by
  have hd := (hasDerivAt_const θ (h x)).div (hasDerivAt_tiltFactor h x θ) hne
  convert! hd using 1
  unfold tiltedScore
  field_simp
  ring

/-- The first derivative itself has derivative `L[(Σs)²−Σs²]`. -/
lemma hasDerivAt_likelihoodFirst (h : Fin n → ℝ → ℝ) (x : Fin n → ℝ) (θ : ℝ)
    (hne : ∀ i, tiltFactor (h i) θ (x i) ≠ 0) :
    HasDerivAt (fun t => likelihoodFirst h t x) (likelihoodSecond h θ x) θ := by
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin n)))
    (fun i _ => hasDerivAt_tiltedScore (h i) (x i) θ (hne i))
  have hd := (hasDerivAt_likelihood h x θ hne).mul hsum
  convert! hd using 1
  simp only [likelihoodSecond, secondLikelihoodCore, likelihoodFirst, completeScore, Finset.sum_neg_distrib]
  ring

@[simp] lemma likelihood_zero (h : Fin n → ℝ → ℝ) (x : Fin n → ℝ) : likelihood h 0 x = 1 := by
  simp [likelihood, tiltFactor]

@[simp] lemma likelihoodFirst_zero (h : Fin n → ℝ → ℝ) (x : Fin n → ℝ) :
    likelihoodFirst h 0 x = completeScore h x := by
  simp [likelihoodFirst, completeScore, tiltedScore, tiltFactor]

/-- Integrability and the uniform L¹ norm of the actual second likelihood derivative. -/
lemma likelihoodSecond_integrable_and_bound (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂μ i = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    Integrable (likelihoodSecond h θ) (Measure.pi μ) ∧
      (∫ x, |likelihoodSecond h θ x| ∂Measure.pi μ) ≤ 4 * information μ h := by
  have hcore := secondLikelihoodCore_integrable_and_bound μ h hh hb hm hθ
  have hprob := productTiltLaw_eq_withDensity μ h hh hb hm hθ
  have hdmeas : Measurable (fun x : Fin n → ℝ => ENNReal.ofReal (likelihood h θ x)) :=
    (measurable_likelihood hh θ).ennreal_ofReal
  have hfinite : ∀ᵐ x : Fin n → ℝ ∂Measure.pi μ, ENNReal.ofReal (likelihood h θ x) < ∞ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  have hL0 := likelihood_ae_nonnegative μ h hb hθ
  have hiCore := hcore.1
  rw [hprob] at hiCore
  have hi := (integrable_withDensity_iff_integrable_smul' hdmeas hfinite).mp hiCore
  have he : (fun x : Fin n → ℝ => (ENNReal.ofReal (likelihood h θ x)).toReal • secondLikelihoodCore h θ x) =ᵐ[Measure.pi μ]
      likelihoodSecond h θ := by
    filter_upwards [hL0] with x hx
    rw [ENNReal.toReal_ofReal hx, smul_eq_mul]
    rfl
  refine ⟨hi.congr he, ?_⟩
  have hchange := integral_withDensity_eq_integral_toReal_smul hdmeas hfinite (fun x => |secondLikelihoodCore h θ x|)
  rw [← hprob] at hchange
  calc
    _ = ∫ x : Fin n → ℝ, (ENNReal.ofReal (likelihood h θ x)).toReal • |secondLikelihoodCore h θ x| ∂Measure.pi μ := by
      apply integral_congr_ae
      filter_upwards [hL0] with x hx
      rw [likelihoodSecond, abs_mul, abs_of_nonneg hx, ENNReal.toReal_ofReal hx, smul_eq_mul]
    _ = ∫ x, |secondLikelihoodCore h θ x| ∂productTiltLaw μ h θ := hchange.symm
    _ ≤ 4 * information μ h := hcore.2

lemma integral_productTiltLaw (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂μ i, |h i x| ≤ 1) (hm : ∀ i, ∫ x, h i x ∂μ i = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 4) (F : (Fin n → ℝ) → ℝ) :
    (∫ x, F x ∂productTiltLaw μ h θ) = ∫ x, likelihood h θ x * F x ∂Measure.pi μ := by
  rw [productTiltLaw_eq_withDensity μ h hh hb hm hθ,
    integral_withDensity_eq_integral_toReal_smul (measurable_likelihood hh θ |>.ennreal_ofReal)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [likelihood_ae_nonnegative μ h hb hθ] with x hx
  rw [ENNReal.toReal_ofReal hx, smul_eq_mul]

end ProphetSecretary.Probability


namespace ProphetSecretary.Model.Instance

open ProphetSecretary.Probability

variable {n : ℕ}

/-- A product likelihood tilt of the original nonnegative offer marginals. -/
noncomputable def likelihoodTilt (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1)
    (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) (θ : ℝ) (hθ : |θ| ≤ 1 / 4) : Instance n where
  law i := tiltLaw (P.law i) (h i) θ
  probability i := tiltLaw_probability (hh i) (hb i) (hm i) hθ
  nonnegative i := (tiltLaw_absolutelyContinuous (P.law i) (h i) θ).ae_le (P.nonnegative i)

lemma likelihoodTilt_valuesLaw (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1)
    (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) (θ : ℝ) (hθ : |θ| ≤ 1 / 4) :
    (P.likelihoodTilt h hh hb hm θ hθ).valuesLaw =
      P.valuesLaw.withDensity (fun x => ENNReal.ofReal (likelihood h θ x)) :=
  productTiltLaw_eq_withDensity P.law h hh hb hm hθ

end ProphetSecretary.Model.Instance
