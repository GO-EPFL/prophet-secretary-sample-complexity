import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Strict covariance of the value and an antitone response

On a bounded offer law, an antitone response in [0,1] has nonpositive
covariance with the value. Equality forces the response to be almost surely
constant. The proof uses the actual two-copy product integral and Fubini, so
atoms and arbitrary infinite supports are both included.
-/
open MeasureTheory Set Filter
namespace ProphetSecretary.Probability

noncomputable def valueCovariance (μ : Measure ℝ) (g : ℝ → ℝ) : ℝ :=
  ∫ x, (x - ∫ y, y ∂μ) * g x ∂μ

def covarianceKernel (g : ℝ → ℝ) (z : ℝ × ℝ) : ℝ := (z.1-z.2) * (g z.1-g z.2)

lemma covarianceKernel_nonpositive {g : ℝ → ℝ} (hg : Antitone g) (z : ℝ × ℝ) :
    covarianceKernel g z ≤ 0 := by
  rcases le_total z.1 z.2 with h | h
  · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (sub_nonneg.mpr (hg h))
  · exact mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h) (sub_nonpos.mpr (hg h))

lemma covarianceKernel_eq_zero_implies (g : ℝ → ℝ) {x y : ℝ}
    (hz : covarianceKernel g (x,y) = 0) : g x = g y := by
  rcases mul_eq_zero.mp hz with h | h
  · exact congrArg g (sub_eq_zero.mp h)
  · exact sub_eq_zero.mp h

section BoundedLaw
variable (μ : Measure ℝ) [IsProbabilityMeasure μ] {H : ℝ}
    (hX : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) H)
    (g : ℝ → ℝ) (hgm : Measurable g) (hgB : ∀ᵐ x ∂μ, g x ∈ Icc (0 : ℝ) 1)

include hX in
lemma integrable_value_of_support : Integrable (fun x : ℝ => x) μ := by
  apply Integrable.of_bound measurable_id.aestronglyMeasurable H
  filter_upwards [hX] with x hx
  change ‖x‖ ≤ H
  simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2

include hgm hgB in
lemma integrable_response_of_bound : Integrable g μ := by
  apply Integrable.of_bound hgm.aestronglyMeasurable 1
  filter_upwards [hgB] with x hx
  change ‖g x‖ ≤ 1
  simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2

include hX hgm hgB

lemma integrable_value_response : Integrable (fun x => x * g x) μ := by
  apply Integrable.of_bound (measurable_id.mul hgm).aestronglyMeasurable H
  filter_upwards [hX,hgB] with x hx hg
  change ‖x * g x‖ ≤ H
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hx.1,abs_of_nonneg hg.1]
  exact mul_le_of_le_one_right hx.1 hg.2 |>.trans hx.2

lemma integrable_cross_response : Integrable (fun z : ℝ × ℝ => z.1 * g z.2) (μ.prod μ) := by
  apply Integrable.of_bound (measurable_fst.mul (hgm.comp measurable_snd)).aestronglyMeasurable H
  filter_upwards [(measurePreserving_fst (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hX,
    (measurePreserving_snd (μ := μ) (ν := μ)).quasiMeasurePreserving.ae hgB] with z hx hg
  change ‖z.1 * g z.2‖ ≤ H
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hx.1,abs_of_nonneg hg.1]
  exact mul_le_of_le_one_right hx.1 hg.2 |>.trans hx.2

lemma valueCovariance_eq_sub : valueCovariance μ g =
    (∫ x, x * g x ∂μ) - (∫ x, x ∂μ) * (∫ x, g x ∂μ) := by
  have hG := integrable_response_of_bound μ g hgm hgB
  have hXG := integrable_value_response μ hX g hgm hgB
  unfold valueCovariance
  have heq : (fun x : ℝ => (x - ∫ y, y ∂μ) * g x) =
      fun x => x * g x - (∫ y, y ∂μ) * g x := by funext x; ring
  rw [heq,integral_sub hXG (hG.const_mul _),integral_const_mul]

lemma integrable_covarianceKernel : Integrable (covarianceKernel g) (μ.prod μ) := by
  have hXG := integrable_value_response μ hX g hgm hgB
  have hCross := integrable_cross_response μ hX g hgm hgB
  have hSwap : Integrable (fun z : ℝ × ℝ => g z.1 * z.2) (μ.prod μ) := by
    have hs := Measure.measurePreserving_swap (μ := μ) (ν := μ)
    have h := hs.integrable_comp_of_integrable hCross
    change Integrable (fun z : ℝ × ℝ => z.2 * g z.1) (μ.prod μ) at h
    convert h using 1
    funext z
    ring
  have hi := ((hXG.comp_fst μ).add (hXG.comp_snd μ)).sub (hCross.add hSwap)
  have heq : covarianceKernel g = (fun z : ℝ × ℝ =>
      (z.1 * g z.1 + z.2 * g z.2) - (z.1 * g z.2 + g z.1 * z.2)) := by
    funext z
    unfold covarianceKernel
    ring
  rw [heq]
  exact hi

/-- The double-product covariance identity for the actual offer law. -/
lemma integral_covarianceKernel : (∫ z, covarianceKernel g z ∂μ.prod μ) = 2 * valueCovariance μ g := by
  have hXG := integrable_value_response μ hX g hgm hgB
  have hCross := integrable_cross_response μ hX g hgm hgB
  have hSwap : Integrable (fun z : ℝ × ℝ => g z.1 * z.2) (μ.prod μ) := by
    have hs := Measure.measurePreserving_swap (μ := μ) (ν := μ)
    have h := hs.integrable_comp_of_integrable hCross
    change Integrable (fun z : ℝ × ℝ => z.2 * g z.1) (μ.prod μ) at h
    convert h using 1
    funext z
    ring
  have heq : covarianceKernel g = (fun z : ℝ × ℝ =>
      (z.1 * g z.1 + z.2 * g z.2) - (z.1 * g z.2 + g z.1 * z.2)) := by
    funext z
    unfold covarianceKernel
    ring
  rw [heq]
  change (∫ z : ℝ × ℝ, (z.1 * g z.1 + z.2 * g z.2) - (z.1 * g z.2 + g z.1 * z.2) ∂μ.prod μ) = _
  rw [integral_sub (f := fun z : ℝ × ℝ => z.1 * g z.1 + z.2 * g z.2)
      (g := fun z => z.1 * g z.2 + g z.1 * z.2)
      ((hXG.comp_fst μ).add (hXG.comp_snd μ)) (hCross.add hSwap),
    integral_add (f := fun z : ℝ × ℝ => z.1 * g z.1) (g := fun z => z.2 * g z.2)
      (hXG.comp_fst μ) (hXG.comp_snd μ),
    integral_add (f := fun z : ℝ × ℝ => z.1 * g z.2) (g := fun z => g z.1 * z.2) hCross hSwap,
    integral_fun_fst (fun x : ℝ => x * g x),integral_fun_snd (fun x : ℝ => x * g x),
    integral_prod_mul (fun x : ℝ => x) g,integral_prod_mul g (fun x : ℝ => x),
    valueCovariance_eq_sub μ hX g hgm hgB]
  simp only [probReal_univ,one_smul]
  ring

/-- Nonpositivity is restricted to the explicitly antitone response class. -/
theorem valueCovariance_nonpositive (hga : Antitone g) : valueCovariance μ g ≤ 0 := by
  have h := integral_nonpos (μ := μ.prod μ) (fun z => covarianceKernel_nonpositive hga z)
  rw [integral_covarianceKernel μ hX g hgm hgB] at h
  linarith only [h]

/-- Equality forces the response to be constant under the actual marginal law. -/
theorem valueCovariance_eq_zero_iff_ae_constant (hga : Antitone g) :
    valueCovariance μ g = 0 ↔ ∃ c : ℝ, g =ᵐ[μ] fun _ => c := by
  constructor
  · intro hz
    have hI := (integrable_covarianceKernel μ hX g hgm hgB).neg
    have hnonneg : 0 ≤ (fun z => -covarianceKernel g z) := fun z => neg_nonneg.mpr (covarianceKernel_nonpositive hga z)
    have hzero : (∫ z, -covarianceKernel g z ∂μ.prod μ) = 0 := by
      rw [integral_neg,integral_covarianceKernel μ hX g hgm hgB,hz]
      ring
    have hae := (integral_eq_zero_iff_of_nonneg hnonneg hI).mp hzero
    have hpair : ∀ᵐ z ∂μ.prod μ, g z.1 = g z.2 := by
      filter_upwards [hae] with z hz
      apply covarianceKernel_eq_zero_implies g
      change -covarianceKernel g z = 0 at hz
      linarith only [hz]
    obtain ⟨x,hx⟩ := (Measure.ae_ae_of_ae_prod hpair).exists
    exact ⟨g x,hx.mono (fun y hy => hy.symm)⟩
  · rintro ⟨c,hc⟩
    have hXint := integrable_value_of_support μ hX
    unfold valueCovariance
    have heq : (fun x : ℝ => (x - ∫ y, y ∂μ) * g x) =ᵐ[μ]
        fun x => c * (x - ∫ y, y ∂μ) := hc.mono fun x hx => by dsimp only at hx ⊢; rw [hx]; ring
    rw [integral_congr_ae heq,integral_const_mul,
      integral_sub hXint (integrable_const _),integral_const,probReal_univ,one_smul]
    ring

/-- The strict version needed for a nonconstant individual duration response. -/
theorem valueCovariance_negative_of_not_ae_constant (hga : Antitone g)
    (hn : ¬∃ c : ℝ, g =ᵐ[μ] fun _ => c) : valueCovariance μ g < 0 := by
  apply lt_of_le_of_ne (valueCovariance_nonpositive μ hX g hgm hgB hga)
  intro heq
  exact hn ((valueCovariance_eq_zero_iff_ae_constant μ hX g hgm hgB hga).mp heq)

/-- Division by the positive offer cap preserves the strict sign for the
normalized centered-value score used by the individual-variable direction. -/
theorem normalized_valueCovariance_negative_of_not_ae_constant (hH : 0 < H)
    (hga : Antitone g) (hn : ¬∃ c : ℝ, g =ᵐ[μ] fun _ => c) :
    (∫ x, ((x - ∫ y, y ∂μ) / H) * g x ∂μ) < 0 := by
  have heq : (fun x : ℝ => ((x - ∫ y, y ∂μ) / H) * g x) =
      fun x => ((x - ∫ y, y ∂μ) * g x) / H := by funext x; ring
  rw [heq,integral_div]
  exact div_neg_of_neg_of_pos (valueCovariance_negative_of_not_ae_constant μ hX g hgm hgB hga hn) hH

end BoundedLaw
end ProphetSecretary.Probability
