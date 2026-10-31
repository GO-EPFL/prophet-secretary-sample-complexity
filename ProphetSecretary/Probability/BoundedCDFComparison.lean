import ProphetSecretary.Probability.BoundedCDFMean

/-!
# Explicit bounded-mean errors from ordered distribution functions

The probability spaces may differ. A uniform CDF error δ on [0,H] yields
an expected-maximum error at most Hδ through strict bounded layer cake.
-/

open MeasureTheory Set
open scoped NNReal

namespace ProphetSecretary.Probability

lemma bounded_integral_sub_le_of_cdf {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) (ν : Measure Ξ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ξ → ℝ) (hX : Measurable X) (hY : Measurable Y) (H : ℝ≥0) (δ : ℝ)
    (hXR : ∀ᵐ x ∂μ, X x ∈ Icc (0 : ℝ) H) (hYR : ∀ᵐ y ∂ν, Y y ∈ Icc (0 : ℝ) H)
    (hCDF : ∀ t ∈ Ioc (0 : ℝ) H,
      0 ≤ ν.real {y | Y y ≤ t}-μ.real {x | X x ≤ t} ∧
      ν.real {y | Y y ≤ t}-μ.real {x | X x ≤ t} ≤ δ) :
    0 ≤ (∫ x, X x ∂μ)-(∫ y, Y y ∂ν) ∧
      (∫ x, X x ∂μ)-(∫ y, Y y ∂ν) ≤ (H : ℝ)*δ := by
  let T := volume.restrict (Ioc (0 : ℝ) H)
  let F : ℝ → ℝ := fun t => μ.real {x | t < X x}
  let G : ℝ → ℝ := fun t => ν.real {y | t < Y y}
  have hFa : Antitone F := fun a b hab => measureReal_mono (fun _ hx => hab.trans_lt hx)
  have hGa : Antitone G := fun a b hab => measureReal_mono (fun _ hx => hab.trans_lt hx)
  have hFI : Integrable F T := by
    apply Integrable.of_bound hFa.measurable.aestronglyMeasurable 1
    filter_upwards [] with t
    rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hGI : Integrable G T := by
    apply Integrable.of_bound hGa.measurable.aestronglyMeasurable 1
    filter_upwards [] with t
    rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
    exact measureReal_le_one
  have hp : ∀ᵐ t ∂T, G t ≤ F t ∧ F t ≤ G t+δ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have h := hCDF t ht
    change ν.real {y | t < Y y} ≤ μ.real {x | t < X x} ∧
      μ.real {x | t < X x} ≤ ν.real {y | t < Y y}+δ
    rw [probReal_gt_eq_one_sub_le μ hX t,probReal_gt_eq_one_sub_le ν hY t]
    constructor <;> linarith only [h.1,h.2]
  have hLower := integral_mono_ae hGI hFI (hp.mono (fun _ ht => ht.1))
  have hUpper := integral_mono_ae hFI (hGI.add (integrable_const δ)) (hp.mono (fun _ ht => ht.2))
  change (∫ t, F t ∂T) ≤ ∫ t, G t+δ ∂T at hUpper
  rw [integral_add hGI (integrable_const δ),integral_const] at hUpper
  have hT : T.real univ = (H : ℝ) := by
    simp [T,Measure.real,Real.volume_Ioc]
  change (∫ t, F t ∂T) ≤ (∫ t, G t ∂T)+T.real univ*δ at hUpper
  rw [hT] at hUpper
  rw [integral_eq_bounded_strict_layercake μ hX H hXR,
    integral_eq_bounded_strict_layercake ν hY H hYR]
  change 0 ≤ (∫ t, F t ∂T)-(∫ t, G t ∂T) ∧
    (∫ t, F t ∂T)-(∫ t, G t ∂T) ≤ (H : ℝ)*δ
  constructor <;> linarith only [hLower,hUpper]

end ProphetSecretary.Probability
