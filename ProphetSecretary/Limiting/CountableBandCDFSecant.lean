import ProphetSecretary.Limiting.CountableBandIntensityMeasure
import ProphetSecretary.Limiting.CountableMaximumDistribution
import ProphetSecretary.Analysis.ExponentialDeletionSecant

/-!
# A pointwise maximum-CDF secant for deleting a finite positive band

The exact independent-product/Poisson void formula factors the band tail.
A single exponential bound, uniform in the threshold level, controls full
deletion by a small positive intensity increment.
-/

open MeasureTheory Set
open scoped Classical NNReal ENNReal BigOperators

namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def maximumCdf (B : CountableInstance) (t : ℝ) : ℝ := B.valueLaw.real {v | B.maximum v≤t}

lemma maximumCdf_scaleBand (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    (r : ℝ≥0) {t : ℝ} (ht : (B.terminal : ℝ)<t) :
    (B.scaleBand S r).maximumCdf t=
      Real.exp (-(B.intensity.real (Ioi t∩Sᶜ)+(r : ℝ)*B.intensity.real (Ioi t∩S)))*
        (∏' i, (B.individuals i : Measure ℝ) (Iic t)).toReal := by
  unfold maximumCdf
  change ((B.scaleBand S r).valueLaw {v | (B.scaleBand S r).maximum v≤t}).toReal=_
  rw [(B.scaleBand S r).maximum_probability_Iic ht,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,B.scaleBand_intensity_tail_real hS r ht]
  rfl

lemma maximumCdf_band_deletion_secant (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b)
    {h : ℝ} (hh : 0<h) (hh1 : h≤1) {r : ℝ≥0} (hr : (r : ℝ)=1+h)
    {t : ℝ} (ht : (B.terminal : ℝ)<t) :
    h*((B.scaleBand S 0).maximumCdf t-B.maximumCdf t)≤
      Real.exp (2*B.intensity.real S)*(B.maximumCdf t-(B.scaleBand S r).maximumCdf t) := by
  let a := B.intensity.real (Ioi t∩Sᶜ)
  let z := B.intensity.real (Ioi t∩S)
  let I := (∏' i, (B.individuals i : Measure ℝ) (Iic t)).toReal
  have h0 := B.maximumCdf_scaleBand hS 0 ht
  have h1 := B.maximumCdf_scaleBand hS 1 ht
  rw [B.scaleBand_one] at h1
  have hrCdf := B.maximumCdf_scaleBand hS r ht
  rw [hr] at hrCdf
  simp only [NNReal.coe_zero,NNReal.coe_one,zero_mul,add_zero,one_mul] at h0 h1
  have hNumeric := ProphetSecretary.Analysis.exponential_deletion_secant
    (show 0≤z from ENNReal.toReal_nonneg) (B.band_tail_real_le hb hSub t) hh hh1
  have hScaled := mul_le_mul_of_nonneg_left hNumeric
    (mul_nonneg (Real.exp_pos (-a)).le (show 0≤I from ENNReal.toReal_nonneg))
  rw [h0,h1,hrCdf]
  change h*(Real.exp (-a)*I-Real.exp (-(a+z))*I)≤
    Real.exp (2*B.intensity.real S)*(Real.exp (-(a+z))*I-Real.exp (-(a+(1+h)*z))*I)
  have hExpOne : Real.exp (-(a+z))=Real.exp (-a)*Real.exp (-z) := by rw [neg_add,Real.exp_add]
  have hExpR : Real.exp (-(a+(1+h)*z))=Real.exp (-a)*Real.exp (-(1+h)*z) := by
    rw [neg_add,Real.exp_add]
    congr 1
    ring
  rw [hExpOne,hExpR]
  nlinarith only [hScaled]

end ProphetSecretary.Limiting.CountableInstance
