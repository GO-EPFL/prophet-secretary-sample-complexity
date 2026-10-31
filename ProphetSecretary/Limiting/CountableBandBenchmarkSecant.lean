import ProphetSecretary.Limiting.CountableBandCDFSecant
import ProphetSecretary.Probability.BoundedCDFMean

/-!
# Integrating the Poisson-band deletion secant

Bounded layer cake turns the exact CDF inequality into a benchmark bound.
The coefficient depends only on the finite affected intensity, uniformly in
all individual laws and their number.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal Topology

namespace ProphetSecretary.Limiting.CountableInstance

lemma maximumCdf_mem_unit (B : CountableInstance) (t : ℝ) : B.maximumCdf t∈Icc (0 : ℝ) 1 :=
  ⟨measureReal_nonneg,measureReal_le_one⟩

lemma measurable_maximumCdf (B : CountableInstance) : Measurable B.maximumCdf := by
  apply Monotone.measurable
  intro s t hst
  exact measureReal_mono (fun _ hv => hv.trans hst)

lemma integrable_one_sub_maximumCdf (B : CountableInstance) (H : ℝ≥0) :
    Integrable (fun t => 1-B.maximumCdf t) (volume.restrict (Ioc (0 : ℝ) H)) := by
  apply Integrable.of_bound (measurable_const.sub B.measurable_maximumCdf).aestronglyMeasurable.restrict 1
  exact Eventually.of_forall (fun t => by
    change ‖1-B.maximumCdf t‖≤1
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (B.maximumCdf_mem_unit t).2)]
    linarith only [(B.maximumCdf_mem_unit t).1])

lemma expectedMaximum_eq_integral_one_sub_maximumCdf (B : CountableInstance) :
    B.expectedMaximum=∫ t in Ioc (0 : ℝ) B.cap, 1-B.maximumCdf t := by
  have hRange : ∀ᵐ v ∂B.valueLaw, B.maximum v∈Icc (0 : ℝ) B.cap :=
    B.maximum_bounded.mono (fun _ hv => ⟨B.terminal.property.trans hv.1,hv.2⟩)
  have h := ProphetSecretary.Probability.integral_eq_bounded_strict_layercake B.valueLaw B.measurable_maximum B.cap hRange
  change B.expectedMaximum=_ at h
  rw [h]
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => ProphetSecretary.Probability.probReal_gt_eq_one_sub_le B.valueLaw B.measurable_maximum t)

lemma maximumCdf_scaleBand_order (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    {r s : ℝ≥0} (hrs : r≤s) {t : ℝ} (ht : (B.terminal : ℝ)<t) :
    (B.scaleBand S s).maximumCdf t≤(B.scaleBand S r).maximumCdf t := by
  rw [B.maximumCdf_scaleBand hS s ht,B.maximumCdf_scaleBand hS r ht]
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  apply Real.exp_le_exp.mpr
  have hReal : (r : ℝ)≤(s : ℝ) := hrs
  have hMass : 0≤B.intensity.real (Ioi t∩S) := ENNReal.toReal_nonneg
  nlinarith only [hReal,hMass]

lemma expectedMaximum_scaleBand_order (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {r s : ℝ≥0} (hrs : r≤s) :
    (B.scaleBand S r).expectedMaximum≤(B.scaleBand S s).expectedMaximum := by
  rw [(B.scaleBand S r).expectedMaximum_eq_integral_one_sub_maximumCdf,
    (B.scaleBand S s).expectedMaximum_eq_integral_one_sub_maximumCdf]
  apply integral_mono_ae ((B.scaleBand S r).integrable_one_sub_maximumCdf B.cap)
    ((B.scaleBand S s).integrable_one_sub_maximumCdf B.cap)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hAbove : (B.terminal : ℝ)<t := by rw [hZero]; exact ht.1
  linarith only [B.maximumCdf_scaleBand_order hS hrs hAbove]

theorem expectedMaximum_band_deletion_secant (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b)
    {h : ℝ} (hh : 0<h) (hh1 : h≤1) {r : ℝ≥0} (hr : (r : ℝ)=1+h) :
    h*(B.expectedMaximum-(B.scaleBand S 0).expectedMaximum)≤
      Real.exp (2*B.intensity.real S)*((B.scaleBand S r).expectedMaximum-B.expectedMaximum) := by
  let Q := B.scaleBand S 0
  let R := B.scaleBand S r
  let T := volume.restrict (Ioc (0 : ℝ) B.cap)
  have hIB : Integrable (fun t => 1-B.maximumCdf t) T := B.integrable_one_sub_maximumCdf B.cap
  have hIQ : Integrable (fun t => 1-Q.maximumCdf t) T := Q.integrable_one_sub_maximumCdf B.cap
  have hIR : Integrable (fun t => 1-R.maximumCdf t) T := R.integrable_one_sub_maximumCdf B.cap
  have hLeft : Integrable (fun t => h*((1-B.maximumCdf t)-(1-Q.maximumCdf t))) T := (hIB.sub hIQ).const_mul h
  have hRight : Integrable (fun t => Real.exp (2*B.intensity.real S)*((1-R.maximumCdf t)-(1-B.maximumCdf t))) T :=
    (hIR.sub hIB).const_mul _
  have hPoint : ∀ᵐ t ∂T, h*((1-B.maximumCdf t)-(1-Q.maximumCdf t))≤
      Real.exp (2*B.intensity.real S)*((1-R.maximumCdf t)-(1-B.maximumCdf t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have hAbove : (B.terminal : ℝ)<t := by rw [hZero]; exact ht.1
    have hCdf := B.maximumCdf_band_deletion_secant hS hb hSub hh hh1 hr hAbove
    change h*(Q.maximumCdf t-B.maximumCdf t)≤Real.exp (2*B.intensity.real S)*(B.maximumCdf t-R.maximumCdf t) at hCdf
    nlinarith only [hCdf]
  have hI := integral_mono_ae hLeft hRight hPoint
  rw [integral_const_mul,integral_sub hIB hIQ,integral_const_mul,integral_sub hIR hIB] at hI
  have hMB : B.expectedMaximum=∫ t, 1-B.maximumCdf t ∂T := B.expectedMaximum_eq_integral_one_sub_maximumCdf
  have hMQ : Q.expectedMaximum=∫ t, 1-Q.maximumCdf t ∂T := Q.expectedMaximum_eq_integral_one_sub_maximumCdf
  have hMR : R.expectedMaximum=∫ t, 1-R.maximumCdf t ∂T := R.expectedMaximum_eq_integral_one_sub_maximumCdf
  rw [← hMB,← hMQ,← hMR] at hI
  exact hI

end ProphetSecretary.Limiting.CountableInstance
