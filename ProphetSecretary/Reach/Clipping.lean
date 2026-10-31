import ProphetSecretary.Model.BellmanOptimal
import ProphetSecretary.Reach.ClippingPolicy
import ProphetSecretary.Analysis.Normalization
import Mathlib.Topology.Order.IntermediateValue

/-!
# Clipping and bounded normalization

Paper correspondence: `lem:clipping`. Clipping excess reward is transferred to the
duration coefficient. The comparison uses the actual canonical optimizer, cap acceptance,
monotone reach, and strictly positive finite-instance duration.
-/

open MeasureTheory Set
open scoped NNReal

namespace ProphetSecretary.Model

variable {n : ℕ}

/-- The value comparison in `lem:clipping`. This part also permits a zero benchmark. -/
theorem Instance.clippedValue_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    optimalScalarValue (P.cap (P.clippingHeight w c)) w
      (P.clippedDurationCoefficient (P.clippingHeight w c) w c) ≤ optimalScalarValue P w c := by
  let V0 := optimalScalarValue P w c
  let H := P.clippingHeight w c
  let Q := P.cap H
  let ch := P.clippedDurationCoefficient H w c
  let f : ℝ → ℝ := fun d => optimalScalarValue Q w d
  have hQ : Integrable Instance.maximum Q.valuesLaw := P.cap_integrable_maximum H hP
  have hch : 0 ≤ ch := P.clippedDurationCoefficient_nonnegative H hw.le hc
  have hf0 : f 0 ≤ V0 :=
    (optimalScalarValue_cap_le P H hP hw.le le_rfl).trans
      (optimalScalarValue_mono P hP hw.le le_rfl le_rfl hc)
  have hHcoe : (H : ℝ) = V0 / w := P.clippingHeight_coe hP hw hc
  by_contra hnot
  have hbig : V0 < f ch := lt_of_not_ge hnot
  have hf : ContinuousOn f (Icc 0 ch) :=
    (optimalScalarValue_durationWeight_continuousOn Q hQ hw.le).mono (fun _ h => h.1)
  obtain ⟨d, hd, hfd⟩ := intermediate_value_Icc hch hf (show V0 ∈ Icc (f 0) (f ch) from ⟨hf0, hbig.le⟩)
  have hdne : d ≠ ch := by
    intro heq
    rw [heq] at hfd
    exact (ne_of_gt hbig) hfd
  have hdlt : d < ch := lt_of_le_of_ne hd.2 hdne
  let π := Q.valuePolicy hQ hw.le hd.1
  haveI : Subsingleton π.Seed := by change Subsingleton Unit; infer_instance
  have hOpt : π.scalarObjective Q w d = V0 :=
    (Q.valuePolicy_optimal hQ hw hd.1).trans hfd
  have hacc : ∀ᵐ ω : π.World ∂Q.worldLaw π.seedLaw,
      π.rule.AcceptsReachedCap H ω.2.2 ω.1 ω.2.1 := by
    filter_upwards [Q.world_clocks_mem_unitInterval π.seedLaw] with ω hω
    intro i _hr hxi
    have hu : ω.2.2 = () := Subsingleton.elim _ _
    rw [hu]
    apply Q.valueThreshold_accepts_cap hQ hw hd.1 ω.1 ω.2.1 i (hω i).1
    rw [hxi]
    change f d / w ≤ (H : ℝ)
    rw [hfd, hHcoe]
  have hq : ∀ i, π.expectedDuration Q ≤ π.rule.reachProbability Q π.seedLaw i := by
    intro i
    exact thresholdPolicy.meanDuration_le_reachProbability _
      (Q.valueThreshold_monotone hQ hw hd.1)
      (Q.valueThreshold_policy_isMeasurable hQ hw.le hd.1) Q (Measure.dirac ()) i
  have hstrict := π.cap_pullback_scalar_strict P H hP hw.le hacc hq hdlt
  rw [hOpt] at hstrict
  have hupper := scalarObjective_le_optimal
    (π.pullbackValues (capValue H) (measurable_capValue H)) P hP hw.le hc
  exact (not_lt_of_ge hupper) hstrict

/-- The full bounded normalization of `lem:clipping`, with the capped law,
weights and reward scaling given explicitly. -/
theorem Instance.clipping_normalization (P : Instance n) (hP : P.HasPositiveFiniteMaximum)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hratio : optimalScalarValue P w c / (w * P.expectedMaximum + c) < 1) :
    let V0 := optimalScalarValue P w c
    let r0 := V0 / (w * P.expectedMaximum + c)
    let H := P.clippingHeight w c
    let Q := P.cap H
    let d := P.clippedDurationCoefficient H w c
    let D := w * Q.expectedMaximum + d
    let W := Q.scale Q.expectedMaximum⁻¹ (inv_nonneg.mpr Q.expectedMaximum_nonnegative)
    let ww := w * Q.expectedMaximum / D
    let cc := d / D
    W.HasPositiveFiniteMaximum ∧ W.expectedMaximum = 1 ∧ ww + cc = 1 ∧
      ww ∈ Icc (1 - r0) r0 ∧ cc ∈ Icc (1 - r0) r0 ∧
      (∀ i, ∀ᵐ x ∂W.law i, x ≤ r0 / (1 - r0)) ∧
      optimalScalarValue W ww cc / (ww * W.expectedMaximum + cc) ≤ r0 := by
  dsimp only
  let V0 := optimalScalarValue P w c
  let D0 := w * P.expectedMaximum + c
  let r0 := V0 / D0
  let H := P.clippingHeight w c
  let Q := P.cap H
  let d := P.clippedDurationCoefficient H w c
  let D := w * Q.expectedMaximum + d
  let W := Q.scale Q.expectedMaximum⁻¹ (inv_nonneg.mpr Q.expectedMaximum_nonnegative)
  let ww := w * Q.expectedMaximum / D
  let cc := d / D
  change W.HasPositiveFiniteMaximum ∧ W.expectedMaximum = 1 ∧ ww + cc = 1 ∧
    ww ∈ Icc (1 - r0) r0 ∧ cc ∈ Icc (1 - r0) r0 ∧
    (∀ i, ∀ᵐ x ∂W.law i, x ≤ r0 / (1 - r0)) ∧
    optimalScalarValue W ww cc / (ww * W.expectedMaximum + cc) ≤ r0
  have hD0 : 0 < D0 := (mul_pos hw hP.2).trans_le (le_add_of_nonneg_right hc)
  have hV0 : 0 ≤ V0 := optimalScalarValue_nonnegative P hP.1 hw.le hc
  have hVlt : V0 < D0 := (div_lt_one hD0).mp hratio
  have hQ : Integrable Instance.maximum Q.valuesLaw := P.cap_integrable_maximum H hP.1
  have hd : 0 ≤ d := P.clippedDurationCoefficient_nonnegative H hw.le hc
  have hclip : optimalScalarValue Q w d ≤ V0 := P.clippedValue_le hP.1 hw hc
  have hdV : d ≤ V0 := (durationWeight_le_optimalScalarValue Q hQ hw.le hd).trans hclip
  have hHcoe : (H : ℝ) = V0 / w := P.clippingHeight_coe hP.1 hw hc
  have hcapM : Q.expectedMaximum ≤ (H : ℝ) :=
    Q.expectedMaximum_le_of_bounded H.coe_nonneg (P.cap_bounded H)
  have haV : w * Q.expectedMaximum ≤ V0 := by
    have h := mul_le_mul_of_nonneg_left hcapM hw.le
    rw [hHcoe, mul_div_cancel₀ V0 hw.ne'] at h
    exact h
  have hDD : D0 ≤ w * Q.expectedMaximum + d := by
    have h := mul_le_mul_of_nonneg_left (P.expectedMaximum_le_cap_add_tailSum H hP.1) hw.le
    dsimp [D0, d, Instance.clippedDurationCoefficient]
    nlinarith
  obtain ⟨haPos, _hbPos, hD, hsum, haRange, hbRange, hcapRatio⟩ :=
    ProphetSecretary.Analysis.normalization_parameters hD0 hV0 hVlt haV hdV hDD
  have hM : 0 < Q.expectedMaximum := (mul_pos_iff_of_pos_left hw).mp haPos
  have hInv : 0 < Q.expectedMaximum⁻¹ := inv_pos.mpr hM
  have hWI : Integrable Instance.maximum W.valuesLaw :=
    Q.scale_integrable_maximum _ hInv.le hQ
  have hWM : W.expectedMaximum = 1 := by
    rw [Instance.scale_expectedMaximum Q Q.expectedMaximum⁻¹ hInv.le,
      inv_mul_cancel₀ hM.ne']
  have hww : 0 ≤ ww := div_nonneg (mul_nonneg hw.le Q.expectedMaximum_nonnegative) hD.le
  have hcc : 0 ≤ cc := div_nonneg hd hD.le
  have hbound : ∀ i, ∀ᵐ x ∂W.law i, x ≤ r0 / (1 - r0) := by
    intro i
    apply (ae_map_iff (measurable_valueScale Q.expectedMaximum⁻¹).aemeasurable measurableSet_Iic).mpr
    filter_upwards [P.cap_bounded H i] with x hx
    have hscale := mul_le_mul_of_nonneg_left hx hInv.le
    have heq : Q.expectedMaximum⁻¹ * (H : ℝ) = V0 / (w * Q.expectedMaximum) := by
      rw [hHcoe]
      field_simp
    exact hscale.trans (heq ▸ hcapRatio)
  have hvalue : optimalScalarValue W ww cc ≤ r0 := by
    rw [optimalScalarValue_scale Q Q.expectedMaximum⁻¹ hInv hQ hww hcc]
    have hwcoef : Q.expectedMaximum⁻¹ * ww = D⁻¹ * w := by dsimp [ww, D]; field_simp
    have hccoef : cc = D⁻¹ * d := by dsimp [cc]; ring
    rw [hwcoef, hccoef, optimalScalarValue_smul Q hQ (a := D⁻¹)
      (inv_nonneg.mpr hD.le) hw.le hd]
    calc
      D⁻¹ * optimalScalarValue Q w d = optimalScalarValue Q w d / D := by ring
      _ ≤ V0 / D0 := ProphetSecretary.Analysis.normalized_ratio_le hV0 hD0 hDD hclip
  have hbench : ww * W.expectedMaximum + cc = 1 := by rw [hWM, mul_one]; exact hsum
  exact ⟨⟨hWI, by rw [hWM]; norm_num⟩, hWM, hsum, haRange, hbRange, hbound,
    by rw [hbench, div_one]; exact hvalue⟩

end ProphetSecretary.Model

