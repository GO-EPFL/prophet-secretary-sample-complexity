import ProphetSecretary.Limiting.CountableIndividualLocationKernels

/-!
# The individual location identity in the absence of positive ties

Bounded measurable displacements supported above an arbitrary positive level
identify the two conditional kernels. Testing their bounded difference gives
an integral of a nonnegative square. A countable exhaustion yields the identity
on all positive marginal values.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

noncomputable def individualLocationSelection (B : CountableInstance) (w c : ℝ) (i : ℕ) (x : ℝ) : ℝ :=
  (B.valueRule w c).conditionalSelectionAtValue B (Measure.dirac ()) i x

noncomputable def individualLocationProphet (B : CountableInstance) (i : ℕ) (x : ℝ) : ℝ :=
  (B.competingMaximumLaw i : Measure ℝ).real (Iio x)

lemma measurable_individualLocationProphet (B : CountableInstance) (i : ℕ) :
    Measurable (B.individualLocationProphet i) := by
  apply Monotone.measurable
  intro x y hxy
  exact measureReal_mono (fun z hz => hz.trans_le hxy)

lemma individualLocationProphet_mem_unit (B : CountableInstance) (i : ℕ) (x : ℝ) :
    B.individualLocationProphet i x∈Icc (0 : ℝ) 1 := by
  refine ⟨measureReal_nonneg,?_⟩
  have h := measureReal_mono (μ := (B.competingMaximumLaw i : Measure ℝ)) (subset_univ (Iio x))
  simpa only [individualLocationProphet,probReal_univ] using h

theorem critical_individual_location_above (B : CountableInstance) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (hCritical : B.IsCritical w c) (i : ℕ) {b : ℝ} (hb : 0<b)
    (hNoTie : ∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()),
      0<v.2.1 i → v.2.1 i≠B.competingMaximum i v) :
    ∀ᵐ x ∂(B.individuals i : Measure ℝ), b≤x →
      B.individualLocationSelection w c i x=optimalCompetitiveRatio*B.individualLocationProphet i x := by
  let a := B.individualLocationSelection w c i
  let p := B.individualLocationProphet i
  let f := fun x => a x-optimalCompetitiveRatio*p x
  let φ := fun x => if b≤x then f x else 0
  have ha : Measurable a := (B.valueRule w c).measurable_conditionalSelectionAtValue
    (B.valueRule_isMeasurable hw.le hc.le) B (Measure.dirac ()) i
  have hp : Measurable p := B.measurable_individualLocationProphet i
  have hf : Measurable f := ha.sub (hp.const_mul optimalCompetitiveRatio)
  have hφ : Measurable φ := Measurable.ite (measurableSet_le measurable_const measurable_id) hf measurable_const
  have haUnit (x : ℝ) : a x∈Icc (0 : ℝ) 1 := (B.valueRule w c).conditionalSelectionAtValue_mem_unit
    (B.valueRule_isMeasurable hw.le hc.le) B (Measure.dirac ()) i x
  have hpUnit (x : ℝ) : p x∈Icc (0 : ℝ) 1 := B.individualLocationProphet_mem_unit i x
  have hfBound (x : ℝ) : |f x|≤1 := by
    have ha0 := (haUnit x).1
    have ha1 := (haUnit x).2
    have hp0 := mul_nonneg optimalCompetitiveRatio_nonnegative (hpUnit x).1
    have hp1 : optimalCompetitiveRatio*p x≤1 := (mul_le_mul optimalCompetitiveRatio_le_one (hpUnit x).2 (hpUnit x).1 zero_le_one).trans_eq (one_mul _)
    exact abs_le.mpr ⟨by dsimp only [f]; linarith,by dsimp only [f]; linarith⟩
  have hφBound (x : ℝ) : |φ x|≤1 := by
    dsimp only [φ]
    split_ifs
    · exact hfBound x
    · norm_num
  have hVanish (x : ℝ) (hx : x<b) : φ x=0 := if_neg (not_le.mpr hx)
  have hRegular : ∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()),
      φ (v.2.1 i)=0 ∨ v.2.1 i≠B.competingMaximum i v := hNoTie.mono (fun v hv => by
    by_cases hx : b≤v.2.1 i
    · exact Or.inr (hv (hb.trans_le hx))
    · exact Or.inl (if_neg hx))
  have hStat := B.critical_individual_value_stationarity hw hc hCritical i φ hφ (by norm_num : (0 : ℝ)≤1) hb hφBound hVanish hRegular
  have hSel := (B.valueRule w c).integral_selection_value_weight (B.valueRule_isMeasurable hw.le hc.le) B
    (Measure.dirac ()) i φ hφ (by norm_num : (0 : ℝ)≤1) hφBound
  have hProphet := B.integral_individual_strictMaximum_weight i φ hφ (by norm_num : (0 : ℝ)≤1) hφBound
  change (∫ v : CompleteWorld Unit, (B.valueRule w c).individualSelectionIndicator i v*φ (v.2.1 i)
    ∂B.completeWorldLaw (Measure.dirac ()))=_ at hStat
  rw [hSel,hProphet] at hStat
  change (∫ x, a x*φ x ∂(B.individuals i : Measure ℝ))=optimalCompetitiveRatio*(∫ x, p x*φ x ∂(B.individuals i : Measure ℝ)) at hStat
  have hAI : Integrable (fun x => a x*φ x) (B.individuals i : Measure ℝ) := by
    apply Integrable.of_bound (ha.mul hφ).aestronglyMeasurable 1
    exact Eventually.of_forall (fun x => by
      change ‖a x*φ x‖≤1
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (haUnit x).1]
      exact mul_le_one₀ (haUnit x).2 (abs_nonneg _) (hφBound x))
  have hPI : Integrable (fun x => p x*φ x) (B.individuals i : Measure ℝ) := by
    apply Integrable.of_bound (hp.mul hφ).aestronglyMeasurable 1
    exact Eventually.of_forall (fun x => by
      change ‖p x*φ x‖≤1
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hpUnit x).1]
      exact mul_le_one₀ (hpUnit x).2 (abs_nonneg _) (hφBound x))
  have hFI : Integrable (fun x => f x*φ x) (B.individuals i : Measure ℝ) := by
    apply (hAI.sub (hPI.const_mul optimalCompetitiveRatio)).congr
    exact Eventually.of_forall (fun x => by
      change a x*φ x-optimalCompetitiveRatio*(p x*φ x)=(a x-optimalCompetitiveRatio*p x)*φ x
      ring)
  have hZeroIntegral : (∫ x, f x*φ x ∂(B.individuals i : Measure ℝ))=0 := by
    have hFun : (fun x => f x*φ x)=(fun x => a x*φ x-optimalCompetitiveRatio*(p x*φ x)) := by funext x; dsimp only [f]; ring
    rw [hFun,integral_sub hAI (hPI.const_mul optimalCompetitiveRatio),integral_const_mul,hStat,sub_self]
  have hNonneg (x : ℝ) : 0≤f x*φ x := by
    dsimp only [φ]
    split_ifs
    · exact mul_self_nonneg _
    · simp only [mul_zero,le_refl]
  have hAE := (integral_eq_zero_iff_of_nonneg hNonneg hFI).mp hZeroIntegral
  filter_upwards [hAE] with x hx hbx
  have hx0 : f x=0 := by
    rw [show φ x=f x from if_pos hbx] at hx
    exact (mul_self_eq_zero.mp hx)
  exact sub_eq_zero.mp hx0

theorem critical_individual_location_of_no_positive_ties (B : CountableInstance) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (hCritical : B.IsCritical w c) (i : ℕ)
    (hNoTie : ∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()),
      0<v.2.1 i → v.2.1 i≠B.competingMaximum i v) :
    ∀ᵐ x ∂(B.individuals i : Measure ℝ), 0<x →
      B.individualLocationSelection w c i x=optimalCompetitiveRatio*B.individualLocationProphet i x := by
  have hAll : ∀ k : ℕ, ∀ᵐ x ∂(B.individuals i : Measure ℝ), 1/(k+1 : ℝ)≤x →
      B.individualLocationSelection w c i x=optimalCompetitiveRatio*B.individualLocationProphet i x :=
    fun k => B.critical_individual_location_above hw hc hCritical i (by positivity) hNoTie
  filter_upwards [ae_all_iff.mpr hAll] with x hx hx0
  obtain ⟨k,hk⟩ := exists_nat_one_div_lt hx0
  exact hx k hk.le

end ProphetSecretary.Limiting.CountableInstance
