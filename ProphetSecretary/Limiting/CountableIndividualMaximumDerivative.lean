import ProphetSecretary.Limiting.CountableIndividualValuePath
import ProphetSecretary.Limiting.CountableCompetingMaximumLaw
import ProphetSecretary.Limiting.CountableIndividualScore
import ProphetSecretary.Probability.MaximumValueDerivative

/-!
# The prophet derivative of a displaced individual

The actual competing maximum includes all other individuals and the anonymous
cloud. Excluding ties only where the displacement is nonzero suffices. No
policy observation contains this analytical competing maximum.
-/

open MeasureTheory Set Filter
open scoped Classical Topology NNReal

namespace ProphetSecretary.Limiting.CountableInstance

lemma individualValuePath_zero (B : CountableInstance) (i : ℕ) (φ : ℝ → ℝ) (hφ : Measurable φ)
    {D b : ℝ} (hD : 0≤D) (hb : 0<b) (hBound : ∀ x, |φ x|≤D) (hVanish : ∀ x, x<b → φ x=0) :
    B.individualValuePath i φ hφ D b hD hb hBound hVanish 0=B.withCap (B.cap+1) (by simp) := by
  apply CountableInstance.ext_data
  · rfl
  · rfl
  · funext j
    change Function.update B.individuals i ((B.individuals i).map
      (measurable_individualValueDisplay hφ D b 0).aemeasurable) j=B.individuals j
    by_cases hj : j=i
    · subst j
      rw [Function.update_self]
      apply ProbabilityMeasure.toMeasure_injective
      change (B.individuals i : Measure ℝ).map (individualValueDisplay φ D b 0)=(B.individuals i : Measure ℝ)
      rw [individualValueDisplay_zero,Measure.map_id]
    · rw [Function.update_of_ne hj]
  · rfl

lemma expectedMaximum_mapIndividual_eq_max (B : CountableInstance) (i : ℕ) (g : ℝ → ℝ) (hg : Measurable g)
    (hSupport : ∀ᵐ x ∂(B.individuals i : Measure ℝ), g x∈Icc (0 : ℝ) B.cap) :
    (B.mapIndividual i g hg hSupport).expectedMaximum=
      ∫ v : CompleteWorld Unit, max (g (v.2.1 i)) (B.competingMaximum i v) ∂B.completeWorldLaw (Measure.dirac ()) := by
  let Q := B.mapIndividual i g hg hSupport
  have hValue := (Q.value_projection_measurePreserving (Measure.dirac ())).hasLaw.integral_comp Q.measurable_maximum.aestronglyMeasurable
  have hMP := B.mapSingleIndividualWorld_measurePreserving i g hg hSupport (Measure.dirac ())
  have hF : Measurable (fun v : CompleteWorld Unit => Q.maximum (v.1,v.2.1)) :=
    Q.measurable_maximum.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hMean := hMP.hasLaw.integral_comp hF.aestronglyMeasurable
  calc
    _ = ∫ v : CompleteWorld Unit, Q.maximum (v.1,v.2.1) ∂Q.completeWorldLaw (Measure.dirac ()) := hValue.symm
    _ = ∫ v : CompleteWorld Unit, Q.maximum
        ((mapSingleIndividualWorld i g v).1,(mapSingleIndividualWorld i g v).2.1)
          ∂B.completeWorldLaw (Measure.dirac ()) := hMean.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [B.maximum_replaceIndividual_eq_max_ae (Measure.dirac ()) i] with v hv
      exact hv (g (v.2.1 i))

lemma individualValuePath_expectedMaximum (B : CountableInstance) (i : ℕ) (φ : ℝ → ℝ) (hφ : Measurable φ)
    {D b : ℝ} (hD : 0≤D) (hb : 0<b) (hBound : ∀ x, |φ x|≤D) (hVanish : ∀ x, x<b → φ x=0)
    {θ : ℝ} (hθ : |θ|≤ individualValueRadius D b) :
    (B.individualValuePath i φ hφ D b hD hb hBound hVanish θ).expectedMaximum=
      ∫ v : CompleteWorld Unit, max (v.2.1 i+θ*φ (v.2.1 i)) (B.competingMaximum i v) ∂B.completeWorldLaw (Measure.dirac ()) := by
  have h := (B.withCap (B.cap+1) (by simp)).expectedMaximum_mapIndividual_eq_max i
    (individualValueDisplay φ D b θ) (measurable_individualValueDisplay hφ D b θ)
    (B.individualValueDisplay_supported i hD hb hBound hVanish θ)
  change (B.individualValuePath i φ hφ D b hD hb hBound hVanish θ).expectedMaximum=
    ∫ v : CompleteWorld Unit, max (individualValueDisplay φ D b θ (v.2.1 i)) (B.competingMaximum i v) ∂B.completeWorldLaw (Measure.dirac ()) at h
  rw [h]
  apply integral_congr_ae
  exact Eventually.of_forall (fun v => congrArg (fun x => max x (B.competingMaximum i v))
    (show individualValueDisplay φ D b θ (v.2.1 i)=v.2.1 i+θ*φ (v.2.1 i) from if_pos hθ))

theorem hasDerivAt_expectedMaximum_individualValuePath (B : CountableInstance) (i : ℕ)
    (φ : ℝ → ℝ) (hφ : Measurable φ) {D b : ℝ} (hD : 0≤D) (hb : 0<b)
    (hBound : ∀ x, |φ x|≤D) (hVanish : ∀ x, x<b → φ x=0)
    (hNoTie : ∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()),
      φ (v.2.1 i)=0 ∨ v.2.1 i≠B.competingMaximum i v) :
    HasDerivAt (fun θ => (B.individualValuePath i φ hφ D b hD hb hBound hVanish θ).expectedMaximum)
      (∫ v : CompleteWorld Unit, if B.competingMaximum i v<v.2.1 i then φ (v.2.1 i) else 0
        ∂B.completeWorldLaw (Measure.dirac ())) 0 := by
  have hXi := B.individualValue_completeWorld_measurePreserving (Measure.dirac ()) i
  have hXI : Integrable (fun v : CompleteWorld Unit => v.2.1 i) (B.completeWorldLaw (Measure.dirac ())) := by
    apply Integrable.of_bound hXi.measurable.aestronglyMeasurable (B.cap : ℝ)
    filter_upwards [hXi.quasiMeasurePreserving.ae (B.individual_supported i)] with v hv
    rw [Real.norm_eq_abs,abs_of_nonneg hv.1]
    exact hv.2
  have hYI : Integrable (B.competingMaximum i) (B.completeWorldLaw (Measure.dirac ())) := by
    apply Integrable.of_bound (B.measurable_competingMaximum i).aestronglyMeasurable (B.cap : ℝ)
    filter_upwards [B.competingMaximum_bounded_ae i (Measure.dirac ())] with v hv
    rw [Real.norm_eq_abs,abs_of_nonneg hv.1]
    exact hv.2
  have hd := ProphetSecretary.Probability.hasDerivAt_expected_displaced_max (B.completeWorldLaw (Measure.dirac ()))
    (fun v : CompleteWorld Unit => v.2.1 i) (B.competingMaximum i) (fun v => φ (v.2.1 i)) hXi.measurable
    (B.measurable_competingMaximum i) (measurable_individualScore i hφ) hXI hYI hD
    (Eventually.of_forall (fun v => hBound (v.2.1 i))) hNoTie
  apply hd.congr_of_eventuallyEq
  have hRadius := individualValueRadius_pos hD hb
  filter_upwards [Icc_mem_nhds (neg_lt_zero.mpr hRadius) hRadius] with θ hθ
  exact B.individualValuePath_expectedMaximum i φ hφ hD hb hBound hVanish (abs_le.mpr hθ)

end ProphetSecretary.Limiting.CountableInstance
