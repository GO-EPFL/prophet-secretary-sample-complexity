import ProphetSecretary.Limiting.CountableIndividualPayloadValuePath
import ProphetSecretary.Limiting.CountableCompetingMaximumLaw

/-!
# Actual prophet expectation of a displayed individual payload

The proved forward world map displays the old individual value together with
an independent auxiliary tag. The maximum is the maximum of that displayed
value and the original competing maximum. This identity is analytical and
does not reveal the tag or future observations to a policy.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Limiting.CountableInstance
variable {T : Type} [MeasurableSpace T]

theorem individualPayloadValuePath_expectedMaximum_eq (B : CountableInstance) (i : ℕ)
    (κ : Measure T) [IsProbabilityMeasure κ] (A : ℝ × T → ℝ) (hA : Measurable A)
    {D b : ℝ} (hD : 0≤D) (hb : 0<b) (hBound : ∀ z, |A z|≤D)
    (hVanish : ∀ z, z.1<b → A z=0) (θ : ℝ) :
    (B.individualPayloadValuePath i κ A hA D b hD hb hBound hVanish θ).expectedMaximum=
      ∫ v : CompleteWorld (Unit × T), max
        (payloadValueDisplay A D b θ (v.2.1 i,v.2.2.2.2)) (B.competingMaximum i v)
          ∂B.completeWorldLaw ((Measure.dirac ()).prod κ) := by
  let C := B.withCap (B.cap+1) (by simp)
  let g := payloadValueDisplay A D b θ
  have hg : Measurable g := measurable_payloadValueDisplay hA D b θ
  let hs := B.payloadValueDisplay_supported i κ hD hb hBound hVanish θ
  let Q := C.mapIndividualPayload i κ g hg hs
  have hMaximum : Q.maximum=B.maximum := rfl
  have hMP := C.displayedIndividualWorld_measurePreserving i κ g hg hs (Measure.dirac ())
  have hF : Measurable (fun v : CompleteWorld Unit => Q.maximum (v.1,v.2.1)) :=
    Q.measurable_maximum.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have hMap := hMP.hasLaw.integral_comp hF.aestronglyMeasurable
  have hValue := (Q.value_projection_measurePreserving (Measure.dirac ())).hasLaw.integral_comp Q.measurable_maximum.aestronglyMeasurable
  calc
    _ = ∫ v : CompleteWorld Unit, Q.maximum (v.1,v.2.1) ∂Q.completeWorldLaw (Measure.dirac ()) := hValue.symm
    _ = ∫ v : CompleteWorld (Unit × T), Q.maximum
        ((recoverIndividualWorld i g v).1,(recoverIndividualWorld i g v).2.1)
          ∂C.completeWorldLaw ((Measure.dirac ()).prod κ) := hMap.symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [B.maximum_replaceIndividual_eq_max_ae ((Measure.dirac ()).prod κ) i] with v hv
      change Q.maximum (v.1,Function.update v.2.1 i (g (v.2.1 i,v.2.2.2.2)))=_
      rw [hMaximum]
      exact hv _

end ProphetSecretary.Limiting.CountableInstance
