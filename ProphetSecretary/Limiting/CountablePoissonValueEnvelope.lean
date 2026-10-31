import ProphetSecretary.Limiting.CountablePoissonPayloadEnvelope
import ProphetSecretary.Limiting.HybridCanonicalValueCoefficient
import ProphetSecretary.Limiting.CountableAnonymousCoefficientLimit
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# The Poisson mark-value envelope in the full limiting model

The fixed-base coefficient is the expected amplitude at the selected anonymous
occurrence. Exact truncation laws, coefficient convergence and a common
finite-hybrid remainder prove the derivative of the unrestricted policy value.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def poissonValuePath (B : CountableInstance) (hZero : B.terminal=0)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (D b : ℝ) (hD : 0≤D) (hb : 0<b)
    (hBound : ∀ x, |φ x|≤D) (hVanish : ∀ x, x<b → φ x=0) (θ : ℝ) : CountableInstance :=
  B.poissonPayloadValuePath hZero (Measure.dirac ()) (fun z : ℝ × Unit => φ z.1)
    (hφ.comp measurable_fst) D b hD hb (fun z => hBound z.1) (fun z => hVanish z.1) θ

/-- The anonymous mark-value assertion of paper `lem:envelopes`. The base
canonical policy remains fixed in the selected-amplitude coefficient. -/
theorem hasDerivAt_optimalScalarValue_poissonValuePath (B : CountableInstance)
    (hZero : B.terminal=0) {w c D b : ℝ} (hw : 0<w) (hc : 0<c)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (hD : 0≤D) (hb : 0<b)
    (hBound : ∀ x, |φ x|≤D) (hVanish : ∀ x, x<b → φ x=0) :
    HasDerivAt (fun θ => (B.poissonValuePath hZero φ hφ D b hD hb hBound hVanish θ).optimalScalarValue w c)
      (w*(∫ v, (B.valueRule w c).selectedTag (anonymousPerturbationTag φ) v
        ∂B.completeWorldLaw (Measure.dirac ()))) 0 := by
  obtain ⟨ds,_hAnti,hDs,hDsLim⟩ :=
    (dense_univ : Dense (univ : Set ℝ)).exists_seq_strictAnti_tendsto_of_lt (half_pos hb)
  have hPositive (m : ℕ) : 0<ds m := (hDs m).1.1
  have hSmall (m : ℕ) : ds m<b/2 := (hDs m).1.2
  have hCut (m : ℕ) : (B.terminal : ℝ)<ds m := by
    simpa only [hZero,NNReal.coe_zero] using hPositive m
  apply B.hasDerivAt_poissonPayloadValuePath_of_coefficient_limit hZero hw hc hD hb
    (Measure.dirac ()) () (fun z : ℝ × Unit => φ z.1) (hφ.comp measurable_fst)
    (fun z => hBound z.1) (fun z => hVanish z.1)
    id ds hPositive hSmall tendsto_id hDsLim
  have hLim := B.finiteHybrid_anonymousCoefficient_tendsto hZero hw hc hD hb
    id ds hCut tendsto_id (by simpa only [hZero,NNReal.coe_zero] using hDsLim) φ hφ hBound hVanish
  simp_rw [canonicalChronologicalAmplitudeMean_valueOnly _ (Measure.dirac ()) φ hφ hw.le hc.le]
  exact hLim

end ProphetSecretary.Limiting.CountableInstance
