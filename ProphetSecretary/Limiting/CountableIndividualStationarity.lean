import ProphetSecretary.Limiting.CountableIndividualValueEnvelope
import ProphetSecretary.Limiting.CountableIndividualMaximumDerivative
import ProphetSecretary.Limiting.NoReserve
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Critical stationarity under an individual value displacement

At an interior critical pair, the actual scalar gap is nonnegative along the
constructed perturbation path and vanishes at zero. Its two-sided derivative
is therefore zero. The no-tie condition is explicit, since eliminating
positive ties is a separate use of symmetric perturbations.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

theorem critical_individual_value_stationarity (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c) (i : ℕ)
    (φ : ℝ → ℝ) (hφ : Measurable φ) {D b : ℝ} (hD : 0≤D) (hb : 0<b)
    (hBound : ∀ x, |φ x|≤D) (hVanish : ∀ x, x<b → φ x=0)
    (hNoTie : ∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()),
      φ (v.2.1 i)=0 ∨ v.2.1 i≠B.competingMaximum i v) :
    (B.valuePolicy hw hc).individualPerturbationMean i φ=optimalCompetitiveRatio*
      (∫ v : CompleteWorld Unit, if B.competingMaximum i v<v.2.1 i then φ (v.2.1 i) else 0
        ∂B.completeWorldLaw (Measure.dirac ())) := by
  have hZero := B.terminal_eq_zero_of_critical hw hc.le hCritical
  let family := B.individualValuePath i φ hφ D b hD hb hBound hVanish
  have hBaseGap : (family 0).scalarGap w c=0 := by
    change (B.individualValuePath i φ hφ D b hD hb hBound hVanish 0).scalarGap w c=0
    rw [B.individualValuePath_zero i φ hφ hD hb hBound hVanish]
    unfold scalarGap
    rw [B.withCap_optimalScalarValue,B.withCap_expectedMaximum]
    exact hCritical.2
  have hMin : IsLocalMin (fun θ => (family θ).scalarGap w c) 0 := by
    change ∀ᶠ θ in 𝓝 (0 : ℝ), (family 0).scalarGap w c≤(family θ).scalarGap w c
    rw [hBaseGap]
    exact Eventually.of_forall (fun θ => (family θ).scalarGap_nonnegative hw.le hc.le)
  have hV := B.hasDerivAt_optimalScalarValue_individualValuePath hZero hw hc i φ hφ hD hb hBound hVanish
  have hM := B.hasDerivAt_expectedMaximum_individualValuePath i φ hφ hD hb hBound hVanish hNoTie
  have hGap := hV.sub (((hM.const_mul w).add_const c).const_mul optimalCompetitiveRatio)
  have hStationary := hMin.hasDerivAt_eq_zero hGap
  have hFactor : w*((B.valuePolicy hw hc).individualPerturbationMean i φ-optimalCompetitiveRatio*
      (∫ v : CompleteWorld Unit, if B.competingMaximum i v<v.2.1 i then φ (v.2.1 i) else 0
        ∂B.completeWorldLaw (Measure.dirac ())))=0 := by
    nlinarith only [hStationary]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hFactor).resolve_left (ne_of_gt hw))

end ProphetSecretary.Limiting.CountableInstance
