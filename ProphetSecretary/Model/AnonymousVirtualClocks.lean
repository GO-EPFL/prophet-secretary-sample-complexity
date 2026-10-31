import ProphetSecretary.Model.ZeroSimulationProbability
import Mathlib.Probability.HasLaw
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Independent anonymous and virtual clock blocks

The original clocks, anonymous clocks, and virtual zero-offer clocks are
independent. Reordering the blocks and appending them gives the actual full
independent-uniform clock vector. Fubini then lifts a conditional virtual-clock
bound to the full execution, with no sign restriction on the bound.
-/

open MeasureTheory

namespace ProphetSecretary.Model

variable {n N q : ℕ}

def anonymousVirtualClocks
    (z : (Fin n → ℝ) × ((Fin N → ℝ) × (Fin q → ℝ))) : Fin (n+q+N) → ℝ :=
  ZeroSimulation.appendClocks (ZeroSimulation.appendClocks z.1 z.2.2) z.2.1

lemma anonymousVirtualClocks_measurePreserving (n N q : ℕ) :
    MeasurePreserving (anonymousVirtualClocks (n := n) (N := N) (q := q))
      ((Instance.clocksLaw n).prod ((Instance.clocksLaw N).prod (Instance.clocksLaw q)))
      (Instance.clocksLaw (n+q+N)) := by
  have h0 := (MeasurePreserving.id (Instance.clocksLaw n)).prod
    (Measure.measurePreserving_swap (μ := Instance.clocksLaw N) (ν := Instance.clocksLaw q))
  have h1 := (measurePreserving_prodAssoc (Instance.clocksLaw n) (Instance.clocksLaw q)
    (Instance.clocksLaw N)).symm MeasurableEquiv.prodAssoc
  have h2 := (Instance.appendClocks_measurePreserving n q).prod (MeasurePreserving.id (Instance.clocksLaw N))
  have h3 := Instance.appendClocks_measurePreserving (n+q) N
  exact h3.comp (h2.comp (h1.comp h0))

lemma integral_le_of_anonymousVirtual_inner
    (f : (Fin (n+q+N) → ℝ) → ℝ) (hF : Integrable f (Instance.clocksLaw (n+q+N))) (D : ℝ)
    (hInner : ∀ᵐ u ∂Instance.clocksLaw n, ∀ᵐ v ∂Instance.clocksLaw N,
      (∫ z, f (anonymousVirtualClocks (u,(v,z))) ∂Instance.clocksLaw q) ≤ D) :
    (∫ s, f s ∂Instance.clocksLaw (n+q+N)) ≤ D := by
  let F := fun a : (Fin n → ℝ) × ((Fin N → ℝ) × (Fin q → ℝ)) => f (anonymousVirtualClocks a)
  have hp := anonymousVirtualClocks_measurePreserving n N q
  have hFI : Integrable F ((Instance.clocksLaw n).prod ((Instance.clocksLaw N).prod (Instance.clocksLaw q))) :=
    hp.integrable_comp_of_integrable hF
  have hOuter : ∀ᵐ u ∂Instance.clocksLaw n,
      (∫ a, F (u,a) ∂(Instance.clocksLaw N).prod (Instance.clocksLaw q)) ≤ D := by
    filter_upwards [hFI.prod_right_ae,hInner] with u hI hBound
    rw [integral_prod _ hI]
    simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono_ae hI.integral_prod_left (integrable_const D) hBound
  have hAll := integral_mono_ae hFI.integral_prod_left (integrable_const D) hOuter
  have hEq := hp.hasLaw.integral_comp hF.aestronglyMeasurable
  calc
    (∫ s, f s ∂Instance.clocksLaw (n+q+N)) =
        ∫ a, F a ∂(Instance.clocksLaw n).prod ((Instance.clocksLaw N).prod (Instance.clocksLaw q)) := hEq.symm
    _ = ∫ u, (∫ a, F (u,a) ∂(Instance.clocksLaw N).prod (Instance.clocksLaw q)) ∂Instance.clocksLaw n :=
      integral_prod _ hFI
    _ ≤ D := by simpa only [integral_const,probReal_univ,one_smul] using hAll

end ProphetSecretary.Model
