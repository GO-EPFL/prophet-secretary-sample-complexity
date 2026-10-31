import ProphetSecretary.Statistics.CanonicalCandidateLoss
import ProphetSecretary.Model.CrossLawBellmanLoss

/-!
# Canonical candidate integration under a separate online law

The decision law, target continuation law and actual online product law are
separate parameters. Actual value/clock replacement under the online law and
proved canonical value-invariance give the candidate marginal integral. This
is used for true-policy mixed-design loss on independent TRUE online offers.
-/

open MeasureTheory Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Model
variable {n : ℕ}

noncomputable def candidateLossMeanUnder (Q T E : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (z : ℝ) (hz : 0≤z)
    (i : Fin n) (u : Fin n → ℝ) : ℝ :=
  ∫ x, (∫ t, canonicalCandidateLoss Q T hQ z hz i u x t ∂Instance.uniformClock) ∂E.law i

/-- Actual product-law resampling and integration, not an independence interface. -/
theorem canonical_arrivalLoss_candidate_integral_under (Q T E : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hT : Integrable Instance.maximum T.valuesLaw) (hE : Integrable Instance.maximum E.valuesLaw)
    (z : ℝ) (hz : 0≤z) (i : Fin n) :
    Integrable (candidateLossMeanUnder Q T E hQ z hz i) (Instance.clocksLaw n) ∧
    (∫ ω : World n Unit, (Q.valuePolicy hQ zero_le_one hz).rule.arrivalBellmanLoss T 1 z () ω.1 ω.2.1 i
      ∂E.worldLaw (Measure.dirac ())) = ∫ u, candidateLossMeanUnder Q T E hQ z hz i u ∂Instance.clocksLaw n := by
  let π : Policy Unit n := (Q.valuePolicy hQ zero_le_one hz).rule
  let μ := E.worldLaw (Measure.dirac ())
  let f : World n Unit → ℝ := fun ω => π.arrivalBellmanLoss T 1 z () ω.1 ω.2.1 i
  have hπ : π.IsMeasurable := Q.valueThreshold_policy_isMeasurable hQ zero_le_one hz
  have hfm : Measurable f := π.measurable_arrivalBellmanLoss hπ T hT zero_lt_one hz measurable_const
    (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  have hf : Integrable f μ := by
    have hI := π.integrable_arrivalBellmanLoss_under hπ T E hT hE (Measure.dirac ()) zero_lt_one hz i
    apply hI.congr
    exact Eventually.of_forall fun ω => by rcases ω with ⟨x,u,r⟩; cases r; rfl
  let R : (World n Unit × ℝ) × ℝ → World n Unit := fun q =>
    (Function.update q.1.1.1 i q.1.2,(Function.update q.1.1.2.1 i q.2,q.1.1.2.2))
  have hR : MeasurePreserving R ((μ.prod (E.law i)).prod Instance.uniformClock) μ :=
    (E.replaceClock_measurePreserving (Measure.dirac ()) i).comp
      ((E.replaceValue_measurePreserving (Measure.dirac ()) i).prod (MeasurePreserving.id Instance.uniformClock))
  have heq := integral_map (μ := (μ.prod (E.law i)).prod Instance.uniformClock) hR.measurable.aemeasurable hfm.aestronglyMeasurable
  rw [hR.map_eq] at heq
  have hfun : (fun q : (World n Unit × ℝ) × ℝ => f (R q)) =
      fun q => canonicalCandidateLoss Q T hQ z hz i q.1.1.2.1 q.1.2 q.2 := by
    funext q
    exact Q.valuePolicy_arrivalLoss_values_invariant T hQ hz
      (Function.update q.1.1.1 i q.1.2) (Function.update (fun _ => 0) i q.1.2)
      (Function.update q.1.1.2.1 i q.2) i (by simp only [Function.update_self])
  have hLI : Integrable (fun q : (World n Unit × ℝ) × ℝ =>
      canonicalCandidateLoss Q T hQ z hz i q.1.1.2.1 q.1.2 q.2) ((μ.prod (E.law i)).prod Instance.uniformClock) :=
    (hR.integrable_comp_of_integrable hf).congr (Eventually.of_forall fun q => congrFun hfun q)
  have hInner := hLI.integral_prod_left
  have hOuter := hInner.integral_prod_left
  have hLm := measurable_canonicalCandidateLoss Q T hQ hT z hz i
  have hInnerM : Measurable (fun q : (Fin n → ℝ) × ℝ =>
      ∫ t, canonicalCandidateLoss Q T hQ z hz i q.1 q.2 t ∂Instance.uniformClock) :=
    (hLm.stronglyMeasurable.integral_prod_right' (ν:=Instance.uniformClock)).measurable
  have hGm : Measurable (candidateLossMeanUnder Q T E hQ z hz i) :=
    (hInnerM.stronglyMeasurable.integral_prod_right' (ν:=E.law i)).measurable
  have hp := E.world_clocks_measurePreserving (Measure.dirac ())
  have hGIMap := (integrable_map_measure (μ:=μ) hGm.aestronglyMeasurable hp.measurable.aemeasurable).mpr hOuter
  rw [hp.map_eq] at hGIMap
  refine ⟨hGIMap,?_⟩
  have hClock := integral_map (μ:=μ) hp.measurable.aemeasurable hGm.aestronglyMeasurable
  rw [hp.map_eq] at hClock
  calc
    _ = ∫ q : (World n Unit × ℝ) × ℝ, canonicalCandidateLoss Q T hQ z hz i q.1.1.2.1 q.1.2 q.2
        ∂(μ.prod (E.law i)).prod Instance.uniformClock := by
          change (∫ ω : World n Unit, f ω ∂μ) = _
          rw [heq,hfun]
    _ = ∫ q : World n Unit × ℝ, (∫ t, canonicalCandidateLoss Q T hQ z hz i q.1.2.1 q.2 t ∂Instance.uniformClock)
        ∂μ.prod (E.law i) := integral_prod _ hLI
    _ = ∫ ω : World n Unit, (∫ x, (∫ t, canonicalCandidateLoss Q T hQ z hz i ω.2.1 x t ∂Instance.uniformClock) ∂E.law i) ∂μ :=
      integral_prod _ hInner
    _ = _ := hClock.symm

end ProphetSecretary.Model
