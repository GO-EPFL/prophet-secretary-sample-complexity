import ProphetSecretary.Model.UnreachedBellmanLoss
import ProphetSecretary.Model.PairedCanonicalLoss
import ProphetSecretary.Probability.CandidateValue

/-!
# Actual candidate value/clock integration of canonical losses

After dropping reach, a canonical local loss uses only the candidate value and
clock identities/times. Independent value and clock replacement is constructed
from the product model. Fubini then removes all other realized online values.
The dummy values in the analytical formula retain every arrival identity.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def canonicalCandidateLoss (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (z : ℝ) (hz : 0≤z)
    (i : Fin n) (u : Fin n → ℝ) (x t : ℝ) : ℝ :=
  (Q.valuePolicy hQ zero_le_one hz).rule.arrivalBellmanLoss P 1 z ()
    (Function.update (fun _ => 0) i x) (Function.update u i t) i

lemma canonicalCandidateLoss_nonnegative (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (z : ℝ) (hz : 0≤z)
    (i : Fin n) (u : Fin n → ℝ) (x t : ℝ) : 0≤canonicalCandidateLoss Q P hQ z hz i u x t :=
  (Q.valuePolicy hQ zero_le_one hz).rule.arrivalBellmanLoss_nonnegative P 1 z _ _ _ _

lemma measurable_canonicalCandidateLoss (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    (z : ℝ) (hz : 0≤z) (i : Fin n) :
    Measurable (fun q : ((Fin n → ℝ) × ℝ) × ℝ => canonicalCandidateLoss Q P hQ z hz i q.1.1 q.1.2 q.2) := by
  let π : Policy Unit n := (Q.valuePolicy hQ zero_le_one hz).rule
  have hπ : π.IsMeasurable := Q.valueThreshold_policy_isMeasurable hQ zero_le_one hz
  exact π.measurable_arrivalBellmanLoss hπ P hP zero_lt_one hz measurable_const
    (fun j => by fun_prop) (fun j => by fun_prop) i

noncomputable def candidateLossMean (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (z : ℝ) (hz : 0≤z)
    (i : Fin n) (u : Fin n → ℝ) : ℝ :=
  ∫ x, (∫ t, canonicalCandidateLoss Q P hQ z hz i u x t ∂Instance.uniformClock) ∂P.law i

/-- Actual product-law resampling and integration, not an independence interface. -/
theorem canonical_arrivalLoss_candidate_integral (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (hP : Integrable Instance.maximum P.valuesLaw)
    (z : ℝ) (hz : 0≤z) (i : Fin n) :
    Integrable (candidateLossMean Q P hQ z hz i) (Instance.clocksLaw n) ∧
    (∫ ω : World n Unit, (Q.valuePolicy hQ zero_le_one hz).rule.arrivalBellmanLoss P 1 z () ω.1 ω.2.1 i
      ∂P.worldLaw (Measure.dirac ())) = ∫ u, candidateLossMean Q P hQ z hz i u ∂Instance.clocksLaw n := by
  let π : Policy Unit n := (Q.valuePolicy hQ zero_le_one hz).rule
  let μ := P.worldLaw (Measure.dirac ())
  let f : World n Unit → ℝ := fun ω => π.arrivalBellmanLoss P 1 z () ω.1 ω.2.1 i
  have hπ : π.IsMeasurable := Q.valueThreshold_policy_isMeasurable hQ zero_le_one hz
  have hfm : Measurable f := π.measurable_arrivalBellmanLoss hπ P hP zero_lt_one hz measurable_const
    (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  have hf : Integrable f μ := by
    have hI := π.integrable_arrivalBellmanLoss hπ P hP (Measure.dirac ()) zero_lt_one hz i
    apply hI.congr
    exact Eventually.of_forall fun ω => by rcases ω with ⟨x,u,r⟩; cases r; rfl
  let R : (World n Unit × ℝ) × ℝ → World n Unit := fun q =>
    (Function.update q.1.1.1 i q.1.2,(Function.update q.1.1.2.1 i q.2,q.1.1.2.2))
  have hR : MeasurePreserving R ((μ.prod (P.law i)).prod Instance.uniformClock) μ :=
    (P.replaceClock_measurePreserving (Measure.dirac ()) i).comp
      ((P.replaceValue_measurePreserving (Measure.dirac ()) i).prod (MeasurePreserving.id Instance.uniformClock))
  have heq := integral_map (μ := (μ.prod (P.law i)).prod Instance.uniformClock) hR.measurable.aemeasurable hfm.aestronglyMeasurable
  rw [hR.map_eq] at heq
  have hfun : (fun q : (World n Unit × ℝ) × ℝ => f (R q)) =
      fun q => canonicalCandidateLoss Q P hQ z hz i q.1.1.2.1 q.1.2 q.2 := by
    funext q
    exact Q.valuePolicy_arrivalLoss_values_invariant P hQ hz
      (Function.update q.1.1.1 i q.1.2) (Function.update (fun _ => 0) i q.1.2)
      (Function.update q.1.1.2.1 i q.2) i (by simp only [Function.update_self])
  have hLI : Integrable (fun q : (World n Unit × ℝ) × ℝ =>
      canonicalCandidateLoss Q P hQ z hz i q.1.1.2.1 q.1.2 q.2) ((μ.prod (P.law i)).prod Instance.uniformClock) :=
    (hR.integrable_comp_of_integrable hf).congr (Eventually.of_forall fun q => congrFun hfun q)
  have hInner := hLI.integral_prod_left
  have hOuter := hInner.integral_prod_left
  have hLm := measurable_canonicalCandidateLoss Q P hQ hP z hz i
  have hInnerM : Measurable (fun q : (Fin n → ℝ) × ℝ =>
      ∫ t, canonicalCandidateLoss Q P hQ z hz i q.1 q.2 t ∂Instance.uniformClock) :=
    (hLm.stronglyMeasurable.integral_prod_right' (ν:=Instance.uniformClock)).measurable
  have hGm : Measurable (candidateLossMean Q P hQ z hz i) :=
    (hInnerM.stronglyMeasurable.integral_prod_right' (ν:=P.law i)).measurable
  have hp := P.world_clocks_measurePreserving (Measure.dirac ())
  have hGIMap := (integrable_map_measure (μ:=μ) hGm.aestronglyMeasurable hp.measurable.aemeasurable).mpr hOuter
  rw [hp.map_eq] at hGIMap
  refine ⟨hGIMap,?_⟩
  have hClock := integral_map (μ:=μ) hp.measurable.aemeasurable hGm.aestronglyMeasurable
  rw [hp.map_eq] at hClock
  calc
    _ = ∫ q : (World n Unit × ℝ) × ℝ, canonicalCandidateLoss Q P hQ z hz i q.1.1.2.1 q.1.2 q.2
        ∂(μ.prod (P.law i)).prod Instance.uniformClock := by
          change (∫ ω : World n Unit, f ω ∂μ) = _
          rw [heq,hfun]
    _ = ∫ q : World n Unit × ℝ, (∫ t, canonicalCandidateLoss Q P hQ z hz i q.1.2.1 q.2 t ∂Instance.uniformClock)
        ∂μ.prod (P.law i) := integral_prod _ hLI
    _ = ∫ ω : World n Unit, (∫ x, (∫ t, canonicalCandidateLoss Q P hQ z hz i ω.2.1 x t ∂Instance.uniformClock) ∂P.law i) ∂μ :=
      integral_prod _ hInner
    _ = _ := hClock.symm

end ProphetSecretary.Model
