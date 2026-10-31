import ProphetSecretary.Reach.SelectionCharge

/-!
# Complete-vector form of the selection charge

Conditioning a candidate value retains the original design policy. Pending execution
ignores that value, so candidate-value replacement identifies the iterated conditional
charge with its expression on the complete online offer vector.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.crossingSelectionCharge_update_value (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z)
    (a b : ℝ) (A : Finset (Fin n)) (ω : World n Unit) :
    P.crossingSelectionCharge hP i hz a A (Function.update ω.1 i b, ω.2) =
      P.crossingSelectionCharge hP i hz a A ω := by
  let π := (P.valuePolicy hP zero_le_one hz.le).rule
  have he : π.pendingTime () (Function.update ω.1 i b) ω.2.1 i = π.pendingTime () ω.1 ω.2.1 i := by
    simpa only [Function.update_eq_self] using π.pendingTime_update () ω.1 ω.2.1 i b (ω.2.1 i)
  unfold Instance.crossingSelectionCharge
  change (if P.InteriorCrossing hP i z a A ω.2.1 ∧
      (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z a ≤
        π.pendingTime () (Function.update ω.1 i b) ω.2.1 i then _ else 0) = _
  rw [he]

lemma Instance.measurable_crossingSelectionCharge_diagonal (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z)
    (A : Finset (Fin n)) :
    Measurable (fun ω : World n Unit => P.crossingSelectionCharge hP i hz (ω.1 i) A ω) :=
  (P.measurable_crossingSelectionCharge_joint hP i hz A).comp
    (measurable_id.prodMk ((measurable_pi_apply i).comp measurable_fst))

lemma Instance.integrable_crossingSelectionCharge_diagonal (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z)
    (A : Finset (Fin n)) :
    Integrable (fun ω : World n Unit => P.crossingSelectionCharge hP i hz (ω.1 i) A ω)
      (P.worldLaw (Measure.dirac ())) := by
  apply Integrable.of_bound (P.measurable_crossingSelectionCharge_diagonal hP i hz A).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun ω => by
    have h := P.crossingSelectionCharge_mem_unitInterval hP i hz (ω.1 i) A ω
    simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

lemma Instance.integral_crossingSelectionCharge_diagonal (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) {z : ℝ} (hz : 0 < z)
    (A : Finset (Fin n)) :
    (∫ a, ∫ ω, P.crossingSelectionCharge hP i hz a A ω ∂P.worldLaw (Measure.dirac ()) ∂P.law i) =
      ∫ ω, P.crossingSelectionCharge hP i hz (ω.1 i) A ω ∂P.worldLaw (Measure.dirac ()) := by
  let μ := P.worldLaw (Measure.dirac ())
  let f := fun ω : World n Unit => P.crossingSelectionCharge hP i hz (ω.1 i) A ω
  have hm : Measurable f := P.measurable_crossingSelectionCharge_diagonal hP i hz A
  have hrep := P.replaceValue_measurePreserving (Measure.dirac ()) i
  have hmap := integral_map (μ := μ.prod (P.law i)) hrep.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hrep.map_eq] at hmap
  have hcomp (v : World n Unit × ℝ) : f (Instance.replaceValue i v) = P.crossingSelectionCharge hP i hz v.2 A v.1 := by
    dsimp [f, Instance.replaceValue]
    simp only [Function.update_self]
    exact P.crossingSelectionCharge_update_value hP i hz v.2 v.2 A v.1
  calc
    _ = ∫ v, P.crossingSelectionCharge hP i hz v.2 A v.1 ∂μ.prod (P.law i) :=
      (integral_prod_symm _ (P.integrable_crossingSelectionCharge_joint hP i hz A)).symm
    _ = ∫ v, f (Instance.replaceValue i v) ∂μ.prod (P.law i) :=
      integral_congr_ae (Filter.Eventually.of_forall fun v => (hcomp v).symm)
    _ = _ := hmap.symm

/-- The universal finite charge expressed directly on the complete offer vector.
Future offers may occur in this analytical expectation, but remain unobserved by
the history-based executed policy. -/
lemma Instance.mean_total_crossingSelectionCharge_le_one (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z : ℝ} (hz : 0 < z) :
    (∫ ω : World n Unit, ∑ i : Fin n, ∑ A : Finset (Fin n),
      P.crossingSelectionCharge hP i hz (ω.1 i) A ω ∂P.worldLaw (Measure.dirac ())) ≤ 1 := by
  have hi (i : Fin n) : Integrable (fun ω : World n Unit => ∑ A : Finset (Fin n),
      P.crossingSelectionCharge hP i hz (ω.1 i) A ω) (P.worldLaw (Measure.dirac ())) :=
    integrable_finsetSum _ (fun A _ => P.integrable_crossingSelectionCharge_diagonal hP i hz A)
  have he (i : Fin n) : (∫ ω : World n Unit, ∑ A : Finset (Fin n),
      P.crossingSelectionCharge hP i hz (ω.1 i) A ω ∂P.worldLaw (Measure.dirac ())) =
        ∫ a, ∑ A : Finset (Fin n), ∫ ω, P.crossingSelectionCharge hP i hz a A ω
          ∂P.worldLaw (Measure.dirac ()) ∂P.law i := by
    rw [integral_finsetSum _ (fun A _ => P.integrable_crossingSelectionCharge_diagonal hP i hz A)]
    simp_rw [← P.integral_crossingSelectionCharge_diagonal hP i hz]
    exact (integral_finsetSum _ (fun A _ => P.integrable_mean_crossingSelectionCharge hP i hz A)).symm
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [he]
  exact P.total_crossingSelectionCharge_le_one hP hz

end ProphetSecretary.Model
