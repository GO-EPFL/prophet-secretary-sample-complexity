import ProphetSecretary.Model.FirstArrival
import ProphetSecretary.Model.CandidateSplit

/-!
# First-arrival law in the child's original identity labels

This version of the clock decomposition uses `Fin A.card`, where
`A = univ.erase i`, exactly as the continuation instance `P_A`. The source
measure for each first identity is constructed and pushed forward to its actual
first-arrival region.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace ProphetSecretary.Model
namespace Instance

variable {n : ℕ}

lemma firstRegion_insertCandidate (i : Fin (n + 1)) (t : ℝ)
    (v : Fin (remainingSet i).card → ℝ) :
    insertCandidate i (t, v) ∈ firstRegion i ↔ ∀ j, t ≤ v j := by
  constructor
  · intro h j
    simpa only [insertCandidate_same, insertCandidate_remaining] using h (stateEmbedding (remainingSet i) j)
  · intro h k
    by_cases hki : k = i
    · subst k
      exact le_rfl
    · simp only [insertCandidate, dif_neg hki]
      exact h _

lemma lintegral_firstRegion_child_split {f : (Fin (n + 1) → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (i : Fin (n + 1)) :
    (∫⁻ u, (firstRegion i).indicator f u ∂clocksLaw (n + 1)) =
      ∫⁻ t, (∫⁻ v, ({v : Fin (remainingSet i).card → ℝ | ∀ j, t ≤ v j}).indicator
        (fun v ↦ f (insertCandidate i (t, v))) v ∂clocksLaw (remainingSet i).card) ∂uniformClock := by
  have hp := (splitCandidate_clocks_measurePreserving i).symm (splitCandidate i)
  have hg := hf.indicator (measurableSet_firstRegion i)
  rw [← hp.lintegral_comp hg]
  change (∫⁻ z : ℝ × (Fin (remainingSet i).card → ℝ),
    (firstRegion i).indicator f (insertCandidate i z) ∂uniformClock.prod (clocksLaw (remainingSet i).card)) = _
  rw [lintegral_prod (fun z : ℝ × (Fin (remainingSet i).card → ℝ) ↦
    (firstRegion i).indicator f (insertCandidate i z)) (hg.comp hp.measurable).aemeasurable]
  apply lintegral_congr
  intro t
  apply lintegral_congr
  intro v
  by_cases h : ∀ j, t ≤ v j
  · exact (Set.indicator_of_mem ((firstRegion_insertCandidate i t v).mpr h) f).trans
      (Set.indicator_of_mem (s := {v : Fin (remainingSet i).card → ℝ | ∀ j, t ≤ v j}) (a := v) h
        (fun v ↦ f (insertCandidate i (t, v)))).symm
  · exact (Set.indicator_of_notMem (fun hm ↦ h ((firstRegion_insertCandidate i t v).mp hm)) f).trans
      (Set.indicator_of_notMem (s := {v : Fin (remainingSet i).card → ℝ | ∀ j, t ≤ v j}) (a := v) h
        (fun v ↦ f (insertCandidate i (t, v)))).symm

lemma lintegral_firstRegion_child {f : (Fin (n + 1) → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (i : Fin (n + 1)) :
    (∫⁻ u, (firstRegion i).indicator f u ∂clocksLaw (n + 1)) =
      ∫⁻ t, (ENNReal.ofReal (1 - t)) ^ (remainingSet i).card *
        (∫⁻ v, f (insertCandidate i (t, tailClocks (remainingSet i).card t v))
          ∂clocksLaw (remainingSet i).card) ∂uniformClock := by
  rw [lintegral_firstRegion_child_split hf i]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc, uniformClock.ae_ne 1] with t ht hne
  exact lintegral_residual_clocks
    (hf.comp ((measurable_insertCandidate i).comp (measurable_const.prodMk measurable_id)))
    ht.1 (lt_of_le_of_ne ht.2 hne)

/-- The full integration identity using each original-label child state. -/
theorem lintegral_firstArrival_child {f : (Fin (n + 1) → ℝ) → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ u, f u ∂clocksLaw (n + 1)) =
      ∑ i : Fin (n + 1), ∫⁻ t, (ENNReal.ofReal (1 - t)) ^ (remainingSet i).card *
        (∫⁻ v, f (insertCandidate i (t, tailClocks (remainingSet i).card t v))
          ∂clocksLaw (remainingSet i).card) ∂uniformClock := by
  rw [lintegral_firstRegion_partition hf]
  exact Finset.sum_congr rfl (fun i _hi ↦ lintegral_firstRegion_child hf i)

noncomputable def firstChildTimeLaw (i : Fin (n + 1)) : Measure ℝ :=
  uniformClock.withDensity (firstArrivalDensity (remainingSet i).card)

noncomputable def firstChildClocks (i : Fin (n + 1))
    (z : ℝ × (Fin (remainingSet i).card → ℝ)) : Fin (n + 1) → ℝ :=
  insertCandidate i (z.1, tailClocks (remainingSet i).card z.1 z.2)

lemma measurable_firstChildClocks (i : Fin (n + 1)) : Measurable (firstChildClocks i) :=
  (measurable_insertCandidate i).comp
    (measurable_fst.prodMk (measurable_tailClocks_joint (remainingSet i).card))

/-- Each child sampler has exactly the original uniform cube restricted to
its first-arrival region. Its residual clock law is independent of first time. -/
theorem firstChildClocks_measurePreserving (i : Fin (n + 1)) :
    MeasurePreserving (firstChildClocks i)
      ((firstChildTimeLaw i).prod (clocksLaw (remainingSet i).card))
      ((clocksLaw (n + 1)).restrict (firstRegion i)) := by
  refine ⟨measurable_firstChildClocks i, ?_⟩
  apply Measure.ext
  intro s hs
  have hf : Measurable (s.indicator (fun _ ↦ (1 : ℝ≥0∞))) := measurable_const.indicator hs
  have hm := hf.comp (measurable_firstChildClocks i)
  have h := lintegral_firstRegion_child hf i
  rw [lintegral_indicator (measurableSet_firstRegion i)] at h
  have hsource : (∫⁻ z, s.indicator (fun _ ↦ (1 : ℝ≥0∞)) (firstChildClocks i z)
      ∂(firstChildTimeLaw i).prod (clocksLaw (remainingSet i).card)) =
      ∫⁻ t, (ENNReal.ofReal (1 - t)) ^ (remainingSet i).card *
        (∫⁻ v, s.indicator (fun _ ↦ (1 : ℝ≥0∞)) (firstChildClocks i (t, v))
          ∂clocksLaw (remainingSet i).card) ∂uniformClock := by
    rw [lintegral_prod (fun z ↦ s.indicator (fun _ ↦ (1 : ℝ≥0∞)) (firstChildClocks i z)) hm.aemeasurable]
    exact lintegral_withDensity_eq_lintegral_mul uniformClock
      (measurable_firstArrivalDensity (remainingSet i).card) hm.lintegral_prod_right'
  have heq := hsource.trans h.symm
  rw [← lintegral_map (μ := (firstChildTimeLaw i).prod (clocksLaw (remainingSet i).card)) hf
    (measurable_firstChildClocks i)] at heq
  simpa only [lintegral_indicator hs, lintegral_const, Measure.restrict_apply_univ, one_mul] using heq

end Instance
end ProphetSecretary.Model
