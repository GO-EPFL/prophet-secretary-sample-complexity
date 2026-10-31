import ProphetSecretary.Model.ArrivalRankInfiniteTags

/-!
# Actual chronological conditional payload arrays

A fresh infinite auxiliary sequence is independent of the random number of
points. Conditional on N clocks, assigning its entries by chronological rank
retains the independent product law. Coordinatewise conditional sampling then
recovers the old values and occurrence tags jointly with every clock.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Probability

lemma chronological_payload_array_measurePreserving {N : ℕ} {U T : Type*}
    [MeasurableSpace U] [MeasurableSpace T]
    (q p : Measure ℝ) [IsProbabilityMeasure q] [IsProbabilityMeasure p]
    (ρ : Measure U) [IsProbabilityMeasure ρ] (κ : Measure T) [IsProbabilityMeasure κ]
    {F : ℝ × U → ℝ × T} (hF : MeasurePreserving F (q.prod ρ) (p.prod κ)) :
    MeasurePreserving (fun z : (Fin N → ℝ) × ((Fin N → ℝ) × (ℕ → U)) =>
        (z.1,fun i => F (z.2.1 i,z.2.2 (Model.Instance.arrivalRank z.1 i).val)))
      ((Model.Instance.clocksLaw N).prod ((Measure.pi (fun _ : Fin N => q)).prod (Measure.infinitePi (fun _ : ℕ => ρ))))
      ((Model.Instance.clocksLaw N).prod (Measure.pi (fun _ : Fin N => p.prod κ))) := by
  let C := Model.Instance.clocksLaw N
  let Q := Measure.pi (fun _ : Fin N => q)
  let A := Measure.pi (fun _ : Fin N => ρ)
  have hPrefix := (MeasurePreserving.id C).prod ((MeasurePreserving.id Q).prod (iidPrefix_measurePreserving ρ N))
  have hAssoc := (measurePreserving_prodAssoc C Q A).symm MeasurableEquiv.prodAssoc
  have hRank := dependent_iid_reindex_measurePreserving (C.prod Q) ρ
    (fun z : (Fin N → ℝ) × (Fin N → ℝ) => (Model.Instance.arrivalPermutation z.1).symm)
    (fun i => (Model.Instance.measurable_arrivalRank i).comp measurable_fst)
  have hBack := measurePreserving_prodAssoc C Q A
  have hPair := (measurePreserving_arrowProdEquivProdArrow ℝ U (Fin N) (fun _ => q) (fun _ => ρ)).symm
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ U (Fin N))
  have hRows := measurePreserving_pi (fun _ : Fin N => q.prod ρ) (fun _ : Fin N => p.prod κ) (fun _ => hF)
  have hFinal := (MeasurePreserving.id C).prod (hRows.comp hPair)
  exact hFinal.comp (hBack.comp (hRank.comp (hAssoc.comp hPrefix)))

lemma chronological_point_payload_array_measurePreserving {N : ℕ} {U T : Type*}
    [MeasurableSpace U] [MeasurableSpace T]
    (q p : Measure ℝ) [IsProbabilityMeasure q] [IsProbabilityMeasure p]
    (ρ : Measure U) [IsProbabilityMeasure ρ] (κ : Measure T) [IsProbabilityMeasure κ]
    {F : ℝ × U → ℝ × T} (hF : MeasurePreserving F (q.prod ρ) (p.prod κ)) :
    MeasurePreserving (fun z : (Fin N → (ℝ × ℝ)) × (ℕ → U) =>
        fun i => ((z.1 i).1,F ((z.1 i).2,z.2 (Model.Instance.arrivalRank (fun j => (z.1 j).1) i).val)))
      ((Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod q)).prod (Measure.infinitePi (fun _ : ℕ => ρ)))
      (Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod (p.prod κ))) := by
  have hSplit := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin N) (fun _ => Model.Instance.uniformClock) (fun _ => q)).prod
    (MeasurePreserving.id (Measure.infinitePi (fun _ : ℕ => ρ)))
  have hAssoc := measurePreserving_prodAssoc (Model.Instance.clocksLaw N) (Measure.pi (fun _ : Fin N => q))
    (Measure.infinitePi (fun _ : ℕ => ρ))
  have hKernel := chronological_payload_array_measurePreserving (N := N) q p ρ κ hF
  have hJoin := (measurePreserving_arrowProdEquivProdArrow ℝ (ℝ × T) (Fin N) (fun _ => Model.Instance.uniformClock)
    (fun _ => p.prod κ)).symm (MeasurableEquiv.arrowProdEquivProdArrow ℝ (ℝ × T) (Fin N))
  exact hJoin.comp (hKernel.comp (hAssoc.comp hSplit))

end ProphetSecretary.Probability
