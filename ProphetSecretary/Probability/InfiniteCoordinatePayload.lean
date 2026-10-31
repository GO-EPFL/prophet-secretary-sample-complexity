import ProphetSecretary.Probability.InfiniteCoordinateDensity
import Mathlib.Probability.HasLaw

/-!
# Reconstructing one coordinate together with an independent occurrence tag

The joint payload law determines both the reconstructed coordinate and tag.
Erasing the old coordinate is genuinely independent of its value, and fresh
auxiliary randomness is independent of the entire original vector. The joint
pushforward preserves every untouched coordinate and the required tag law.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical

namespace ProphetSecretary.Probability

lemma infinite_randomCoordinate_payload_measurePreserving {ι A U T : Type*} [DecidableEq ι]
    [MeasurableSpace A] [MeasurableSpace U] [MeasurableSpace T]
    (μ : ι → Measure A) [∀ j, IsProbabilityMeasure (μ j)] (i : ι) (a0 : A)
    (ρ : Measure U) [IsProbabilityMeasure ρ] (q : Measure A) [IsProbabilityMeasure q]
    (κ : Measure T) [IsProbabilityMeasure κ] {F : A × U → A × T}
    (hF : MeasurePreserving F ((μ i).prod ρ) (q.prod κ)) :
    MeasurePreserving (fun z : (ι → A) × U => (Function.update z.1 i (F (z.1 i,z.2)).1,(F (z.1 i,z.2)).2))
      ((Measure.infinitePi μ).prod ρ) ((Measure.infinitePi (Function.update μ i q)).prod κ) := by
  let P := Measure.infinitePi μ
  let erase := fun x : ι → A => Function.update x i a0
  let η := P.map erase
  have hErase : Measurable erase := measurable_infinite_erasure i a0
  have hEMP : MeasurePreserving erase P η := ⟨hErase,rfl⟩
  haveI : IsProbabilityMeasure η := P.isProbabilityMeasure_map hErase.aemeasurable
  have hXi := measurePreserving_eval_infinitePi μ i
  have hPairLaw := (infinite_erasure_independent μ i a0).hasLaw_prod hEMP.hasLaw hXi.hasLaw
  have hPair : MeasurePreserving (fun x : ι → A => (erase x,x i)) P (η.prod (μ i)) :=
    ⟨hErase.prodMk (measurable_pi_apply i),hPairLaw.map_eq⟩
  have hSplit := (measurePreserving_prodAssoc η (μ i) ρ).comp
    (hPair.prod (MeasurePreserving.id ρ))
  have hPayload := ((MeasurePreserving.id η).prod hF).comp hSplit
  have hReassociate := ((measurePreserving_prodAssoc η q κ).symm MeasurableEquiv.prodAssoc).comp hPayload
  have hUpdateMeas : Measurable (fun z : (ι → A) × A => Function.update z.1 i z.2) := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j=i
    · subst j
      simpa only [Function.update_self] using (measurable_snd : Measurable (fun z : (ι → A) × A => z.2))
    · simpa only [Function.update_of_ne hj,Function.comp_def] using (measurable_pi_apply j).comp measurable_fst
  have hErasedUpdate : MeasurePreserving (fun z : (ι → A) × A => Function.update z.1 i z.2)
      (η.prod q) (Measure.infinitePi (Function.update μ i q)) := by
    refine ⟨hUpdateMeas,?_⟩
    have hEraseProd := hEMP.prod (MeasurePreserving.id q)
    rw [← hEraseProd.map_eq,Measure.map_map hUpdateMeas hEraseProd.measurable]
    have hFun : (fun z : (ι → A) × A => Function.update (erase z.1) i z.2)=
        (fun z => Function.update z.1 i z.2) := by
      funext z
      exact Function.update_idem a0 z.2 z.1
    change (P.prod q).map (fun z : (ι → A) × A => Function.update (erase z.1) i z.2)=Measure.infinitePi (Function.update μ i q)
    rw [hFun]
    exact (infinite_changeCoordinate_measurePreserving μ i q).map_eq
  have hAll := (hErasedUpdate.prod (MeasurePreserving.id κ)).comp hReassociate
  have hFun : (fun z : (ι → A) × U =>
      (Function.update (erase z.1) i (F (z.1 i,z.2)).1,(F (z.1 i,z.2)).2))=
        (fun z => (Function.update z.1 i (F (z.1 i,z.2)).1,(F (z.1 i,z.2)).2)) := by
    funext z
    exact congrArg (fun x => (x,(F (z.1 i,z.2)).2)) (Function.update_idem a0 (F (z.1 i,z.2)).1 z.1)
  change MeasurePreserving (fun z : (ι → A) × U =>
    (Function.update (erase z.1) i (F (z.1 i,z.2)).1,(F (z.1 i,z.2)).2)) _ _ at hAll
  rw [hFun] at hAll
  exact hAll

end ProphetSecretary.Probability
