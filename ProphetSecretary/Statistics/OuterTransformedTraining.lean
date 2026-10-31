import ProphetSecretary.Model.OuterMeshDisplay
import ProphetSecretary.Statistics.OuterTaggedTraining
import ProphetSecretary.Model.ValueTransform

/-!
# Fresh transformed training observations

The cutoff and scale are fixed parameters for a fresh product block. The map
uses an independent tag on each observation and transforms its own value only.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n q : ℕ}

noncomputable def outerTransformedReservoir (m : ℕ) (t : ℝ × ℝ) (H : ℝ)
    (p : Reservoir n q × (Fin q → Fin n → ℝ)) : Reservoir n q :=
  fun i r => outerMeshDisplay m H (retainAboveTag t (p.1 i r,p.2 r i))

lemma measurable_outerTransformedReservoir (m : ℕ) :
    Measurable (fun p : ((ℝ × ℝ) × ℝ) × (Reservoir n q × (Fin q → Fin n → ℝ)) =>
      outerTransformedReservoir m p.1.1 p.1.2 p.2) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro r
  have hV : Measurable (fun p : ((ℝ × ℝ) × ℝ) × (Reservoir n q × (Fin q → Fin n → ℝ)) => p.2.1 i r) :=
    (measurable_pi_apply r).comp ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  have hA : Measurable (fun p : ((ℝ × ℝ) × ℝ) × (Reservoir n q × (Fin q → Fin n → ℝ)) => p.2.2 r i) :=
    (measurable_pi_apply i).comp ((measurable_pi_apply r).comp (measurable_snd.comp measurable_snd))
  have hY := measurable_retainAboveTag.comp ((measurable_fst.comp measurable_fst).prodMk (hV.prodMk hA))
  simpa only [Function.comp_def,outerTransformedReservoir] using
    (measurable_outerMeshDisplay m).comp ((measurable_snd.comp measurable_fst).prodMk hY)

end ProphetSecretary.Statistics

namespace ProphetSecretary.Model.Instance
open ProphetSecretary.Statistics
variable {n : ℕ}

noncomputable def outerTransformedInstance (P : Instance n) (m : ℕ) (hm : 0<m) (t : ℝ × ℝ) (H : ℝ) : Instance n :=
  (P.retainedAtTag t).mapValues (fun _ => outerMeshDisplay m H)
    (fun _ => (measurable_outerUnitMesh m).comp (measurable_id.div_const H))
    (fun _ => Filter.Eventually.of_forall fun x => (outerUnitMesh_mem_unit m hm (x/H)).1)

lemma outerTransformedInstance_bounded (P : Instance n) (m : ℕ) (hm : 0<m) (t : ℝ × ℝ) (H : ℝ) :
    ∀ i, ∀ᵐ x ∂(P.outerTransformedInstance m hm t H).law i, x≤1 := by
  intro i
  apply (ae_map_iff ((measurable_outerUnitMesh m).comp (measurable_id.div_const H)).aemeasurable measurableSet_Iic).mpr
  exact Filter.Eventually.of_forall fun x => (outerUnitMesh_mem_unit m hm (x/H)).2

lemma outerTransformedInstance_grid (P : Instance n) (m : ℕ) (hm : 0<m) (t : ℝ × ℝ) (H : ℝ) (i : Fin n) :
    ∀ᵐ x ∂(P.outerTransformedInstance m hm t H).law i, x∈meshGrid 1 m := by
  apply (ae_map_iff ((measurable_outerUnitMesh m).comp (measurable_id.div_const H)).aemeasurable (meshGrid 1 m).measurableSet).mpr
  exact Filter.Eventually.of_forall fun x => outerUnitMesh_mem_grid m hm (x/H)

end ProphetSecretary.Model.Instance

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n : ℕ}

lemma outerTransformedReservoir_measurePreserving (P : Instance n) (q m : ℕ) (hm : 0<m) (t : ℝ × ℝ) (H : ℝ) :
    MeasurePreserving (outerTransformedReservoir (n:=n) (q:=q) m t H)
      ((P.reservoirLaw q).prod (outerTagRowsLaw n q)) ((P.outerTransformedInstance m hm t H).reservoirLaw q) := by
  let Q := P.outerTransformedInstance m hm t H
  have hOne : MeasurePreserving (fun z : Fin n → ℝ × ℝ => fun i => outerMeshDisplay m H (retainAboveTag t (z i)))
      P.taggedValuesLaw Q.valuesLaw :=
    ((P.retainedAtTag t).mapValues_measurePreserving (fun _ => outerMeshDisplay m H)
      (fun _ => (measurable_outerUnitMesh m).comp (measurable_id.div_const H))
      (fun _ => Filter.Eventually.of_forall fun x => (outerUnitMesh_mem_unit m hm (x/H)).1)).comp
        (P.taggedRetainedValues_measurePreserving t)
  have hAll : MeasurePreserving
      (fun a : Fin q → Fin n → ℝ × ℝ => fun r i => outerMeshDisplay m H (retainAboveTag t (a r i)))
      (Measure.pi (fun _ : Fin q => P.taggedValuesLaw)) (Measure.pi (fun _ : Fin q => Q.valuesLaw)) := by
    refine ⟨measurable_pi_lambda _ (fun r => hOne.measurable.comp (measurable_pi_apply r)),?_⟩
    rw [Measure.pi_map_pi (fun _ => hOne.measurable.aemeasurable)]
    simp only [hOne.map_eq]
  have hOut := (Q.reservoirCoordinates_symm_measurePreserving q).comp (outerRoundCoordinates_measurePreserving Q q)
  exact hOut.comp (hAll.comp (taggedTrainingRows_measurePreserving P q))

end ProphetSecretary.Statistics
