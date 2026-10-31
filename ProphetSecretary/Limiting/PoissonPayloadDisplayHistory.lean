import ProphetSecretary.Limiting.PoissonPayloadDisplay
import ProphetSecretary.Limiting.ChronologicalConditionalHistory

/-!
# Forward display of the actual strict Poisson past

Preserving clocks makes display commute with strict-past restriction. A
conditional payload/display graph therefore restores the full observed past
without an inverse or injectivity assumption.
-/

open MeasureTheory Set
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting
variable {T : Type*} [MeasurableSpace T]

lemma display_payloadObservedHistory (g : ℝ × T → ℝ) (hg : Measurable g)
    (ω : PayloadConfiguration T) (t : ℝ) :
    (payloadObservedHistory ω t).map (displayPayloadPoint g)=observedHistory (displayPayloadConfiguration g ω) t := by
  have hMap := measurable_displayPayloadPoint hg
  change (∑ j : Fin ω.1, if (ω.2 j).1<t then Measure.dirac (ω.2 j) else 0).map (displayPayloadPoint g)=
    ∑ j : Fin ω.1, if (ω.2 j).1<t then Measure.dirac (displayPayloadPoint g (ω.2 j)) else 0
  simp only [← Measure.mapₗ_apply_of_measurable hMap,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : (ω.2 j).1<t
  · rw [if_pos hj,if_pos hj,Measure.mapₗ_apply_of_measurable hMap,Measure.map_dirac' hMap]
  · rw [if_neg hj,if_neg hj,map_zero]

omit [MeasurableSpace T] in
lemma display_conditionalPayloadConfiguration_eq_self {U : Type*} (F : ℝ × U → ℝ × T)
    (g : ℝ × T → ℝ) (ω : Configuration) (us : ℕ → U)
    (hGraph : ∀ j : Fin ω.1, g (F ((ω.2 j).2,us (Model.Instance.arrivalRank (fun k : Fin ω.1 => (ω.2 k).1) j).val))=(ω.2 j).2) :
    displayPayloadConfiguration g (chronologicalPayloadConfiguration F (ω,us))=ω := by
  rcases ω with ⟨N,v⟩
  change configurationMk N (fun j => ((v j).1,g (F ((v j).2,us (Model.Instance.arrivalRank (fun k : Fin N => (v k).1) j).val))))=configurationMk N v
  apply congrArg (configurationMk N)
  funext j
  apply Prod.ext
  · rfl
  · exact hGraph j

end ProphetSecretary.Limiting
