import ProphetSecretary.Limiting.CountableSelectionValueConstancy
import ProphetSecretary.Limiting.CountableSelection

/-!
# Conditional individual selection on supported values

The conditional selection probability is the integral of the actual selection
indicator after replacing only the candidate value. Under the zero-response
alternative, this is constant on the entire supported convex hull, as used
in the individual contraction step of `lem:nonzero`.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

noncomputable def CountableRule.conditionalSelectionAtValue (π : CountableRule Seed)
    (B : CountableInstance) (ν : Measure Seed) (i : ℕ) (x : ℝ) : ℝ :=
  ∫ v, π.individualSelectionIndicator i (replaceIndividualValue i (v,x)) ∂B.completeWorldLaw ν

lemma CountableRule.measurable_conditionalSelectionAtValue (π : CountableRule Seed) (hπ : π.IsMeasurable)
    (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) :
    Measurable (π.conditionalSelectionAtValue B ν i) :=
  ((π.measurable_individualSelectionIndicator hπ i).comp (measurable_replaceIndividualValue i)).stronglyMeasurable.integral_prod_left'.measurable

omit [MeasurableSpace Seed] in
lemma CountableRule.individualSelectionIndicator_eq_of_selectedCode_eq (π : CountableRule Seed)
    {v z : CompleteWorld Seed} (i : ℕ)
    (h : FirstAcceptance.selectedCode π.codeAccepted codeTime z=FirstAcceptance.selectedCode π.codeAccepted codeTime v) :
    π.individualSelectionIndicator i z=π.individualSelectionIndicator i v := by
  have hSel : π.SelectsIndividual z i ↔ π.SelectsIndividual v i := by
    unfold CountableRule.SelectsIndividual
    rw [← FirstAcceptance.selectedCode_eq_succ_iff,← FirstAcceptance.selectedCode_eq_succ_iff,h]
  simp only [CountableRule.individualSelectionIndicator,hSel]

theorem canonical_conditionalSelectionAtValue_eq_on_support_hull
    (B : CountableInstance) (hZero : B.terminal=0) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) (i : ℕ)
    (hScores : ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, |φ x| ≤ 1) →
      (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0 →
      (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    ∀ x ∈ convexHull ℝ (B.individuals i : Measure ℝ).support,
      (B.valueRule w c).conditionalSelectionAtValue B (Measure.dirac ()) i x=
        (B.valueRule w c).individualSelectionProbability B (Measure.dirac ()) i := by
  intro x hx
  rw [← (B.valueRule w c).integral_individualSelectionIndicator (B.valueRule_isMeasurable hw.le hc.le)]
  apply integral_congr_ae
  filter_upwards [B.canonical_selectedCodeAtValue_ae_constant_on_support_hull hZero hw hc i hScores] with v hv
  exact (B.valueRule w c).individualSelectionIndicator_eq_of_selectedCode_eq i (hv x hx)

end ProphetSecretary.Limiting.CountableInstance
