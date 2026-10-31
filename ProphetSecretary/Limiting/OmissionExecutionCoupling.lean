import ProphetSecretary.Limiting.OmissionCloudCoupling
import ProphetSecretary.Limiting.IndividualOmissionWorld

/-!
# Exact execution marginals for the causal omission simulator

The coupled old cloud is analytical. The simulator sees the finite high cloud,
its retained identities, and independent auxiliary low/tail data. Both actual
online laws and equality of complete anonymous counting measures are proved.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

private lemma swapFirstTwo_measurePreserving {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    MeasurePreserving (fun q : A × (B × C) => (q.2.1,(q.1,q.2.2)))
      (μ.prod (ν.prod ρ)) (ν.prod (μ.prod ρ)) :=
  (measurePreserving_prodAssoc ν μ ρ).comp
    (((Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod (MeasurePreserving.id ρ)).comp
      ((measurePreserving_prodAssoc μ ν ρ).symm MeasurableEquiv.prodAssoc))

lemma lowIntoIndividualWorld_measurePreserving (B : CountableInstance) {Seed : Type*}
    [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (ξ : Measure (Measure Point)) [IsProbabilityMeasure ξ] :
    MeasurePreserving (fun q : Measure Point × ((ℕ → ℝ) × ((ℕ → ℝ) × Seed)) =>
      (q.2.1,(q.2.2.1,(q.2.2.2,q.1))))
      (ξ.prod (B.individualWorldLaw ν)) (B.individualWorldLaw (ν.prod ξ)) := by
  have h₁ := swapFirstTwo_measurePreserving ξ B.individualValuesLaw (individualClocksLaw.prod ν)
  have h₂ := (MeasurePreserving.id B.individualValuesLaw).prod
    (swapFirstTwo_measurePreserving ξ individualClocksLaw ν)
  have h₃ := (MeasurePreserving.id B.individualValuesLaw).prod
    ((MeasurePreserving.id individualClocksLaw).prod (Measure.measurePreserving_swap (μ := ξ) (ν := ν)))
  exact h₃.comp (h₂.comp h₁)

noncomputable def omissionNewWorld (N : ℕ) {Seed : Type*}
    (q : SplitCloud × ((ℕ → ℝ) × ((ℕ → ℝ) × Seed))) : HybridWorld N (OmissionAux Seed) :=
  (q.1.1,splitIndividualsWorld N (q.2.1,(q.2.2.1,(q.2.2.2,q.1.2))))

lemma omissionNewWorld_measurePreserving (B : CountableInstance) {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (N : ℕ) {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    MeasurePreserving (omissionNewWorld (Seed := Seed) N)
      ((B.splitCloudLaw hb).prod (B.individualWorldLaw ν))
      (hybridWorldLaw (B.individualPrefix N) (B.intensityAbove b hb)
        ((ν.prod (B.lowCloudLaw b)).prod ((B.tailValuesLaw N).prod individualClocksLaw))) := by
  have h₁ := measurePreserving_prodAssoc (configurationLaw (B.intensityAbove b hb))
    (B.lowCloudLaw b) (B.individualWorldLaw ν)
  have h₂ := (MeasurePreserving.id (configurationLaw (B.intensityAbove b hb))).prod
    (lowIntoIndividualWorld_measurePreserving B ν (B.lowCloudLaw b))
  have h₃ := (MeasurePreserving.id (configurationLaw (B.intensityAbove b hb))).prod
    (B.splitIndividualsWorld_measurePreserving (ν.prod (B.lowCloudLaw b)) N)
  exact h₃.comp (h₂.comp h₁)

abbrev OmissionExecutionWorld (Seed : Type*) :=
  (SplitCloud × BandConfigurations) × ((ℕ → ℝ) × ((ℕ → ℝ) × Seed))

noncomputable def oldExecutionWorld {Seed : Type*} (q : OmissionExecutionWorld Seed) : CompleteWorld Seed := (q.1.2,q.2)
noncomputable def newExecutionWorld (N : ℕ) {Seed : Type*} (q : OmissionExecutionWorld Seed) : HybridWorld N (OmissionAux Seed) :=
  omissionNewWorld N (q.1.1,q.2)

lemma exists_omissionExecution_coupling (B : CountableInstance) {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (N : ℕ) {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    ∃ Γ : Measure (OmissionExecutionWorld Seed), IsProbabilityMeasure Γ ∧
      MeasurePreserving (newExecutionWorld N) Γ
        (hybridWorldLaw (B.individualPrefix N) (B.intensityAbove b hb)
          ((ν.prod (B.lowCloudLaw b)).prod ((B.tailValuesLaw N).prod individualClocksLaw))) ∧
      MeasurePreserving oldExecutionWorld Γ (B.completeWorldLaw ν) ∧
      (∀ᵐ q ∂Γ, bandCountingMeasure q.1.2 = joinedCloud q.1.1 ∧ LowCloudRegular B b q.1.1.2) := by
  obtain ⟨γ,hγ,hNew,hOld,hCounts⟩ := B.exists_omissionCloud_coupling hb
  letI : IsProbabilityMeasure γ := hγ
  let Γ := γ.prod (B.individualWorldLaw ν)
  have hBaseNew := hNew.prod (MeasurePreserving.id (B.individualWorldLaw ν))
  have hBaseOld := hOld.prod (MeasurePreserving.id (B.individualWorldLaw ν))
  have hN : MeasurePreserving (newExecutionWorld N) Γ _ :=
    (omissionNewWorld_measurePreserving B ν N hb).comp hBaseNew
  have hO : MeasurePreserving oldExecutionWorld Γ (B.completeWorldLaw ν) := hBaseOld
  have hFst : MeasurePreserving (Prod.fst : OmissionExecutionWorld Seed → SplitCloud × BandConfigurations) Γ γ :=
    measurePreserving_fst
  have hLow : MeasurePreserving (fun q : OmissionExecutionWorld Seed => q.1.1.2) Γ (B.lowCloudLaw b) :=
    (measurePreserving_snd : MeasurePreserving (Prod.snd : SplitCloud → Measure Point) (B.splitCloudLaw hb)
      (B.lowCloudLaw b)).comp (hNew.comp hFst)
  refine ⟨Γ,inferInstance,hN,hO,?_⟩
  filter_upwards [hFst.quasiMeasurePreserving.ae hCounts,hLow.quasiMeasurePreserving.ae (B.lowCloudLaw_regular_ae b)] with q hq hl
  exact ⟨hq,hl⟩

end ProphetSecretary.Limiting
