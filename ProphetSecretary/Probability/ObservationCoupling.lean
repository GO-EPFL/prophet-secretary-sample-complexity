import Mathlib.Probability.Kernel.CondDistrib

/-!
# Coupling configurations with the same observable law

Disintegrating the old configuration given its observation constructs an
actual joint measure with the prescribed marginals and equal observations.
Only the old configuration space is standard Borel. An arbitrary independent
policy seed can be adjoined afterward and is not part of that assumption.
The coupling is an analytical construction and supplies no future observation
to an online policy.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ProbabilityTheory

namespace ProphetSecretary.Probability

theorem exists_common_observation_coupling {Old New Obs : Type*}
    [MeasurableSpace Old] [StandardBorelSpace Old] [MeasurableSpace New] [MeasurableSpace Obs]
    (μ : Measure Old) (ν : Measure New) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {X : Old → Obs} {Z : New → Obs} (hX : Measurable X) (hZ : Measurable Z)
    (hLaw : μ.map X = ν.map Z)
    (hGraph : MeasurableSet {q : Obs × Old | X q.2 = q.1}) :
    ∃ γ : Measure (New × Old), IsProbabilityMeasure γ ∧
      MeasurePreserving Prod.fst γ ν ∧ MeasurePreserving Prod.snd γ μ ∧
      (∀ᵐ q ∂γ, X q.2 = Z q.1) := by
  letI : Nonempty Old := nonempty_of_isProbabilityMeasure μ
  let κ : Kernel Obs Old := condDistrib (id : Old → Old) X μ
  let γ : Measure (New × Old) := ν ⊗ₘ κ.comap Z hZ
  have hγ : IsProbabilityMeasure γ := by dsimp only [γ]; infer_instance
  have hFst : MeasurePreserving (Prod.fst : New × Old → New) γ ν :=
    ⟨measurable_fst,Measure.fst_compProd ν (κ.comap Z hZ)⟩
  let Ψ := fun q : New × Old => (Z q.1,q.2)
  have hΨ : Measurable Ψ := hZ.prodMap measurable_id
  have hPair : Measurable (fun o : Old => (X o,o)) := hX.prodMk measurable_id
  have hPush : γ.map Ψ = (ν.map Z) ⊗ₘ κ := by
    ext S hS
    rw [Measure.map_apply hΨ hS,Measure.compProd_apply (hS.preimage hΨ),
      Measure.compProd_apply hS,lintegral_map (Kernel.measurable_kernel_prodMk_left hS) hZ]
    rfl
  have hObsLaw : γ.map Ψ = μ.map (fun o => (X o,o)) := by
    rw [hPush,← hLaw]
    exact compProd_map_condDistrib (Y := (id : Old → Old)) aemeasurable_id
  have hObsMP : MeasurePreserving Ψ γ (μ.map (fun o => (X o,o))) := ⟨hΨ,hObsLaw⟩
  have hOldGraph : MeasurePreserving (Prod.snd : Obs × Old → Old) (μ.map (fun o => (X o,o))) μ := by
    refine ⟨measurable_snd,?_⟩
    rw [Measure.map_map measurable_snd hPair]
    change μ.map id = μ
    exact Measure.map_id
  have hOld : MeasurePreserving (Prod.snd : New × Old → Old) γ μ := hOldGraph.comp hObsMP
  have hGraphOld : ∀ᵐ q ∂μ.map (fun o => (X o,o)), X q.2 = q.1 :=
    (ae_map_iff hPair.aemeasurable hGraph).mpr (Filter.Eventually.of_forall fun _ => rfl)
  have hShared : ∀ᵐ q ∂γ, X q.2 = Z q.1 := hObsMP.quasiMeasurePreserving.ae hGraphOld
  exact ⟨γ,hγ,hFst,hOld,hShared⟩

/-- The same arbitrary independent seed can be retained on both sides of the
coupling; its measurable space need not be standard Borel. -/
theorem exists_common_observation_coupling_with_seed {Old New Obs Seed : Type*}
    [MeasurableSpace Old] [StandardBorelSpace Old] [MeasurableSpace New] [MeasurableSpace Obs]
    [MeasurableSpace Seed] (μ : Measure Old) (ν : Measure New) (ρ : Measure Seed)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ]
    {X : Old → Obs} {Z : New → Obs} (hX : Measurable X) (hZ : Measurable Z)
    (hLaw : μ.map X = ν.map Z) (hGraph : MeasurableSet {q : Obs × Old | X q.2 = q.1}) :
    ∃ γ : Measure ((New × Old) × Seed), IsProbabilityMeasure γ ∧
      MeasurePreserving (fun q => (q.1.1,q.2)) γ (ν.prod ρ) ∧
      MeasurePreserving (fun q => (q.1.2,q.2)) γ (μ.prod ρ) ∧
      (∀ᵐ q ∂γ, X q.1.2 = Z q.1.1) := by
  obtain ⟨γ,hγ,hNew,hOld,hObs⟩ := exists_common_observation_coupling μ ν hX hZ hLaw hGraph
  letI : IsProbabilityMeasure γ := hγ
  have hFirst : MeasurePreserving (Prod.fst : (New × Old) × Seed → New × Old) (γ.prod ρ) γ :=
    measurePreserving_fst
  exact ⟨γ.prod ρ,inferInstance,hNew.prod (MeasurePreserving.id ρ),
    hOld.prod (MeasurePreserving.id ρ),hFirst.quasiMeasurePreserving.ae hObs⟩

end ProphetSecretary.Probability
