import ProphetSecretary.Limiting.CountableCutoffLaw
import ProphetSecretary.Limiting.PoissonRestrictionIndependence
import ProphetSecretary.Probability.IndependenceLawTransport

/-!
# Independence of the high cloud and a finite lower window

The entire cutoff counting-measure law transports finite Poisson independent
increments to the actual countable construction. Both outputs are complete
random measures; no band labels enter either observation.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

lemma measurable_restrict_pointMeasure {U : Set Point} (hU : MeasurableSet U) :
    Measurable (fun m : Measure Point => m.restrict U) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  have he : (fun m : Measure Point => m.restrict U S) = fun m => m (S ∩ U) := by
    funext m
    exact Measure.restrict_apply hS
  rw [he]
  exact Measure.measurable_coe (hS.inter hU)

namespace CountableInstance

variable (B : CountableInstance)

theorem high_low_window_independent {c b : ℝ} (hc : (B.terminal : ℝ) < c) (hcb : c ≤ b) :
    IndepFun (fun ω => (bandCountingMeasure ω).restrict (univ ×ˢ Ioi b))
      (fun ω => (bandCountingMeasure ω).restrict (univ ×ˢ Ioc c b)) B.bandConfigurationsLaw := by
  let U : Set Point := univ ×ˢ Ioi b
  let V : Set Point := univ ×ˢ Ioc c b
  let C : Set Point := univ ×ˢ Ioi c
  have hU : MeasurableSet U := MeasurableSet.univ.prod measurableSet_Ioi
  have hV : MeasurableSet V := MeasurableSet.univ.prod measurableSet_Ioc
  have hUV : Disjoint U V := Set.disjoint_left.mpr (fun p hpU hpV => (not_lt_of_ge hpV.2.2) hpU.2)
  let ρ : Measure (Measure Point) := (configurationLaw (B.intensityAbove c hc)).map countingMeasure
  haveI : IsProbabilityMeasure ρ := Measure.isProbabilityMeasure_map measurable_countingMeasure.aemeasurable
  let rU := fun m : Measure Point => m.restrict U
  let rV := fun m : Measure Point => m.restrict V
  have hRU : Measurable rU := measurable_restrict_pointMeasure hU
  have hRV : Measurable rV := measurable_restrict_pointMeasure hV
  have hFiniteLaw : HasLaw countingMeasure ρ (configurationLaw (B.intensityAbove c hc)) :=
    ⟨measurable_countingMeasure.aemeasurable,rfl⟩
  have hIρ : IndepFun rU rV ρ :=
    (ProphetSecretary.Probability.indepFun_comp_iff_of_hasLaw measurable_countingMeasure hFiniteLaw hRU hRV).mp
      (countingMeasure_restrictions_independent (B.intensityAbove c hc) hU hV hUV)
  let f := fun ω : BandConfigurations => (bandCountingMeasure ω).restrict C
  have hf : Measurable f := measurable_cutoffCountingMeasure c
  have hLaw : HasLaw f ρ B.bandConfigurationsLaw := ⟨hf.aemeasurable,B.cutoff_countingMeasure_law hc⟩
  have hPull := (ProphetSecretary.Probability.indepFun_comp_iff_of_hasLaw hf hLaw hRU hRV).mpr hIρ
  have hUC : U ⊆ C := fun _ h => ⟨h.1,lt_of_le_of_lt hcb h.2⟩
  have hVC : V ⊆ C := fun _ h => ⟨h.1,h.2.1⟩
  have heU : rU ∘ f = (fun ω => (bandCountingMeasure ω).restrict U) := by
    funext ω
    change ((bandCountingMeasure ω).restrict C).restrict U = _
    rw [Measure.restrict_restrict hU,inter_eq_left.mpr hUC]
  have heV : rV ∘ f = (fun ω => (bandCountingMeasure ω).restrict V) := by
    funext ω
    change ((bandCountingMeasure ω).restrict C).restrict V = _
    rw [Measure.restrict_restrict hV,inter_eq_left.mpr hVC]
  rw [heU,heV] at hPull
  exact hPull

end CountableInstance
end ProphetSecretary.Limiting
