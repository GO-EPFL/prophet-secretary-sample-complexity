import ProphetSecretary.Probability.ObservationCoupling
import Mathlib.Probability.Kernel.Representation

/-!
# Sampling a payload conditionally on its displayed value

A standard Borel payload can be sampled measurably from its displayed real
value and one fresh independent uniform. The joint law, rather than only
the displayed-value marginal, is preserved. A policy's separate auxiliary
seed needs no standard Borel assumption. In causal applications the fresh
uniform and reconstructed payload are used only when that value is observed.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ProbabilityTheory unitInterval

namespace ProphetSecretary.Probability

theorem exists_conditional_payload_sampler {T : Type*} [MeasurableSpace T] [StandardBorelSpace T]
    (μ : Measure T) [IsProbabilityMeasure μ] (g : T → ℝ) (hg : Measurable g) :
    ∃ F : ℝ → unitInterval → T, Measurable (Function.uncurry F) ∧
      MeasurePreserving (fun a : ℝ × unitInterval => (F a.1 a.2,a.1))
        ((μ.map g).prod volume) (μ.map (fun x => (x,g x))) ∧
      MeasurePreserving (fun a : ℝ × unitInterval => F a.1 a.2) ((μ.map g).prod volume) μ ∧
      (∀ᵐ a ∂(μ.map g).prod (volume : Measure unitInterval), g (F a.1 a.2)=a.1) := by
  letI : Nonempty T := nonempty_of_isProbabilityMeasure μ
  let κ := condDistrib (id : T → T) g μ
  obtain ⟨F,hF,hLaw⟩ := Kernel.exists_measurable_map_eq_unitInterval κ
  let Ψ : ℝ × unitInterval → ℝ × T := fun a => (a.1,F a.1 a.2)
  have hΨ : Measurable Ψ := measurable_fst.prodMk hF
  have hJoint : ((μ.map g).prod (volume : Measure unitInterval)).map Ψ = (μ.map g) ⊗ₘ κ := by
    ext S hS
    rw [Measure.map_apply hΨ hS,Measure.prod_apply (hS.preimage hΨ),Measure.compProd_apply hS]
    apply lintegral_congr_ae
    filter_upwards [] with y
    have hFY : Measurable (F y) := hF.comp (measurable_const.prodMk measurable_id)
    have hSection : MeasurableSet {x : T | (y,x)∈S} := measurable_prodMk_left hS
    have h := congrArg (fun ν : Measure T => ν {x | (y,x)∈S}) (hLaw y)
    rw [Measure.map_apply hFY hSection] at h
    exact h
  have hOriginal : ((μ.map g).prod (volume : Measure unitInterval)).map Ψ =
      μ.map (fun x => (g x,x)) := by
    rw [hJoint]
    exact compProd_map_condDistrib (Y:=(id : T → T)) aemeasurable_id
  have hPair : Measurable (fun x : T => (x,g x)) := measurable_id.prodMk hg
  have hPairRev : Measurable (fun x : T => (g x,x)) := hg.prodMk measurable_id
  have hMap : ((μ.map g).prod (volume : Measure unitInterval)).map
      (fun a : ℝ × unitInterval => (F a.1 a.2,a.1)) = μ.map (fun x => (x,g x)) := by
    rw [show (fun a : ℝ × unitInterval => (F a.1 a.2,a.1))=Prod.swap ∘ Ψ from rfl,
      ← Measure.map_map measurable_swap hΨ,hOriginal,Measure.map_map measurable_swap hPairRev]
    rfl
  have hMP : MeasurePreserving (fun a : ℝ × unitInterval => (F a.1 a.2,a.1))
      ((μ.map g).prod volume) (μ.map (fun x => (x,g x))) :=
    ⟨hF.prodMk measurable_fst,hMap⟩
  have hGraph : MeasurableSet {a : T × ℝ | g a.1=a.2} :=
    measurableSet_eq_fun (hg.comp measurable_fst) measurable_snd
  have hAE : ∀ᵐ a ∂μ.map (fun x => (x,g x)), g a.1=a.2 :=
    (ae_map_iff hPair.aemeasurable hGraph).mpr (Eventually.of_forall (fun _ => rfl))
  have hOld : MeasurePreserving (Prod.fst : T × ℝ → T) (μ.map (fun x => (x,g x))) μ := by
    refine ⟨measurable_fst,?_⟩
    rw [Measure.map_map measurable_fst hPair]
    change μ.map id=μ
    exact Measure.map_id
  exact ⟨F,hF,hMP,hOld.comp hMP,hMP.quasiMeasurePreserving.ae hAE⟩

end ProphetSecretary.Probability
