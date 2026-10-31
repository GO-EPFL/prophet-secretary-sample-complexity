import ProphetSecretary.Probability.ProductRegrouping
import ProphetSecretary.Model.Independence

/-!
# Pairing two independent coordinate experiments

Independent pairs on two independent product factors remain independent after
matching their first components and their second components. The proof uses
actual pushforward product laws and the measurable four-factor shuffle.
-/
open MeasureTheory ProbabilityTheory
namespace ProphetSecretary.Probability

lemma indepFun_product_pairs {Ω Ξ A B C D : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] [MeasurableSpace D]
    {μ : Measure Ω} {ν : Measure Ξ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω → A} {g : Ω → B} {h : Ξ → C} {k : Ξ → D}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (hk : Measurable k)
    (hfg : IndepFun f g μ) (hhk : IndepFun h k ν) :
    IndepFun (fun z : Ω × Ξ => (f z.1,h z.2)) (fun z => (g z.1,k z.2)) (μ.prod ν) := by
  haveI : IsProbabilityMeasure (μ.map f) := Measure.isProbabilityMeasure_map hf.aemeasurable
  haveI : IsProbabilityMeasure (μ.map g) := Measure.isProbabilityMeasure_map hg.aemeasurable
  haveI : IsProbabilityMeasure (ν.map h) := Measure.isProbabilityMeasure_map hh.aemeasurable
  haveI : IsProbabilityMeasure (ν.map k) := Measure.isProbabilityMeasure_map hk.aemeasurable
  have h₁ : MeasurePreserving (fun x => (f x,g x)) μ ((μ.map f).prod (μ.map g)) :=
    ⟨hf.prodMk hg,hfg.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable⟩
  have h₂ : MeasurePreserving (fun x => (h x,k x)) ν ((ν.map h).prod (ν.map k)) :=
    ⟨hh.prodMk hk,hhk.map_prod_eq_prod_map_map hh.aemeasurable hk.aemeasurable⟩
  have hT := (productPairShuffle_measurePreserving (μ.map f) (μ.map g) (ν.map h) (ν.map k)).comp (h₁.prod h₂)
  exact ProphetSecretary.Model.indepFun_pullback hT measurable_fst measurable_snd
    (indepFun_prod measurable_id measurable_id)

end ProphetSecretary.Probability
