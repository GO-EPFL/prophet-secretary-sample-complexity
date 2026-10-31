import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic

/-!
# Transporting independence through an actual observation law

Two measurable functionals of an observation are independent precisely when
their corresponding functionals are independent under its actual image law.
-/

open MeasureTheory ProbabilityTheory

namespace ProphetSecretary.Probability

theorem indepFun_comp_iff_of_hasLaw {Ω A B C : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure A} [IsProbabilityMeasure μ]
    {Z : Ω → A} (hZ : Measurable Z) (hLaw : HasLaw Z μ P)
    {f : A → B} {g : A → C} (hf : Measurable f) (hg : Measurable g) :
    IndepFun (f ∘ Z) (g ∘ Z) P ↔ IndepFun f g μ := by
  have hJoint : P.map (fun ω => (f (Z ω),g (Z ω))) = μ.map (fun a => (f a,g a)) := by
    calc
      _ = (P.map Z).map (fun a => (f a,g a)) := (Measure.map_map (hf.prodMk hg) hZ).symm
      _ = _ := congrArg (fun ν : Measure A => ν.map (fun a => (f a,g a))) hLaw.map_eq
  have hF : P.map (f ∘ Z) = μ.map f := by
    rw [← Measure.map_map hf hZ,hLaw.map_eq]
  have hG : P.map (g ∘ Z) = μ.map g := by
    rw [← Measure.map_map hg hZ,hLaw.map_eq]
  rw [indepFun_iff_map_prod_eq_prod_map_map (hf.comp hZ).aemeasurable (hg.comp hZ).aemeasurable,
    indepFun_iff_map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable,hF,hG]
  change P.map (fun ω => (f (Z ω),g (Z ω))) = _ ↔ _
  rw [hJoint]

end ProphetSecretary.Probability
