import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Independent observations avoid null sections

An independent random parameter may select an arbitrary null section of an
observed variable's law. The product-law and Fubini steps below establish the
joint almost-sure assertion explicitly.
-/

open MeasureTheory ProbabilityTheory Filter

namespace ProphetSecretary.Probability

theorem indepFun_ae_of_sections {Ω A B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure A} [IsProbabilityMeasure μ]
    {X : Ω → A} {Y : Ω → B} (hI : IndepFun X Y P)
    (hMX : Measurable X) (hMY : Measurable Y) (hX : HasLaw X μ P)
    {p : A → B → Prop} (hp : MeasurableSet {q : A × B | p q.1 q.2})
    (hsections : ∀ b, ∀ᵐ a ∂μ, p a b) :
    ∀ᵐ ω ∂P, p (X ω) (Y ω) := by
  letI : IsProbabilityMeasure (P.map Y) := Measure.isProbabilityMeasure_map hMY.aemeasurable
  have hY : HasLaw Y (P.map Y) P := ⟨hMY.aemeasurable,rfl⟩
  have hJoint := (hI.hasLaw_prod hX hY).measurePreserving (hMX.prodMk hMY)
  have hs : ∀ᵐ b ∂P.map Y, ∀ᵐ a ∂μ, p a b := Filter.Eventually.of_forall hsections
  have hprod : ∀ᵐ q ∂μ.prod (P.map Y), p q.1 q.2 :=
    (Measure.ae_prod_iff_ae_ae hp).mpr ((Measure.ae_ae_comm hp).mpr hs)
  exact hJoint.quasiMeasurePreserving.ae hprod

/-- In particular, an independent observation cannot equal an atomless one. -/
theorem indepFun_ae_ne_of_atomless {Ω A : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSingletonClass A]
    {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure A} [IsProbabilityMeasure μ]
    [NullSingletonClass μ] {X Y : Ω → A} (hI : IndepFun X Y P)
    (hMX : Measurable X) (hMY : Measurable Y) (hX : HasLaw X μ P)
    (hp : MeasurableSet {q : A × A | q.1 ≠ q.2}) :
    ∀ᵐ ω ∂P, X ω ≠ Y ω :=
  indepFun_ae_of_sections hI hMX hMY hX hp (fun b => μ.ae_ne b)

end ProphetSecretary.Probability
