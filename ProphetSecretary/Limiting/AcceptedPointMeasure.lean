import ProphetSecretary.Limiting.FiniteMeasurePast
import ProphetSecretary.Limiting.HybridPolicy

/-!
# The accepted-point measure of a label-free finite observer

The input contains the finite anonymous counting measure and the retained
value/clock world. The rule is evaluated only with strict past observations.
This constructs a measurable accepted-point measure without recovering an
ordered array or revealing the total anonymous count to the policy.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Limiting

abbrev FiniteObserverWorld (n : ℕ) (Seed : Type*) := FiniteMeasure Point × Model.World n Seed

variable {n : ℕ} {Seed : Type*}

noncomputable def HybridRule.individualMeasureAction (π : HybridRule n Seed)
    (v : FiniteObserverWorld n Seed) (i : Fin n) : Bool :=
  π.individual v.2.2.2 (v.2.2.1 i) i (v.2.1 i)
    (Model.history Finset.univ v.2.1 v.2.2.1 (v.2.2.1 i)) (finitePast v.1 (v.2.2.1 i))

noncomputable def HybridRule.anonymousMeasureAction (π : HybridRule n Seed)
    (v : FiniteObserverWorld n Seed) (p : Point) : Bool :=
  π.poisson v.2.2.2 p.1 p.2 (Model.history Finset.univ v.2.1 v.2.2.1 p.1) (finitePast v.1 p.1)

noncomputable def HybridRule.individualMeasureAccepted (π : HybridRule n Seed)
    (v : FiniteObserverWorld n Seed) (i : Fin n) : Prop :=
  v.2.2.1 i ∈ Icc (0 : ℝ) 1 ∧ π.individualMeasureAction v i = true

noncomputable def HybridRule.anonymousMeasureAccepted (π : HybridRule n Seed)
    (v : FiniteObserverWorld n Seed) (p : Point) : Prop :=
  p.1 ∈ Icc (0 : ℝ) 1 ∧ π.anonymousMeasureAction v p = true

noncomputable def HybridRule.acceptedAnonymousMeasure (π : HybridRule n Seed)
    (v : FiniteObserverWorld n Seed) : Measure Point :=
  (v.1 : Measure Point).restrict {p | π.anonymousMeasureAccepted v p}

noncomputable def HybridRule.acceptedPointMeasureRaw (π : HybridRule n Seed)
    (v : FiniteObserverWorld n Seed) : Measure Point :=
  (∑ i : Fin n, if π.individualMeasureAccepted v i then Measure.dirac (v.2.2.1 i,v.2.1 i) else 0) +
    π.acceptedAnonymousMeasure v

noncomputable def HybridRule.acceptedPointMeasure (π : HybridRule n Seed)
    (v : FiniteObserverWorld n Seed) : FiniteMeasure Point :=
  ⟨π.acceptedPointMeasureRaw v,by
    unfold HybridRule.acceptedPointMeasureRaw HybridRule.acceptedAnonymousMeasure
    letI hfin : ∀ i : Fin n, IsFiniteMeasure (if π.individualMeasureAccepted v i then
        Measure.dirac (v.2.2.1 i,v.2.1 i) else 0) := by
      intro i
      split_ifs <;> infer_instance
    infer_instance⟩

variable [MeasurableSpace Seed]

lemma HybridRule.measurable_individualMeasureAction (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (i : Fin n) : Measurable (fun v => π.individualMeasureAction v i) := by
  have hr : Measurable (fun v : FiniteObserverWorld n Seed => v.2.2.2) := by fun_prop
  have ht : Measurable (fun v : FiniteObserverWorld n Seed => v.2.2.1 i) := by fun_prop
  have hx : Measurable (fun v : FiniteObserverWorld n Seed => v.2.1 i) := by fun_prop
  have hH := Model.measurable_history Finset.univ
    (x := fun v : FiniteObserverWorld n Seed => v.2.1) (u := fun v => v.2.2.1)
    (fun j => by fun_prop) (fun j => by fun_prop) ht
  have hξ : Measurable (fun v : FiniteObserverWorld n Seed => finitePast v.1 (v.2.2.1 i)) :=
    measurable_finitePast.comp (measurable_fst.prodMk ht)
  exact hπ.1.comp (hr.prodMk (ht.prodMk (measurable_const.prodMk (hx.prodMk (hH.prodMk hξ)))))

lemma HybridRule.measurable_anonymousMeasureAction (π : HybridRule n Seed) (hπ : π.IsMeasurable) :
    Measurable (fun q : FiniteObserverWorld n Seed × Point => π.anonymousMeasureAction q.1 q.2) := by
  have hr : Measurable (fun q : FiniteObserverWorld n Seed × Point => q.1.2.2.2) := by fun_prop
  have ht : Measurable (fun q : FiniteObserverWorld n Seed × Point => q.2.1) := by fun_prop
  have hx : Measurable (fun q : FiniteObserverWorld n Seed × Point => q.2.2) := by fun_prop
  have hH := Model.measurable_history Finset.univ
    (x := fun q : FiniteObserverWorld n Seed × Point => q.1.2.1) (u := fun q => q.1.2.2.1)
    (fun j => by fun_prop) (fun j => by fun_prop) ht
  have hξ : Measurable (fun q : FiniteObserverWorld n Seed × Point => finitePast q.1.1 q.2.1) :=
    measurable_finitePast.comp ((measurable_fst.comp measurable_fst).prodMk ht)
  exact hπ.2.comp (hr.prodMk ((ht.prodMk hx).prodMk (hH.prodMk hξ)))

lemma HybridRule.measurableSet_individualMeasureAccepted (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (i : Fin n) : MeasurableSet {v | π.individualMeasureAccepted v i} :=
  ((show Measurable (fun v : FiniteObserverWorld n Seed => v.2.2.1 i) by fun_prop) measurableSet_Icc).inter
    ((π.measurable_individualMeasureAction hπ i) (measurableSet_singleton true))

lemma HybridRule.measurableSet_anonymousMeasureAccepted (π : HybridRule n Seed) (hπ : π.IsMeasurable) :
    MeasurableSet {q : FiniteObserverWorld n Seed × Point | π.anonymousMeasureAccepted q.1 q.2} :=
  ((show Measurable (fun q : FiniteObserverWorld n Seed × Point => q.2.1) by fun_prop) measurableSet_Icc).inter
    ((π.measurable_anonymousMeasureAction hπ) (measurableSet_singleton true))

lemma HybridRule.measurable_acceptedAnonymousMeasure (π : HybridRule n Seed) (hπ : π.IsMeasurable) :
    Measurable π.acceptedAnonymousMeasure := by
  let κ : Kernel (FiniteObserverWorld n Seed) Point :=
    ⟨fun v => (v.1 : Measure Point),measurable_subtype_coe.comp measurable_fst⟩
  have hfinite (v : FiniteObserverWorld n Seed) : IsFiniteMeasure (κ v) := by
    change IsFiniteMeasure (v.1 : Measure Point)
    infer_instance
  apply Measure.measurable_of_measurable_coe
  intro S hS
  have hT : MeasurableSet {q : FiniteObserverWorld n Seed × Point |
      q.2 ∈ S ∧ π.anonymousMeasureAccepted q.1 q.2} :=
    (hS.preimage measurable_snd).inter (π.measurableSet_anonymousMeasureAccepted hπ)
  have hm := Kernel.measurable_kernel_prodMk_left_of_finite hT hfinite
  have he : (fun v : FiniteObserverWorld n Seed => π.acceptedAnonymousMeasure v S) =
      fun v => κ v (Prod.mk v ⁻¹' {q : FiniteObserverWorld n Seed × Point |
        q.2 ∈ S ∧ π.anonymousMeasureAccepted q.1 q.2}) := by
    funext v
    rw [HybridRule.acceptedAnonymousMeasure,Measure.restrict_apply hS]
    rfl
  rw [he]
  exact hm

lemma HybridRule.measurable_acceptedPointMeasureRaw (π : HybridRule n Seed) (hπ : π.IsMeasurable) :
    Measurable π.acceptedPointMeasureRaw := by
  apply Measurable.add _ (π.measurable_acceptedAnonymousMeasure hπ)
  apply Finset.measurable_fun_sum
  intro i _
  exact Measurable.ite (π.measurableSet_individualMeasureAccepted hπ i)
    (Measure.measurable_dirac.comp (by fun_prop)) measurable_const

lemma HybridRule.measurable_acceptedPointMeasure (π : HybridRule n Seed) (hπ : π.IsMeasurable) :
    Measurable π.acceptedPointMeasure :=
  (π.measurable_acceptedPointMeasureRaw hπ).subtype_mk

end ProphetSecretary.Limiting
