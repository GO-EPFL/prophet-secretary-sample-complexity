import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.Data.Finset.Basic

/-!
# Measurably coding a finite set of possible observations

Off-alphabet observations receive none. The code is defined on every raw input,
so finite response patching has a fixed fallback on impossible observations.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Probability
variable {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass A]

noncomputable def finiteObservationCode (D : Finset A) (a : A) : Option {x : A // x∈D} :=
  if h : a∈D then some ⟨a,h⟩ else none

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma finiteObservationCode_some (D : Finset A) (a : A) (ha : a∈D) :
    finiteObservationCode D a=some ⟨a,ha⟩ := by simp only [finiteObservationCode,dif_pos ha]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma finiteObservationCode_none (D : Finset A) (a : A) (ha : a∉D) :
    finiteObservationCode D a=none := by simp only [finiteObservationCode,dif_neg ha]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma finiteObservationCode_preimage_some (D : Finset A) (a : {x : A // x∈D}) :
    (finiteObservationCode D) ⁻¹' {some a}={a.val} := by
  ext x
  simp only [Set.mem_preimage,Set.mem_singleton_iff]
  constructor
  · intro hx
    unfold finiteObservationCode at hx
    split_ifs at hx with h
    · exact congrArg Subtype.val (Option.some.inj hx)
  · intro hx
    subst x
    exact finiteObservationCode_some D a.val a.property

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma finiteObservationCode_preimage_none (D : Finset A) :
    (finiteObservationCode D) ⁻¹' {none}=(D:Set A)ᶜ := by
  ext a
  simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_compl_iff,Finset.mem_coe]
  by_cases ha : a∈D <;> simp [finiteObservationCode,ha]

instance finiteObservationCode_measurableSpace (D : Finset A) : MeasurableSpace (Option {x : A // x∈D}) := ⊤

instance finiteObservationCode_discrete (D : Finset A) : DiscreteMeasurableSpace (Option {x : A // x∈D}) := ⟨fun _ => trivial⟩

lemma measurable_finiteObservationCode (D : Finset A) : Measurable (finiteObservationCode D) := by
  apply measurable_to_countable'
  intro x
  cases x with
  | none => rw [finiteObservationCode_preimage_none];exact D.finite_toSet.measurableSet.compl
  | some a => rw [finiteObservationCode_preimage_some];exact measurableSet_singleton _

noncomputable def finiteObservationLookup {B : Type*} (D : Finset A) (fallback : B) (v : {a : A // a∈D} → B) (a : A) : B :=
  match finiteObservationCode D a with
  | none => fallback
  | some x => v x

lemma measurable_finiteObservationLookup {B : Type*} [MeasurableSpace B]
    (D : Finset A) (fallback : B) (v : {a : A // a∈D} → B) :
    Measurable (finiteObservationLookup D fallback v) := by
  let g : Option {a : A // a∈D} → B := fun o => match o with | none => fallback | some x => v x
  exact (measurable_of_finite g).comp (measurable_finiteObservationCode D)

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma finiteObservationLookup_on {B : Type*} (D : Finset A) (fallback : B) (v : {a : A // a∈D} → B)
    (a : A) (ha : a∈D) : finiteObservationLookup D fallback v a=v ⟨a,ha⟩ := by
  simp only [finiteObservationLookup,finiteObservationCode_some D a ha]

omit [MeasurableSpace A] [MeasurableSingletonClass A] in
lemma finiteObservationLookup_off {B : Type*} (D : Finset A) (fallback : B) (v : {a : A // a∈D} → B)
    (a : A) (ha : a∉D) : finiteObservationLookup D fallback v a=fallback := by
  simp only [finiteObservationLookup,finiteObservationCode_none D a ha]

end ProphetSecretary.Probability
