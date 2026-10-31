import ProphetSecretary.Limiting.CountableClockReplacement

/-!
# Independent replacement of an actual countable individual value

The candidate identity, arrival clock, other values, anonymous configuration
and independent seed are retained. Replacing the value by a fresh draw from
its own marginal preserves the actual full product law. Counterfactual fixed
values below are analytical inputs to the same executed callback.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

def replaceIndividualValue (i : ℕ) (z : CompleteWorld Seed × ℝ) : CompleteWorld Seed :=
  (z.1.1,(Function.update z.1.2.1 i z.2,z.1.2.2))

lemma replaceIndividualValue_self (i : ℕ) (v : CompleteWorld Seed) :
    replaceIndividualValue i (v,v.2.1 i)=v := by
  unfold replaceIndividualValue
  rw [Function.update_eq_self]

lemma candidatePresent_replaceIndividualValue (i : ℕ) (z : CompleteWorld Seed × ℝ) (c : Candidate) :
    candidatePresent (replaceIndividualValue i z) c ↔ candidatePresent z.1 c := by cases c <;> rfl

lemma candidatePoint_replaceIndividualValue_of_ne (i : ℕ) (z : CompleteWorld Seed × ℝ)
    (c : Candidate) (hc : c ≠ Sum.inl i) :
    candidatePoint (replaceIndividualValue i z) c=candidatePoint z.1 c := by
  cases c with
  | inl j =>
    have hji : j ≠ i := fun h => hc (congrArg Sum.inl h)
    simp only [candidatePoint,replaceIndividualValue,Function.update_of_ne hji]
  | inr kj => rfl

lemma codeTime_replaceIndividualValue (i : ℕ) (z : CompleteWorld Seed × ℝ) (k : ℕ) :
    codeTime (replaceIndividualValue i z) k=codeTime z.1 k := by
  unfold codeTime codePoint
  cases candidateEnumeration.symm k <;> rfl

variable [MeasurableSpace Seed]

lemma measurable_replaceIndividualValue (i : ℕ) : Measurable (replaceIndividualValue (Seed := Seed) i) := by
  have hValues : Measurable (fun z : CompleteWorld Seed × ℝ => Function.update z.1.2.1 i z.2) := by
    apply measurable_pi_lambda
    intro j
    by_cases hji : j=i
    · subst j
      simpa only [Function.update_self] using (measurable_snd : Measurable (fun z : CompleteWorld Seed × ℝ => z.2))
    · simpa only [Function.update_of_ne hji,Function.comp_def] using
        (measurable_pi_apply j).comp (measurable_fst.comp (measurable_snd.comp measurable_fst))
  exact (measurable_fst.comp measurable_fst).prodMk
    (hValues.prodMk (measurable_snd.comp (measurable_snd.comp measurable_fst)))

lemma replaceIndividualValue_measurePreserving (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ) :
    MeasurePreserving (replaceIndividualValue i)
      ((B.completeWorldLaw ν).prod (B.individuals i : Measure ℝ)) (B.completeWorldLaw ν) := by
  have hSwap := Model.measurePreserving_swap_last B.individualValuesLaw
    (individualClocksLaw.prod ν) (B.individuals i : Measure ℝ)
  have hReplace := ProphetSecretary.Probability.infinite_replaceCoordinate_measurePreserving
    (fun j => (B.individuals j : Measure ℝ)) i
  have hInner := (hReplace.prod (MeasurePreserving.id (individualClocksLaw.prod ν))).comp hSwap
  have hAssoc := measurePreserving_prodAssoc B.bandConfigurationsLaw
    (B.individualWorldLaw ν) (B.individuals i : Measure ℝ)
  exact ((MeasurePreserving.id B.bandConfigurationsLaw).prod hInner).comp hAssoc

end ProphetSecretary.Limiting.CountableInstance
