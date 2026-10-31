import ProphetSecretary.Limiting.CountableObservations
import Mathlib.Logic.Denumerable

/-!
# Analytical labels for countably many actual candidates

Individual labels are observed. A Poisson construction label is used only to
identify an actual point in the execution; anonymous decision callbacks do not
receive this label, its band, or the array length.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting.CountableInstance

abbrev Candidate := ℕ ⊕ (ℕ × ℕ)

noncomputable def configurationPoint (j : ℕ) (ω : Configuration) : Point :=
  if hj : j < ω.1 then ω.2 ⟨j,hj⟩ else (1,0)

lemma measurable_configurationPoint (j : ℕ) : Measurable (configurationPoint j) := by
  apply measurable_of_configuration_branches
  intro N
  by_cases hj : j < N
  · simpa only [configurationPoint,configurationMk,dif_pos hj] using
      (measurable_pi_apply (⟨j,hj⟩ : Fin N))
  · simpa only [configurationPoint,configurationMk,dif_neg hj] using
      (measurable_const : Measurable (fun _ : Fin N → Point => ((1 : ℝ),(0 : ℝ))))

lemma measurableSet_configurationPoint_present (j : ℕ) :
    MeasurableSet {ω : Configuration | j < ω.1} :=
  measurable_configuration_count (Set.to_countable _).measurableSet

noncomputable def candidatePoint {Seed : Type*} (v : CompleteWorld Seed) : Candidate → Point
  | Sum.inl i => (v.2.2.1 i,v.2.1 i)
  | Sum.inr kj => configurationPoint kj.2 (v.1 kj.1)

def candidatePresent {Seed : Type*} (v : CompleteWorld Seed) : Candidate → Prop
  | Sum.inl _ => True
  | Sum.inr kj => kj.2 < (v.1 kj.1).1

lemma measurable_candidatePoint {Seed : Type*} [MeasurableSpace Seed] (i : Candidate) :
    Measurable (fun v : CompleteWorld Seed => candidatePoint v i) := by
  cases i with
  | inl i =>
    exact ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))).prodMk
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  | inr kj =>
    exact (measurable_configurationPoint kj.2).comp ((measurable_pi_apply kj.1).comp measurable_fst)

lemma measurableSet_candidatePresent {Seed : Type*} [MeasurableSpace Seed] (i : Candidate) :
    MeasurableSet {v : CompleteWorld Seed | candidatePresent v i} := by
  cases i with
  | inl i => exact MeasurableSet.univ
  | inr kj =>
    exact (measurableSet_configurationPoint_present kj.2).preimage
      ((measurable_pi_apply kj.1).comp measurable_fst)

noncomputable def candidateEnumeration : Candidate ≃ ℕ := Denumerable.eqv Candidate

noncomputable def codePoint {Seed : Type*} (v : CompleteWorld Seed) (i : ℕ) : Point :=
  candidatePoint v (candidateEnumeration.symm i)

noncomputable def codePresent {Seed : Type*} (v : CompleteWorld Seed) (i : ℕ) : Prop :=
  candidatePresent v (candidateEnumeration.symm i)

lemma measurable_codePoint {Seed : Type*} [MeasurableSpace Seed] (i : ℕ) :
    Measurable (fun v : CompleteWorld Seed => codePoint v i) :=
  measurable_candidatePoint _

lemma measurableSet_codePresent {Seed : Type*} [MeasurableSpace Seed] (i : ℕ) :
    MeasurableSet {v : CompleteWorld Seed | codePresent v i} :=
  measurableSet_candidatePresent _

lemma individual_candidate_present {Seed : Type*} (v : CompleteWorld Seed) (i : ℕ) :
    codePresent v (candidateEnumeration (Sum.inl i)) := by
  simp only [codePresent,Equiv.symm_apply_apply,candidatePresent]

lemma individual_candidate_point {Seed : Type*} (v : CompleteWorld Seed) (i : ℕ) :
    codePoint v (candidateEnumeration (Sum.inl i)) = (v.2.2.1 i,v.2.1 i) := by
  simp only [codePoint,Equiv.symm_apply_apply,candidatePoint]

lemma poisson_candidate_present {Seed : Type*} (v : CompleteWorld Seed) (k : ℕ) (j : Fin (v.1 k).1) :
    codePresent v (candidateEnumeration (Sum.inr (k,j.val))) := by
  simpa only [codePresent,Equiv.symm_apply_apply,candidatePresent] using j.isLt

lemma poisson_candidate_point {Seed : Type*} (v : CompleteWorld Seed) (k : ℕ) (j : Fin (v.1 k).1) :
    codePoint v (candidateEnumeration (Sum.inr (k,j.val))) = (v.1 k).2 j := by
  simp only [codePoint,Equiv.symm_apply_apply,candidatePoint,configurationPoint,dif_pos j.isLt]

end ProphetSecretary.Limiting.CountableInstance
