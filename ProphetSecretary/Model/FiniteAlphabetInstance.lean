import ProphetSecretary.Model.TrainingCoordinates
import ProphetSecretary.Probability.FiniteProbabilityGrid

/-!
# Product instances on a finite offer alphabet

Finite integer atom counts give an actual finite family of independent
instances. The value alphabet need not be injectively encoded; all offer
values are explicitly assumed nonnegative. General finite-support laws are
represented separately from the policies acting on their observations.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model
open ProphetSecretary.Probability

variable {n : ℕ} {Θ : Type*} [Fintype Θ] [MeasurableSpace Θ] [MeasurableSingletonClass Θ]

noncomputable def finiteAlphabetInstance (v : Θ → ℝ) (hv : ∀ a, 0≤v a)
    (p : Fin n → Θ → ℝ) (hp : ∀ i, p i∈stdSimplex ℝ Θ) : Instance n where
  law i := (finiteSimplexLaw (p i) (hp i)).map v
  probability _ :=  Measure.isProbabilityMeasure_map (measurable_of_finite v).aemeasurable
  nonnegative _ :=  (ae_map_iff (measurable_of_finite v).aemeasurable measurableSet_Ici).mpr
    (Filter.Eventually.of_forall hv)

lemma finiteAlphabetInstance_value_map (v : Θ → ℝ) (hv : ∀ a, 0≤v a)
    (p : Fin n → Θ → ℝ) (hp : ∀ i, p i∈stdSimplex ℝ Θ) :
    MeasurePreserving (fun a i => v (a i)) (Measure.pi (fun i => finiteSimplexLaw (p i) (hp i)))
      (finiteAlphabetInstance v hv p hp).valuesLaw :=
  measurePreserving_pi _ _ (fun _ => ⟨measurable_of_finite v,rfl⟩)

lemma finiteAlphabetInstance_supported (v : Θ → ℝ) (hv : ∀ a, 0≤v a)
    (p : Fin n → Θ → ℝ) (hp : ∀ i, p i∈stdSimplex ℝ Θ) (i : Fin n) :
    ∀ᵐ x ∂(finiteAlphabetInstance v hv p hp).law i, x∈Set.range v := by
  apply (ae_map_iff (measurable_of_finite v).aemeasurable (Set.finite_range v).measurableSet).mpr
  exact Filter.Eventually.of_forall fun a => ⟨a,rfl⟩

noncomputable def probabilityGridInstance (v : Θ → ℝ) (hv : ∀ a, 0≤v a)
    {N : ℕ} (hN : 0<N) (a : Fin n → ProbabilityCounts Θ N) : Instance n :=
  finiteAlphabetInstance v hv (fun i => countProbability (a i)) (fun i => countProbability_simplex hN (a i))

lemma rounded_instance_in_finite_family [DecidableEq Θ] (v : Θ → ℝ) (hv : ∀ a, 0≤v a)
    (p : Fin n → Θ → ℝ) (hp : ∀ i, p i∈stdSimplex ℝ Θ) {N : ℕ} (hN : 0<N) (z : Θ) :
    ∃ a : Fin n → ProbabilityCounts Θ N,
      probabilityGridInstance v hv hN a = finiteAlphabetInstance v hv
        (fun i => roundedProbability (p i) N z) (fun i => roundedProbability_simplex (p i) (hp i) hN z) := by
  classical
  choose a ha using fun i => roundedProbability_mem_finite_grid (p i) (hp i) hN z
  refine ⟨a,?_⟩
  have hEq : (fun i => countProbability (a i))=(fun i => roundedProbability (p i) N z) := funext ha
  unfold probabilityGridInstance
  congr 1

abbrev LearningArrayIndex (n k : ℕ) := Fin n ⊕ (Fin n × Fin k)

def LearningArrayIndex.variableIndex {k : ℕ} : LearningArrayIndex n k → Fin n := Sum.elim id Prod.fst

def alphabetData {k : ℕ} (v : Θ → ℝ) (a : LearningArrayIndex n k → Θ) :
    (Fin n → ℝ) × Reservoir n k :=
  (fun i => v (a (.inl i)),fun i j => v (a (.inr (i,j))))

lemma alphabetData_measurePreserving {k : ℕ} (v : Θ → ℝ) (hv : ∀ a, 0≤v a)
    (p : Fin n → Θ → ℝ) (hp : ∀ i, p i∈stdSimplex ℝ Θ) :
    MeasurePreserving (alphabetData (k:=k) v)
      (Measure.pi (fun q : LearningArrayIndex n k => finiteSimplexLaw (p q.variableIndex) (hp q.variableIndex)))
      ((finiteAlphabetInstance v hv p hp).valuesLaw.prod ((finiteAlphabetInstance v hv p hp).reservoirLaw k)) := by
  let P := finiteAlphabetInstance v hv p hp
  have hValue : MeasurePreserving (fun a q => v (a q))
      (Measure.pi (fun q : LearningArrayIndex n k => finiteSimplexLaw (p q.variableIndex) (hp q.variableIndex)))
      (Measure.pi (fun q : LearningArrayIndex n k => P.law q.variableIndex)) :=
    measurePreserving_pi _ _ (fun _ => ⟨measurable_of_finite v,rfl⟩)
  have hSplit := measurePreserving_sumPiEquivProdPi (fun q : LearningArrayIndex n k => P.law q.variableIndex)
  exact ((MeasurePreserving.id P.valuesLaw).prod (P.reservoirCoordinates_symm_measurePreserving k)).comp
    (hSplit.comp hValue)

end ProphetSecretary.Model
