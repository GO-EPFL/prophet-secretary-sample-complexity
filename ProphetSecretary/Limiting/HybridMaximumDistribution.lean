import ProphetSecretary.Limiting.PoissonVoid
import ProphetSecretary.Limiting.HybridOutcomes

/-!
# The distribution of the hybrid prophet maximum

The retained-value product and the Poisson void event are independent because
the actual value law is their product. Atoms at the tested level are retained.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal ENNReal

namespace ProphetSecretary.Limiting

variable {n : ℕ}

lemma hybridMaximum_le_iff {a t : ℝ} (ht : 0 ≤ t) (v : Configuration × (Fin n → ℝ)) :
    hybridMaximum a v ≤ t ↔ a ≤ t ∧ (∀ i, v.2 i ≤ t) ∧ (∀ j, (v.1.2 j).2 ≤ t) := by
  constructor
  · intro h
    have hM := (le_max_right a (Model.Instance.maximum (combinedValues v.2 v.1.2))).trans h
    refine ⟨(le_max_left _ _).trans h, ?_, ?_⟩
    · intro i
      simpa [combinedValues] using (Model.Instance.le_maximum (combinedValues v.2 v.1.2) (Fin.castAdd v.1.1 i)).trans hM
    · intro j
      simpa [combinedValues] using (Model.Instance.le_maximum (combinedValues v.2 v.1.2) (Fin.natAdd n j)).trans hM
  · rintro ⟨ha,hx,hp⟩
    apply max_le ha
    apply Model.Instance.maximum_le _ ht
    intro k
    exact Fin.addCases (fun i => by simpa [combinedValues] using hx i)
      (fun j => by simpa [combinedValues] using hp j) k

lemma measurableSet_no_marks_above (t : ℝ) :
    MeasurableSet {ω : Configuration | ∀ j, (ω.2 j).2 ≤ t} := by
  have he : {ω : Configuration | ∀ j, (ω.2 j).2 ≤ t} =
      pointCount (univ ×ˢ Ioi t) ⁻¹' {0} := by
    ext ω
    simp [pointCount_eq_zero_iff]
  rw [he]
  exact (measurable_pointCount (MeasurableSet.univ.prod measurableSet_Ioi)) (measurableSet_singleton 0)

lemma hybridMaximum_probability_Iic (P : Model.Instance n) (μ : FiniteMeasure ℝ)
    {a t : ℝ} (ht : 0 ≤ t) (hat : a ≤ t) :
    hybridValueLaw P μ {v | hybridMaximum a v ≤ t} =
      ENNReal.ofReal (Real.exp (-(μ : Measure ℝ).real (Ioi t))) *
        ∏ i, P.law i (Iic t) := by
  have he : {v : Configuration × (Fin n → ℝ) | hybridMaximum a v ≤ t} =
      {ω : Configuration | ∀ j, (ω.2 j).2 ≤ t} ×ˢ (univ.pi (fun _ : Fin n => Iic t)) := by
    ext v
    simp only [mem_setOf_eq, hybridMaximum_le_iff ht, hat, true_and, mem_prod,
      mem_pi, mem_univ, forall_const]
    exact and_comm
  rw [he,hybridValueLaw,Measure.prod_prod,configuration_no_marks_above_probability]
  change _ * Measure.pi P.law (univ.pi (fun _ : Fin n => Iic t)) = _
  rw [Measure.pi_pi]

end ProphetSecretary.Limiting
