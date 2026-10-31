import ProphetSecretary.Statistics.EmpiricalRowShuffles
import Mathlib.Probability.Moments.Variance

/-!
# Independent complete-instance training blocks

Transposing the actual independent training array yields k independent offer
vectors, each with the original complete product law. This is an exact
measure-preserving equivalence, not an assumed independence interface.
-/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n k : ℕ}

noncomputable def trainingColumns : ((Fin n × Fin k) → ℝ) ≃ᵐ (Fin k → (Fin n → ℝ)) where
  toFun a j i := a (i,j)
  invFun b q := b q.2 q.1
  left_inv a := rfl
  right_inv b := rfl
  measurable_toFun := by
    change Measurable (fun a : ((Fin n × Fin k) → ℝ) => fun j i => a (i,j))
    exact measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun i => measurable_pi_apply (i,j)
  measurable_invFun := by
    change Measurable (fun b : Fin k → (Fin n → ℝ) => fun q : Fin n × Fin k => b q.2 q.1)
    exact measurable_pi_lambda _ fun q : Fin n × Fin k => (measurable_pi_apply q.1).comp (measurable_pi_apply q.2)

lemma trainingColumns_symm_measurePreserving (P : Instance n) :
    MeasurePreserving (trainingColumns (n := n) (k := k)).symm
      (Measure.pi (fun _ : Fin k => P.valuesLaw)) (P.trainingCoordinateLaw k) := by
  have hm := (trainingColumns (n := n) (k := k)).symm.measurable
  refine ⟨hm,?_⟩
  haveI : IsProbabilityMeasure ((Measure.pi (fun _ : Fin k => P.valuesLaw)).map trainingColumns.symm) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have he : trainingColumns.symm ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun j : Fin k => Set.univ.pi (fun i : Fin n => s (i,j))) := by
    ext b
    simp only [mem_preimage,mem_pi,mem_univ,forall_true_left]
    constructor
    · intro h j i
      exact h (i,j)
    · intro h q
      exact h q.2 q.1
  rw [he,Measure.pi_pi]
  simp only [Instance.valuesLaw,Measure.pi_pi]
  rw [← Finset.univ_product_univ,Finset.prod_product]
  exact Finset.prod_comm

lemma trainingColumns_measurePreserving (P : Instance n) :
    MeasurePreserving (trainingColumns (n := n) (k := k))
      (P.trainingCoordinateLaw k) (Measure.pi (fun _ : Fin k => P.valuesLaw)) :=
  (trainingColumns_symm_measurePreserving P).symm trainingColumns.symm

lemma trainingColumn_measurePreserving (P : Instance n) (j : Fin k) :
    MeasurePreserving (fun a : (Fin n × Fin k) → ℝ => fun i => a (i,j))
      (P.trainingCoordinateLaw k) P.valuesLaw :=
  (measurePreserving_eval (fun _ : Fin k => P.valuesLaw) j).comp (trainingColumns_measurePreserving P)

lemma measurable_empiricalBlockAverage [NeZero k] {F : (Fin n → ℝ) → ℝ} (hF : Measurable F) :
    Measurable (empiricalBlockAverage (k := k) F) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro j _
  exact hF.comp (measurable_pi_lambda _ fun i => measurable_pi_apply (i,j))

lemma integral_trainingColumn (P : Instance n) {F : (Fin n → ℝ) → ℝ}
    (hF : Measurable F) (j : Fin k) :
    (∫ a, F (fun i => a (i,j)) ∂P.trainingCoordinateLaw k) = ∫ x, F x ∂P.valuesLaw := by
  have hp := trainingColumn_measurePreserving P j
  have hi := integral_map (μ := P.trainingCoordinateLaw k) hp.measurable.aemeasurable hF.aestronglyMeasurable
  rw [hp.map_eq] at hi
  exact hi.symm

lemma integral_empiricalBlockAverage [NeZero k] (P : Instance n) {F : (Fin n → ℝ) → ℝ}
    (hF : Measurable F) (hFI : Integrable F P.valuesLaw) :
    (∫ a, empiricalBlockAverage (k := k) F a ∂P.trainingCoordinateLaw k) = ∫ x, F x ∂P.valuesLaw := by
  have hI (j : Fin k) : Integrable (fun a : (Fin n × Fin k) → ℝ => F (fun i => a (i,j))) (P.trainingCoordinateLaw k) :=
    (trainingColumn_measurePreserving P j).integrable_comp_of_integrable hFI
  unfold empiricalBlockAverage
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun j _ => hI j)]
  simp_rw [integral_trainingColumn P hF]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← mul_assoc,inv_mul_cancel₀ (by exact_mod_cast NeZero.ne k),one_mul]

/-- The ordinary iid block mean has exactly the original variance divided by
k; block independence is supplied by the constructed transposition law. -/
lemma variance_empiricalBlockAverage [NeZero k] (P : Instance n) {F : (Fin n → ℝ) → ℝ}
    (hF : Measurable F) (hF2 : MemLp F 2 P.valuesLaw) :
    variance (empiricalBlockAverage (k := k) F) (P.trainingCoordinateLaw k) = variance F P.valuesLaw/(k : ℝ) := by
  let G : (Fin k → (Fin n → ℝ)) → ℝ := fun b => (k : ℝ)⁻¹ * ∑ j : Fin k, F (b j)
  have hGm : Measurable G := by
    apply Measurable.const_mul
    exact Finset.measurable_sum _ (fun j _ => hF.comp (measurable_pi_apply j))
  have hp := trainingColumns_measurePreserving (k := k) P
  have hVar := variance_map (μ := P.trainingCoordinateLaw k) (Y := trainingColumns) (X := G)
    (by rw [hp.map_eq]; exact hGm.aemeasurable) hp.measurable.aemeasurable
  rw [hp.map_eq] at hVar
  change variance (G ∘ trainingColumns) (P.trainingCoordinateLaw k) = _
  rw [← hVar]
  dsimp only [G]
  rw [variance_const_mul]
  have hs := variance_sum_pi (μ := fun _ : Fin k => P.valuesLaw) (X := fun _ => F) (fun _ => hF2)
  have he : (∑ j : Fin k, (fun b : Fin k → (Fin n → ℝ) => F (b j))) = fun b => ∑ j : Fin k, F (b j) := by
    funext b
    simp only [Finset.sum_apply]
  rw [← he,hs]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp

end ProphetSecretary.Statistics
