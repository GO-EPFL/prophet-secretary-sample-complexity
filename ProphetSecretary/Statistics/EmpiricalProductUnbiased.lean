import ProphetSecretary.Model.EmpiricalMomentsMeasurability
import ProphetSecretary.Model.TrainingCoordinates

/-!
# Unbiased evaluation of bounded fixed functions under the product empirical law

One sample index is chosen independently for each identity. At every fixed index
vector, the selected independent training coordinates have exactly the true
product law. Independent index averaging and Fubini give unbiasedness for every
bounded measurable function fixed before training.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

omit [NeZero k] in
lemma Instance.fixedSampleVector_measurePreserving (P : Instance n) (a : Fin n → Fin k) :
    MeasurePreserving (fun y : Reservoir n k => fun i => max 0 (y i (a i)))
      (P.reservoirLaw k) P.valuesLaw := by
  have hi (i : Fin n) : MeasurePreserving (fun y : Fin k → ℝ => max 0 (y (a i)))
      (Measure.pi (fun _ : Fin k => P.law i)) (P.law i) := by
    have hp := measurePreserving_eval (fun _ : Fin k => P.law i) (a i)
    refine ⟨measurable_const.max (measurable_pi_apply (a i)),?_⟩
    have he : (fun y : Fin k → ℝ => max 0 (y (a i))) =ᵐ[Measure.pi (fun _ : Fin k => P.law i)]
        (fun y => y (a i)) :=
      (hp.quasiMeasurePreserving.ae (P.nonnegative i)).mono fun _ hy => max_eq_right hy
    rw [Measure.map_congr he]
    exact hp.map_eq
  exact measurePreserving_pi _ _ hi

lemma measurable_empiricalProduct_fixed {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) :
    Measurable (fun y : Reservoir n k => ∫ x, f x ∂(totalEmpiricalInstance y).valuesLaw) := by
  have hm : Measurable (fun q : Reservoir n k × (Fin n → Fin k) =>
      f (fun i => max 0 (q.1 i (q.2 i)))) := by
    apply measurable_from_prod_countable_left
    intro a
    exact hf.comp (measurable_pi_lambda _ (fun i => measurable_const.max
      ((measurable_pi_apply (a i)).comp (measurable_pi_apply i))))
  have hInt := (hm.stronglyMeasurable.integral_prod_right' (ν:=empiricalIndicesLaw n k)).measurable
  convert hInt using 1
  funext y
  have hp := totalEmpiricalValues_measurePreserving y
  have h := integral_map (μ:=empiricalIndicesLaw n k) hp.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hp.map_eq] at h
  exact h

lemma Instance.integrable_empiricalProduct_bounded_fixed (P : Instance n)
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, ‖f x‖≤C) :
    Integrable (fun y : Reservoir n k => ∫ x, f x ∂(totalEmpiricalInstance y).valuesLaw) (P.reservoirLaw k) := by
  apply Integrable.of_bound (measurable_empiricalProduct_fixed hf).aestronglyMeasurable C
  exact Eventually.of_forall fun y => by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ:=(totalEmpiricalInstance y).valuesLaw) (Eventually.of_forall hC)

/-- This statement is fixed-function unbiasedness, with no data-selected
function or coefficient in its quantifiers. -/
theorem Instance.integral_empiricalProduct_bounded_fixed (P : Instance n)
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, ‖f x‖≤C) :
    (∫ y : Reservoir n k, (∫ x, f x ∂(totalEmpiricalInstance y).valuesLaw)
      ∂P.reservoirLaw k) = ∫ x, f x ∂P.valuesLaw := by
  let F : Reservoir n k × (Fin n → Fin k) → ℝ :=
    fun q => f (fun i => max 0 (q.1 i (q.2 i)))
  have hF : Measurable F := by
    apply measurable_from_prod_countable_left
    intro a
    exact hf.comp (measurable_pi_lambda _ (fun i => measurable_const.max
      ((measurable_pi_apply (a i)).comp (measurable_pi_apply i))))
  have hI : Integrable F ((P.reservoirLaw k).prod (empiricalIndicesLaw n k)) :=
    Integrable.of_bound hF.aestronglyMeasurable C (Eventually.of_forall fun q => hC _)
  have hy (y : Reservoir n k) :
      (∫ x, f x ∂(totalEmpiricalInstance y).valuesLaw) =
      ∫ a, F (y,a) ∂empiricalIndicesLaw n k := by
    have hp := totalEmpiricalValues_measurePreserving y
    have h := integral_map (μ:=empiricalIndicesLaw n k) hp.measurable.aemeasurable hf.aestronglyMeasurable
    rw [hp.map_eq] at h
    exact h
  have ha (a : Fin n → Fin k) : (∫ y, F (y,a) ∂P.reservoirLaw k) = ∫ x, f x ∂P.valuesLaw := by
    have hp := P.fixedSampleVector_measurePreserving (k:=k) a
    have h := integral_map (μ:=P.reservoirLaw k) hp.measurable.aemeasurable hf.aestronglyMeasurable
    rw [hp.map_eq] at h
    exact h.symm
  simp_rw [hy]
  rw [integral_integral_swap hI]
  simp_rw [ha]
  simp

end ProphetSecretary.Model
