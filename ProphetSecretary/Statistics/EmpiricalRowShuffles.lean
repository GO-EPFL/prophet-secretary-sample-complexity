import ProphetSecretary.Model.EmpiricalMomentsMeasurability
import ProphetSecretary.Model.TrainingCoordinates
import Mathlib.Data.ZMod.Basic

/-!
# Cyclic row shuffles of the actual independent training array

Independent uniform cyclic shifts of the sample rows preserve the training
law. Averaging the ordinary block sample mean over these shifts gives exactly
the product-empirical expectation. The shifts are analytical auxiliary
randomness, with no added observation supplied to an online policy.
-/
open MeasureTheory Set
open scoped BigOperators Classical ENNReal
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

omit [NeZero k] in
lemma empiricalIndexLaw_equiv_measurePreserving (e : Equiv.Perm (Fin k)) :
    MeasurePreserving e (empiricalIndexLaw k) (empiricalIndexLaw k) := by
  have hm : Measurable e := measurable_of_finite _
  refine ⟨hm,?_⟩
  simp only [empiricalIndexLaw,Measure.map_smul,Measure.map_finset_sum' hm.aemeasurable,Measure.map_dirac' hm]
  congr 1
  exact Equiv.sum_comp e (fun j => Measure.dirac j)

lemma integrable_empiricalIndicesLaw (F : (Fin n → Fin k) → ℝ) :
    Integrable F (empiricalIndicesLaw n k) := by
  apply Integrable.of_bound (measurable_of_finite F).aestronglyMeasurable (∑ a : Fin n → Fin k, |F a|)
  exact Filter.Eventually.of_forall fun a => by
    rw [Real.norm_eq_abs]
    exact Finset.single_le_sum (fun b _ => abs_nonneg (F b)) (Finset.mem_univ a)

noncomputable def shiftedIndices (j : Fin k) (a : Fin n → Fin k) : Fin n → Fin k := fun i => j+a i

lemma shiftedIndices_measurePreserving (j : Fin k) :
    MeasurePreserving (shiftedIndices (n := n) j) (empiricalIndicesLaw n k) (empiricalIndicesLaw n k) :=
  measurePreserving_pi (fun _ : Fin n => empiricalIndexLaw k) (fun _ : Fin n => empiricalIndexLaw k)
    (fun _ => empiricalIndexLaw_equiv_measurePreserving (Equiv.addLeft j))

noncomputable def rowShiftIndex (a : Fin n → Fin k) : Equiv.Perm (Fin n × Fin k) where
  toFun q := (q.1,q.2+a q.1)
  invFun q := (q.1,q.2-a q.1)
  left_inv q := by ext <;> simp
  right_inv q := by ext <;> simp

noncomputable def shiftTraining (a : Fin n → Fin k) (y : (Fin n × Fin k) → ℝ) : (Fin n × Fin k) → ℝ :=
  fun q => y (q.1,q.2+a q.1)

lemma shiftTraining_measurePreserving (P : Instance n) (a : Fin n → Fin k) :
    MeasurePreserving (shiftTraining a) (P.trainingCoordinateLaw k) (P.trainingCoordinateLaw k) := by
  have hp := measurePreserving_piCongrLeft (fun q : Fin n × Fin k => P.law q.1) (rowShiftIndex a)
  change MeasurePreserving (MeasurableEquiv.piCongrLeft (fun _ : Fin n × Fin k => ℝ) (rowShiftIndex a))
    (P.trainingCoordinateLaw k) (P.trainingCoordinateLaw k) at hp
  have hs := hp.symm (MeasurableEquiv.piCongrLeft (fun _ : Fin n × Fin k => ℝ) (rowShiftIndex a))
  exact hs

noncomputable def empiricalProductAverage (F : (Fin n → ℝ) → ℝ) (y : (Fin n × Fin k) → ℝ) : ℝ :=
  ∫ a, F (fun i => y (i,a i)) ∂empiricalIndicesLaw n k
noncomputable def empiricalBlockAverage (F : (Fin n → ℝ) → ℝ) (y : (Fin n × Fin k) → ℝ) : ℝ :=
  (k : ℝ)⁻¹ * ∑ j : Fin k, F (fun i => y (i,j))

lemma integral_empirical_shifted_block (F : (Fin n → ℝ) → ℝ) (y : (Fin n × Fin k) → ℝ) (j : Fin k) :
    (∫ a, F (fun i => shiftTraining a y (i,j)) ∂empiricalIndicesLaw n k) = empiricalProductAverage F y := by
  have hp := shiftedIndices_measurePreserving (n := n) j
  have hi := integral_map (μ := empiricalIndicesLaw n k) hp.measurable.aemeasurable
    (measurable_of_finite (fun a : Fin n → Fin k => F (fun i => y (i,a i)))).aestronglyMeasurable
  rw [hp.map_eq] at hi
  exact hi.symm

/-- Exact conditional averaging identity, before any integration in training. -/
lemma empiricalProductAverage_eq_integral_shifted_blocks (F : (Fin n → ℝ) → ℝ) (y : (Fin n × Fin k) → ℝ) :
    empiricalProductAverage F y =
      ∫ a, empiricalBlockAverage F (shiftTraining a y) ∂empiricalIndicesLaw n k := by
  unfold empiricalBlockAverage
  rw [integral_const_mul,integral_finsetSum Finset.univ (fun j _ => integrable_empiricalIndicesLaw
    (fun a => F (fun i => shiftTraining a y (i,j))))]
  simp_rw [integral_empirical_shifted_block F y]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [← mul_assoc,inv_mul_cancel₀ (by exact_mod_cast NeZero.ne k),one_mul]

end ProphetSecretary.Statistics
