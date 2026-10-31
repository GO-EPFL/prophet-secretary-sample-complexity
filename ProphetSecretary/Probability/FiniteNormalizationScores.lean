import ProphetSecretary.Model.FiniteBaseNormalization
import ProphetSecretary.Probability.NormalizedScoreResponse
import ProphetSecretary.Model.TrainingCoordinates

/-!
# Actual scores and training arrays under fixed-base value normalization

The transformed component score at y is h_i(My), with M fixed at the base
law. Positive linear value and sample maps preserve its mean, every bound,
its complete-vector realization and its exact sum of second moments.
-/

open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

def fixedBaseNormalizedScore (M : ℝ) (h : Fin n → ℝ → ℝ) : Fin n → ℝ → ℝ :=
  fun i y => h i (M*y)

lemma fixedBaseNormalizedScore_measurable (M : ℝ) {h : Fin n → ℝ → ℝ}
    (hh : ∀ i, Measurable (h i)) (i : Fin n) : Measurable (fixedBaseNormalizedScore M h i) :=
  (hh i).comp (measurable_valueScale M)

lemma fixedBaseNormalizedScore_bound (M : ℝ) {h : Fin n → ℝ → ℝ} {A : ℝ}
    (hBound : ∀ i x, |h i x|≤A) : ∀ i y, |fixedBaseNormalizedScore M h i y|≤A :=
  fun i y => hBound i (M*y)

lemma fixedBaseNormalizedScore_zero (M : ℝ) (h : Fin n → ℝ → ℝ) (i : Fin n) :
    fixedBaseNormalizedScore M h i 0=h i 0 := by simp only [fixedBaseNormalizedScore,mul_zero]

lemma completeScore_fixedBaseNormalizedScore {M : ℝ} (hM : 0<M)
    (h : Fin n → ℝ → ℝ) (x : Fin n → ℝ) :
    completeScore (fixedBaseNormalizedScore M h) (fun i => M⁻¹*x i)=completeScore h x := by
  unfold completeScore
  apply Finset.sum_congr rfl
  intro i _
  change h i (M*(M⁻¹*x i))=h i (x i)
  rw [←mul_assoc,mul_inv_cancel₀ hM.ne',one_mul]

lemma Instance.integral_fixedBaseNormalizedScore (P : Instance n) {M : ℝ} (hM : 0<M)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i)) (i : Fin n) :
    (∫ y, fixedBaseNormalizedScore M h i y ∂(P.scale M⁻¹ (inv_nonneg.mpr hM.le)).law i)=
      ∫ x, h i x ∂P.law i := by
  change (∫ y, h i (M*y) ∂(P.law i).map (M⁻¹*·))=_
  rw [integral_map (μ:=P.law i) (f:=fun y => h i (M*y))
    (measurable_valueScale M⁻¹).aemeasurable
    ((hh i).comp (measurable_valueScale M)).aestronglyMeasurable]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    change h i (M*(M⁻¹*x))=h i x
    rw [←mul_assoc,mul_inv_cancel₀ hM.ne',one_mul])

lemma Instance.fixedBaseNormalizedScore_centered (P : Instance n) {M : ℝ} (hM : 0<M)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hm : ∀ i, ∫ x, h i x ∂P.law i=0) :
    ∀ i, ∫ y, fixedBaseNormalizedScore M h i y ∂(P.scale M⁻¹ (inv_nonneg.mpr hM.le)).law i=0 := by
  intro i
  rw [P.integral_fixedBaseNormalizedScore hM h hh i,hm i]

lemma Instance.fixedBaseNormalizedScore_information (P : Instance n) {M : ℝ} (hM : 0<M)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i)) :
    (∑ i, ∫ y, (fixedBaseNormalizedScore M h i y)^2
      ∂(P.scale M⁻¹ (inv_nonneg.mpr hM.le)).law i)=∑ i, ∫ x, (h i x)^2 ∂P.law i := by
  apply Finset.sum_congr rfl
  intro i _
  exact P.integral_fixedBaseNormalizedScore hM (fun i x => (h i x)^2) (fun i => (hh i).pow_const 2) i

lemma Instance.fixedBaseNormalization_zero_atom (P : Instance n) {M : ℝ} (hM : 0<M) (i : Fin n) :
    (P.scale M⁻¹ (inv_nonneg.mpr hM.le)).law i {0}=P.law i {0} := by
  change (P.law i).map (M⁻¹*·) {0}=P.law i {0}
  rw [Measure.map_apply (measurable_valueScale M⁻¹) (measurableSet_singleton 0)]
  have hPre : (M⁻¹*·) ⁻¹' ({0} : Set ℝ)={0} := by
    ext x
    simp only [Set.mem_preimage,Set.mem_singleton_iff,mul_eq_zero,inv_eq_zero,hM.ne',false_or]
  rw [hPre]

def scaleTrainingCoordinates (a : ℝ) {k : ℕ} (x : (Fin n × Fin k) → ℝ) : (Fin n × Fin k) → ℝ :=
  fun q => a*x q

lemma Instance.scaleTrainingCoordinates_measurePreserving (P : Instance n) (a : ℝ) (ha : 0≤a) (k : ℕ) :
    MeasurePreserving (scaleTrainingCoordinates (n:=n) (k:=k) a) (P.trainingCoordinateLaw k)
      ((P.scale a ha).trainingCoordinateLaw k) := by
  refine ⟨measurable_pi_lambda _ (fun q => measurable_const.mul (measurable_pi_apply q)),?_⟩
  exact Measure.pi_map_pi (fun _ => (measurable_valueScale a).aemeasurable)

lemma scaleTrainingCoordinates_inverse {M : ℝ} (hM : 0<M) {k : ℕ} (x : (Fin n × Fin k) → ℝ) :
    scaleTrainingCoordinates M (scaleTrainingCoordinates M⁻¹ x)=x := by
  funext q
  change M*(M⁻¹*x q)=x q
  rw [←mul_assoc,mul_inv_cancel₀ hM.ne',one_mul]

end ProphetSecretary.Model
