import ProphetSecretary.Probability.Hoeffding.BoundedRepresentative
import ProphetSecretary.Probability.LikelihoodTilt

/-!
# Likelihood direction from actual first conditional projections

For a fixed kernel f, the first-projection variance is the sum of the squared
conditional fluctuations g_i. The direction -g_i/2 is centered and bounded on
the actual marginal law, and its information and kernel response are computed.
The complete-vector score is analytical and may involve offers after stopping.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators NNReal

namespace ProphetSecretary.Model

open ProphetSecretary.Probability ProphetSecretary.Probability.Hoeffding

variable {n : ℕ}

noncomputable def Instance.firstProjectionVariance (P : Instance n) (f : (Fin n → ℝ) → ℝ) : ℝ :=
  ∑ i, ∫ a, firstProjection P.law f i a^2 ∂P.law i

noncomputable def Instance.firstProjectionDirection (P : Instance n) (f : (Fin n → ℝ) → ℝ)
    (i : Fin n) (a : ℝ) : ℝ := (-1/2 : ℝ)*firstProjection P.law f i a

lemma Instance.firstProjectionVariance_nonnegative (P : Instance n) (f : (Fin n → ℝ) → ℝ) :
    0 ≤ P.firstProjectionVariance f := Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _))

lemma Instance.measurable_firstProjectionDirection (P : Instance n) {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (i : Fin n) : Measurable (P.firstProjectionDirection f i) :=
  (measurable_firstProjection P.law hf i).const_mul (-1/2 : ℝ)

lemma Instance.firstProjectionDirection_abs_le_ae (P : Instance n) {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (hb : ∀ᵐ x ∂P.valuesLaw, |f x| ≤ 1) (i : Fin n) :
    ∀ᵐ a ∂P.law i, |P.firstProjectionDirection f i a| ≤ 1 := by
  filter_upwards [firstProjection_abs_le_ae P.law hf 1 hb i] with a ha
  have ha' : |firstProjection P.law f i a| ≤ 2 := by simpa using ha
  calc
    _ = (1/2 : ℝ)*|firstProjection P.law f i a| := by rw [firstProjectionDirection,abs_mul]; norm_num
    _ ≤ (1/2 : ℝ)*2 := mul_le_mul_of_nonneg_left ha' (by norm_num)
    _ = 1 := by norm_num

lemma Instance.integral_firstProjectionDirection (P : Instance n) {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (hb : ∀ᵐ x ∂P.valuesLaw, |f x| ≤ 1) (i : Fin n) :
    (∫ a, P.firstProjectionDirection f i a ∂P.law i) = 0 := by
  change (∫ a, (-1/2 : ℝ)*firstProjection P.law f i a ∂P.law i) = 0
  rw [integral_const_mul,integral_firstProjection_of_ae_bounded P.law hf 1 hb i,mul_zero]

lemma Instance.information_firstProjectionDirection (P : Instance n) (f : (Fin n → ℝ) → ℝ) :
    information P.law (P.firstProjectionDirection f) = (1/4 : ℝ)*P.firstProjectionVariance f := by
  have he (i : Fin n) : (fun a => P.firstProjectionDirection f i a^2) =
      (fun a => (1/4 : ℝ)*firstProjection P.law f i a^2) := by
    funext a
    unfold firstProjectionDirection
    ring
  unfold information firstProjectionVariance
  simp_rw [he,integral_const_mul]
  exact (Finset.mul_sum _ _ _).symm

lemma Instance.integral_kernel_firstProjectionDirection (P : Instance n) {f : (Fin n → ℝ) → ℝ}
    (hf : Measurable f) (hb : ∀ᵐ x ∂P.valuesLaw, |f x| ≤ 1) :
    (∫ x, f x*completeScore (P.firstProjectionDirection f) x ∂P.valuesLaw) =
      (-1/2 : ℝ)*P.firstProjectionVariance f := by
  have hProd (i : Fin n) : Integrable (fun x => f x*firstProjection P.law f i (x i)) P.valuesLaw := by
    have hm : Measurable (fun x => f x*firstProjection P.law f i (x i)) :=
      hf.mul ((measurable_firstProjection P.law hf i).comp (measurable_pi_apply i))
    apply Integrable.of_bound hm.aestronglyMeasurable 2
    filter_upwards [hb,(measurePreserving_eval P.law i).quasiMeasurePreserving.ae
      (firstProjection_abs_le_ae P.law hf 1 hb i)] with x hfx hgi
    have hgi' : |firstProjection P.law f i (x i)| ≤ 2 := by simpa using hgi
    rw [Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul hfx hgi' (abs_nonneg _) zero_le_one).trans_eq (by norm_num)
  have he : (fun x => f x*completeScore (P.firstProjectionDirection f) x) =
      (fun x => ∑ i : Fin n, (-1/2 : ℝ)*(f x*firstProjection P.law f i (x i))) := by
    funext x
    rw [completeScore,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold firstProjectionDirection
    ring
  have hCov (i : Fin n) : (∫ x, f x*firstProjection P.law f i (x i) ∂P.valuesLaw) =
      ∫ a, firstProjection P.law f i a^2 ∂P.law i :=
    integral_kernel_firstProjection_of_ae_bounded P.law hf 1 hb i
  rw [he,integral_finsetSum _ (fun i _ => (hProd i).const_mul (-1/2 : ℝ))]
  simp_rw [integral_const_mul,hCov]
  exact (Finset.mul_sum _ _ _).symm

lemma Instance.integral_kernel_firstProjectionDirection_eq_information (P : Instance n)
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) (hb : ∀ᵐ x ∂P.valuesLaw, |f x| ≤ 1) :
    (∫ x, f x*completeScore (P.firstProjectionDirection f) x ∂P.valuesLaw) =
      -2*information P.law (P.firstProjectionDirection f) := by
  rw [P.integral_kernel_firstProjectionDirection hf hb,P.information_firstProjectionDirection]
  ring

end ProphetSecretary.Model
