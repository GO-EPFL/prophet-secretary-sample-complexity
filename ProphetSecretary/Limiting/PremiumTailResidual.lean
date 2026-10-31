import ProphetSecretary.Model.PositivePremiumTail
import ProphetSecretary.Limiting.SharpTailHazardIntegral

/-!
# Signed premium errors controlled by tail errors

The coefficient vector may have either sign. Layer-cake integration converts
its positive-premium discrepancy into the same linear combination of strict
offer tails. Taking the absolute value before dropping the threshold indicator
is the generator estimate used for arbitrary history-dependent policies.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {N : ℕ}

lemma distributionTail_mem_unit (P : Model.Instance N) (i : Fin N) (x : ℝ) :
    distributionTail P x i ∈ Icc (0 : ℝ) 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

lemma integrable_distributionTail (P : Model.Instance N) (H : ℝ) (i : Fin N) :
    Integrable (fun x => distributionTail P x i) (volume.restrict (Icc 0 H)) := by
  apply Integrable.of_bound (measurable_distributionTail P i).aestronglyMeasurable 1
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (distributionTail_mem_unit P i x).1]
    exact (distributionTail_mem_unit P i x).2

lemma integrable_cutoff_distributionTail (P : Model.Instance N) (H q : ℝ) (i : Fin N) :
    Integrable (fun x => if q < x then distributionTail P x i else 0) (volume.restrict (Icc 0 H)) :=
  (integrable_distributionTail P H i).indicator measurableSet_Ioi

lemma weighted_positivePremium_eq_tail_integral (P : Model.Instance N) {H w v : ℝ}
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H) (hw : 0 < w) (hv : 0 ≤ v) (b : Fin N → ℝ) :
    (∑ i, b i * Model.positivePremium (P.law i) w v) =
      w * ∫ x in Icc 0 H, if v / w < x then ∑ i, b i * distributionTail P x i else 0 := by
  have hi (i : Fin N) : Integrable (fun x => b i * (if v / w < x then distributionTail P x i else 0))
      (volume.restrict (Icc 0 H)) := (integrable_cutoff_distributionTail P H (v / w) i).const_mul (b i)
  have hfun : (fun x => if v / w < x then ∑ i, b i * distributionTail P x i else 0) =
      (fun x => ∑ i, b i * (if v / w < x then distributionTail P x i else 0)) := by
    funext x
    split_ifs <;> simp
  rw [hfun, integral_finsetSum _ (fun i _ => hi i), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Model.positivePremium_eq_integral_tail (P.law i) (hcap i) hw hv, integral_const_mul]
  unfold distributionTail
  ring

lemma weighted_positivePremium_abs_le_tail_integral (P : Model.Instance N) {H w v : ℝ}
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H) (hw : 0 < w) (hv : 0 ≤ v) (b : Fin N → ℝ) :
    |∑ i, b i * Model.positivePremium (P.law i) w v| ≤
      w * ∫ x in Icc 0 H, |∑ i, b i * distributionTail P x i| := by
  let ν := volume.restrict (Icc (0 : ℝ) H)
  let F : ℝ → ℝ := fun x => ∑ i, b i * distributionTail P x i
  have hF : Integrable F ν := integrable_finsetSum _ fun i _ =>
    (integrable_distributionTail P H i).const_mul (b i)
  have hcut : Integrable (fun x => if v / w < x then F x else 0) ν := hF.indicator measurableSet_Ioi
  have hmono : (∫ x, |if v / w < x then F x else 0| ∂ν) ≤ ∫ x, |F x| ∂ν := by
    apply integral_mono hcut.abs hF.abs
    intro x
    change |if v / w < x then F x else 0| ≤ |F x|
    split_ifs <;> simp
  rw [weighted_positivePremium_eq_tail_integral P hcap hw hv b, abs_mul, abs_of_pos hw]
  apply mul_le_mul_of_nonneg_left _ hw.le
  exact (abs_integral_le_integral_abs).trans hmono

lemma tailHazardError_eq_weighted_sum (a : Fin N → ℝ) (t : ℝ) (u : Fin N → ℝ) :
    tailHazardError a t u = ∑ i, ((if t < u i then (1 : ℝ) else 0) / (1 - t) - 1) * a i := by
  have hterm (i : Fin N) : ((if t < u i then (1 : ℝ) else 0) / (1 - t) - 1) * a i =
      (if t < u i then a i else 0) / (1 - t) - a i := by
    split_ifs <;> ring
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div]
  rfl

noncomputable def premiumHazardError (P : Model.Instance N) (w v t : ℝ) (u : Fin N → ℝ) : ℝ :=
  tailHazardError (fun i => Model.positivePremium (P.law i) w v) t u

/-- Uniform in the nonnegative continuation value. Taking absolute values
before dropping a stopping indicator allows all admissible policy histories. -/
lemma premiumHazardError_abs_le (P : Model.Instance N) {H w v : ℝ}
    (hcap : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H) (hw : 0 < w) (hv : 0 ≤ v)
    (t : ℝ) (u : Fin N → ℝ) :
    |premiumHazardError P w v t u| ≤
      w * ∫ x in Icc 0 H, |tailHazardError (distributionTail P x) t u| := by
  unfold premiumHazardError
  have h := weighted_positivePremium_abs_le_tail_integral P hcap hw hv
    (fun i => (if t < u i then (1 : ℝ) else 0) / (1 - t) - 1)
  simp_rw [← tailHazardError_eq_weighted_sum] at h
  exact h

end ProphetSecretary.Limiting
