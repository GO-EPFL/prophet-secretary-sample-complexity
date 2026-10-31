import ProphetSecretary.Model.MappedRewardPerformance
import ProphetSecretary.Stability.SelectedOccurrence

/-!
# First-order support under perturbations of values

The selected response is computed with the base policy held fixed. The mapped
Bellman identity proves the lower half of `upmom:transport`, including
noninjective value maps and all independent auxiliary policy randomness.
-/

open MeasureTheory Filter

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def RandomizedPolicy.selectedResponse (π : RandomizedPolicy n) (P : Instance n)
    (ψ : Fin n → ℝ → ℝ) : ℝ :=
  ∫ ω : π.World, π.rule.mappedReward ψ ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw π.seedLaw

lemma RandomizedPolicy.integrable_selectedResponse (π : RandomizedPolicy n) (P : Instance n)
    (ψ : Fin n → ℝ → ℝ) (hψ : ∀ i, Measurable (ψ i)) (hbound : ∀ i x, |ψ i x| ≤ 1) :
    Integrable (fun ω : π.World => π.rule.mappedReward ψ ω.2.2 Finset.univ ω.1 ω.2.1)
      (P.worldLaw π.seedLaw) :=
  π.rule.integrable_selectedTag π.measurable_rule (P.worldLaw π.seedLaw)
    (measurable_snd.comp measurable_snd) (fun i => (measurable_pi_apply i).comp measurable_fst)
    (fun i => (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
    (fun i => (hψ i).comp ((measurable_pi_apply i).comp measurable_fst)) zero_le_one
    (Eventually.of_forall fun ω i => hbound i (ω.1 i))

lemma RandomizedPolicy.selectedResponse_abs_le_one (π : RandomizedPolicy n) (P : Instance n)
    (ψ : Fin n → ℝ → ℝ) (hbound : ∀ i x, |ψ i x| ≤ 1) : |π.selectedResponse P ψ| ≤ 1 := by
  have h := norm_integral_le_of_norm_le_const (μ := P.worldLaw π.seedLaw)
    (f := fun ω : π.World => π.rule.mappedReward ψ ω.2.2 Finset.univ ω.1 ω.2.1)
    (Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      exact π.rule.selectedTag_abs_le ω.2.2 ω.1 ω.2.1 (fun i => ψ i (ω.1 i)) zero_le_one
        (fun i => hbound i (ω.1 i)))
  simpa only [selectedResponse, Real.norm_eq_abs, probReal_univ, mul_one] using h

lemma perturbation_displacement (ψ : Fin n → ℝ → ℝ) (hbound : ∀ i x, |ψ i x| ≤ 1)
    (t : ℝ) (i : Fin n) (x : ℝ) : |(x + t * ψ i x) - x| ≤ |t| := by
  rw [add_sub_cancel_left, abs_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hbound i x) (abs_nonneg t)

theorem RandomizedPolicy.mappedScalarObjective_perturbation (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ψ : Fin n → ℝ → ℝ)
    (hψ : ∀ i, Measurable (ψ i)) (hbound : ∀ i x, |ψ i x| ≤ 1) (t w c : ℝ) :
    π.mappedScalarObjective P (fun i x => x + t * ψ i x) w c =
      π.scalarObjective P w c + w * t * π.selectedResponse P ψ := by
  have hm : ∀ i, Measurable (fun x => x + t * ψ i x) := fun i =>
    measurable_id.add (measurable_const.mul (hψ i))
  rw [π.mappedScalarObjective_eq P hP _ hm (abs_nonneg t) (perturbation_displacement ψ hbound t)]
  have heq : (∫ ω : π.World, π.mappedRewardDifference (fun i x => x + t * ψ i x) ω ∂P.worldLaw π.seedLaw) =
      t * π.selectedResponse P ψ := by
    have hpoint (ω : π.World) : π.mappedRewardDifference (fun i x => x + t * ψ i x) ω =
        t * π.rule.mappedReward ψ ω.2.2 Finset.univ ω.1 ω.2.1 := by
      unfold mappedRewardDifference realizedReward
      rw [π.rule.mappedReward_affine]
      ring
    rw [integral_congr_ae (Eventually.of_forall hpoint), integral_const_mul]
    rfl
  rw [heq]
  ring

theorem RandomizedPolicy.valuePerturbation_lower_support (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ψ : Fin n → ℝ → ℝ)
    (hψ : ∀ i, Measurable (ψ i)) (hbound : ∀ i x, |ψ i x| ≤ 1) (t : ℝ)
    (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ x + t * ψ i x)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (hopt : π.scalarObjective P w c = optimalScalarValue P w c) :
    optimalScalarValue P w c + w * t * π.selectedResponse P ψ ≤
      optimalScalarValue (P.mapValues (fun i x => x + t * ψ i x)
        (fun i => measurable_id.add (measurable_const.mul (hψ i))) hnn) w c := by
  have h := π.mappedScalarObjective_le_optimal P hP (fun i x => x + t * ψ i x)
    (fun i => measurable_id.add (measurable_const.mul (hψ i))) hnn (abs_nonneg t) hw hc
    (perturbation_displacement ψ hbound t)
  rwa [π.mappedScalarObjective_perturbation P hP ψ hψ hbound t w c, hopt] at h

end ProphetSecretary.Model
