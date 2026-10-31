import ProphetSecretary.Model.EmpiricalPolicy
import ProphetSecretary.Model.BellmanResidual

/-!
# Candidate-row independence and empirical residual centering

The design continuation excludes the arriving identity. Replacing that identity's
entire training row therefore leaves its continuation unchanged. The residual is then
an actual centered sample average when the scalar is fixed. This statement does not
assert centering after selecting the scalar from that row's observations.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma totalEmpiricalInstance_restrictTo_update_row (y : Reservoir n k) (i : Fin n)
    (v : Fin k → ℝ) (A : Finset (Fin n)) (hi : i ∉ A) :
    (totalEmpiricalInstance (Function.update y i v)).restrictTo A =
      (totalEmpiricalInstance y).restrictTo A := by
  apply Instance.eq_of_law_eq
  funext j
  have hj : stateEmbedding A j ∈ A := A.orderEmbOfFin_mem rfl j
  have hne : stateEmbedding A j ≠ i := fun h => hi (h ▸ hj)
  change empiricalLaw (fun l => max 0 ((Function.update y i v) (stateEmbedding A j) l)) =
    empiricalLaw (fun l => max 0 (y (stateEmbedding A j) l))
  rw [Function.update_of_ne hne]

lemma totalEmpiricalInstance_continuationAtArrival_update_row (y : Reservoir n k)
    (i : Fin n) (v : Fin k → ℝ) (w c : ℝ) (x u : Fin n → ℝ) :
    (totalEmpiricalInstance (Function.update y i v)).continuationAtArrival w c x u i =
      (totalEmpiricalInstance y).continuationAtArrival w c x u i := by
  unfold Instance.continuationAtArrival Instance.continuationValue
  rw [totalEmpiricalInstance_restrictTo_update_row y i v _ (by simp)]

/-- The continuation is fixed while the arriving identity's training row is varied. -/
lemma totalEmpiricalInstance_transitionResidual_update_row (P : Instance n) (y : Reservoir n k)
    (i : Fin n) (v : Fin k → ℝ) (w c : ℝ) (u : Fin n → ℝ) :
    (totalEmpiricalInstance (Function.update y i v)).transitionResidual P w c u i =
      (k : ℝ)⁻¹ * ∑ j : Fin k,
        max (w * max 0 (v j) - (totalEmpiricalInstance y).continuationAtArrival w c (fun _ => 0) u i) 0 -
      positivePremium (P.law i) w ((totalEmpiricalInstance y).continuationAtArrival w c (fun _ => 0) u i) := by
  unfold Instance.transitionResidual Instance.lawResidual
  rw [totalEmpiricalInstance_continuationAtArrival_update_row]
  unfold positivePremium
  rw [totalEmpiricalInstance_integral]
  simp only [Function.update_self]

end ProphetSecretary.Model

namespace ProphetSecretary.Statistics

variable {k : ℕ} [NeZero k]

omit [NeZero k] in
lemma integrable_empirical_average (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hf : Integrable f μ) :
    Integrable (fun v : Fin k → ℝ => (k : ℝ)⁻¹ * ∑ j, f (v j))
      (Measure.pi (fun _ : Fin k => μ)) :=
  (integrable_finsetSum _ (fun j _ =>
    (measurePreserving_eval (fun _ : Fin k => μ) j).integrable_comp_of_integrable hf)).const_mul _

lemma integral_empirical_average (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {f : ℝ → ℝ} (hfm : Measurable f) (hf : Integrable f μ) :
    (∫ v : Fin k → ℝ, (k : ℝ)⁻¹ * ∑ j, f (v j) ∂Measure.pi (fun _ : Fin k => μ)) = ∫ x, f x ∂μ := by
  have hj (j : Fin k) : (∫ v : Fin k → ℝ, f (v j) ∂Measure.pi (fun _ : Fin k => μ)) = ∫ x, f x ∂μ := by
    have hp := measurePreserving_eval (fun _ : Fin k => μ) j
    have he := integral_map (μ := Measure.pi (fun _ : Fin k => μ)) hp.measurable.aemeasurable hfm.aestronglyMeasurable
    rw [hp.map_eq] at he
    exact he.symm
  rw [integral_const_mul, integral_finsetSum]
  · simp only [hj, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne k)
    rw [← mul_assoc, inv_mul_cancel₀ hk, one_mul]
  · intro j _
    exact (measurePreserving_eval (fun _ : Fin k => μ) j).integrable_comp_of_integrable hf

end ProphetSecretary.Statistics

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

/-- Actual fixed-weight centering over fresh independent candidate samples. The
candidate's value distribution is integrated explicitly, rather than assumed independent
of a continuation that could still inspect its training row. -/
theorem Instance.empirical_transitionResidual_centered_row (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (y : Reservoir n k) (i : Fin n)
    (w c : ℝ) (u : Fin n → ℝ) :
    (∫ v : Fin k → ℝ,
      (totalEmpiricalInstance (Function.update y i v)).transitionResidual P w c u i
      ∂Measure.pi (fun _ : Fin k => P.law i)) = 0 := by
  let θ := (totalEmpiricalInstance y).continuationAtArrival w c (fun _ => 0) u i
  let f : ℝ → ℝ := fun x => max (w * max 0 x - θ) 0
  have hμ := P.integrable_maximum_iff.mp hP i
  have hf : Integrable f (P.law i) :=
    (((integrable_const 0).sup hμ).const_mul w |>.sub (integrable_const θ)).sup (integrable_const 0)
  have hfm : Measurable f :=
    ((measurable_const.mul (measurable_const.max measurable_id)).sub measurable_const).max measurable_const
  have hmean : (∫ x, f x ∂P.law i) = positivePremium (P.law i) w θ := by
    apply integral_congr_ae
    filter_upwards [P.nonnegative i] with x hx
    dsimp [f]
    rw [max_eq_right hx]
  have havg := ProphetSecretary.Statistics.integral_empirical_average (k := k) (P.law i) hfm hf
  have hI := ProphetSecretary.Statistics.integrable_empirical_average (k := k) (P.law i) hf
  have heq : (fun v : Fin k → ℝ =>
      (totalEmpiricalInstance (Function.update y i v)).transitionResidual P w c u i) =
      (fun v => (k : ℝ)⁻¹ * ∑ j, f (v j) - positivePremium (P.law i) w θ) := by
    funext v
    exact totalEmpiricalInstance_transitionResidual_update_row P y i v w c u
  rw [heq, integral_sub hI (integrable_const _), integral_const, probReal_univ, one_smul, havg, hmean, sub_self]

end ProphetSecretary.Model
