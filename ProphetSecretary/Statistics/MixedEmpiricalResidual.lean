import ProphetSecretary.Model.MixedEmpiricalInstance
import ProphetSecretary.Model.BellmanResidual
import ProphetSecretary.Statistics.EmpiricalResidual

/-!
# Exact-known rows create no Bellman residual

The arriving identity's entire sample row is absent from its continuation.
Known identities do not use that row anywhere. Their signed residual is exactly
zero; unknown identities retain the literal centered empirical-average formula.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma mixedEmpiricalInstance_update_known_row (P : Instance n) (known : Finset (Fin n))
    (y : Reservoir n k) {i : Fin n} (hi : i∈known) (v : Fin k → ℝ) :
    mixedEmpiricalInstance P known (Function.update y i v) = mixedEmpiricalInstance P known y := by
  apply Instance.eq_of_law_eq
  funext j
  by_cases hj : j∈known
  · simp only [mixedEmpiricalInstance,if_pos hj]
  · have hji : j≠i := fun h => hj (h.symm ▸ hi)
    simp only [mixedEmpiricalInstance,if_neg hj]
    change empiricalLaw (fun l => max 0 (Function.update y i v j l)) = empiricalLaw (fun l => max 0 (y j l))
    rw [Function.update_of_ne hji]

lemma mixedEmpiricalInstance_restrictTo_update_row (P : Instance n) (known : Finset (Fin n))
    (y : Reservoir n k) (i : Fin n) (v : Fin k → ℝ) (A : Finset (Fin n)) (hi : i∉A) :
    (mixedEmpiricalInstance P known (Function.update y i v)).restrictTo A =
      (mixedEmpiricalInstance P known y).restrictTo A := by
  apply Instance.eq_of_law_eq
  funext j
  have hj : stateEmbedding A j∈A := A.orderEmbOfFin_mem rfl j
  have hji : stateEmbedding A j≠i := fun h => hi (h ▸ hj)
  by_cases hk : stateEmbedding A j∈known
  · change (if stateEmbedding A j∈known then _ else _) = (if stateEmbedding A j∈known then _ else _)
    simp only [if_pos hk]
  · change (if stateEmbedding A j∈known then _ else _) = (if stateEmbedding A j∈known then _ else _)
    simp only [if_neg hk]
    change empiricalLaw (fun l => max 0 (Function.update y i v (stateEmbedding A j) l)) =
      empiricalLaw (fun l => max 0 (y (stateEmbedding A j) l))
    rw [Function.update_of_ne hji]

lemma mixedEmpiricalInstance_continuationAtArrival_update_row (P : Instance n) (known : Finset (Fin n))
    (y : Reservoir n k) (i : Fin n) (v : Fin k → ℝ) (w c : ℝ) (x u : Fin n → ℝ) :
    (mixedEmpiricalInstance P known (Function.update y i v)).continuationAtArrival w c x u i =
      (mixedEmpiricalInstance P known y).continuationAtArrival w c x u i := by
  unfold Instance.continuationAtArrival Instance.continuationValue
  rw [mixedEmpiricalInstance_restrictTo_update_row P known y i v _ (by simp)]

lemma mixedEmpiricalInstance_lawResidual_known_zero (P : Instance n) (known : Finset (Fin n))
    (y : Reservoir n k) {i : Fin n} (hi : i∈known) (w v : ℝ) :
    (mixedEmpiricalInstance P known y).lawResidual P i w v = 0 := by
  simp only [Instance.lawResidual,mixedEmpiricalInstance_law_known P known y hi,sub_self]

lemma mixedEmpiricalInstance_transitionResidual_known_zero (P : Instance n) (known : Finset (Fin n))
    (y : Reservoir n k) {i : Fin n} (hi : i∈known) (w c : ℝ) (u : Fin n → ℝ) :
    (mixedEmpiricalInstance P known y).transitionResidual P w c u i = 0 :=
  mixedEmpiricalInstance_lawResidual_known_zero P known y hi w _

lemma mixedEmpiricalInstance_transitionResidual_update_unknown_row (P : Instance n) (known : Finset (Fin n))
    (y : Reservoir n k) {i : Fin n} (hi : i∉known) (v : Fin k → ℝ) (w c : ℝ) (u : Fin n → ℝ) :
    (mixedEmpiricalInstance P known (Function.update y i v)).transitionResidual P w c u i =
      (k:ℝ)⁻¹*∑ l : Fin k,
        max (w*max 0 (v l)-(mixedEmpiricalInstance P known y).continuationAtArrival w c (fun _ => 0) u i) 0-
      positivePremium (P.law i) w ((mixedEmpiricalInstance P known y).continuationAtArrival w c (fun _ => 0) u i) := by
  unfold Instance.transitionResidual Instance.lawResidual
  rw [mixedEmpiricalInstance_continuationAtArrival_update_row]
  unfold positivePremium
  rw [mixedEmpiricalInstance_integral_unknown P known (Function.update y i v) hi]
  simp only [Function.update_self]

/-- Fixed weights permit independent averaging of each candidate row. For known
rows the integrand is zero; unknown rows are actual centered sample averages. -/
theorem Instance.mixedEmpirical_transitionResidual_centered_row (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) (y : Reservoir n k)
    (i : Fin n) (w c : ℝ) (u : Fin n → ℝ) :
    (∫ v : Fin k → ℝ,
      (mixedEmpiricalInstance P known (Function.update y i v)).transitionResidual P w c u i
      ∂Measure.pi (fun _ : Fin k => P.law i)) = 0 := by
  by_cases hi : i∈known
  · simp only [mixedEmpiricalInstance_transitionResidual_known_zero P known _ hi,integral_zero]
  · let θ := (mixedEmpiricalInstance P known y).continuationAtArrival w c (fun _ => 0) u i
    let f : ℝ → ℝ := fun x => max (w*max 0 x-θ) 0
    have hμ := P.integrable_maximum_iff.mp hP i
    have hf : Integrable f (P.law i) :=
      (((integrable_const 0).sup hμ).const_mul w |>.sub (integrable_const θ)).sup (integrable_const 0)
    have hm : Measurable f := ((measurable_const.mul (measurable_const.max measurable_id)).sub measurable_const).max measurable_const
    have havg := ProphetSecretary.Statistics.integral_empirical_average (k:=k) (P.law i) hm hf
    have hI := ProphetSecretary.Statistics.integrable_empirical_average (k:=k) (P.law i) hf
    simp_rw [mixedEmpiricalInstance_transitionResidual_update_unknown_row P known y hi]
    rw [integral_sub hI (integrable_const _),havg]
    have he : f =ᵐ[P.law i] (fun x => max (w*x-θ) 0) := (P.nonnegative i).mono fun x hx => by
      dsimp [f]
      rw [max_eq_right hx]
    rw [integral_congr_ae he]
    simp only [positivePremium,integral_const,probReal_univ,one_smul]
    exact sub_self _

end ProphetSecretary.Model
