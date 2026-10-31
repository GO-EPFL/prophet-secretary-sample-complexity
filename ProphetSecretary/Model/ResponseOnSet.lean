import ProphetSecretary.Model.AggregatePositiveMeasure

/-!
# Testing marginal discrepancies on a measurable set

A common indicator perturbation compares the aggregate mass of a set with
the fixed policy's response minus C times the prophet response. This is the
integrated comparison used for the high-tail set in `upmom:logtail`.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

theorem RandomizedPolicy.responseDifference_ge_set_mass (π : RandomizedPolicy n) (P : Instance n)
    {B : Set ℝ} (hB : MeasurableSet B) (C b : ℝ)
    (hbound : ∀ i x, x ∈ B → b ≤ π.rule.selectionProbabilityAtValue P π.seedLaw i x -
      C * P.prophetProbabilityAtValue π.seedLaw i x) :
    b * (∑ i, (P.law i).real B) ≤
      π.selectedResponse P (fun _ x => if x ∈ B then 1 else 0) -
        C * P.expectedProphetResponse (fun _ x => if x ∈ B then 1 else 0) := by
  let ψ : Fin n → ℝ → ℝ := fun _ x => if x ∈ B then 1 else 0
  have hm : ∀ i, Measurable (ψ i) := fun _ => Measurable.ite hB measurable_const measurable_const
  have hb : ∀ i x, |ψ i x| ≤ 1 := by intro i x; dsimp [ψ]; split_ifs <;> norm_num
  rw [π.response_difference_eq_marginal_integrals P ψ hm hb C, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  let f : ℝ → ℝ := fun x => π.rule.selectionProbabilityAtValue P π.seedLaw i x -
    C * P.prophetProbabilityAtValue π.seedLaw i x
  have hbI : Integrable (P.prophetProbabilityAtValue π.seedLaw i) (P.law i) := by
    apply Integrable.of_bound (P.measurable_prophetProbabilityAtValue π.seedLaw i).aestronglyMeasurable 1
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by linarith [(P.prophetProbabilityAtValue_mem_unit π.seedLaw i x).1],
        (P.prophetProbabilityAtValue_mem_unit π.seedLaw i x).2⟩
  have hfI : Integrable f (P.law i) :=
    (π.rule.integrable_selectionProbabilityAtValue π.measurable_rule P π.seedLaw i).sub (hbI.const_mul C)
  have hpoint : B.indicator (fun _ => b) ≤ᵐ[P.law i] B.indicator f :=
    Eventually.of_forall fun x => by
      by_cases hx : x ∈ B
      · simpa only [Set.indicator_of_mem hx] using hbound i x hx
      · simp only [Set.indicator_of_notMem hx, le_refl]
  have hint := integral_mono_ae ((integrable_const b).indicator hB) (hfI.indicator hB) hpoint
  rw [integral_indicator_const b hB] at hint
  have heq : (fun x => f x * ψ i x) = B.indicator f := by
    funext x
    by_cases hx : x ∈ B <;> simp [ψ, hx]
  change b * (P.law i).real B ≤ ∫ x, f x * ψ i x ∂P.law i
  rw [heq]
  simpa only [smul_eq_mul, mul_comm] using hint

end ProphetSecretary.Model
