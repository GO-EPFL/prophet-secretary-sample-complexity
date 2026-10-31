import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Independence of count vectors from generating tests

The finite coordinate sets may be empty. Complex parameters of norm at most
one include all characteristic-function tests; real linear forms on finite
vectors are decomposed into their actual coordinate maps.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped Classical BigOperators

namespace ProphetSecretary.Probability

lemma exp_linearForm_natVector {ι : Type*} [Fintype ι]
    (L : (ι → ℝ) →L[ℝ] ℝ) (N : ι → ℕ) :
    Complex.exp (((L (fun i => (N i : ℝ)) : ℝ) : ℂ)*Complex.I) =
      ∏ i, Complex.exp (((L (Pi.single i 1) : ℝ) : ℂ)*Complex.I)^N i := by
  rw [← L.sum_comp_single,Complex.ofReal_sum,Finset.sum_mul,Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  have hLi : (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i)) (N i : ℝ) =
      (N i : ℝ)*(L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i)) 1 := by
    simpa only [smul_eq_mul,mul_one] using
      (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => ℝ) i)).map_smul (N i : ℝ) (1 : ℝ)
  rw [hLi,← Complex.exp_nat_mul]
  congr 1
  push_cast
  change (N i : ℂ)*(L (Pi.single i 1) : ℂ)*Complex.I = _
  ring

theorem indepFun_natCastVectors_of_generating_factorization {Ω ι κ : Type*}
    [MeasurableSpace Ω] [Fintype ι] [Fintype κ]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ι → ℕ} {Y : Ω → κ → ℕ}
    (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ (z : ι → ℂ) (w : κ → ℂ), (∀ i, ‖z i‖ ≤ 1) → (∀ j, ‖w j‖ ≤ 1) →
      (∫ ω, (∏ i, z i ^ X ω i)*(∏ j, w j ^ Y ω j) ∂P) =
        (∫ ω, ∏ i, z i ^ X ω i ∂P)*(∫ ω, ∏ j, w j ^ Y ω j ∂P)) :
    IndepFun (fun ω i => (X ω i : ℝ)) (fun ω j => (Y ω j : ℝ)) P := by
  have hXR : Measurable (fun ω i => (X ω i : ℝ)) := measurable_pi_lambda _ (fun i =>
    (Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp ((measurable_pi_apply i).comp hX))
  have hYR : Measurable (fun ω j => (Y ω j : ℝ)) := measurable_pi_lambda _ (fun j =>
    (Measurable.of_discrete : Measurable (Nat.cast : ℕ → ℝ)).comp ((measurable_pi_apply j).comp hY))
  apply (indepFun_iff_charFunDual_prod hXR.aemeasurable hYR.aemeasurable).mpr
  intro L
  rw [charFunDual_apply,charFunDual_apply,charFunDual_apply,
    integral_map (hXR.prodMk hYR).aemeasurable (by fun_prop),
    integral_map hXR.aemeasurable (by fun_prop),integral_map hYR.aemeasurable (by fun_prop)]
  simp_rw [← L.comp_inl_add_comp_inr,Complex.ofReal_add,add_mul,Complex.exp_add,exp_linearForm_natVector]
  exact h _ _ (fun i => by simp [Complex.norm_exp]) (fun j => by simp [Complex.norm_exp])

end ProphetSecretary.Probability
