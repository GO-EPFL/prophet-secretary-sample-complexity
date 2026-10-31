import ProphetSecretary.Model.AggregateAtomResponse
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# A marginal prophet probability is exponentially small below many offers

Winning after fixing Xᵢ=x requires every other offer to be at most x. Product
independence and 1−p≤exp(−p) give bᵢ(x)≤exp(1−L_x), the estimate used in
`upmom:logtail`. Clock and policy seeds have already been integrated out.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma Instance.otherBelow_probability (P : Instance n) (i : Fin n) (a : ℝ) :
    P.valuesLaw.real {x : Fin n → ℝ | ∀ j, j ≠ i → x j ≤ a} =
      ∏ j ∈ Finset.univ.erase i, (P.law j).real (Iic a) := by
  have heq : {x : Fin n → ℝ | ∀ j, j ≠ i → x j ≤ a} =
      Set.pi Set.univ (fun j => if j = i then Set.univ else Iic a) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro hx j
      by_cases hj : j = i <;> simp [hj, hx j]
    · intro hx j hji
      simpa only [if_neg hji, Set.mem_Iic] using hx j
  rw [heq]
  unfold Measure.real Instance.valuesLaw
  rw [Measure.pi_pi, ENNReal.toReal_prod]
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  simp only [ite_true, measure_univ, ENNReal.toReal_one, mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  simp only [if_neg (Finset.mem_erase.mp hj).1]

lemma Instance.prophetProbabilityAtValue_le_otherBelow (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin n) (a : ℝ) :
    P.prophetProbabilityAtValue ν i a ≤ ∏ j ∈ Finset.univ.erase i, (P.law j).real (Iic a) := by
  rw [P.prophetProbabilityAtValue_eq_valuesIntegral ν i a, ← P.otherBelow_probability i a]
  let W : Set (Fin n → ℝ) := {x | ProphetWins (Function.update x i a) i}
  have hW : MeasurableSet W :=
    (measurable_pi_lambda _ (fun j => by fun_prop)) (measurableSet_prophetWins i)
  have heq : (∫ x, if ProphetWins (Function.update x i a) i then (1 : ℝ) else 0 ∂P.valuesLaw) =
      P.valuesLaw.real W := by
    simpa only [W, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply] using
      (integral_indicator_one (μ := P.valuesLaw) hW)
  rw [heq]
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  intro x hx j hji
  have hm := hx.2.1
  rw [Function.update_self] at hm
  have hj := Instance.le_maximum (Function.update x i a) j
  rw [Function.update_of_ne hji] at hj
  exact hj.trans_eq hm.symm

/-- The exponential bound is uniform in the finite number of offers. -/
theorem Instance.prophetProbabilityAtValue_le_exp_tailCount (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin n) (a : ℝ) :
    P.prophetProbabilityAtValue ν i a ≤ Real.exp (1 - P.tailCount a) := by
  apply (P.prophetProbabilityAtValue_le_otherBelow ν i a).trans
  have hp (j : Fin n) : (P.law j).real (Iic a) = 1 - (P.law j).real (Ioi a) := by
    have heq : Iic a = (Ioi a)ᶜ := by ext x; simp
    rw [heq, measureReal_compl measurableSet_Ioi, probReal_univ]
  have hprod : (∏ j ∈ Finset.univ.erase i, (P.law j).real (Iic a)) ≤
      ∏ j ∈ Finset.univ.erase i, Real.exp (-(P.law j).real (Ioi a)) := by
    apply Finset.prod_le_prod (fun j _ => measureReal_nonneg)
    intro j _
    rw [hp j]
    have he := Real.add_one_le_exp (-(P.law j).real (Ioi a))
    linarith only [he]
  apply hprod.trans
  rw [← Real.exp_sum]
  apply Real.exp_le_exp.mpr
  have hi : (P.law i).real (Ioi a) ≤ 1 := measureReal_le_one
  have hs := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n)))
    (fun j => (P.law j).real (Ioi a)) (Finset.mem_univ i)
  rw [Finset.sum_neg_distrib]
  change -(∑ j ∈ Finset.univ.erase i, (P.law j).real (Ioi a)) ≤ 1 - ∑ j, (P.law j).real (Ioi a)
  linarith only [hi, hs]

end ProphetSecretary.Model
