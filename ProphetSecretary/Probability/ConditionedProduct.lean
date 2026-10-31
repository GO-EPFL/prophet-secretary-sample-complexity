import ProphetSecretary.Probability.SingletonCountMoments
import Mathlib.Probability.ConditionalProbability

/-!
# Conditioning independent coordinates below a common level

Conditioning the full product on every coordinate being at most a is exactly
the product of the individually conditioned laws. Rectangle probabilities
prove this equality; no conditional independence is assumed.
-/
open MeasureTheory ProbabilityTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Probability
variable {n : ℕ}

lemma pi_conditionBelow_eq_condition_pi (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (a : ℝ) (hpos : ∀ i, μ i (Iic a) ≠ 0) :
    Measure.pi (fun i => (μ i)[|Iic a]) =
      (Measure.pi μ)[|Set.pi Set.univ (fun _ => Iic a)] := by
  letI (i : Fin n) : IsProbabilityMeasure ((μ i)[|Iic a]) := cond_isProbabilityMeasure (hpos i)
  apply Measure.pi_eq
  intro s hs
  have hE : MeasurableSet (Set.pi Set.univ (fun _ : Fin n => Iic a)) :=
    MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Iic)
  rw [cond_apply hE, Measure.pi_pi]
  have hset : (Set.pi Set.univ (fun _ : Fin n => Iic a)) ∩ Set.pi Set.univ s =
      Set.pi Set.univ (fun i => Iic a ∩ s i) := by
    ext x
    simp only [mem_inter_iff, mem_pi, mem_univ, forall_const]
    constructor
    · rintro ⟨ha, hs⟩ i
      exact ⟨ha i, hs i⟩
    · intro hx
      exact ⟨fun i => (hx i).1, fun i => (hx i).2⟩
  rw [hset, Measure.pi_pi, ENNReal.prod_inv_distrib (fun i _ j _ _ => Or.inl (hpos i)),
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact (cond_apply measurableSet_Iic (μ i) (s i)).symm

lemma conditionBelow_atom_ge (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (a : ℝ) (hpos : μ (Iic a) ≠ 0) : μ.real {a} ≤ (μ[|Iic a]).real {a} := by
  have heq : Iic a ∩ ({a} : Set ℝ) = {a} := by ext x; simp
  have hp : 0 < μ.real (Iic a) := ENNReal.toReal_pos hpos (measure_ne_top μ _)
  have hle : μ.real (Iic a) ≤ 1 := measureReal_le_one
  change (μ {a}).toReal ≤ ((μ[|Iic a]) {a}).toReal
  rw [cond_apply measurableSet_Iic, heq, ENNReal.toReal_mul, ENNReal.toReal_inv]
  have h : μ.real {a} * μ.real (Iic a) ≤ μ.real {a} := by
    have hh := mul_le_mul_of_nonneg_left hle (measureReal_nonneg (μ := μ) (s := {a}))
    simpa only [mul_one] using hh
  rw [mul_comm, ← div_eq_mul_inv]
  exact (le_div_iff₀ hp).mpr h

end ProphetSecretary.Probability
