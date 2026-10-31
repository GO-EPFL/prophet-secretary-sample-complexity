import ProphetSecretary.Model.ValuePerturbationTies
import ProphetSecretary.Model.AggregateAtomResponse
import ProphetSecretary.Probability.ConditionedProduct

/-!
# Large aggregate atoms force tied maxima

Conditioning all independent offers below a preserves their product structure.
The conditional mean number equal to a is at least the original aggregate atom.
The proved two-moment support bound then makes a tied maximum occur with
conditional probability at least one sixth. Zero conditioning events are
handled directly, without defining a spurious conditional probability law.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

lemma singletonCount_gt_one_implies_two (a : ℝ) (x : Fin n → ℝ)
    (hcount : 1 < singletonCount a x) : ∃ i j, i ≠ j ∧ x i = a ∧ x j = a := by
  by_contra hn
  by_cases hex : ∃ i, x i = a
  · obtain ⟨i, hi⟩ := hex
    have hothers : ∀ j, j ≠ i → x j ≠ a := by
      intro j hji hj
      exact hn ⟨i,j,hji.symm,hi,hj⟩
    have heq : singletonCount a x = 1 := by
      unfold singletonCount
      rw [Finset.sum_eq_single i]
      · simp [singletonBit, hi]
      · intro j _ hji
        exact if_neg (hothers j hji)
      · simp
    linarith only [hcount, heq]
  · have hx : ∀ i, x i ≠ a := not_exists.mp hex
    have heq : singletonCount a x = 0 := by simp only [singletonCount, singletonBit, hx, if_false, Finset.sum_const_zero]
    linarith only [hcount, heq]

/-- The one-sixth conditional-count argument in the paragraph following
`upmom:atomeq`, stated as an unconditional finite-instance inequality. -/
theorem Instance.maximum_atom_le_six_tied_atom (P : Instance n) {a : ℝ}
    (ha : 0 < a) (hmass : 2 ≤ P.aggregateAtomMass a) :
    P.valuesLaw.real {x : Fin n → ℝ | Instance.maximum x = a} ≤
      6 * P.valuesLaw.real {x : Fin n → ℝ | Instance.maximum x = a ∧ MaximumTiedAtLeast a x} := by
  let E : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ => Iic a)
  let B : Set (Fin n → ℝ) := {x | 1 < singletonCount a x}
  let T : Set (Fin n → ℝ) := {x | Instance.maximum x = a ∧ MaximumTiedAtLeast a x}
  have hEm : MeasurableSet E := MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Iic)
  have hsubM : {x : Fin n → ℝ | Instance.maximum x = a} ⊆ E := by
    intro x hx j _
    exact (Instance.le_maximum x j).trans_eq hx
  have hsubT : E ∩ B ⊆ T := by
    rintro x ⟨hx,hB⟩
    obtain ⟨i,j,hij,hi,hj⟩ := singletonCount_gt_one_implies_two a x hB
    have hmax : Instance.maximum x = a := le_antisymm
      (Instance.maximum_le x ha.le (fun j => hx j (Set.mem_univ _)))
      (by simpa only [hi] using Instance.le_maximum x i)
    exact ⟨hmax, hmax.ge, i,j,hij,hi.trans hmax.symm,hj.trans hmax.symm⟩
  have hEprob : P.valuesLaw E = ∏ i, P.law i (Iic a) := Measure.pi_pi _ _
  by_cases hpos : ∀ i, P.law i (Iic a) ≠ 0
  · let ν : Fin n → Measure ℝ := fun i => (P.law i)[|Iic a]
    letI (i : Fin n) : IsProbabilityMeasure (ν i) := cond_isProbabilityMeasure (hpos i)
    have hm : 2 ≤ ∑ i, (ν i).real {a} :=
      hmass.trans (Finset.sum_le_sum fun i _ => conditionBelow_atom_ge (P.law i) a (hpos i))
    have hcount := singletonCount_probability_gt_one_ge_sixth ν a hm
    have hprod := pi_conditionBelow_eq_condition_pi P.law a hpos
    change Measure.pi ν = P.valuesLaw[|E] at hprod
    rw [hprod] at hcount
    have hE0 : P.valuesLaw E ≠ 0 := by
      rw [hEprob]
      exact Finset.prod_ne_zero_iff.mpr fun i _ => hpos i
    have hq : 0 < P.valuesLaw.real E := ENNReal.toReal_pos hE0 (measure_ne_top _ _)
    have hratio : (P.valuesLaw[|E]).real B = P.valuesLaw.real (E ∩ B) / P.valuesLaw.real E := by
      unfold Measure.real
      rw [cond_apply hEm, ENNReal.toReal_mul, ENNReal.toReal_inv]
      ring
    change (1 : ℝ) / 6 ≤ (P.valuesLaw[|E]).real B at hcount
    rw [hratio] at hcount
    have hscaled := (le_div_iff₀ hq).mp hcount
    have hmono := measureReal_mono hsubT (μ := P.valuesLaw)
    have hbound : P.valuesLaw.real E ≤ 6 * P.valuesLaw.real T := by linarith only [hscaled, hmono]
    exact (measureReal_mono hsubM).trans hbound
  · obtain ⟨i, hi⟩ := not_forall.mp hpos
    have hi0 : P.law i (Iic a) = 0 := not_ne_iff.mp hi
    have hE0 : P.valuesLaw E = 0 := by
      rw [hEprob]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hi0
    have hzero : P.valuesLaw.real {x : Fin n → ℝ | Instance.maximum x = a} = 0 := by
      apply le_antisymm _ measureReal_nonneg
      have h := measureReal_mono hsubM (μ := P.valuesLaw)
      simpa only [Measure.real, hE0, ENNReal.toReal_zero] using h
    rw [hzero]
    positivity

end ProphetSecretary.Model
