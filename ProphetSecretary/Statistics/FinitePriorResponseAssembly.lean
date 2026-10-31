import ProphetSecretary.Statistics.FiniteResponseGame
import ProphetSecretary.Statistics.FinitePriorClassifier

/-!
# Conditional assembly from finitely many local response guarantees

The hypotheses give explicit bounds on the finitely many observable selection
cells. Their sum, together with the classifier error estimate, bounds the payoff
of the actual patched learner.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Analysis
variable {n : ℕ}

lemma sum_selection_cell_probabilities {A ι : Type*} [MeasurableSpace A] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι] (μ : Measure A) [IsFiniteMeasure μ]
    (s : A → ι) (hs : Measurable s) (E : Set A) :
    (∑ c : ι, μ.real {a | s a=c ∧ a∈E})=μ.real E := by
  have hSum := sum_measureReal_preimage_singleton (μ:=μ.restrict E) Finset.univ
    (fun c _ => hs (measurableSet_singleton c))
  rw [Finset.coe_univ,Set.preimage_univ,measureReal_restrict_apply_univ] at hSum
  calc
    (∑ c : ι, μ.real {a | s a=c ∧ a∈E})=∑ c : ι, (μ.restrict E).real (s ⁻¹' {c}) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [measureReal_restrict_apply (hs (measurableSet_singleton c))]
      rfl
    _=μ.real E := hSum

/-- Cellwise response bounds and classifier error control the actual finite-prior
payoff of the measurable patched learner. -/
theorem finitePriorResponse_bound_of_cellwise (F : FinitePrior n) {m d : ℕ} (hm : 2≤m)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1) {Sstar : ℝ} (hS : 1≤Sstar)
    {ι : Type} [Fintype ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (s : ((Fin n × Fin (classifierRounds m)) → ℝ) → ι) (hs : Measurable s)
    (L : ι → Learner n d) (C κ : ℝ)
    (hLocal : ∀ c : ι,
      -κ*(∑ θ : Fin F.size, (F.weight θ:ℝ)*
        ((F.offerInstance θ).trainingCoordinateLaw (classifierRounds m)).real {a | s a=c})-
      (∑ θ : Fin F.size, (F.weight θ:ℝ)*
        ((F.offerInstance θ).trainingCoordinateLaw (classifierRounds m)).real
          {a | s a=c ∧ a∈invalidFirstMomentClass Sstar (F.offerInstance θ).totalFirstMoment})≤
      ∑ θ : Fin F.size, (F.weight θ:ℝ)*
        ((F.offerInstance θ).trainingCoordinateLaw (classifierRounds m)).real {a | s a=c}*
        (L c).targetGamePayoff (F.offerInstance θ) (F.target θ) C) :
    -κ-1/(m:ℝ)^4≤∑ θ : Fin F.size, (F.weight θ:ℝ)*
      (finiteResponseLearner s hs L).targetGamePayoff (F.offerInstance θ) (F.target θ) C := by
  have hW : (∑ θ : Fin F.size, (F.weight θ:ℝ))=1 := by exact_mod_cast F.weight_sum
  have hMass : (∑ c : ι, ∑ θ : Fin F.size, (F.weight θ:ℝ)*
      ((F.offerInstance θ).trainingCoordinateLaw (classifierRounds m)).real {a | s a=c})=1 := by
    rw [Finset.sum_comm]
    simp_rw [←Finset.mul_sum,sum_selection_probabilities _ _ _ hs,mul_one]
    exact hW
  have hErrorSum : (∑ c : ι, ∑ θ : Fin F.size, (F.weight θ:ℝ)*
      ((F.offerInstance θ).trainingCoordinateLaw (classifierRounds m)).real
        {a | s a=c ∧ a∈invalidFirstMomentClass Sstar (F.offerInstance θ).totalFirstMoment})=
      ∑ θ : Fin F.size, (F.weight θ:ℝ)*((F.offerInstance θ).trainingCoordinateLaw (classifierRounds m)).real
        (invalidFirstMomentClass Sstar (F.offerInstance θ).totalFirstMoment) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro θ _
    rw [←Finset.mul_sum,sum_selection_cell_probabilities _ s hs]
  have hError : (∑ θ : Fin F.size, (F.weight θ:ℝ)*((F.offerInstance θ).trainingCoordinateLaw (classifierRounds m)).real
      (invalidFirstMomentClass Sstar (F.offerInstance θ).totalFirstMoment))≤1/(m:ℝ)^4 := by
    calc
      _≤∑ θ : Fin F.size, (F.weight θ:ℝ)*(1/(m:ℝ)^4) := Finset.sum_le_sum fun θ _ =>
        mul_le_mul_of_nonneg_left (firstMomentClassifier_invalid_probability (F.offerInstance θ) (hcap θ) hm hS)
          (F.weight θ).coe_nonneg
      _=1/(m:ℝ)^4 := by rw [←Finset.sum_mul,hW,one_mul]
  have hGame : (∑ θ : Fin F.size, (F.weight θ:ℝ)*
      (finiteResponseLearner s hs L).targetGamePayoff (F.offerInstance θ) (F.target θ) C)=
      ∑ c : ι, ∑ θ : Fin F.size, (F.weight θ:ℝ)*
        ((F.offerInstance θ).trainingCoordinateLaw (classifierRounds m)).real {a | s a=c}*
        (L c).targetGamePayoff (F.offerInstance θ) (F.target θ) C := by
    simp_rw [finiteResponseLearner_targetGamePayoff _
      ((F.offerInstance _).integrable_maximum_of_bounded (hcap _)) s hs L,Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c _
    apply Finset.sum_congr rfl
    intro θ _
    ring
  have hSum := Finset.sum_le_sum (s:=Finset.univ) (fun c _ => hLocal c)
  rw [Finset.sum_sub_distrib,←Finset.mul_sum,hMass,mul_one,hErrorSum,←hGame] at hSum
  linarith only [hSum,hError]

end ProphetSecretary.Statistics
