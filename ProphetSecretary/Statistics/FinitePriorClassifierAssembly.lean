import ProphetSecretary.Statistics.FinitePriorClassifierCell

/-!
# Actual finite-prior classifier response assembly

Only the finitely many observed sample cells require a response choice. Each
response uses fresh independent training columns. The actual finite patch
preserves endpoint actions on every raw outcome and adds the preliminary
classifier rounds to the hard per-distribution budget.
-/

open MeasureTheory Set
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model ProphetSecretary.Probability ProphetSecretary.Analysis
variable {n m d : ℕ}

theorem exists_classifier_response_of_reweighted_responses (F : FinitePrior n) (G : Finset ℝ)
    (hm : 2≤m) (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1)
    (hG : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x∈G)
    {Sstar C loss : ℝ} (hS : 1≤Sstar) (hC : C∈Icc (0 : ℝ) 1) (hLoss : 0≤loss)
    (hResponse : ∀ (q : Fin F.size → ℝ≥0) (hq : 0<∑ θ, q θ) (low : Bool),
      (∀ θ : Fin (F.reweightedPrior q hq).size, 0<(F.reweightedPrior q hq).weight θ →
        if low=true then (F.offerInstance θ).totalFirstMoment≤3*Sstar
        else Sstar≤(F.offerInstance θ).totalFirstMoment) →
      ∃ L : Learner n d,
        (∀ y r t i H, L.policy.decide (y,r) t i 1 H=true) ∧
        (∀ y r t i H, L.policy.decide (y,r) t i 0 H=false) ∧
        -loss≤∑ θ : Fin (F.reweightedPrior q hq).size,
          ((F.reweightedPrior q hq).weight θ : ℝ)*L.targetGamePayoff
            ((F.reweightedPrior q hq).offerInstance θ) ((F.reweightedPrior q hq).target θ) C) :
    ∃ L : Learner n (classifierRounds m+d),
      (∀ y r t i H, L.policy.decide (y,r) t i 1 H=true) ∧
      (∀ y r t i H, L.policy.decide (y,r) t i 0 H=false) ∧
      -loss-1/(m : ℝ)^4≤∑ θ : Fin F.size, (F.weight θ : ℝ)*
        L.targetGamePayoff (F.offerInstance θ) (F.target θ) C := by
  let I := GridResponseIndex n (classifierRounds m) G
  let s := finiteObservationCode (preliminaryGrid n (classifierRounds m) G)
  have hs : Measurable s := measurable_finiteObservationCode _
  have hCells : ∀ c : I, ∃ L : Learner n d,
      (∀ y r t i H, L.policy.decide (y,r) t i 1 H=true) ∧
      (∀ y r t i H, L.policy.decide (y,r) t i 0 H=false) ∧
      -loss*(∑ θ : Fin F.size, (F.weight θ : ℝ)*
        ((F.offerInstance θ).trainingCoordinateLaw (classifierRounds m)).real {a | s a=c})-
      (∑ θ : Fin F.size, (F.weight θ : ℝ)*
        ((F.offerInstance θ).trainingCoordinateLaw (classifierRounds m)).real
          {a | s a=c ∧ a∈invalidFirstMomentClass Sstar (F.offerInstance θ).totalFirstMoment})≤
      ∑ θ : Fin F.size, (F.weight θ : ℝ)*
        ((F.offerInstance θ).trainingCoordinateLaw (classifierRounds m)).real {a | s a=c}*
        L.targetGamePayoff (F.offerInstance θ) (F.target θ) C := by
    intro c
    cases c with
    | some y => exact F.exists_classifierCell_response G hcap hC hLoss hResponse y
    | none =>
      have hNone (θ : Fin F.size) :
          ((F.offerInstance θ).trainingCoordinateLaw (classifierRounds m)).real {a | s a=none}=0 :=
        classifierCell_off_grid_mass (F.offerInstance θ) G (hG θ)
      have hInvalid (θ : Fin F.size) :
          ((F.offerInstance θ).trainingCoordinateLaw (classifierRounds m)).real
            {a | s a=none ∧ a∈invalidFirstMomentClass Sstar (F.offerInstance θ).totalFirstMoment}=0 := by
        apply le_antisymm _ measureReal_nonneg
        exact (measureReal_mono (fun _ h => h.1) (measure_ne_top _ _)).trans (hNone θ).le
      refine ⟨capOnlyFallback n d,?_,?_,?_⟩
      · intro y r t i H
        simp [capOnlyFallback_decide]
      · intro y r t i H
        simp only [capOnlyFallback_decide,zero_ne_one,if_false]
      · simp only [hNone,hInvalid,mul_zero,zero_mul,Finset.sum_const_zero,sub_zero,le_refl]
  choose L hCap hZero hGame using hCells
  refine ⟨finiteGridResponseLearner G L,?_,?_,?_⟩
  · intro y r t i H
    change (finiteResponseLearner s hs L).policy.decide (y,r) t i 1 H=true
    rw [finiteResponseLearner_decide]
    exact hCap _ _ _ _ _ _
  · intro y r t i H
    change (finiteResponseLearner s hs L).policy.decide (y,r) t i 0 H=false
    rw [finiteResponseLearner_decide]
    exact hZero _ _ _ _ _ _
  · exact finitePriorResponse_bound_of_cellwise F hm hcap hS s hs L C loss hGame

end ProphetSecretary.Statistics.FinitePrior
