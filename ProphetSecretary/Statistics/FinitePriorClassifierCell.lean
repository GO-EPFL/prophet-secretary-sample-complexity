import ProphetSecretary.Statistics.ClassifierObservationCells
import ProphetSecretary.Statistics.FinitePriorReweight

/-!
# Genuine prior normalization on each finite classifier cell

The retained masses are actual prior weights times actual preliminary-cell
probabilities, with invalid atoms removed. Positive retained mass is normalized
to an actual finite prior. The selected response is then unnormalized; discarded
mass is charged using the universal game lower bound.
-/

open MeasureTheory Set
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model ProphetSecretary.Probability ProphetSecretary.Analysis

variable {n m d : ℕ}

theorem exists_classifierCell_response (F : FinitePrior n) (G : Finset ℝ)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1)
    {Sstar C loss : ℝ} (hC : C∈Icc (0 : ℝ) 1) (hLoss : 0≤loss)
    (hResponse : ∀ (q : Fin F.size → ℝ≥0) (hq : 0<∑ θ, q θ) (low : Bool),
      (∀ θ : Fin (F.reweightedPrior q hq).size, 0<(F.reweightedPrior q hq).weight θ →
        if low=true then (F.offerInstance θ).totalFirstMoment≤3*Sstar
        else Sstar≤(F.offerInstance θ).totalFirstMoment) →
      ∃ L : Learner n d,
        (∀ y r t i H, L.policy.decide (y,r) t i 1 H=true) ∧
        (∀ y r t i H, L.policy.decide (y,r) t i 0 H=false) ∧
        -loss≤∑ θ : Fin (F.reweightedPrior q hq).size,
          ((F.reweightedPrior q hq).weight θ : ℝ)*L.targetGamePayoff
            ((F.reweightedPrior q hq).offerInstance θ) ((F.reweightedPrior q hq).target θ) C)
    (y : {a : (Fin n × Fin (classifierRounds m)) → ℝ // a∈preliminaryGrid n (classifierRounds m) G}) :
    ∃ L : Learner n d,
      (∀ a r t i H, L.policy.decide (a,r) t i 1 H=true) ∧
      (∀ a r t i H, L.policy.decide (a,r) t i 0 H=false) ∧
      -loss*(∑ θ : Fin F.size, (F.weight θ : ℝ)*
        ((F.offerInstance θ).trainingCoordinateLaw (classifierRounds m)).real
          {a | finiteObservationCode (preliminaryGrid n (classifierRounds m) G) a=some y})-
      (∑ θ : Fin F.size, (F.weight θ : ℝ)*
        ((F.offerInstance θ).trainingCoordinateLaw (classifierRounds m)).real
          {a | finiteObservationCode (preliminaryGrid n (classifierRounds m) G) a=some y ∧
            a∈invalidFirstMomentClass Sstar (F.offerInstance θ).totalFirstMoment})≤
      ∑ θ : Fin F.size, (F.weight θ : ℝ)*
        ((F.offerInstance θ).trainingCoordinateLaw (classifierRounds m)).real
          {a | finiteObservationCode (preliminaryGrid n (classifierRounds m) G) a=some y}*
        L.targetGamePayoff (F.offerInstance θ) (F.target θ) C := by
  let w : Fin F.size → ℝ≥0 := fun θ => F.weight θ *
    (((F.offerInstance θ).trainingCoordinateLaw (classifierRounds m))
      {a | finiteObservationCode (preliminaryGrid n (classifierRounds m) G) a=some y}).toNNReal
  let q : Fin F.size → ℝ≥0 := fun θ =>
    if y.val∈invalidFirstMomentClass Sstar (F.offerInstance θ).totalFirstMoment then 0 else w θ
  have hW (θ : Fin F.size) : (w θ : ℝ)=(F.weight θ : ℝ)*
      ((F.offerInstance θ).trainingCoordinateLaw (classifierRounds m)).real
        {a | finiteObservationCode (preliminaryGrid n (classifierRounds m) G) a=some y} := rfl
  have hValid (hq : 0<∑ θ, q θ) (θ : Fin F.size)
      (hθ : 0<(F.reweightedPrior q hq).weight θ) :
      y.val∉invalidFirstMomentClass Sstar (F.offerInstance θ).totalFirstMoment := by
    have hn := F.reweightedPrior_positive_support q hq θ hθ
    intro hy
    exact hn (by simp only [q,if_pos hy])
  have hChosen : ∃ L : Learner n d,
      (∀ a r t i H, L.policy.decide (a,r) t i 1 H=true) ∧
      (∀ a r t i H, L.policy.decide (a,r) t i 0 H=false) ∧
      -loss*(∑ θ : Fin F.size, (q θ : ℝ))≤
        ∑ θ : Fin F.size, (q θ : ℝ)*L.targetGamePayoff (F.offerInstance θ) (F.target θ) C := by
    by_cases hq : 0<∑ θ, q θ
    · have hClass : ∀ θ : Fin (F.reweightedPrior q hq).size,
          0<(F.reweightedPrior q hq).weight θ →
          if selectLowFirstMoment Sstar y.val=true then (F.offerInstance θ).totalFirstMoment≤3*Sstar
          else Sstar≤(F.offerInstance θ).totalFirstMoment := by
        intro θ hθ
        have hv := hValid hq θ hθ
        cases hl : selectLowFirstMoment Sstar y.val with
        | false => exact validClassifier_high y.val Sstar _ hv hl
        | true => exact validClassifier_low y.val Sstar _ hv hl
      obtain ⟨L,hCap,hZero,hGame⟩ := hResponse q hq (selectLowFirstMoment Sstar y.val) hClass
      have hMass : 0≤∑ θ : Fin F.size, (q θ : ℝ) := Finset.sum_nonneg (fun θ _ => (q θ).coe_nonneg)
      have hScaled := mul_le_mul_of_nonneg_left hGame hMass
      rw [←F.reweightedPrior_targetGamePayoff q hq L C] at hScaled
      exact ⟨L,hCap,hZero,by nlinarith only [hScaled]⟩
    · have hZero : (∑ θ : Fin F.size, q θ)=0 := le_antisymm (le_of_not_gt hq) (show (0 : ℝ≥0)≤_ from bot_le)
      have hEach (θ : Fin F.size) : q θ=0 := by
        apply le_antisymm _ (show (0 : ℝ≥0)≤_ from bot_le)
        exact (Finset.single_le_sum (fun j _ => (show (0 : ℝ≥0)≤q j from bot_le)) (Finset.mem_univ θ)).trans hZero.le
      refine ⟨capOnlyFallback n d,?_,?_,?_⟩
      · intro a r t i H
        simp [capOnlyFallback_decide]
      · intro a r t i H
        simp only [capOnlyFallback_decide,zero_ne_one,if_false]
      · simp only [hEach,NNReal.coe_zero,mul_zero,zero_mul,Finset.sum_const_zero,le_refl]
  obtain ⟨L,hCap,hZero,hGood⟩ := hChosen
  refine ⟨L,hCap,hZero,?_⟩
  have hq (θ : Fin F.size) : 0≤(q θ : ℝ) ∧ (q θ : ℝ)≤(w θ : ℝ) := by
    constructor
    · exact (q θ).coe_nonneg
    · dsimp only [q]
      split_ifs
      · exact (w θ).coe_nonneg
      · exact le_rfl
  have hBad (θ : Fin F.size) : (w θ : ℝ)-(q θ : ℝ)=
      (F.weight θ : ℝ)*((F.offerInstance θ).trainingCoordinateLaw (classifierRounds m)).real
        {a | finiteObservationCode (preliminaryGrid n (classifierRounds m) G) a=some y ∧
          a∈invalidFirstMomentClass Sstar (F.offerInstance θ).totalFirstMoment} := by
    rw [classifierCell_invalid_mass]
    dsimp only [q]
    split_ifs
    · simpa only [NNReal.coe_zero,sub_zero] using hW θ
    · simp only [sub_self,mul_zero]
  have hBound := discardedMass_game_bound (fun θ => (w θ : ℝ)) (fun θ => (q θ : ℝ))
    (fun θ => L.targetGamePayoff (F.offerInstance θ) (F.target θ) C) hLoss hq
    (fun θ => ProphetSecretary.Statistics.Learner.targetGamePayoff_ge_neg_one L (F.offerInstance θ) (hcap θ) (F.target θ) hC) hGood
  simp only [hBad] at hBound
  simpa only [hW] using hBound

end ProphetSecretary.Statistics.FinitePrior
