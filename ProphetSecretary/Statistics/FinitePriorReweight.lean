import ProphetSecretary.Statistics.FinitePriorSupport

/-!
# Normalizing finite prior masses on an observed class cell

The masses may be prior weights multiplied by the likelihood of an observed
preliminary cell and by its validity indicator. Normalization is used only
when retained mass is positive. Zero-weight atoms are then removed before
applying a response theorem whose hypotheses hold on every retained atom.
-/

open MeasureTheory Set
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ}

noncomputable def reweightedPrior (F : FinitePrior n) (q : Fin F.size → ℝ≥0)
    (hq : 0<∑ θ, q θ) : FinitePrior n where
  size := F.size
  weight θ := q θ/(∑ j, q j)
  weight_sum := by rw [←Finset.sum_div,div_self (ne_of_gt hq)]
  offerInstance := F.offerInstance
  target := F.target

lemma reweightedPrior_positive_support (F : FinitePrior n) (q : Fin F.size → ℝ≥0)
    (hq : 0<∑ θ, q θ) (θ : Fin F.size)
    (hPositive : 0<(F.reweightedPrior q hq).weight θ) : q θ≠0 := by
  intro hZero
  have hWeight : (F.reweightedPrior q hq).weight θ=0 := by simp only [reweightedPrior,hZero,zero_div]
  exact (ne_of_gt hPositive) hWeight

lemma reweightedPrior_weighted_sum (F : FinitePrior n) (q : Fin F.size → ℝ≥0)
    (hq : 0<∑ θ, q θ) (g : Fin F.size → ℝ) :
    (∑ θ, (q θ : ℝ)*g θ)=(∑ θ, (q θ : ℝ))*
      (∑ θ : Fin (F.reweightedPrior q hq).size, ((F.reweightedPrior q hq).weight θ : ℝ)*g θ) := by
  have hSum : (∑ θ, (q θ : ℝ))≠0 := by
    have hPos : 0<∑ θ, (q θ : ℝ) := by exact_mod_cast hq
    exact hPos.ne'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro θ _
  change (q θ : ℝ)*g θ=(∑ j, (q j : ℝ))*(((q θ/(∑ j, q j) : ℝ≥0) : ℝ)*g θ)
  rw [NNReal.coe_div,NNReal.coe_sum]
  field_simp [hSum]

/-- The equality concerns the actual learner's training and online payoff. -/
theorem reweightedPrior_targetGamePayoff (F : FinitePrior n) (q : Fin F.size → ℝ≥0)
    (hq : 0<∑ θ, q θ) {d : ℕ} (L : Learner n d) (C : ℝ) :
    (∑ θ : Fin F.size, (q θ : ℝ)*L.targetGamePayoff (F.offerInstance θ) (F.target θ) C)=
      (∑ θ : Fin F.size, (q θ : ℝ))*
        (∑ θ : Fin (F.reweightedPrior q hq).size, ((F.reweightedPrior q hq).weight θ : ℝ)*
          L.targetGamePayoff ((F.reweightedPrior q hq).offerInstance θ) ((F.reweightedPrior q hq).target θ) C) :=
  F.reweightedPrior_weighted_sum q hq (fun θ => L.targetGamePayoff (F.offerInstance θ) (F.target θ) C)

lemma positiveReweightedPrior_supported (F : FinitePrior n) (q : Fin F.size → ℝ≥0)
    (hq : 0<∑ θ, q θ) {Q : Instance n → Option (Fin n) → Prop}
    (hClass : ∀ θ, q θ≠0 → Q (F.offerInstance θ) (F.target θ)) :
    ∀ θ : Fin (F.reweightedPrior q hq).positivePrior.size,
      Q ((F.reweightedPrior q hq).positivePrior.offerInstance θ) ((F.reweightedPrior q hq).positivePrior.target θ) :=
  (F.reweightedPrior q hq).positivePrior_supported (fun θ hPositive =>
    hClass θ (F.reweightedPrior_positive_support q hq θ hPositive))

/-- Normalize positive retained masses, apply the actual class response, and
return its unnormalized Bayes bound without changing any offer law or target. -/
theorem exists_classResponse_for_positive_masses (F : FinitePrior n) (q : Fin F.size → ℝ≥0)
    (hq : 0<∑ θ, q θ) {d : ℕ} (C loss : ℝ) {Q : Instance n → Option (Fin n) → Prop}
    (hClass : ∀ θ, q θ≠0 → Q (F.offerInstance θ) (F.target θ))
    (hResponse : ∀ A : FinitePrior n, (∀ θ, Q (A.offerInstance θ) (A.target θ)) →
      ∃ L : Learner n d,
        (∀ y r t i H, L.policy.decide (y,r) t i 1 H=true) ∧
        (∀ y r t i H, L.policy.decide (y,r) t i 0 H=false) ∧
        -loss≤∑ θ : Fin A.size, (A.weight θ : ℝ)*L.targetGamePayoff (A.offerInstance θ) (A.target θ) C) :
    ∃ L : Learner n d,
      (∀ y r t i H, L.policy.decide (y,r) t i 1 H=true) ∧
      (∀ y r t i H, L.policy.decide (y,r) t i 0 H=false) ∧
      -loss*(∑ θ : Fin F.size, (q θ : ℝ))≤
        ∑ θ : Fin F.size, (q θ : ℝ)*L.targetGamePayoff (F.offerInstance θ) (F.target θ) C := by
  let A := F.reweightedPrior q hq
  obtain ⟨L,hCap,hZero,hGame⟩ := hResponse A.positivePrior (F.positiveReweightedPrior_supported q hq hClass)
  have hGameA : -loss≤∑ θ : Fin A.size, (A.weight θ : ℝ)*
      L.targetGamePayoff (A.offerInstance θ) (A.target θ) C := by
    rw [←A.positivePrior_targetGamePayoff L C]
    exact hGame
  have hSum : 0≤∑ θ : Fin F.size, (q θ : ℝ) := Finset.sum_nonneg (fun θ _ => (q θ).coe_nonneg)
  have hScaled := mul_le_mul_of_nonneg_left hGameA hSum
  have hWeight := F.reweightedPrior_targetGamePayoff q hq L C
  change (∑ θ : Fin F.size, (q θ : ℝ)*L.targetGamePayoff (F.offerInstance θ) (F.target θ) C)=
    (∑ θ : Fin F.size, (q θ : ℝ))*(∑ θ : Fin A.size, (A.weight θ : ℝ)*
      L.targetGamePayoff (A.offerInstance θ) (A.target θ) C) at hWeight
  rw [←hWeight] at hScaled
  refine ⟨L,hCap,hZero,?_⟩
  nlinarith only [hScaled]

end ProphetSecretary.Statistics.FinitePrior
