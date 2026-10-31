import ProphetSecretary.Statistics.OuterBayesUpperBound
import ProphetSecretary.Limiting.ScalarDiameter

/-!
# Bounded reward/reach and the sample upper bound

The proved uniform quadratic scalar diameter discharges the last structural
input to the actual Bayes responses, finite rate program and outer reduction.
The constants precede the instance size and unknown laws. Training budgets
hold for every raw outcome; all performance expectations include training,
online arrivals and independent policy randomness. Paper correspondence:
`upbayes:theorem` and `upouter:theorem`.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

private lemma unit_scalar_diameter (mu : ℝ) (hmu : 0<mu) :
    ∀ S0 : ℝ, 0<S0 → ∃ D : ℝ, 0≤D ∧
      ∀ (n : ℕ) (P : Instance n), (∀ i, ∀ᵐ x ∂P.law i, x≤1) →
      mu≤P.expectedMaximum → P.totalFirstMoment≤S0 → ∀ a b : ℝ,
      a∈Icc (0 : ℝ) 1 → b∈Icc (0 : ℝ) 1 →
      (a-b)^2≤D*(normalizedScalarGap P a+normalizedScalarGap P b) := by
  intro S0 hS0
  obtain ⟨D,hD,hBound⟩ := ProphetSecretary.Limiting.bounded_scalarGap_quadratic_diameter 1 S0 mu hS0 hmu
  refine ⟨D,hD.le,?_⟩
  intro n P hcap hMean hS a b ha hb
  have hSq : (a-b)^2=(b-a)^2 := by ring
  rw [hSq]
  exact hBound n P hcap hS hMean a b ha hb

/-- `upbayes:theorem`: the selected learner is fixed before the unknown law. -/
theorem bounded_reward_reach (mu : ℝ) (hmu : 0<mu) (hmuHi : mu<1/80)
 :
    ∃ K : ℝ, 0<K ∧ ∀ (n m : ℕ), 1≤m → ∀ (G : Finset ℝ)
      (_hBound : ∀ x∈G, x∈Icc (0 : ℝ) 1), (0 : ℝ)∈G → (1 : ℝ)∈G →
      ∃ L : Learner n (4*m),
        (∀ y r t i H, L.policy.decide (y,r) t i 1 H=true) ∧
        (∀ y r t i H, L.policy.decide (y,r) t i 0 H=false) ∧
        (∀ (y : Reservoir n (4*m)) (r : L.Seed) (i : Fin n),
          requests (trainingTranscript L.request r y) i=4*m) ∧
        ∀ P : Instance n, (∀ i, ∀ᵐ x ∂P.law i, x∈G) →
          mu≤P.expectedMaximum → P.expectedMaximum≤1/80 →
          P.positiveCount≤2*Real.log (m : ℝ) →
          optimalCompetitiveRatio*P.expectedMaximum-K/(m : ℝ)≤L.expectedReward P ∧
          ∀ i, optimalCompetitiveRatio-K/(m : ℝ)≤L.reachProbability P i := by
  obtain ⟨K,hK,hAll⟩ := exists_bounded_reward_reach_of_scalarDiameter mu hmu hmuHi
    (unit_scalar_diameter (mu/2) (by positivity))
  refine ⟨K,hK,?_⟩
  intro n m hm G hBound hz _hOne
  exact hAll n m hm G hBound hz

/-- `upouter:theorem`: one universal constant works for every finite size and
all independent nonnegative offers with positive finite expected maximum. -/
theorem sample_upper_bound :
    ∃ Kout : ℝ, 0<Kout ∧ ∀ k : ℕ, 1≤k → FeasibleBudget (Kout/(k : ℝ)) k :=
  outer_sample_upper_bound_of_scalarDiameter
    (unit_scalar_diameter ((1/10000000 : ℝ)/2) (by norm_num))

end ProphetSecretary.Statistics
