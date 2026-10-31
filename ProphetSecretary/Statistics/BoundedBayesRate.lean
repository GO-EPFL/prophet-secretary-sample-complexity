import ProphetSecretary.Statistics.FiniteNaturePrior
import ProphetSecretary.Statistics.BoundedClockRateGuarantee

/-!
# The actual bounded finite-program rate from Bayes responses

A prior on finite nature actions is an actual hidden-instance prior after a
finite relabelling. The resulting clock response is transported causally to
ranks and enters the proved finite rate program. One explicit constant covers
all sample counts, including those below the statistical sample threshold.
-/

open MeasureTheory Set
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability ProphetSecretary.Analysis

theorem exists_boundedMesh_rate_of_scalarDiameter (mu : ℝ) (hmu : 0<mu) (hmuHi : mu<1/80)
    (hDiameter : ∀ S0 : ℝ, 0<S0 → ∃ D : ℝ, 0≤D ∧
      ∀ (n : ℕ) (P : Instance n), (∀ i, ∀ᵐ x ∂P.law i, x≤1) →
      mu/2≤P.expectedMaximum → P.totalFirstMoment≤S0 → ∀ a b : ℝ,
      a∈Icc (0 : ℝ) 1 → b∈Icc (0 : ℝ) 1 →
      (a-b)^2≤D*(normalizedScalarGap P a+normalizedScalarGap P b)) :
    ∃ A : ℝ, 0<A ∧ ∀ (n m : ℕ), 1≤m → ∀ (G : Finset ℝ)
      (hBound : ∀ x∈G, x∈Icc (0 : ℝ) 1),
      optimalCompetitiveRatio-A/(m : ℝ)≤
        boundedMeshRate n (4*m) m G (fun x hx => (hBound x hx).1) mu (1/80) (2*Real.log (m : ℝ)) := by
  have hHalf : 0<mu/2 := by positivity
  obtain ⟨K,m0,hK,hm0,hAll⟩ :=
    FinitePrior.exists_finitePrior_bayes_response_of_scalarDiameter (mu/2) hHalf hDiameter
  let A := K/(mu/2)+(m0 : ℝ)
  have hA : 0<A := add_pos_of_pos_of_nonneg (div_pos hK hHalf) (Nat.cast_nonneg m0)
  refine ⟨A,hA,?_⟩
  intro n m hm G hBound
  have hmPos : (0 : ℝ)<m := by exact_mod_cast (show 0<m by omega)
  letI : NeZero m := ⟨by omega⟩
  let hNonneg := fun x hx => (hBound x hx).1
  let N := boundedGridMeshDenominator n (4*m) m G mu
  have hN : 0<N := boundedGridMeshDenominator_positive n (4*m) m G mu
  by_cases hLarge : m0≤m
  · let Θ := BoundedNatureAction (n:=n) G hNonneg hN (mu/2) (1/80) (2*Real.log (m : ℝ))
    let P : Θ → Instance n := boundedNatureInstance G hNonneg hN (mu/2) (1/80) (2*Real.log (m : ℝ))
    let J : Θ → Option (Fin n) := fun a => a.2
    have hSupported (θ : Θ) (i : Fin n) : ∀ᵐ x ∂(P θ).law i, x∈G :=
      boundedNatureInstance_supported G hNonneg hN (mu/2) (1/80) (2*Real.log (m : ℝ)) θ i
    have hCap (θ : Θ) (i : Fin n) : ∀ᵐ x ∂(P θ).law i, x≤1 :=
      (hSupported θ i).mono (fun x hx => (hBound x hx).2)
    have hMean (θ : Θ) : mu/2≤(P θ).expectedMaximum := θ.1.property.1
    have hUpper (θ : Θ) : (P θ).expectedMaximum≤1/80 := θ.1.property.2.1
    have hCount (θ : Θ) : (P θ).positiveCount≤2*Real.log (m : ℝ) := θ.1.property.2.2
    have hBayes : ∀ p∈stdSimplex ℝ Θ, ∃ L : RankLearner n (4*m),
        (∀ y r q i H, L.policy.decide (y,r) q i 1 H=true) ∧
        (∀ y r q i H, L.policy.decide (y,r) q i 0 H=false) ∧
        -K/(m : ℝ)≤∑ a : Θ, p a*L.targetGamePayoff (P a) (J a) optimalCompetitiveRatio := by
      intro p hp
      let F := naturePrior P J p hp
      obtain ⟨L,hLCap,hLZero,hGame⟩ := hAll n m hLarge F G
        (fun i j => hCap ((Fintype.equivFin Θ).symm i) j)
        (fun i j => hSupported ((Fintype.equivFin Θ).symm i) j)
        (fun i => hMean ((Fintype.equivFin Θ).symm i))
        (fun i => hUpper ((Fintype.equivFin Θ).symm i))
        (fun i => hCount ((Fintype.equivFin Θ).symm i))
      have hGame' : -K/(m : ℝ)≤∑ a : Θ, p a*L.targetGamePayoff (P a) (J a) optimalCompetitiveRatio := by
        rwa [naturePrior_targetGamePayoff] at hGame
      refine ⟨L.clockToRank,?_,?_,?_⟩
      · exact L.clockToRank_fixedAction 1 true hLCap
      · exact L.clockToRank_fixedAction 0 false hLZero
      · simpa only [L.clockToRank_targetGamePayoff] using hGame'
    have hRate := boundedGridRate_ge_of_bayes (n:=n) (k:=4*m) G hNonneg hN (mu/2) (1/80)
      (2*Real.log (m : ℝ)) (fun x hx => (hBound x hx).2) hHalf (by linarith only [hmuHi])
      optimalCompetitiveRatio_le_one (div_nonneg hK.le hmPos.le)
      (by simpa only [neg_div] using hBayes)
    have hRate' : optimalCompetitiveRatio-(K/(mu/2))/(m : ℝ)≤
        boundedMeshRate n (4*m) m G hNonneg mu (1/80) (2*Real.log (m : ℝ)) := by
      have hSwap : (K/(mu/2))/(m : ℝ)=(K/(m : ℝ))/(mu/2) := by ring
      rw [hSwap]
      exact hRate
    have hCoeff : (K/(mu/2))/(m : ℝ)≤A/(m : ℝ) :=
      div_le_div_of_nonneg_right (le_add_of_nonneg_right (Nat.cast_nonneg m0)) hmPos.le
    exact (sub_le_sub_left hCoeff optimalCompetitiveRatio).trans hRate'
  · have hRate0 : 0≤boundedMeshRate n (4*m) m G hNonneg mu (1/80) (2*Real.log (m : ℝ)) :=
      (boundedGridRate_mem_Icc (n:=n) (k:=4*m) G hNonneg hN (mu/2) (1/80) (2*Real.log (m : ℝ))).1
    have hm0Real : (m : ℝ)≤m0 := by exact_mod_cast (show m≤m0 by omega)
    have hLower : (m : ℝ)≤A := hm0Real.trans (le_add_of_nonneg_left (div_nonneg hK.le hHalf.le))
    have hOne : 1≤A/(m : ℝ) := (le_div_iff₀ hmPos).mpr (by simpa only [one_mul] using hLower)
    have hNonpos : optimalCompetitiveRatio-A/(m : ℝ)≤0 := by linarith only [optimalCompetitiveRatio_le_one,hOne]
    exact hNonpos.trans hRate0

end ProphetSecretary.Statistics
