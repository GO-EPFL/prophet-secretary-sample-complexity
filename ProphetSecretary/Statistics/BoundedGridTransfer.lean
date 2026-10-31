import ProphetSecretary.Statistics.BoundedNatureGrid
import ProphetSecretary.Model.FiniteProbabilityApproximation

/-!
# Transfer of the fixed finite-grid learner to all supported laws

The optimizing learner is fixed independently of the unknown atom
probabilities. Its constraints at the rounded law give the stated reward
and reach deficits under the original law, uniformly over all strategies.
The lower mean floor requires only the explicit rounding margin.
-/

open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n k N : ℕ}

lemma exists_boundedNatureCounts_for_rounded (G : Finset ℝ)
    (hBound : ∀ x∈G, x∈Icc (0 : ℝ) 1) (hN : 0<N) (hz : (0 : ℝ)∈G)
    (μlo μhi ℓ : ℝ) (P : Instance n) (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G)
    (hLower : μlo+P.atomRoundingLoss G N hz≤P.expectedMaximum)
    (hUpper : P.expectedMaximum≤μhi) (hCount : P.positiveCount≤ℓ) :
    ∃ a : BoundedNatureCounts (n:=n) G (fun x hx => (hBound x hx).1) hN μlo μhi ℓ,
      probabilityGridInstance (fun a : G => a.val) (fun a => (hBound a.val a.property).1) hN a.val =
        P.roundAtomProbabilities G (fun x hx => (hBound x hx).1) hG N hN hz := by
  obtain ⟨a,ha⟩ := P.roundAtomProbabilities_mem_grid G (fun x hx => (hBound x hx).1) hG N hN hz
  have hM := P.roundAtomProbabilities_benchmark_bounds G hBound hG N hN hz
  have hT := P.roundAtomProbabilities_tailCount_le G (fun x hx => (hBound x hx).1) hG N hN hz (b:=0) le_rfl
  have hEligible : μlo≤(probabilityGridInstance (fun a : G => a.val)
        (fun a => (hBound a.val a.property).1) hN a).expectedMaximum ∧
      (probabilityGridInstance (fun a : G => a.val)
        (fun a => (hBound a.val a.property).1) hN a).expectedMaximum≤μhi ∧
      (probabilityGridInstance (fun a : G => a.val)
        (fun a => (hBound a.val a.property).1) hN a).positiveCount≤ℓ := by
    rw [ha]
    refine ⟨by linarith only [hM.1,hLower],hM.2.trans hUpper,?_⟩
    exact hT.trans hCount
  exact ⟨⟨a,hEligible⟩,ha⟩

theorem boundedGridLearner_rounding_transfer (G : Finset ℝ)
    (hBound : ∀ x∈G, x∈Icc (0 : ℝ) 1) (hN : 0<N) (hz : (0 : ℝ)∈G)
    (μlo μhi ℓ : ℝ) (P : Instance n) (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G)
    (hLower : μlo+P.atomRoundingLoss G N hz≤P.expectedMaximum)
    (hUpper : P.expectedMaximum≤μhi) (hCount : P.positiveCount≤ℓ) :
    boundedGridRate (n:=n) (k:=k) G (fun x hx => (hBound x hx).1) hN μlo μhi ℓ*P.expectedMaximum-
        ((k : ℝ)+2)*P.atomRoundingLoss G N hz ≤
      (boundedGridLearner (k:=k) G (fun x hx => (hBound x hx).1) hN μlo μhi ℓ).expectedReward P ∧
    ∀ i, boundedGridRate (n:=n) (k:=k) G (fun x hx => (hBound x hx).1) hN μlo μhi ℓ-
        ((k : ℝ)+1)*P.atomRoundingLoss G N hz ≤
      (boundedGridLearner (k:=k) G (fun x hx => (hBound x hx).1) hN μlo μhi ℓ).reachProbability P i := by
  let hNonneg := fun x hx => (hBound x hx).1
  let L : RankLearner n k := boundedGridLearner G hNonneg hN μlo μhi ℓ
  let γ := boundedGridRate (n:=n) (k:=k) G hNonneg hN μlo μhi ℓ
  let Q := P.roundAtomProbabilities G hNonneg hG N hN hz
  obtain ⟨a,ha⟩ := exists_boundedNatureCounts_for_rounded G hBound hN hz μlo μhi ℓ P hG hLower hUpper hCount
  have hReward : γ*Q.expectedMaximum≤L.expectedReward Q := by
    have h := boundedGridLearner_target_constraints (k:=k) G hNonneg hN μlo μhi ℓ
      (fun x hx => (hBound x hx).2) (a,none)
    change γ*(probabilityGridInstance (fun a : G => a.val)
      (fun a => hNonneg a.val a.property) hN a.val).expectedMaximum ≤
      L.expectedReward (probabilityGridInstance (fun a : G => a.val)
        (fun a => hNonneg a.val a.property) hN a.val) at h
    rwa [ha] at h
  have hReach (i : Fin n) : γ≤L.reachProbability Q i := by
    have h := boundedGridLearner_target_constraints (k:=k) G hNonneg hN μlo μhi ℓ
      (fun x hx => (hBound x hx).2) (a,some i)
    change γ*1≤L.reachProbability (probabilityGridInstance (fun a : G => a.val)
      (fun a => hNonneg a.val a.property) hN a.val) i at h
    simpa only [ha,mul_one] using h
  have h := rankLearner_rounding_guarantee_transfer L (fun a : G => a.val)
    (fun a => hBound a.val a.property) (fun i (a : G) => (P.law i).real {a.val})
    (fun i => finiteSupport_weights_simplex (P.law i) G (hG i)) N hN ⟨0,hz⟩
    (boundedGridRate_mem_Icc G hNonneg hN μlo μhi ℓ) hReward hReach
  rwa [finiteSupportInstance_eq P G hNonneg hG] at h

end ProphetSecretary.Statistics
