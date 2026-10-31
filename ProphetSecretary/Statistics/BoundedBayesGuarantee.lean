import ProphetSecretary.Statistics.BoundedBayesRate

/-!
# Bounded reward and reach for the fixed finite-program learner

The learner depends only on dimension, alphabet, sample count and public mean
floor. Its program maximizes the feasible rate and requires no value of the
optimal global ratio as input. Endpoint actions and exact sample counts hold
on every raw training outcome. Paper correspondence: `upbayes:theorem`.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

lemma boundedClockMeshLearner_source_guarantees_of_rate {n m : ℕ}
    (G : Finset ℝ) (hBound : ∀ x∈G, x∈Icc (0 : ℝ) 1) (hz : (0 : ℝ)∈G)
    (hm : 0<m) {mu A : ℝ} (hmu : 0<mu) (hA : 0≤A)
    (hRate : optimalCompetitiveRatio-A/(m : ℝ)≤
      boundedMeshRate n (4*m) m G (fun x hx => (hBound x hx).1) mu (1/80) (2*Real.log (m : ℝ)))
    (P : Instance n) (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G)
    (hMean : mu≤P.expectedMaximum) (hUpper : P.expectedMaximum≤1/80)
    (hCount : P.positiveCount≤2*Real.log (m : ℝ)) :
    optimalCompetitiveRatio*P.expectedMaximum-boundedResponseConstant A mu/(m : ℝ)≤
      (boundedClockMeshLearner (n:=n) (k:=4*m) m G (fun x hx => (hBound x hx).1)
        mu (1/80) (2*Real.log (m : ℝ))).expectedReward P ∧
    ∀ i, optimalCompetitiveRatio-boundedResponseConstant A mu/(m : ℝ)≤
      (boundedClockMeshLearner (n:=n) (k:=4*m) m G (fun x hx => (hBound x hx).1)
        mu (1/80) (2*Real.log (m : ℝ))).reachProbability P i := by
  have h := boundedClockMeshLearner_guarantees_of_rate G hBound hz hm hmu (1/80)
    (2*Real.log (m : ℝ)) hRate P hG hMean hUpper hCount
  have hM : P.expectedMaximum≤1 := hUpper.trans (by norm_num)
  have hCost : boundedResponseConstant A mu/(m : ℝ)*P.expectedMaximum≤
      boundedResponseConstant A mu/(m : ℝ) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hM
      (div_nonneg (boundedResponseConstant_positive hA hmu).le (Nat.cast_nonneg m))
  refine ⟨?_,h.2⟩
  calc
    _ ≤ optimalCompetitiveRatio*P.expectedMaximum-
        (boundedResponseConstant A mu/(m : ℝ))*P.expectedMaximum := sub_le_sub_left hCost _
    _ = (optimalCompetitiveRatio-boundedResponseConstant A mu/(m : ℝ))*P.expectedMaximum := by ring
    _ ≤ _ := h.1

theorem exists_bounded_reward_reach_of_scalarDiameter (mu : ℝ) (hmu : 0<mu) (hmuHi : mu<1/80)
    (hDiameter : ∀ S0 : ℝ, 0<S0 → ∃ D : ℝ, 0≤D ∧
      ∀ (n : ℕ) (P : Instance n), (∀ i, ∀ᵐ x ∂P.law i, x≤1) →
      mu/2≤P.expectedMaximum → P.totalFirstMoment≤S0 → ∀ a b : ℝ,
      a∈Icc (0 : ℝ) 1 → b∈Icc (0 : ℝ) 1 →
      (a-b)^2≤D*(normalizedScalarGap P a+normalizedScalarGap P b)) :
    ∃ K : ℝ, 0<K ∧ ∀ (n m : ℕ), 1≤m → ∀ (G : Finset ℝ)
      (_hBound : ∀ x∈G, x∈Icc (0 : ℝ) 1), (0 : ℝ)∈G →
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
  obtain ⟨A,hA,hRate⟩ := exists_boundedMesh_rate_of_scalarDiameter mu hmu hmuHi hDiameter
  refine ⟨boundedResponseConstant A mu,boundedResponseConstant_positive hA.le hmu,?_⟩
  intro n m hm G hBound hz
  let L : Learner n (4*m) := boundedClockMeshLearner m G (fun x hx => (hBound x hx).1)
    mu (1/80) (2*Real.log (m : ℝ))
  refine ⟨L,?_,?_,?_,?_⟩
  · exact boundedClockMeshLearner_accepts_cap m G (fun x hx => (hBound x hx).1)
      mu (1/80) (2*Real.log (m : ℝ))
  · exact boundedClockMeshLearner_rejects_zero m G (fun x hx => (hBound x hx).1)
      mu (1/80) (2*Real.log (m : ℝ))
  · exact boundedClockMeshLearner_requests_eq m G (fun x hx => (hBound x hx).1)
      mu (1/80) (2*Real.log (m : ℝ))
  · intro P hG hMean hUpper hCount
    exact boundedClockMeshLearner_source_guarantees_of_rate G hBound hz (by omega) hmu hA.le
      (hRate n m hm G hBound) P hG hMean hUpper hCount

end ProphetSecretary.Statistics
