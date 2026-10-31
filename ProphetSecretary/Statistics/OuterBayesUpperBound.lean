import ProphetSecretary.Statistics.BoundedBayesGuarantee
import ProphetSecretary.Statistics.OuterSampleUpperBound
import ProphetSecretary.Model.OuterUnitMeshGrid

/-!
# The actual sample upper bound from the scalar diameter inequality

The bounded learner is the same finite-program optimizer for every unknown
law. Its verified reward, reach and cap rules discharge the outer reduction's
statistical premise. The remaining input is one explicit uniform scalar
inequality, independent of the number of variables. Paper correspondence:
`upouter:theorem`.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

private lemma unitMesh_nonnegative (m : ℕ) : ∀ x∈meshGrid 1 m, 0≤x := by
  intro x hx
  obtain ⟨j,_hj,rfl⟩ := Finset.mem_image.mp hx
  change 0≤(1 : ℝ)/(m : ℝ)*(j : ℝ)
  positivity

noncomputable def outerBoundedMeshLearner (mu : ℝ) (n m : ℕ) : Learner n (4*m) :=
  boundedClockMeshLearner m (meshGrid 1 m) (unitMesh_nonnegative m)
    mu (1/80) (2*Real.log (m : ℝ))

theorem outer_sample_upper_bound_of_scalarDiameter
    (hDiameter : ∀ S0 : ℝ, 0<S0 → ∃ D : ℝ, 0≤D ∧
      ∀ (n : ℕ) (P : Instance n), (∀ i, ∀ᵐ x ∂P.law i, x≤1) →
      (1/10000000 : ℝ)/2≤P.expectedMaximum → P.totalFirstMoment≤S0 → ∀ a b : ℝ,
      a∈Icc (0 : ℝ) 1 → b∈Icc (0 : ℝ) 1 →
      (a-b)^2≤D*(normalizedScalarGap P a+normalizedScalarGap P b)) :
    ∃ Kout : ℝ, 0<Kout ∧ ∀ k : ℕ, 1≤k → FeasibleBudget (Kout/(k : ℝ)) k := by
  obtain ⟨A,hA,hRate⟩ := exists_boundedMesh_rate_of_scalarDiameter (1/10000000)
    (by norm_num) (by norm_num) hDiameter
  let K := boundedResponseConstant A (1/10000000)
  have hK : 0<K := boundedResponseConstant_positive hA.le (by norm_num)
  have hBounded : ∀ (n m : ℕ), 1≤m → ∀ Q : Instance n,
      (1/10000000≤Q.expectedMaximum ∧ Q.expectedMaximum≤1/80) →
      Q.positiveCount≤2*Real.log (m : ℝ) →
      (∀ i, ∀ᵐ x ∂Q.law i, x∈meshGrid 1 m) →
      (∀ i, ∀ᵐ x ∂Q.law i, x≤1) →
      (∀ᵐ ω : ((outerBoundedMeshLearner (1/10000000) n m).randomizedPolicy Q).World
          ∂Q.worldLaw ((outerBoundedMeshLearner (1/10000000) n m).randomizedPolicy Q).seedLaw,
        (outerBoundedMeshLearner (1/10000000) n m).policy.AcceptsReachedCap 1 ω.2.2 ω.1 ω.2.1) ∧
      (optimalCompetitiveRatio*Q.expectedMaximum-K/(m : ℝ)≤
        (outerBoundedMeshLearner (1/10000000) n m).expectedReward Q) ∧
      (∀ i, optimalCompetitiveRatio-K/(m : ℝ)≤
        (outerBoundedMeshLearner (1/10000000) n m).reachProbability Q i) := by
    intro n m hm Q hMean hCount hG _hCap
    have hmPos : 0<m := by omega
    have hBound : ∀ x∈meshGrid 1 m, x∈Icc (0 : ℝ) 1 := fun x hx => meshGrid_unit_subset m hmPos hx
    have h := boundedClockMeshLearner_source_guarantees_of_rate (meshGrid 1 m) hBound
      (zero_mem_meshGrid 1 m) hmPos (by norm_num) hA.le
      (hRate n m hm (meshGrid 1 m) hBound) Q hG hMean.1 hMean.2 hCount
    refine ⟨Filter.Eventually.of_forall (fun ω => ?_),h.1,h.2⟩
    intro i _hReach hi
    unfold Policy.action
    rw [hi]
    exact boundedClockMeshLearner_accepts_cap m (meshGrid 1 m) (unitMesh_nonnegative m)
      (1/10000000) (1/80) (2*Real.log (m : ℝ)) _ _ _ _ _
  refine ⟨outerUpperConstant K,?_⟩
  exact outer_sample_upper_bound_of_bounded_guarantees hK.le
    (outerBoundedMeshLearner (1/10000000)) hBounded

end ProphetSecretary.Statistics
