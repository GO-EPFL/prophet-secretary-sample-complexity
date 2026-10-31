import ProphetSecretary.Limiting.HybridContinuationClockForms
import ProphetSecretary.Limiting.HybridDesignLossComparison
import ProphetSecretary.Model.AnonymousVirtualClocks

/-!
# Continuation errors after separating anonymous and virtual clocks

The analytical clock permutation keeps original and anonymous identities in
their existing order and inserts the virtual block. Exact continuation-state
identities, including the observed zero histories, then put the error into
the form controlled by virtual-clock averaging.
-/
open MeasureTheory Set
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n q N : ℕ}

lemma anonymousVirtualClocks_keep (u : Fin n → ℝ) (v : Fin N → ℝ) (z : Fin q → ℝ) :
    Model.anonymousVirtualClocks (u,(v,z)) ∘ (HybridZeroSimulation.keepEmbedding n q N).toEmbedding =
      Model.ZeroSimulation.appendClocks u v := by
  funext k
  exact HybridZeroSimulation.combinedClocks_keep u z (fun j => (v j,0)) k

lemma finiteDesignContinuation_retained_clockForm (Q : Model.Instance (n+q))
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (u : Fin n → ℝ) (v : Fin N → ℝ) (z : Fin q → ℝ) (i : Fin n) (ht : u i ∈ Icc (0 : ℝ) 1) :
    (Q.appendZeros N).continuationAtArrival w c (fun _ => 0) (Model.anonymousVirtualClocks (u,(v,z)))
      ((HybridZeroSimulation.keepEmbedding n q N).toEmbedding (i.castAdd N)) =
      Model.optimalScalarValue (Q.restrictTo (virtualClockState u (u i) (some i) z)) w (c*(remainingTime (u i) : ℝ)) := by
  have hU : Model.anonymousVirtualClocks (u,(v,z)) =
      combinedClocks (Model.ZeroSimulation.appendClocks u z) (fun j : Fin N => (v j,0)) := rfl
  have hIndex : (HybridZeroSimulation.keepEmbedding n q N).toEmbedding (i.castAdd N) = (i.castAdd q).castAdd N :=
    HybridZeroSimulation.keepEmbedding_left i
  rw [hIndex,hU,appended_continuation_individual Q hQ hw.le hc
    (fun _ => 0) (fun _ => 0) (Model.ZeroSimulation.appendClocks u z) (fun j : Fin N => (v j,0)) (i.castAdd q)]
  simp only [Model.Instance.continuationAtArrival,Model.Instance.continuationValue,
    virtualClockState,virtualContinuationState,Option.elim_some,Model.ZeroSimulation.appendClocks,Fin.addCases_left]
  rw [coe_remainingTime ht.2,max_eq_right (sub_nonneg.mpr ht.2)]
  rw [Fin.addCases_left]

lemma finiteDesignContinuation_anonymous_clockForm (Q : Model.Instance (n+q))
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (u : Fin n → ℝ) (v : Fin N → ℝ) (z : Fin q → ℝ) (j : Fin N) (ht : v j ∈ Icc (0 : ℝ) 1) :
    (Q.appendZeros N).continuationAtArrival w c (fun _ => 0) (Model.anonymousVirtualClocks (u,(v,z)))
      ((HybridZeroSimulation.keepEmbedding n q N).toEmbedding (j.natAdd n)) =
      Model.optimalScalarValue (Q.restrictTo (virtualClockState u (v j) none z)) w (c*(remainingTime (v j) : ℝ)) := by
  have hU : Model.anonymousVirtualClocks (u,(v,z)) =
      combinedClocks (Model.ZeroSimulation.appendClocks u z) (fun j : Fin N => (v j,0)) := rfl
  have hIndex : (HybridZeroSimulation.keepEmbedding n q N).toEmbedding (j.natAdd n) = j.natAdd (n+q) :=
    HybridZeroSimulation.keepEmbedding_right j
  rw [hIndex,hU,appended_continuation_poisson Q hQ hw.le hc
    (fun _ => 0) (Model.ZeroSimulation.appendClocks u z) (fun j : Fin N => (v j,0)) j]
  simp only [poissonContinuation,Model.Instance.continuationValue,virtualClockState,virtualContinuationState,Option.elim_none]
  rw [coe_remainingTime ht.2,max_eq_right (sub_nonneg.mpr ht.2)]

lemma FiniteIntensityHybridInstance.finiteDesignContinuationError_retained_clockForm
    (B : FiniteIntensityHybridInstance n) (Q : Model.Instance (n+q))
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (u : Fin n → ℝ) (v : Fin N → ℝ) (z : Fin q → ℝ) (i : Fin n) (ht : u i ∈ Icc (0 : ℝ) 1) :
    B.finiteDesignContinuationError Q w c (Model.anonymousVirtualClocks (u,(v,z))) (i.castAdd N) =
      |Model.optimalScalarValue (Q.restrictTo (virtualClockState u (u i) (some i) z)) w (c*(remainingTime (u i) : ℝ))-
        ((B.restrictIndividuals (retainedClockState u (u i) (some i))).remainingHorizon (remainingTime (u i))).optimalScalarValue w (c*(remainingTime (u i) : ℝ))| := by
  unfold FiniteIntensityHybridInstance.finiteDesignContinuationError
  dsimp only
  rw [anonymousVirtualClocks_keep,finiteDesignContinuation_retained_clockForm Q hQ hw hc u v z i ht,
    B.finiteContinuation_retained_clockForm hw c u v i]

lemma FiniteIntensityHybridInstance.finiteDesignContinuationError_anonymous_clockForm
    (B : FiniteIntensityHybridInstance n) (Q : Model.Instance (n+q))
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (u : Fin n → ℝ) (v : Fin N → ℝ) (z : Fin q → ℝ) (j : Fin N) (ht : v j ∈ Icc (0 : ℝ) 1) :
    B.finiteDesignContinuationError Q w c (Model.anonymousVirtualClocks (u,(v,z))) (j.natAdd n) =
      |Model.optimalScalarValue (Q.restrictTo (virtualClockState u (v j) none z)) w (c*(remainingTime (v j) : ℝ))-
        ((B.restrictIndividuals (retainedClockState u (v j) none)).remainingHorizon (remainingTime (v j))).optimalScalarValue w (c*(remainingTime (v j) : ℝ))| := by
  unfold FiniteIntensityHybridInstance.finiteDesignContinuationError
  dsimp only
  rw [anonymousVirtualClocks_keep,finiteDesignContinuation_anonymous_clockForm Q hQ hw hc u v z j ht,
    B.finiteContinuation_anonymous_clockForm hw c u v j]

end ProphetSecretary.Limiting
