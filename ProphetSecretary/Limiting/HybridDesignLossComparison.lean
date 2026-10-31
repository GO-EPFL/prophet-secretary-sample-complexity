import ProphetSecretary.Model.IgnoreExtrasBellmanLoss
import ProphetSecretary.Limiting.HybridDesignPerformance
import ProphetSecretary.Limiting.HybridBellmanLossMeasurability

/-!
# Comparing finite-design loss with actual hybrid continuation loss

The original policy is lifted by the proved causal ignore-extra map. Added
zero identities remain observable in the augmented instance; that lifted
policy deliberately ignores them. Their design loss is zero. At every
original or anonymous label, the sharp one-Lipschitz decision-loss estimate
bounds the loss discrepancy by its actual continuation error.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting
variable {n q N : ℕ} {Seed : Type*}

noncomputable def appendZeroClockWorld (v : HybridWorld n Seed) (z : Fin q → ℝ) : HybridWorld (n+q) Seed :=
  (v.1,(Model.ZeroSimulation.appendValues v.2.1,(Model.ZeroSimulation.appendClocks v.2.2.1 z,v.2.2.2)))

lemma FiniteIntensityHybridInstance.finiteContinuationAtArrival_values_invariant
    (B : FiniteIntensityHybridInstance n) (w c : ℝ) (x y u : Fin (n+N) → ℝ) (k : Fin (n+N)) :
    B.finiteContinuationAtArrival w c x u k = B.finiteContinuationAtArrival w c y u k := by
  unfold FiniteIntensityHybridInstance.finiteContinuationAtArrival
  rw [Model.unseen_history_values Finset.univ x y u (u k)]

lemma HybridRule.reachedValueLoss_eq_gapLoss (π : HybridRule n Seed) (B : FiniteIntensityHybridInstance n)
    (w c : ℝ) (v : HybridWorld n Seed) :
    π.reachedValueLoss B w c v = ∑ k : Fin (n+v.1.1), if (π.asFinitePolicy v.1.1).Reaches v.2.2.2
      (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) k then
      ProphetSecretary.Analysis.gapLoss ((π.asFinitePolicy v.1.1).action v.2.2.2 Finset.univ
        (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) k)
        (w*combinedValues v.2.1 v.1.2 k-B.finiteContinuationAtArrival w c
          (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) k) else 0 := by
  unfold HybridRule.reachedValueLoss
  apply Finset.sum_congr rfl
  intro k _
  split_ifs
  · exact (ProphetSecretary.Analysis.gapLoss_eq_decisionLoss _ _ _).symm
  · rfl

noncomputable def FiniteIntensityHybridInstance.finiteDesignContinuationError
    (B : FiniteIntensityHybridInstance n) (Q : Model.Instance (n+q)) (w c : ℝ)
    (u : Fin (n+q+N) → ℝ) (k : Fin (n+N)) : ℝ :=
  let e := (HybridZeroSimulation.keepEmbedding n q N).toEmbedding
  |(Q.appendZeros N).continuationAtArrival w c (fun _ => 0) u (e k)-
    B.finiteContinuationAtArrival w c (fun _ => 0) (u ∘ e) k|

/-- Pathwise comparison for any original causal rule and arbitrary independent
auxiliary seed type. Every continuation error on the right is analytical. -/
theorem HybridRule.ignoreIndividualExtras_designLoss_error
    (π : HybridRule n Seed) (B : FiniteIntensityHybridInstance n) (Q : Model.Instance (n+q))
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (v : HybridWorld n Seed) (z : Fin q → ℝ) :
    |(π.ignoreIndividualExtras (Fin.castAddEmb q)).designActionLoss Q w c (appendZeroClockWorld v z)-
      π.reachedValueLoss B w c v| ≤
      ∑ k : Fin (n+v.1.1), B.finiteDesignContinuationError Q w c
        (combinedClocks (Model.ZeroSimulation.appendClocks v.2.2.1 z) v.1.2) k := by
  let N := v.1.1
  let e := (HybridZeroSimulation.keepEmbedding n q N).toEmbedding
  let X := combinedValues (Model.ZeroSimulation.appendValues (m := q) v.2.1) v.1.2
  let U := combinedClocks (Model.ZeroSimulation.appendClocks v.2.2.1 z) v.1.2
  let x := combinedValues v.2.1 v.1.2
  let u := combinedClocks v.2.2.1 v.1.2
  have hX : X ∘ e = x := by
    funext i
    exact HybridZeroSimulation.combinedValues_keep v.2.1 v.1.2 i
  have hU : U ∘ e = u := by
    funext i
    exact HybridZeroSimulation.combinedClocks_keep v.2.2.1 z v.1.2 i
  have hz : ∀ j : Fin (n+q+N), (∀ i, e i ≠ j) → X j = 0 := by
    intro j
    induction j using Fin.addCases with
    | left j =>
      induction j using Fin.addCases with
      | left i =>
        intro hNo
        exact False.elim (hNo (i.castAdd N) (HybridZeroSimulation.keepEmbedding_left (n := n) (k := q) (N := N) i))
      | right j =>
        intro _hNo
        simp only [N,X,combinedValues,Fin.addCases_left,Model.ZeroSimulation.appendValues,Fin.addCases_right]
    | right j =>
      intro hNo
      exact False.elim (hNo (j.natAdd n) (HybridZeroSimulation.keepEmbedding_right (n := n) (k := q) (N := N) j))
  have h := (π.asFinitePolicy N).ignoreExtras_reachedBellmanLoss_error e (Q.appendZeros N)
    (Q.appendZeros_integrable_maximum N hQ) hw hc v.2.2.2 X U hz
    (fun k => B.finiteContinuationAtArrival w c x u k)
  dsimp only [e] at h
  rw [← π.ignoreIndividualExtras_adapter q N,hX,hU] at h
  have hXi (i : Fin (n+N)) : X ((HybridZeroSimulation.keepEmbedding n q N).toEmbedding i) = x i := congrFun hX i
  simp_rw [hXi] at h
  rw [← π.reachedValueLoss_eq_gapLoss B w c v] at h
  have hRhs : (∑ k : Fin (n+N), |(Q.appendZeros N).continuationAtArrival w c X U (e k)-
      B.finiteContinuationAtArrival w c x u k|) = ∑ k : Fin (n+N), B.finiteDesignContinuationError Q w c U k := by
    apply Finset.sum_congr rfl
    intro k _
    unfold FiniteIntensityHybridInstance.finiteDesignContinuationError
    dsimp only
    rw [hU,(Q.appendZeros N).continuationAtArrival_values_invariant w c X (fun _ => 0) U (e k),
      B.finiteContinuationAtArrival_values_invariant w c x (fun _ => 0) u k]
  rw [hRhs] at h
  exact h

end ProphetSecretary.Limiting
