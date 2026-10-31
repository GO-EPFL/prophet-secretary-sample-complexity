import ProphetSecretary.Limiting.HybridBellmanIdentity

/-!
# Actual Bellman identity at zero anonymous intensity

The constructed zero-intensity law is the empty configuration. Its actual
continuation potential equals the proved finite-instance continuation in every
retained state, including all observed zero identities. The finite all-policy
performance identity therefore supplies the missing boundary case directly.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma FiniteIntensityHybridInstance.finiteContinuation_zero_intensity
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity = 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (x u : Fin n → ℝ) (i : Fin n) :
    B.finiteContinuationAtArrival (N := 0) w c x u i = B.individuals.continuationAtArrival w c x u i := by
  have hHistory (H : Model.History n) : retainedHistory (N := 0) H = H := by funext j; rfl
  have hUnseen (H : Model.History n) : retainedUnseen (N := 0) (Model.unseen H) = Model.unseen H := by
    rw [retainedUnseen_unseen,hHistory]
  have hAll (k : Fin (n+0)) : B.finiteContinuationAtArrival (N := 0) w c x u k =
      B.individuals.continuationAtArrival w c x u k := by
    induction k using Fin.addCases with
    | left k =>
      have hCast : k.castAdd 0 = k := by apply Fin.ext; rfl
      unfold FiniteIntensityHybridInstance.finiteContinuationAtArrival
      simp only [finiteHybridThreshold,Fin.addCases_left]
      rw [hCast,hUnseen,B.valueHybridThreshold_eq_finite_of_zero_intensity ha hμ hw.le hc]
      exact (B.individuals.continuationAtArrival_eq_threshold hw c x u k).symm
    | right j => exact Fin.elim0 j
  exact hAll i

lemma RandomizedHybridPolicy.reachedValueLoss_empty_configuration (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity = 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (v : Model.World n π.Seed) :
    π.rule.reachedValueLoss B w c (emptyConfiguration,v) =
      (emptyPoissonPolicy π).rule.reachedBellmanLoss B.individuals w c v.2.2 v.1 v.2.1 := by
  have hx : combinedValues v.1 (fun j : Fin 0 => (Fin.elim0 j : Point)) = v.1 := by
    funext i
    induction i using Fin.addCases with
    | left i => simp only [combinedValues,Fin.addCases_left]; congr 1
    | right j => exact Fin.elim0 j
  have hu : combinedClocks v.2.1 (fun j : Fin 0 => (Fin.elim0 j : Point)) = v.2.1 := by
    funext i
    induction i using Fin.addCases with
    | left i => simp only [combinedClocks,Fin.addCases_left]; congr 1
    | right j => exact Fin.elim0 j
  have hArrival (i : Fin n) : π.rule.arrivalValueLoss B w c (emptyConfiguration,v) i =
      (emptyPoissonPolicy π).rule.arrivalBellmanLoss B.individuals w c v.2.2 v.1 v.2.1 i := by
    unfold HybridRule.arrivalValueLoss
    dsimp only [emptyConfiguration,configurationMk]
    change (max (w*combinedValues v.1 (fun j : Fin 0 => (Fin.elim0 j : Point)) i)
      (B.finiteContinuationAtArrival (N := 0) w c (combinedValues v.1 (fun j : Fin 0 => (Fin.elim0 j : Point)))
        (combinedClocks v.2.1 (fun j : Fin 0 => (Fin.elim0 j : Point))) i)-
      (if (π.rule.asFinitePolicy 0).action v.2.2 (Finset.univ : Finset (Fin n))
        (combinedValues v.1 (fun j : Fin 0 => (Fin.elim0 j : Point)))
        (combinedClocks v.2.1 (fun j : Fin 0 => (Fin.elim0 j : Point))) i = true then
          w*combinedValues v.1 (fun j : Fin 0 => (Fin.elim0 j : Point)) i else
          B.finiteContinuationAtArrival (N := 0) w c (combinedValues v.1 (fun j : Fin 0 => (Fin.elim0 j : Point)))
            (combinedClocks v.2.1 (fun j : Fin 0 => (Fin.elim0 j : Point))) i)) = _
    simp only [hx,hu,emptyPoissonPolicy_adapter,B.finiteContinuation_zero_intensity ha hμ hw hc,
      Model.Policy.arrivalBellmanLoss]
    rfl
  change (∑ i : Fin n, if (π.rule.asFinitePolicy 0).Reaches v.2.2
      (combinedValues v.1 (fun j : Fin 0 => (Fin.elim0 j : Point)))
      (combinedClocks v.2.1 (fun j : Fin 0 => (Fin.elim0 j : Point))) i then
        π.rule.arrivalValueLoss B w c (emptyConfiguration,v) i else 0) = _
  unfold Model.Policy.reachedBellmanLoss
  simp only [hx,hu,emptyPoissonPolicy_adapter,hArrival]
  rfl

lemma RandomizedHybridPolicy.expectedValueLoss_zero_intensity_eq_finite (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity = 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    π.expectedValueLoss B w c = (emptyPoissonPolicy π).expectedReachedBellmanLoss B.individuals w c := by
  have hMP : MeasurePreserving (fun v : Model.World n π.Seed => (emptyConfiguration,v))
      (B.individuals.worldLaw π.seedLaw) (B.law π.seedLaw) := by
    change MeasurePreserving _ _ (hybridWorldLaw B.individuals B.intensity π.seedLaw)
    rw [hμ]
    exact zeroIntensityWorld_measurePreserving B.individuals π.seedLaw
  have h : (∫ v : Model.World n π.Seed, π.rule.reachedValueLoss B w c (emptyConfiguration,v)
      ∂B.individuals.worldLaw π.seedLaw) = π.expectedValueLoss B w c :=
    hMP.hasLaw.integral_comp (π.rule.measurable_reachedValueLoss π.measurable_rule B hw hc).aestronglyMeasurable
  rw [← h]
  unfold Model.RandomizedPolicy.expectedReachedBellmanLoss
  apply integral_congr_ae
  exact Eventually.of_forall fun v => π.reachedValueLoss_empty_configuration B ha hμ hw hc v

/-- The actual all-policy Bellman identity also includes the zero-Poisson-rate
boundary, with empty or zero-mean retained families allowed. -/
theorem RandomizedHybridPolicy.actual_bellmanIdentity_zero_intensity
    (π : RandomizedHybridPolicy n) (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    (hμ : B.intensity = 0) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    B.optimalScalarValue w c-π.scalarObjective B w c = π.expectedValueLoss B w c := by
  rw [B.value_zero_intensity ha hμ hw.le hc,emptyPoissonPolicy_scalarObjective π B ha hμ w c,
    π.expectedValueLoss_zero_intensity_eq_finite B ha hμ hw hc]
  exact (emptyPoissonPolicy π).bellman_performanceDifference B.individuals
    (B.individuals.integrable_maximum_of_bounded B.individual_bounded) hw hc

/-- Actual regret equals actual reached Bellman loss for every competing
randomized hybrid policy. No positive maximum or anonymous-rate hypothesis
is imposed; reward weight is positive and duration weight nonnegative. -/
theorem RandomizedHybridPolicy.actual_bellmanIdentity
    (π : RandomizedHybridPolicy n) (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    B.optimalScalarValue w c-π.scalarObjective B w c = π.expectedValueLoss B w c := by
  by_cases hμ : B.intensity = 0
  · exact π.actual_bellmanIdentity_zero_intensity B ha hμ hw hc
  · exact π.actual_bellmanIdentity_of_nonzero_intensity B ha hμ hw hc

end ProphetSecretary.Limiting
