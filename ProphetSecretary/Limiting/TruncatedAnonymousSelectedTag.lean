import ProphetSecretary.Limiting.AnonymousSelectedTagObservable

/-!
# Anonymous selected coefficients on the actual truncation laws

Both the finite hybrid execution and its countable extension project to the
same finite observer. The selected anonymous mark coefficient therefore has
exactly the same expectation, including retained zero-valued observations.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting
open CountableInstance

variable {N : ℕ} {Seed : Type*} [MeasurableSpace Seed]

omit [MeasurableSpace Seed] in
lemma HybridRule.realizedReward_zero_eq_finite (π : HybridRule N Seed) (v : HybridWorld N Seed) :
    π.realizedReward 0 v = (π.asFinitePolicy v.1.1).reward v.2.2.2 Finset.univ
      (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) := by
  unfold HybridRule.realizedReward HybridRule.reward
  split_ifs with h
  · rfl
  · exact ((π.asFinitePolicy v.1.1).reward_eq_zero_of_no_actualSelection _ _ _ _
      (fun i hi => h ⟨i,hi⟩)).symm

lemma HybridRule.anonymousSelectedTag_eq_observable_ae (π : HybridRule N Seed) (hπ : π.IsMeasurable)
    (B : FiniteIntensityHybridInstance N) (hZero : B.terminal=0)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (φ : ℝ → ℝ) (hφ0 : φ 0=0) :
    ∀ᵐ v ∂B.law ν,
      (π.asFinitePolicy v.1.1).selectedTag v.2.2.2 (combinedValues v.2.1 v.1.2)
        (combinedClocks v.2.2.1 v.1.2)
        (Fin.addCases (fun _ : Fin N => 0) (fun j : Fin v.1.1 => φ ((v.1.2 j).2))) =
      π.anonymousSelectedTagObservable φ (hybridObserverWorld v) := by
  filter_upwards [hybrid_combined_clocks_regular B.individuals B.intensity ν,
    π.hybrid_payoffs_eq_observable hπ B ν] with v hv hPay
  have hR : π.observableReward 0 (hybridObserverWorld v)=
      (π.asFinitePolicy v.1.1).reward v.2.2.2 Finset.univ
        (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) := by
    simpa only [hZero,NNReal.coe_zero,π.realizedReward_zero_eq_finite] using hPay.2
  have hFin := finite_anonymousSelectedTag_eq (π.asFinitePolicy v.1.1) v.2.2.2
    (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) φ hφ0 hv.1
  change _ = if ∀ i : Fin N, π.observableDuration (hybridObserverWorld v) ≠ v.2.2.1 i
    then φ (π.observableReward 0 (hybridObserverWorld v)) else 0
  rw [hPay.1,hR]
  have hX (j : Fin v.1.1) : combinedValues v.2.1 v.1.2 (j.natAdd N)=(v.1.2 j).2 := by
    simp only [combinedValues,Fin.addCases_right]
  have hU (i : Fin N) : combinedClocks v.2.2.1 v.1.2 (i.castAdd v.1.1)=v.2.2.1 i := by
    simp only [combinedClocks,Fin.addCases_left]
  simp only [hX,hU] at hFin
  unfold HybridRule.realizedDuration HybridRule.stoppingTime
  convert hFin using 1

lemma HybridRule.integrable_anonymousSelectedTag (π : HybridRule N Seed) (hπ : π.IsMeasurable)
    (B : FiniteIntensityHybridInstance N) (hZero : B.terminal=0)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (φ : ℝ → ℝ) (hφ : Measurable φ)
    (hφ0 : φ 0=0) {D : ℝ} (hD : 0≤D) (hBound : ∀ x, |φ x|≤D) :
    Integrable (fun v => (π.asFinitePolicy v.1.1).selectedTag v.2.2.2
      (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2)
      (Fin.addCases (fun _ : Fin N => 0) (fun j : Fin v.1.1 => φ ((v.1.2 j).2)))) (B.law ν) := by
  have hF := π.measurable_anonymousSelectedTagObservable hπ hφ
  have hMP := hybrid_finiteObserver_measurePreserving B.individuals B.intensity ν
  have hInt : Integrable (fun v => π.anonymousSelectedTagObservable φ (hybridObserverWorld v)) (B.law ν) := by
    apply Integrable.of_bound (hF.comp hMP.measurable).aestronglyMeasurable D
    filter_upwards [] with v
    change ‖if ∀ i : Fin N, π.observableDuration (hybridObserverWorld v) ≠ v.2.2.1 i
      then φ (π.observableReward 0 (hybridObserverWorld v)) else 0‖≤D
    split_ifs
    · exact (Real.norm_eq_abs _).trans_le (hBound _)
    · simpa only [norm_zero] using hD
  exact hInt.congr ((π.anonymousSelectedTag_eq_observable_ae hπ B hZero ν φ hφ0).mono (fun _ h => h.symm))

lemma HybridRule.extended_anonymousSelectedTag_eq_observable_ae
    (π : HybridRule N Seed) (hπ : π.IsMeasurable) (B : CountableInstance) (hZero : B.terminal=0)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {b : ℝ} (hb : (B.terminal : ℝ)<b)
    (φ : ℝ → ℝ) (hφ0 : φ 0=0) :
    ∀ᵐ v ∂B.completeWorldLaw ν,
      (extendTruncatedRule π b).selectedTag (anonymousPerturbationTag φ) v =
      π.anonymousSelectedTagObservable φ
        (truncatedObserverWorld (finiteCutoffCountingMeasure b v.1) v) := by
  filter_upwards [π.extended_payoffs_eq_observable hπ B ν hb,
    B.present_candidate_times_injective ν] with v hPay hv
  have hRet (j : ℕ) (hj : (extendTruncatedRule π b).codeAccepted v (candidateEnumeration (Sum.inl j))) :
      j<N := by
    by_contra hn
    exact extended_individual_notAccepted π b v j hn hj
  have hTag := ProphetSecretary.Limiting.CountableRule.anonymousSelectedTag_eq
    (extendTruncatedRule π b) v φ hφ0 hRet hv
  change _ = if ∀ i : Fin N, π.observableDuration
    (truncatedObserverWorld (finiteCutoffCountingMeasure b v.1) v) ≠ v.2.2.1 i.val
    then φ (π.observableReward 0 (truncatedObserverWorld (finiteCutoffCountingMeasure b v.1) v)) else 0
  have hR : π.observableReward 0 (truncatedObserverWorld (finiteCutoffCountingMeasure b v.1) v)=
      (extendTruncatedRule π b).realizedReward 0 v := by
    simpa only [hZero,NNReal.coe_zero] using hPay.2
  rw [hPay.1,hR]
  exact hTag

/-- Exact transport of a finite hybrid anonymous coefficient to its full-world
execution. It is an analytical expectation identity for the same callbacks. -/
theorem HybridRule.integral_anonymousSelectedTag_eq_extended
    (π : HybridRule N Seed) (hπ : π.IsMeasurable) (B : CountableInstance) (hZero : B.terminal=0)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {b : ℝ} (hb : (B.terminal : ℝ)<b)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (hφ0 : φ 0=0) :
    (∫ v, (π.asFinitePolicy v.1.1).selectedTag v.2.2.2 (combinedValues v.2.1 v.1.2)
      (combinedClocks v.2.2.1 v.1.2)
      (Fin.addCases (fun _ : Fin N => 0) (fun j : Fin v.1.1 => φ ((v.1.2 j).2)))
      ∂(B.truncation N b hb).law ν) =
    ∫ v, (extendTruncatedRule π b).selectedTag (anonymousPerturbationTag φ) v
      ∂B.completeWorldLaw ν := by
  let F := π.anonymousSelectedTagObservable φ
  have hF : Measurable F := π.measurable_anonymousSelectedTagObservable hπ hφ
  have hHybrid := hybrid_finiteObserver_measurePreserving (B.individualPrefix N) (B.intensityAbove b hb) ν
  have hFull := B.finiteObserverProjection_measurePreserving ν N hb
  have hHM := integral_map (μ:=hybridWorldLaw (B.individualPrefix N) (B.intensityAbove b hb) ν)
    hHybrid.measurable.aemeasurable hF.aestronglyMeasurable
  have hFM := integral_map (μ:=B.completeWorldLaw ν) hFull.measurable.aemeasurable hF.aestronglyMeasurable
  rw [hHybrid.map_eq] at hHM
  rw [hFull.map_eq] at hFM
  calc
    _ = ∫ v, F (hybridObserverWorld v) ∂(B.truncation N b hb).law ν :=
      integral_congr_ae (π.anonymousSelectedTag_eq_observable_ae hπ (B.truncation N b hb) hZero ν φ hφ0)
    _ = ∫ v, F v ∂finiteObserverLaw (B.individualPrefix N) (B.intensityAbove b hb) ν := hHM.symm
    _ = ∫ v, F (truncatedObserverWorld (finiteCutoffCountingMeasure b v.1) v)
        ∂B.completeWorldLaw ν := hFM
    _ = _ := integral_congr_ae
      ((π.extended_anonymousSelectedTag_eq_observable_ae hπ B hZero ν hb φ hφ0).mono (fun _ h => h.symm))

end ProphetSecretary.Limiting
