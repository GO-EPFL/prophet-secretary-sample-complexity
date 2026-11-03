import ProphetSecretary.Statistics.CalibratedOuter.PreparedExecution
import ProphetSecretary.Statistics.OuterCutoffRounding

/-!
# A common reservoir for all reserved outer marks

The cutoff, pilot, inner-training and online marks are independent groups of
one finite uniform array. On injectivity of its rounded keys, each retained
training and online value is preserved.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

abbrev OuterMarkIndex (n m : ℕ) :=
  (Fin n × Fin m) ⊕ ((Fin n × Fin (outerPilotRounds m)) ⊕
    ((Fin n × Fin (2*m)) ⊕ Fin n))

lemma outerMarkIndex_card (n m : ℕ) :
    Fintype.card (OuterMarkIndex n m) = n*(outerSampleBudget m+1) := by
  simp only [OuterMarkIndex, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, outerSampleBudget]
  ring

def outerMarkSlotCount (n m : ℕ) : ℕ := n*(m+(outerPilotRounds m+2*m)+1)

def outerMarkIndexEquiv (n m : ℕ) :
    OuterMarkIndex n m ≃ Fin (outerMarkSlotCount n m) :=
  let a := (Equiv.sumCongr finProdFinEquiv (Equiv.refl (Fin n))).trans finSumFinEquiv
  let b := (Equiv.sumCongr finProdFinEquiv a).trans finSumFinEquiv
  let c := (Equiv.sumCongr finProdFinEquiv b).trans finSumFinEquiv
  c.trans (finCongr (by unfold outerMarkSlotCount; ring))

abbrev OuterMarks (n m : ℕ) (K : Type) :=
  (Fin m → Fin n → K) × ((Fin (outerPilotRounds m) → Fin n → K) ×
    ((Fin (2*m) → Fin n → K) × (Fin n → K)))

def unpackOuterMarks {n m : ℕ} {K : Type}
    (u : Fin (outerMarkSlotCount n m) → K) : OuterMarks n m K :=
  let e := outerMarkIndexEquiv n m
  (fun r i => u (e (.inl (i,r))),
   fun r i => u (e (.inr (.inl (i,r)))),
   fun r i => u (e (.inr (.inr (.inl (i,r))))),
   fun i => u (e (.inr (.inr (.inr i)))))

noncomputable def uniformOfferInstance (n : ℕ) : Instance n where
  law _ := Instance.uniformClock
  probability _ := inferInstance
  nonnegative _ :=
    (show ∀ᵐ x ∂Instance.uniformClock, x∈Icc (0 : ℝ) 1 from ae_restrict_mem measurableSet_Icc).mono
      (fun _ h => h.1)

noncomputable def outerMarksLaw (n m : ℕ) : Measure (OuterMarks n m ℝ) :=
  (outerTagRowsLaw n m).prod ((outerTagRowsLaw n (outerPilotRounds m)).prod
    ((outerTagRowsLaw n (2*m)).prod (Instance.clocksLaw n)))

lemma measurePreserving_unpackOuterMarks (n m : ℕ) :
    MeasurePreserving (unpackOuterMarks (n := n) (m := m) (K := ℝ))
      (Instance.clocksLaw (n*(outerSampleBudget m+1))) (outerMarksLaw n m) := by
  let μ := Instance.uniformClock
  let e := outerMarkIndexEquiv n m
  have h₀ := (measurePreserving_piCongrLeft (fun _ : Fin (n*(outerSampleBudget m+1)) => μ) e).symm
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (n*(outerSampleBudget m+1)) => ℝ) e)
  have h₁ := measurePreserving_sumPiEquivProdPi (fun _ : OuterMarkIndex n m => μ)
  have h₂ := measurePreserving_sumPiEquivProdPi
    (fun _ : (Fin n × Fin (outerPilotRounds m)) ⊕ ((Fin n × Fin (2*m)) ⊕ Fin n) => μ)
  have h₃ := measurePreserving_sumPiEquivProdPi (fun _ : (Fin n × Fin (2*m)) ⊕ Fin n => μ)
  have hr₀ := (outerRoundCoordinates_measurePreserving (uniformOfferInstance n) m).symm
    (outerRoundCoordinates n m)
  have hr₁ := (outerRoundCoordinates_measurePreserving (uniformOfferInstance n) (outerPilotRounds m)).symm
    (outerRoundCoordinates n (outerPilotRounds m))
  have hr₂ := (outerRoundCoordinates_measurePreserving (uniformOfferInstance n) (2*m)).symm
    (outerRoundCoordinates n (2*m))
  have h₄ := hr₀.prod (hr₁.prod (hr₂.prod (MeasurePreserving.id (Instance.clocksLaw n))))
  exact h₄.comp (((MeasurePreserving.id _).prod (((MeasurePreserving.id _).prod h₃).comp h₂)).comp (h₁.comp h₀))

def outerSeedFromMarks {n m : ℕ} (L : Learner n (2*m)) (u : OuterMarks n m ℝ) (s : L.Seed) :
    OuterLearnerSeed m L := (u.1,u.2.1,u.2.2.1,u.2.2.2,s)

lemma outerSeedFromMarks_measurePreserving {n m : ℕ} (L : Learner n (2*m)) :
    MeasurePreserving (fun q : OuterMarks n m ℝ × L.Seed => outerSeedFromMarks L q.1 q.2)
      ((outerMarksLaw n m).prod L.seedLaw) (outerLearnerSeedLaw m L) := by
  let μ₀ := outerTagRowsLaw n m
  let μ₁ := outerTagRowsLaw n (outerPilotRounds m)
  let μ₂ := outerTagRowsLaw n (2*m)
  let μ₃ := Instance.clocksLaw n
  let σ := L.seedLaw
  exact ((MeasurePreserving.id μ₀).prod (((MeasurePreserving.id μ₁).prod
    (measurePreserving_prodAssoc μ₂ μ₃ σ)).comp (measurePreserving_prodAssoc μ₁ (μ₂.prod μ₃) σ))).comp
      (measurePreserving_prodAssoc μ₀ (μ₁.prod (μ₂.prod μ₃)) σ)

variable {n m N : ℕ}

lemma outerRetention_unpack_rounding (hn : 0<n) (hm : 1≤m) (hN : 0<N)
    (cut : Reservoir n m) (u : Fin (n*(outerSampleBudget m+1)) → ℝ)
    (hu : Function.Injective (fun j => uniformGridIndex N hN (u j))) (j : Fin (n*(outerSampleBudget m+1)))
    (x : ℝ) :
    retainAboveTag (outerCutoff m hm (cut,(unpackOuterMarks (fun i => uniformGridRound N hN (u i))).1))
      (x,uniformGridRound N hN (u j)) =
    retainAboveTag (outerCutoff m hm (cut,(unpackOuterMarks u).1)) (x,u j) :=
  retainAboveOuterCutoff_rounding hn m hm hN (fun r i => cut i r) u hu
    (fun r i => outerMarkIndexEquiv n m (.inl (i,r))) j x

theorem outerPolicy_unpack_rounding (hn : 0<n) (hm : 1≤m) (hN : 0<N)
    (L : Learner n (2*m)) (y : Reservoir n (outerSampleBudget m)) (s : L.Seed)
    (u : Fin (n*(outerSampleBudget m+1)) → ℝ)
    (hu : Function.Injective (fun j => uniformGridIndex N hN (u j))) :
    let p := (y,outerSeedFromMarks L (unpackOuterMarks u) s)
    let p' := (y,outerSeedFromMarks L (unpackOuterMarks (fun i => uniformGridRound N hN (u i))) s)
    ∀ t i x H, (outerPolicy m hm L).decide p' t i x H = (outerPolicy m hm L).decide p t i x H := by
  dsimp only
  let u' := fun i => uniformGridRound N hN (u i)
  let p : OuterLearnerInput m L := (y,outerSeedFromMarks L (unpackOuterMarks u) s)
  let p' : OuterLearnerInput m L := (y,outerSeedFromMarks L (unpackOuterMarks u') s)
  let blocks := outerReservoirBlocks n m y
  have hRet := outerRetention_unpack_rounding hn hm hN blocks.1 u hu
  have hPilot : outerPilotAt m hm L p'=outerPilotAt m hm L p := by
    unfold outerPilotAt outerPilotValue
    apply congrArg (numericalPilotOrder (outerPilotRank m) (outerPilotRank_pos hm))
    funext r
    unfold retainedPilotSamples retainedMaximumAtTag
    apply congrArg Instance.maximum
    funext i
    exact hRet (outerMarkIndexEquiv n m (.inr (.inl (i,r)))) (blocks.2.1 i r)
  have hInner : outerInnerTraining m hm L p'=outerInnerTraining m hm L p := by
    unfold outerInnerTraining
    rw [hPilot]
    funext i r
    unfold outerTransformedReservoir
    exact congrArg (outerMeshDisplay m (1000*outerPilotAt m hm L p))
      (hRet (outerMarkIndexEquiv n m (.inr (.inr (.inl (i,r))))) (blocks.2.2 i r))
  have hOnline (i : Fin n) (x : ℝ) : outerRetainedObservation m hm L p' i x =
      outerRetainedObservation m hm L p i x :=
    hRet (outerMarkIndexEquiv n m (.inr (.inr (.inr i)))) x
  have hDisplay : outerDisplayedObservation m hm L p' = outerDisplayedObservation m hm L p := by
    funext i x
    unfold outerDisplayedObservation
    rw [hPilot,hOnline]
  intro t i x H
  change (outerPolicy m hm L).decide p' t i x H = (outerPolicy m hm L).decide p t i x H
  simp only [outerPolicy, hPilot]
  split_ifs
  · simp only [outerPositivePolicy, Policy.pullbackValuesBy, hOnline, firstPositiveRule]
  · simp only [outerBoundedPolicy, Policy.pullbackValuesBy, hInner, hDisplay]
    rfl

end ProphetSecretary.Statistics.Calibration
