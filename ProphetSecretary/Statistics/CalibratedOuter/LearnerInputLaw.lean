import ProphetSecretary.Statistics.CalibratedOuter.Learner
import ProphetSecretary.Probability.ProductRegrouping

/-!
# Actual independence of the outer data and seed blocks

The fixed law-independent sampling program is analyzed by regrouping its
reservoir and auxiliary product factors. This yields genuinely fresh cutoff,
pilot, inner, and online tags, without a conditional independence interface.
-/

open MeasureTheory
namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability
variable {n : ℕ}

noncomputable def outerLearnerInputLaw (P : Instance n) (m : ℕ) (L : Learner n (2*m)) : Measure (OuterLearnerInput m L) :=
  (P.reservoirLaw (outerSampleBudget m)).prod (outerLearnerSeedLaw m L)

instance outerLearnerInputLaw_probability (P : Instance n) (m : ℕ) (L : Learner n (2*m)) :
    IsProbabilityMeasure (outerLearnerInputLaw P m L) := by
  unfold outerLearnerInputLaw
  infer_instance

abbrev OuterIndependentInputs (m : ℕ) (L : Learner n (2*m)) :=
  (Reservoir n m × (Fin m → Fin n → ℝ)) ×
    ((Reservoir n (outerPilotRounds m) × (Fin (outerPilotRounds m) → Fin n → ℝ)) ×
      ((Reservoir n (2*m) × (Fin (2*m) → Fin n → ℝ)) × ((Fin n → ℝ) × L.Seed)))

noncomputable def outerIndependentInputs (m : ℕ) (L : Learner n (2*m)) (p : OuterLearnerInput m L) : OuterIndependentInputs m L :=
  (outerCutoffInput m L p,(outerPilotInput m L p,(outerInnerInput m L p,(outerOnlineTags m L p,outerInnerPolicySeed m L p))))

noncomputable def outerIndependentInputsLaw (P : Instance n) (m : ℕ) (L : Learner n (2*m)) : Measure (OuterIndependentInputs m L) :=
  (outerCutoffDataLaw P m).prod ((outerPilotInputsLaw P m).prod
    (((P.reservoirLaw (2*m)).prod (outerTagRowsLaw n (2*m))).prod ((Instance.clocksLaw n).prod L.seedLaw)))

/-- The product law of all four actual sampling/randomness blocks. -/
theorem outerIndependentInputs_measurePreserving (P : Instance n) (m : ℕ) (L : Learner n (2*m)) :
    MeasurePreserving (outerIndependentInputs m L) (outerLearnerInputLaw P m L) (outerIndependentInputsLaw P m L) := by
  let μ0 := P.reservoirLaw m
  let μ1 := P.reservoirLaw (outerPilotRounds m)
  let μ2 := P.reservoirLaw (2*m)
  let ν0 := outerTagRowsLaw n m
  let ν1 := outerTagRowsLaw n (outerPilotRounds m)
  let ν2 := outerTagRowsLaw n (2*m)
  let ν3 := (Instance.clocksLaw n).prod L.seedLaw
  have h0 := (outerReservoirBlocks_measurePreserving P m).prod (MeasurePreserving.id (outerLearnerSeedLaw m L))
  have h1 := productPairShuffle_measurePreserving μ0 (μ1.prod μ2) ν0 (ν1.prod (ν2.prod ν3))
  have h2 := (MeasurePreserving.id (μ0.prod ν0)).prod
    (productPairShuffle_measurePreserving μ1 μ2 ν1 (ν2.prod ν3))
  have h3 := (MeasurePreserving.id (μ0.prod ν0)).prod
    ((MeasurePreserving.id (μ1.prod ν1)).prod
      ((measurePreserving_prodAssoc μ2 ν2 ν3).symm
        (MeasurableEquiv.prodAssoc : ((Reservoir n (2*m) × (Fin (2*m) → Fin n → ℝ)) × ((Fin n → ℝ) × L.Seed)) ≃ᵐ
          (Reservoir n (2*m) × ((Fin (2*m) → Fin n → ℝ) × ((Fin n → ℝ) × L.Seed))))))
  exact h3.comp (h2.comp (h1.comp h0))

end ProphetSecretary.Statistics.Calibration
