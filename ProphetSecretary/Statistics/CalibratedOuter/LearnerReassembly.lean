import ProphetSecretary.Statistics.CalibratedOuter.LearnerInputLaw

/-!
# Reassembling observed outer data and fresh inner randomness

The cutoff and pilot blocks form the outer data. All inner training and online
randomness remain in an independent factor. Reassembly is an actual measurable
equivalence, including on impossible raw training outcomes.
-/

open MeasureTheory
namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model
variable {n : ℕ}

abbrev OuterObservedData (n m : ℕ) :=
  (Reservoir n m × (Fin m → Fin n → ℝ)) ×
    (Reservoir n (outerPilotRounds m) × (Fin (outerPilotRounds m) → Fin n → ℝ))

abbrev OuterFreshInput (m : ℕ) (L : Learner n (2*m)) :=
  (Reservoir n (2*m) × (Fin (2*m) → Fin n → ℝ)) × ((Fin n → ℝ) × L.Seed)

noncomputable def outerReassemble (m : ℕ) (L : Learner n (2*m))
    (p : OuterObservedData n m × OuterFreshInput m L) : OuterLearnerInput m L :=
  ((outerReservoirBlocks n m).symm (p.1.1.1,(p.1.2.1,p.2.1.1)),
    (p.1.1.2,(p.1.2.2,(p.2.1.2,(p.2.2.1,p.2.2.2)))))

lemma measurable_outerReassemble (m : ℕ) (L : Learner n (2*m)) : Measurable (outerReassemble m L) := by
  have hSamples : Measurable (fun p : OuterObservedData n m × OuterFreshInput m L =>
      (p.1.1.1,(p.1.2.1,p.2.1.1))) :=
    (measurable_fst.comp (measurable_fst.comp measurable_fst)).prodMk
      (((measurable_fst.comp (measurable_snd.comp measurable_fst))).prodMk
        (measurable_fst.comp (measurable_fst.comp measurable_snd)))
  have hTags : Measurable (fun p : OuterObservedData n m × OuterFreshInput m L =>
      (p.1.1.2,(p.1.2.2,(p.2.1.2,(p.2.2.1,p.2.2.2))))) := by fun_prop
  exact ((outerReservoirBlocks n m).symm.measurable.comp hSamples).prodMk hTags

noncomputable def outerSeparate (m : ℕ) (L : Learner n (2*m))
    (p : OuterLearnerInput m L) : OuterObservedData n m × OuterFreshInput m L :=
  ((outerCutoffInput m L p,outerPilotInput m L p),
    (outerInnerInput m L p,(outerOnlineTags m L p,outerInnerPolicySeed m L p)))

lemma measurable_outerSeparate (m : ℕ) (L : Learner n (2*m)) : Measurable (outerSeparate m L) :=
  ((measurable_outerCutoffInput m L).prodMk (measurable_outerPilotInput m L)).prodMk
    ((measurable_outerInnerInput m L).prodMk ((measurable_outerOnlineTags m L).prodMk (measurable_outerInnerPolicySeed m L)))

noncomputable def outerReassembly (m : ℕ) (L : Learner n (2*m)) :
    (OuterObservedData n m × OuterFreshInput m L) ≃ᵐ OuterLearnerInput m L where
  toFun := outerReassemble m L
  invFun := outerSeparate m L
  left_inv := by
    intro p
    simp only [outerSeparate,outerReassemble,outerCutoffInput,outerPilotInput,outerInnerInput,
      outerOnlineTags,outerInnerPolicySeed,MeasurableEquiv.apply_symm_apply]
  right_inv := by
    intro p
    have hSamples : (outerReservoirBlocks n m).symm
        ((outerReservoirBlocks n m p.1).1,((outerReservoirBlocks n m p.1).2.1,(outerReservoirBlocks n m p.1).2.2))=p.1 :=
      (outerReservoirBlocks n m).symm_apply_apply p.1
    simp only [outerSeparate,outerReassemble,outerCutoffInput,outerPilotInput,outerInnerInput,
      outerOnlineTags,outerInnerPolicySeed,hSamples]
  measurable_toFun := measurable_outerReassemble m L
  measurable_invFun := measurable_outerSeparate m L

noncomputable def outerObservedDataLaw (P : Instance n) (m : ℕ) : Measure (OuterObservedData n m) :=
  (outerCutoffDataLaw P m).prod (outerPilotInputsLaw P m)

noncomputable def outerFreshInputLaw (P : Instance n) (m : ℕ) (L : Learner n (2*m)) : Measure (OuterFreshInput m L) :=
  ((P.reservoirLaw (2*m)).prod (outerTagRowsLaw n (2*m))).prod ((Instance.clocksLaw n).prod L.seedLaw)

instance outerObservedDataLaw_probability (P : Instance n) (m : ℕ) : IsProbabilityMeasure (outerObservedDataLaw P m) := by
  unfold outerObservedDataLaw
  infer_instance

instance outerFreshInputLaw_probability (P : Instance n) (m : ℕ) (L : Learner n (2*m)) : IsProbabilityMeasure (outerFreshInputLaw P m L) := by
  unfold outerFreshInputLaw
  infer_instance

lemma outerSeparate_measurePreserving (P : Instance n) (m : ℕ) (L : Learner n (2*m)) :
    MeasurePreserving (outerSeparate m L) (outerLearnerInputLaw P m L)
      ((outerObservedDataLaw P m).prod (outerFreshInputLaw P m L)) := by
  have h0 := outerIndependentInputs_measurePreserving P m L
  have h1 := (measurePreserving_prodAssoc (outerCutoffDataLaw P m) (outerPilotInputsLaw P m) (outerFreshInputLaw P m L)).symm
    (MeasurableEquiv.prodAssoc : (OuterObservedData n m × OuterFreshInput m L) ≃ᵐ
      ((Reservoir n m × (Fin m → Fin n → ℝ)) ×
        ((Reservoir n (outerPilotRounds m) × (Fin (outerPilotRounds m) → Fin n → ℝ)) × OuterFreshInput m L)))
  exact h1.comp h0

lemma outerReassemble_measurePreserving (P : Instance n) (m : ℕ) (L : Learner n (2*m)) :
    MeasurePreserving (outerReassemble m L) ((outerObservedDataLaw P m).prod (outerFreshInputLaw P m L))
      (outerLearnerInputLaw P m L) :=
  (outerSeparate_measurePreserving P m L).symm (outerReassembly m L).symm

end ProphetSecretary.Statistics.Calibration
