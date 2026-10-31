import ProphetSecretary.Limiting.CountableValueDecision
import ProphetSecretary.Limiting.CountableMaskOrder
import ProphetSecretary.Limiting.CountableHorizonOrder
import ProphetSecretary.Limiting.CountableCapSelection

/-!
# Actual canonical acceptance above the full continuation value

A remaining horizon at most one lowers the waiting coefficient and intensity;
deleting seen individuals lowers the optimal continuation value. Thus every
canonical child continuation is at most the full optimized value. Before time1
the positive gate is redundant, so a reached cap above that value is accepted.
-/

open MeasureTheory Set Filter
open scoped NNReal Classical
namespace ProphetSecretary.Limiting.CountableInstance

lemma continuationValue_le_full (B : CountableInstance) (hZero : B.terminal=0)
    (keep : IndividualMask) (u : ℝ≥0) (hu : u≤1) {w c : ℝ} (hw : 0≤w) (hc : 0≤c) :
    B.continuationValue keep w c u≤B.optimalScalarValue w c := by
  have hMask := B.remainingState_value_mono_mask hZero keep (fun _ => true)
    (fun _ _ => rfl) 1 hw hc
  calc
    _ ≤ B.continuationValue keep w c 1 := B.continuationValue_mono keep hw hc hu
    _ = (B.remainingState keep 1).optimalScalarValue w c := by simp only [continuationValue,NNReal.coe_one,mul_one]
    _ ≤ (B.remainingState (fun _ => true) 1).optimalScalarValue w c := hMask
    _ = _ := by rw [remainingState,B.maskIndividuals_all,B.remainingHorizon_one]

lemma valueRule_accepts_above_full (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (v : CompleteWorld Unit) (j : Candidate)
    (ht0 : 0≤(candidatePoint v j).1) (ht1 : (candidatePoint v j).1<1)
    (hx : B.optimalScalarValue w c≤w*(candidatePoint v j).2) :
    (B.valueRule w c).candidateAction v j=true := by
  apply (B.valueRule_candidateAction_iff_preterminal hw hc v j ht1).mpr
  apply LE.le.trans _ hx
  exact B.continuationValue_le_full hZero _ _ (remainingTime_le_one ht0) hw.le hc.le

lemma valuePolicy_accepts_individual_cap (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (i : ℕ) (K : ℝ)
    (hValue : B.optimalScalarValue w c≤w*K) :
    ∀ᵐ v ∂B.completeWorldLaw (B.valuePolicy hw hc).seedLaw,
      v.2.2.1 i≤(B.valuePolicy hw hc).rule.realizedDuration v → v.2.1 i=K →
        (B.valuePolicy hw hc).rule.candidateAction v (Sum.inl i)=true := by
  filter_upwards [B.present_candidate_times_mem_Ioo (B.valuePolicy hw hc).seedLaw] with v hv _hReach hXi
  have ht := hv (Sum.inl i) trivial
  apply B.valueRule_accepts_above_full hZero hw hc v (Sum.inl i) ht.1.le ht.2
  simpa only [candidatePoint,hXi] using hValue

lemma valuePolicy_selectionProbability_ge_cap_mass (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (i : ℕ) (K : ℝ)
    (hValue : B.optimalScalarValue w c≤w*K) :
    (B.valuePolicy hw hc).individualSelectionProbability i≥
      (B.valuePolicy hw hc).individualReachProbability i*(B.individuals i : Measure ℝ).real {K} :=
  (B.valuePolicy hw hc).individualSelectionProbability_ge_reach_mul_atom i K
    (B.valuePolicy_accepts_individual_cap hZero hw hc i K hValue)

end ProphetSecretary.Limiting.CountableInstance
