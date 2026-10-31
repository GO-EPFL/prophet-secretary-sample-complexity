import ProphetSecretary.Limiting.CountableSingleValueReward
import ProphetSecretary.Limiting.CountableValueReplacementIndependence

/-!
# Expected reward under individual mean substitution

If substituting a candidate's mean preserves its selected occurrence, the
old policy's expected reward is preserved. The selection indicator on the
substituted world is independent of the original value by actual product
erasure, so its multiplication by the centered value has expectation zero.
The result concerns one fixed callback, not the reoptimized scalar value.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

theorem CountableRule.integral_reward_mean_substitution_eq (π : CountableRule Seed)
    (hπ : π.IsMeasurable) (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : ℕ)
    (hCode : ∀ᵐ v ∂B.completeWorldLaw ν,
      FirstAcceptance.selectedCode π.codeAccepted codeTime
        (replaceIndividualValue i (v,∫ x, x ∂(B.individuals i : Measure ℝ)))=
      FirstAcceptance.selectedCode π.codeAccepted codeTime v) :
    (∫ v, π.realizedReward B.terminal
      (replaceIndividualValue i (v,∫ x, x ∂(B.individuals i : Measure ℝ))) ∂B.completeWorldLaw ν)=
      ∫ v, π.realizedReward B.terminal v ∂B.completeWorldLaw ν := by
  let m : ℝ := ∫ x, x ∂(B.individuals i : Measure ℝ)
  let f : CompleteWorld Seed → ℝ := fun v => π.individualSelectionIndicator i (replaceIndividualValue i (v,m))
  have hf : Measurable f := (π.measurable_individualSelectionIndicator hπ i).comp
    ((measurable_replaceIndividualValue i).comp (measurable_id.prodMk measurable_const))
  have hfBound : ∀ v, ‖f v‖ ≤ 1 := fun v => by
    change ‖π.individualSelectionIndicator i (replaceIndividualValue i (v,m))‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (π.individualSelectionIndicator_mem_unit i _).1]
    exact (π.individualSelectionIndicator_mem_unit i _).2
  have hfInt : Integrable f (B.completeWorldLaw ν) :=
    Integrable.of_bound hf.aestronglyMeasurable 1 (Eventually.of_forall hfBound)
  have hXi : MeasurePreserving (fun v : CompleteWorld Seed => v.2.1 i)
      (B.completeWorldLaw ν) (B.individuals i : Measure ℝ) :=
    (B.individualValue_measurePreserving i).comp (measurePreserving_fst.comp measurePreserving_snd)
  have hxInt : Integrable (fun v : CompleteWorld Seed => v.2.1 i) (B.completeWorldLaw ν) :=
    hXi.integrable_comp_of_integrable (B.integrable_individualValue i)
  have hfxInt : Integrable (fun v => f v*v.2.1 i) (B.completeWorldLaw ν) :=
    hxInt.bdd_mul hf.aestronglyMeasurable (Eventually.of_forall hfBound)
  have hfmInt : Integrable (fun v => f v*m) (B.completeWorldLaw ν) := hfInt.mul_const m
  have hCorInt : Integrable (fun v => f v*(m-v.2.1 i)) (B.completeWorldLaw ν) := by
    apply (hfmInt.sub hfxInt).congr
    exact Eventually.of_forall (fun v => by
      change f v*m-f v*v.2.1 i=f v*(m-v.2.1 i)
      ring)
  have hFactor : (∫ v, f v*v.2.1 i ∂B.completeWorldLaw ν)=(∫ v, f v ∂B.completeWorldLaw ν)*m :=
    B.integral_replaced_observable_mul_value ν i m _ (π.measurable_individualSelectionIndicator hπ i)
  have hCor : (∫ v, f v*(m-v.2.1 i) ∂B.completeWorldLaw ν)=0 := by
    simp_rw [mul_sub]
    rw [integral_sub hfmInt hfxInt,integral_mul_const,hFactor,sub_self]
  calc
    _ = ∫ v, π.realizedReward B.terminal v+f v*(m-v.2.1 i) ∂B.completeWorldLaw ν := by
      apply integral_congr_ae
      filter_upwards [hCode] with v hv
      have hI := π.individualSelectionIndicator_eq_of_selectedCode_eq i hv
      exact (π.reward_replaceIndividualValue_eq_of_selectedCode_eq B.terminal i v m hv).trans
        (congrArg (fun z : ℝ => π.realizedReward B.terminal v+z*(m-v.2.1 i)) hI.symm)
    _ = (∫ v, π.realizedReward B.terminal v ∂B.completeWorldLaw ν)+
        ∫ v, f v*(m-v.2.1 i) ∂B.completeWorldLaw ν :=
      integral_add (π.integrable_reward B ν hπ) hCorInt
    _ = _ := by rw [hCor,add_zero]

theorem canonical_integral_reward_mean_substitution_eq
    (B : CountableInstance) (hZero : B.terminal=0) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) (i : ℕ)
    (hScores : ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, |φ x| ≤ 1) →
      (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0 →
      (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    (∫ v, (B.valueRule w c).realizedReward B.terminal
      (replaceIndividualValue i (v,∫ x, x ∂(B.individuals i : Measure ℝ)))
        ∂B.completeWorldLaw (Measure.dirac ()))=
      ∫ v, (B.valueRule w c).realizedReward B.terminal v ∂B.completeWorldLaw (Measure.dirac ()) :=
  (B.valueRule w c).integral_reward_mean_substitution_eq (B.valueRule_isMeasurable hw.le hc.le)
    B (Measure.dirac ()) i (B.canonical_selectedCodeAtValue_mean_ae_eq hZero hw hc i hScores)

end ProphetSecretary.Limiting.CountableInstance
