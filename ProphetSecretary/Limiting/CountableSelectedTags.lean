import ProphetSecretary.Limiting.CountableOutcomeError
import ProphetSecretary.Limiting.CountablePairEvents
import ProphetSecretary.Limiting.FirstAcceptanceTagIntegral

/-!
# Actual selected tags in the full limiting instance

A tag is a common analytical assignment to each occurrence. It may include
independent randomness attached to that occurrence. The canonical policy
ignores the competitor's seed, while both selected tags use this same
assignment. No tag is additional future information supplied to a callback.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

abbrev CountableTags (Seed : Type*) := CompleteWorld Seed → ℕ → ℝ

def CountableTags.IsMeasurable {Seed : Type*} [MeasurableSpace Seed]
    (tag : CountableTags Seed) : Prop := ∀ i, Measurable (fun v => tag v i)

namespace CountableInstance

noncomputable def canonicalAccepted (B : CountableInstance) {Seed : Type*} (w c : ℝ)
    (v : CompleteWorld Seed) (i : ℕ) : Prop := (B.valueRule w c).codeAccepted (eraseCompleteSeed v) i

lemma measurableSet_canonicalAccepted (B : CountableInstance) {Seed : Type*} [MeasurableSpace Seed]
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (i : ℕ) :
    MeasurableSet {v : CompleteWorld Seed | B.canonicalAccepted w c v i} := by
  have hErase : Measurable (eraseCompleteSeed (Seed := Seed)) :=
    measurable_fst.prodMk (measurable_snd.fst.prodMk (measurable_snd.snd.fst.prodMk measurable_const))
  exact ((B.valueRule w c).measurableSet_codeAccepted (B.valueRule_isMeasurable hw hc) i).preimage hErase

lemma closePositivePair_code_iff {Seed : Type*} (v : CompleteWorld Seed) (b η : ℝ) :
    FirstAcceptance.ClosePositivePair (codePresent v) b η (codeValue v) (codeTime v) ↔
      v ∈ closePositivePair b η := by
  constructor
  · rintro ⟨i,j,hij,hi,hj,hbi,hbj,hTime⟩
    exact ⟨candidateEnumeration.symm i,candidateEnumeration.symm j,
      (fun he => hij (candidateEnumeration.symm.injective he)),hi,hj,hbi,hbj,hTime⟩
  · rintro ⟨i,j,hij,hi,hj,hbi,hbj,hTime⟩
    refine ⟨candidateEnumeration i,candidateEnumeration j,(fun he => hij (candidateEnumeration.injective he)),?_,?_,?_,?_,?_⟩
    · simpa only [codePresent,Equiv.symm_apply_apply] using hi
    · simpa only [codePresent,Equiv.symm_apply_apply] using hj
    · simpa only [codeValue,codePoint,Equiv.symm_apply_apply] using hbi
    · simpa only [codeValue,codePoint,Equiv.symm_apply_apply] using hbj
    · simpa only [codeTime,codePoint,Equiv.symm_apply_apply] using hTime

noncomputable def CountableRule.selectedTag {Seed : Type*} (π : CountableRule Seed)
    (tag : CountableTags Seed) (v : CompleteWorld Seed) : ℝ :=
  FirstAcceptance.reward 0 π.codeAccepted codeTime tag v

noncomputable def CountableRule.coupledSelectedTagError {Seed : Type*} (π : CountableRule Seed)
    (B : CountableInstance) (w c : ℝ) (tag : CountableTags Seed) (v : CompleteWorld Seed) : ℝ :=
  |π.selectedTag tag v-FirstAcceptance.reward 0 (B.canonicalAccepted w c) codeTime tag v|

lemma CountableRule.integral_selectedTagDifference_le {Seed : Type*} [MeasurableSpace Seed]
    (π : CountableRule Seed) (hπ : π.IsMeasurable) (B : CountableInstance) (hZero : B.terminal=0)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {w c D b η : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (hD : 0 ≤ D) (hb : 0 < b) (hη : 0 < η)
    (tag : CountableTags Seed) (hTag : tag.IsMeasurable)
    (hBound : ∀ᵐ v ∂B.completeWorldLaw ν, ∀ i, |tag v i| ≤ D)
    (hTagZero : ∀ᵐ v ∂B.completeWorldLaw ν, ∀ i, codeValue v i < b → tag v i=0) :
    (∫ v, π.coupledSelectedTagError B w c tag v ∂B.completeWorldLaw ν) ≤
      2*D*(2*(∫ v, π.coupledValueOutcomeError B w c v ∂B.completeWorldLaw ν)/b+
        (∫ v, π.coupledValueOutcomeError B w c v ∂B.completeWorldLaw ν)/η+
          (B.completeWorldLaw ν).real (closePositivePair (b/2) η)) := by
  have hPairSet : {v : CompleteWorld Seed | FirstAcceptance.ClosePositivePair
      (codePresent v) (b/2) η (codeValue v) (codeTime v)}=closePositivePair (b/2) η :=
    Set.ext (fun v => closePositivePair_code_iff v (b/2) η)
  have hPair : MeasurableSet {v : CompleteWorld Seed | FirstAcceptance.ClosePositivePair
      (codePresent v) (b/2) η (codeValue v) (codeTime v)} := by
    rw [hPairSet]
    exact measurableSet_closePositivePair _ _
  let Error := fun v : CompleteWorld Seed =>
    |FirstAcceptance.reward 0 π.codeAccepted codeTime codeValue v-
      FirstAcceptance.reward 0 (B.canonicalAccepted w c) codeTime codeValue v|+
    |FirstAcceptance.stoppingTime π.codeAccepted codeTime v-
      FirstAcceptance.stoppingTime (B.canonicalAccepted w c) codeTime v|
  have hErrorEq (v : CompleteWorld Seed) : Error v=π.coupledValueOutcomeError B w c v := by
    rw [CountableRule.coupledValueOutcomeError,hZero]
    rfl
  have hError : Integrable Error (B.completeWorldLaw ν) :=
    (π.integrable_coupledValueOutcomeError hπ B ν hw hc).congr
      (Eventually.of_forall (fun v => (hErrorEq v).symm))
  have h := FirstAcceptance.integral_selectedTag_difference_le π.codeAccepted (B.canonicalAccepted w c)
    codeTime codeValue tag codePresent (B.completeWorldLaw ν) (π.measurableSet_codeAccepted hπ)
    (B.measurableSet_canonicalAccepted hw hc) measurable_codeTime hTag
    (fun _ _ hi => hi.1) (fun _ _ hi => hi.1) hD hb hη hBound hTagZero hPair hError
  rw [hPairSet] at h
  have hIntegral : (∫ v, Error v ∂B.completeWorldLaw ν)=
      ∫ v, π.coupledValueOutcomeError B w c v ∂B.completeWorldLaw ν :=
    integral_congr_ae (Eventually.of_forall hErrorEq)
  change (∫ v, π.coupledSelectedTagError B w c tag v ∂B.completeWorldLaw ν) ≤
    2*D*(2*(∫ v, Error v ∂B.completeWorldLaw ν)/b+
      (∫ v, Error v ∂B.completeWorldLaw ν)/η+(B.completeWorldLaw ν).real (closePositivePair (b/2) η)) at h
  rw [hIntegral] at h
  exact h

end CountableInstance

noncomputable def RandomizedCountablePolicy.expectedSelectedTagError {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (w c : ℝ) (tag : CountableTags π.Seed) : ℝ :=
  ∫ v, π.rule.coupledSelectedTagError B w c tag v ∂B.completeWorldLaw π.seedLaw

end ProphetSecretary.Limiting
