import ProphetSecretary.Limiting.CountableTruncationScoreLimit
import ProphetSecretary.Limiting.CountableSelectedTagBounds

/-!
# Selected perturbation means along actual canonical truncations

A common bounded measurable tag vanishes below a positive value. The proved
outcome-error convergence and the explicit selected-tag estimate imply
convergence of its expectation on the selected occurrence. Prefixes and
positive cutoffs may follow any cofinal path. This supplies the selected
perturbation coefficient in `lem:envelopes`.
-/

open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting
open CountableInstance

lemma CountableInstance.CountableRule.integrable_selectedTag {Seed : Type*} [MeasurableSpace Seed]
    (π : CountableRule Seed) (hπ : π.IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (tag : CountableTags Seed) (hTag : tag.IsMeasurable)
    {D : ℝ} (hD : 0≤D) (hBound : ∀ᵐ v ∂B.completeWorldLaw ν, ∀ i, |tag v i|≤D) :
    Integrable (π.selectedTag tag) (B.completeWorldLaw ν) :=
  FirstAcceptance.integrable_selectedTag π.codeAccepted codeTime tag (B.completeWorldLaw ν)
    (π.measurableSet_codeAccepted hπ) measurable_codeTime hTag hD hBound

lemma CountableInstance.truncatedValuePolicy_selectedTagError_tendsto (B : CountableInstance)
    (hZero : B.terminal=0) {w c D b : ℝ} (hw : 0<w) (hc : 0<c) (hD : 0≤D) (hb : 0<b)
    (Ns : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ m, (B.terminal : ℝ)<bs m)
    (hNs : Tendsto Ns atTop atTop) (hbsLim : Tendsto bs atTop (𝓝 (B.terminal : ℝ)))
    (tag : CountableTags Unit) (hTag : tag.IsMeasurable)
    (hBound : ∀ᵐ v ∂B.completeWorldLaw (Measure.dirac ()), ∀ i, |tag v i|≤D)
    (hVanish : ∀ᵐ v ∂B.completeWorldLaw (Measure.dirac ()), ∀ i, codeValue v i<b → tag v i=0) :
    Tendsto (fun m => (B.truncatedValuePolicy (Ns m) (bs m) (hbs m) hw.le hc.le).expectedSelectedTagError w c tag)
      atTop (𝓝 (0 : ℝ)) := by
  let π := fun m => B.truncatedValuePolicy (Ns m) (bs m) (hbs m) hw.le hc.le
  have hOutcome := B.truncatedValuePolicy_outcomeError_tendsto hZero hw hc Ns bs hbs hNs hbsLim
  have hLimit := Model.selectedTagErrorBound_tendsto_zero hOutcome D b (1+(B.totalTailMass (b/2)).toReal)
  apply squeeze_zero (fun m => integral_nonneg (fun _ => abs_nonneg _)) _ hLimit
  intro m
  exact (π m).selectedTag_stability_of_outcome_bound hZero hw.le hc.le hD hb le_rfl le_rfl
    tag hTag hBound hVanish

theorem CountableInstance.truncatedValueRule_selectedTagMean_tendsto (B : CountableInstance)
    (hZero : B.terminal=0) {w c D b : ℝ} (hw : 0<w) (hc : 0<c) (hD : 0≤D) (hb : 0<b)
    (Ns : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ m, (B.terminal : ℝ)<bs m)
    (hNs : Tendsto Ns atTop atTop) (hbsLim : Tendsto bs atTop (𝓝 (B.terminal : ℝ)))
    (tag : CountableTags Unit) (hTag : tag.IsMeasurable)
    (hBound : ∀ᵐ v ∂B.completeWorldLaw (Measure.dirac ()), ∀ i, |tag v i|≤D)
    (hVanish : ∀ᵐ v ∂B.completeWorldLaw (Measure.dirac ()), ∀ i, codeValue v i<b → tag v i=0) :
    Tendsto (fun m => ∫ v, (B.truncatedValueRule (Ns m) (bs m) (hbs m) w c).selectedTag tag v
      ∂B.completeWorldLaw (Measure.dirac ())) atTop
      (𝓝 (∫ v, (B.valueRule w c).selectedTag tag v ∂B.completeWorldLaw (Measure.dirac ()))) := by
  let π := fun m => B.truncatedValuePolicy (Ns m) (bs m) (hbs m) hw.le hc.le
  have hLimit := B.truncatedValuePolicy_selectedTagError_tendsto hZero hw hc hD hb Ns bs hbs hNs hbsLim
    tag hTag hBound hVanish
  let σ := fun m => B.truncatedValueRule (Ns m) (bs m) (hbs m) w c
  have hσ (m : ℕ) : (σ m).IsMeasurable :=
    (B.truncatedValuePolicy (Ns m) (bs m) (hbs m) hw.le hc.le).measurable_rule
  have hBase := (B.valueRule w c).integrable_selectedTag (B.valueRule_isMeasurable hw.le hc.le) B
    (Measure.dirac ()) tag hTag hD hBound
  have hInt (m : ℕ) := (σ m).integrable_selectedTag (hσ m) B
    (Measure.dirac ()) tag hTag hD hBound
  have hErase (v : CompleteWorld Unit) : eraseCompleteSeed v=v := by
    apply Prod.ext rfl
    apply Prod.ext rfl
    exact Prod.ext rfl (Subsingleton.elim _ _)
  have hAccepted : B.canonicalAccepted (Seed:=Unit) w c=(B.valueRule w c).codeAccepted := by
    funext v i
    unfold canonicalAccepted
    rw [hErase]
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hLimit
  intro m
  change ‖(∫ v : CompleteWorld Unit, (σ m).selectedTag tag v ∂B.completeWorldLaw (Measure.dirac ()))-
    (∫ v : CompleteWorld Unit, (B.valueRule w c).selectedTag tag v ∂B.completeWorldLaw (Measure.dirac ()))‖≤
    ∫ v : CompleteWorld Unit, |(σ m).selectedTag tag v-
      FirstAcceptance.reward 0 (B.canonicalAccepted w c) codeTime tag v| ∂B.completeWorldLaw (Measure.dirac ())
  rw [hAccepted,←integral_sub (hInt m) hBase]
  have hNorm := norm_integral_le_integral_norm (μ:=B.completeWorldLaw (Measure.dirac ()))
    (f:=fun v : CompleteWorld Unit => (σ m).selectedTag tag v-(B.valueRule w c).selectedTag tag v)
  simpa only [CountableRule.selectedTag,Real.norm_eq_abs] using hNorm

namespace CountableInstance

noncomputable def anonymousPerturbationTag {Seed : Type*} (φ : ℝ → ℝ) : CountableTags Seed :=
  fun v k => match candidateEnumeration.symm k with
    | Sum.inl _ => 0
    | Sum.inr _ => φ (codeValue v k)

lemma anonymousPerturbationTag_measurable {Seed : Type*} [MeasurableSpace Seed]
    {φ : ℝ → ℝ} (hφ : Measurable φ) : (anonymousPerturbationTag (Seed:=Seed) φ).IsMeasurable := by
  intro k
  cases h : candidateEnumeration.symm k with
  | inl i => simpa only [anonymousPerturbationTag,h] using (measurable_const : Measurable (fun _ : CompleteWorld Seed => (0 : ℝ)))
  | inr p => simpa only [anonymousPerturbationTag,h,Function.comp_def] using hφ.comp (measurable_codeValue k)

lemma anonymousPerturbationTag_bound {Seed : Type*} {φ : ℝ → ℝ} {D : ℝ}
    (hD : 0≤D) (hBound : ∀ x, |φ x|≤D) (v : CompleteWorld Seed) (k : ℕ) :
    |anonymousPerturbationTag φ v k|≤D := by
  cases h : candidateEnumeration.symm k with
  | inl i => simpa only [anonymousPerturbationTag,h,abs_zero] using hD
  | inr p => simpa only [anonymousPerturbationTag,h] using hBound (codeValue v k)

lemma anonymousPerturbationTag_vanish {Seed : Type*} {φ : ℝ → ℝ} {b : ℝ}
    (hVanish : ∀ x, x<b → φ x=0) (v : CompleteWorld Seed) (k : ℕ) (hk : codeValue v k<b) :
    anonymousPerturbationTag φ v k=0 := by
  cases h : candidateEnumeration.symm k with
  | inl i => simp only [anonymousPerturbationTag,h]
  | inr p => simp only [anonymousPerturbationTag,h,hVanish _ hk]

/-- The bounded anonymous-mark perturbation coefficient converges along every
actual cofinal canonical truncation path. -/
theorem truncatedValueRule_anonymousPerturbationMean_tendsto (B : CountableInstance)
    (hZero : B.terminal=0) {w c D b : ℝ} (hw : 0<w) (hc : 0<c) (hD : 0≤D) (hb : 0<b)
    (Ns : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ m, (B.terminal : ℝ)<bs m)
    (hNs : Tendsto Ns atTop atTop) (hbsLim : Tendsto bs atTop (𝓝 (B.terminal : ℝ)))
    (φ : ℝ → ℝ) (hφ : Measurable φ) (hBound : ∀ x, |φ x|≤D)
    (hVanish : ∀ x, x<b → φ x=0) :
    Tendsto (fun m => ∫ v, (B.truncatedValueRule (Ns m) (bs m) (hbs m) w c).selectedTag
      (anonymousPerturbationTag φ) v ∂B.completeWorldLaw (Measure.dirac ())) atTop
      (𝓝 (∫ v, (B.valueRule w c).selectedTag (anonymousPerturbationTag φ) v
        ∂B.completeWorldLaw (Measure.dirac ()))) :=
  B.truncatedValueRule_selectedTagMean_tendsto hZero hw hc hD hb Ns bs hbs hNs hbsLim
    (anonymousPerturbationTag φ) (anonymousPerturbationTag_measurable hφ)
    (Eventually.of_forall (fun v k => anonymousPerturbationTag_bound hD hBound v k))
    (Eventually.of_forall (fun v k hk => anonymousPerturbationTag_vanish hVanish v k hk))

end CountableInstance

end ProphetSecretary.Limiting
