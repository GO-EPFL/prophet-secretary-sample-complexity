import ProphetSecretary.Limiting.HybridSelectedTag
import ProphetSecretary.Limiting.HybridPositivePairs

/-!
# Explicit selected-tag bounds in hybrid instances

A tag discrepancy is charged to coupled outcome error or an unconditional
pair of positive offers with close clocks. The pair estimate is derived from
the actual marked Poisson law. The resulting square-root bound also covers
zero outcome error and arbitrary independent auxiliary tags.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*}

lemma HybridRule.selectedTagDifference_le_outcome_pair (π : HybridRule n Seed)
    (B : FiniteIntensityHybridInstance n) (w c : ℝ) (tag : HybridTags n Seed)
    (v : HybridWorld n Seed) {D b η : ℝ} (hD : 0 ≤ D) (hb : 0 < b) (hη : 0 < η)
    (hTag : ∀ k, |tag v k| ≤ D)
    (hZero : ∀ k, combinedValues v.2.1 v.1.2 k < b → tag v k=0) :
    |π.selectedTagDifference B w c tag v| ≤
      2*D*(2*π.coupledValueOutcomeError B w c v/b+π.coupledValueOutcomeError B w c v/η+
        if v ∈ hybridClosePositivePair (b/2) η then 1 else 0) := by
  let x := combinedValues v.2.1 v.1.2
  let u := combinedClocks v.2.2.1 v.1.2
  let σ := π.asFinitePolicy v.1.1
  let ρ := (B.valueRule w c).asFinitePolicy v.1.1
  have h := σ.selectedTag_difference_le ρ v.2.2.2 () x u (tag v) hD hb hη hTag hZero
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (by norm_num) hD)
  have hR : |σ.reward v.2.2.2 Finset.univ x u-ρ.reward () Finset.univ x u| ≤
      π.coupledValueOutcomeError B w c v := le_add_of_nonneg_right (abs_nonneg _)
  have hT : |σ.stoppingTime v.2.2.2 Finset.univ x u-ρ.stoppingTime () Finset.univ x u| ≤
      π.coupledValueOutcomeError B w c v := le_add_of_nonneg_left (abs_nonneg _)
  exact add_le_add (add_le_add
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hR (by norm_num)) hb.le)
    (div_le_div_of_nonneg_right hT hη.le)) le_rfl

variable [MeasurableSpace Seed]

lemma HybridRule.integral_selectedTagDifference_le (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (B : FiniteIntensityHybridInstance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c D b η : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (hD : 0 ≤ D) (hb : 0 < b) (hη : 0 < η)
    (tag : HybridTags n Seed) (hTag : tag.IsMeasurable)
    (hBound : ∀ᵐ v ∂B.law ν, ∀ k, |tag v k| ≤ D)
    (hZero : ∀ᵐ v ∂B.law ν, ∀ k, combinedValues v.2.1 v.1.2 k < b → tag v k=0) :
    (∫ v, |π.selectedTagDifference B w c tag v| ∂B.law ν) ≤
      2*D*(2*(∫ v, π.coupledValueOutcomeError B w c v ∂B.law ν)/b+
        (∫ v, π.coupledValueOutcomeError B w c v ∂B.law ν)/η+
          (B.law ν).real (hybridClosePositivePair (b/2) η)) := by
  let E := hybridClosePositivePair (n := n) (Seed := Seed) (b/2) η
  let I : HybridWorld n Seed → ℝ := E.indicator (fun _ => 1)
  have hE : MeasurableSet E := measurableSet_hybridClosePositivePair _ _
  have hI : Integrable I (B.law ν) := (integrable_const (1 : ℝ)).indicator hE
  have hIeq : (∫ v, I v ∂B.law ν)=(B.law ν).real E := integral_indicator_one hE
  have hError := π.integrable_coupledValueOutcomeError hπ B ν hw hc
  have hTagI := (π.integrable_selectedTagDifference hπ B ν hw hc hD tag hTag hBound).abs
  have hRHS : Integrable (fun v => 2*D*(2*π.coupledValueOutcomeError B w c v/b+
      π.coupledValueOutcomeError B w c v/η+I v)) (B.law ν) :=
    ((((hError.const_mul 2).div_const b).add (hError.div_const η)).add hI).const_mul (2*D)
  have hPoint : ∀ᵐ v ∂B.law ν, |π.selectedTagDifference B w c tag v| ≤
      2*D*(2*π.coupledValueOutcomeError B w c v/b+π.coupledValueOutcomeError B w c v/η+I v) := by
    filter_upwards [hBound,hZero] with v hv hz
    simpa only [I,E,Set.indicator_apply,Pi.one_apply] using
      π.selectedTagDifference_le_outcome_pair B w c tag v hD hb hη hv hz
  have h := integral_mono_ae hTagI hRHS hPoint
  rw [integral_const_mul,
    integral_add (f := fun v => 2*π.coupledValueOutcomeError B w c v/b+π.coupledValueOutcomeError B w c v/η)
      (g := I) (((hError.const_mul 2).div_const b).add (hError.div_const η)) hI,
    integral_add (f := fun v => 2*π.coupledValueOutcomeError B w c v/b)
      (g := fun v => π.coupledValueOutcomeError B w c v/η)
      ((hError.const_mul 2).div_const b) (hError.div_const η),integral_div,integral_div,integral_const_mul,hIeq] at h
  exact h

theorem RandomizedHybridPolicy.selectedTag_stability_bound (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) {w c D b η L : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (hD : 0 ≤ D) (hb : 0 < b) (hη : 0 < η)
    (hL : B.tailCount (b/2) ≤ L) (tag : HybridTags n π.Seed) (hTag : tag.IsMeasurable)
    (hBound : ∀ᵐ v ∂B.law π.seedLaw, ∀ k, |tag v k| ≤ D)
    (hZero : ∀ᵐ v ∂B.law π.seedLaw, ∀ k, combinedValues v.2.1 v.1.2 k < b → tag v k=0) :
    π.expectedSelectedTagError B w c tag ≤ 2*D*(2*π.expectedValueOutcomeError B w c/b+
      π.expectedValueOutcomeError B w c/η+2*η*(1+L)^2) := by
  have h := π.rule.integral_selectedTagDifference_le π.measurable_rule B π.seedLaw hw hc hD hb hη tag hTag hBound hZero
  have hPair := B.closePositivePair_probability π.seedLaw (b/2) hη.le
  have hL0 := B.tailCount_nonnegative (b/2)
  have hPoly : (B.tailCount (b/2))^2+B.tailCount (b/2) ≤ (1+L)^2 := by nlinarith
  have hPair' := hPair.trans (mul_le_mul_of_nonneg_left hPoly (mul_nonneg (by norm_num) hη.le))
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hPair') (mul_nonneg (by norm_num) hD))

theorem RandomizedHybridPolicy.selectedTag_stability_of_outcome_bound (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) {w c D b L W : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (hD : 0 ≤ D) (hb : 0 < b)
    (hL : B.tailCount (b/2) ≤ L) (hW : π.expectedValueOutcomeError B w c ≤ W)
    (tag : HybridTags n π.Seed) (hTag : tag.IsMeasurable)
    (hBound : ∀ᵐ v ∂B.law π.seedLaw, ∀ k, |tag v k| ≤ D)
    (hZero : ∀ᵐ v ∂B.law π.seedLaw, ∀ k, combinedValues v.2.1 v.1.2 k < b → tag v k=0) :
    π.expectedSelectedTagError B w c tag ≤ Model.selectedTagErrorBound D b (1+L) W := by
  have hOutcome0 : 0 ≤ π.expectedValueOutcomeError B w c :=
    integral_nonneg (π.rule.coupledValueOutcomeError_nonnegative B w c)
  have hBase : π.expectedSelectedTagError B w c tag ≤
      Model.selectedTagErrorBound D b (1+L) (π.expectedValueOutcomeError B w c) :=
    Model.selectedTag_error_optimize hD hb hOutcome0
      (fun _ hη => π.selectedTag_stability_bound B hw hc hD hb hη hL tag hTag hBound hZero)
  exact hBase.trans (Model.selectedTagErrorBound_monotone hD hb hW)

end ProphetSecretary.Limiting
