import ProphetSecretary.Limiting.HybridOutcomeError
import ProphetSecretary.Stability.SelectedOccurrence

/-!
# Measurable selected tags on actual hybrid occurrences

A common tag assignment is an analytical function on the complete experiment,
with one coordinate for each actual retained or anonymous occurrence. Branch
measurability is explicit. This includes value-dependent and independent
auxiliary tags without adding future information to either executed callback.
No selection receives tag zero.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*}

abbrev HybridTags (n : ℕ) (Seed : Type*) :=
  (v : HybridWorld n Seed) → Fin (n+v.1.1) → ℝ

def HybridTags.IsMeasurable [MeasurableSpace Seed] (tag : HybridTags n Seed) : Prop :=
  ∀ N (k : Fin (n+N)), Measurable (fun z : (Fin N → Point) × Model.World n Seed =>
    tag (configurationMk N z.1,z.2) k)

noncomputable def HybridRule.selectedTagDifference (π : HybridRule n Seed)
    (B : FiniteIntensityHybridInstance n) (w c : ℝ) (tag : HybridTags n Seed) (v : HybridWorld n Seed) : ℝ :=
  let x := combinedValues v.2.1 v.1.2
  let u := combinedClocks v.2.2.1 v.1.2
  (π.asFinitePolicy v.1.1).selectedTag v.2.2.2 x u (tag v)-
    ((B.valueRule w c).asFinitePolicy v.1.1).selectedTag () x u (tag v)

lemma HybridRule.selectedTagDifference_abs_le (π : HybridRule n Seed)
    (B : FiniteIntensityHybridInstance n) (w c : ℝ) (tag : HybridTags n Seed)
    (v : HybridWorld n Seed) {D : ℝ} (hD : 0 ≤ D) (hTag : ∀ k, |tag v k| ≤ D) :
    |π.selectedTagDifference B w c tag v| ≤ 2*D := by
  calc
    _ ≤ |(π.asFinitePolicy v.1.1).selectedTag v.2.2.2 (combinedValues v.2.1 v.1.2)
        (combinedClocks v.2.2.1 v.1.2) (tag v)|+
      |((B.valueRule w c).asFinitePolicy v.1.1).selectedTag () (combinedValues v.2.1 v.1.2)
        (combinedClocks v.2.2.1 v.1.2) (tag v)| := abs_sub _ _
    _ ≤ D+D := add_le_add ((π.asFinitePolicy v.1.1).selectedTag_abs_le _ _ _ _ hD hTag)
      (((B.valueRule w c).asFinitePolicy v.1.1).selectedTag_abs_le _ _ _ _ hD hTag)
    _ = _ := by ring

variable [MeasurableSpace Seed]

lemma HybridRule.measurable_selectedTagDifference (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (B : FiniteIntensityHybridInstance n) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (tag : HybridTags n Seed) (hTag : tag.IsMeasurable) :
    Measurable (π.selectedTagDifference B w c tag) := by
  apply measurable_of_configuration_prod_branches
  intro N
  let Ω := (Fin N → Point) × Model.World n Seed
  have hr : Measurable (fun v : Ω => v.2.2.2) := by fun_prop
  have hx (i : Fin n) : Measurable (fun v : Ω => v.2.1 i) := by fun_prop
  have hu (i : Fin n) : Measurable (fun v : Ω => v.2.2.1 i) := by fun_prop
  have hp (j : Fin N) : Measurable (fun v : Ω => v.1 j) := (measurable_pi_apply j).comp measurable_fst
  have hX (k : Fin (n+N)) := measurable_combinedValues_family _ hx _ hp k
  have hU (k : Fin (n+N)) := measurable_combinedClocks_family _ hu _ hp k
  have hσ := π.asFinitePolicy_isMeasurable hπ N
  have hρ := (B.valueRule w c).asFinitePolicy_isMeasurable (B.valueRule_isMeasurable hw hc) N
  exact ((π.asFinitePolicy N).measurable_selectedTag hσ hr hX hU (hTag N)).sub
    (((B.valueRule w c).asFinitePolicy N).measurable_selectedTag hρ measurable_const hX hU (hTag N))

lemma HybridRule.integrable_selectedTagDifference (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (B : FiniteIntensityHybridInstance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c D : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (hD : 0 ≤ D)
    (tag : HybridTags n Seed) (hTag : tag.IsMeasurable)
    (hBound : ∀ᵐ v ∂B.law ν, ∀ k, |tag v k| ≤ D) :
    Integrable (π.selectedTagDifference B w c tag) (B.law ν) := by
  apply Integrable.of_bound (π.measurable_selectedTagDifference hπ B hw hc tag hTag).aestronglyMeasurable (2*D)
  filter_upwards [hBound] with v hv
  rw [Real.norm_eq_abs]
  exact π.selectedTagDifference_abs_le B w c tag v hD hv

noncomputable def RandomizedHybridPolicy.expectedSelectedTagError (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (w c : ℝ) (tag : HybridTags n π.Seed) : ℝ :=
  ∫ v, |π.rule.selectedTagDifference B w c tag v| ∂B.law π.seedLaw

lemma RandomizedHybridPolicy.expectedSelectedTagError_nonnegative (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (w c : ℝ) (tag : HybridTags n π.Seed) :
    0 ≤ π.expectedSelectedTagError B w c tag := integral_nonneg (fun _ => abs_nonneg _)

end ProphetSecretary.Limiting
