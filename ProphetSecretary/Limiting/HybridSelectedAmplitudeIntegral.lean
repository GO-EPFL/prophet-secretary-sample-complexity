import ProphetSecretary.Limiting.TaggedHybridAmplitudeLaw
import ProphetSecretary.Limiting.HybridOccurrenceStability
import ProphetSecretary.Limiting.HybridBellmanIdentity

/-!
# Integrals of selected amplitudes and their canonical comparison

The complete amplitude assignment is analytical. The policy observes only
its causal tagged history. Its expected discrepancy from the canonical
selection is controlled by the actual selected-occurrence error.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed T : Type*} [MeasurableSpace Seed] [MeasurableSpace T]

noncomputable def HybridRule.selectedAmplitude (π : HybridRule n Seed) (tag : HybridTags n Seed)
    (v : HybridWorld n Seed) : ℝ :=
  (π.asFinitePolicy v.1.1).selectedTag v.2.2.2 (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) (tag v)

lemma HybridRule.measurable_selectedAmplitude (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (tag : HybridTags n Seed) (hTag : tag.IsMeasurable) : Measurable (π.selectedAmplitude tag) := by
  apply measurable_of_configuration_prod_branches
  intro N
  let Ω := (Fin N → Point) × Model.World n Seed
  have hx (i : Fin n) : Measurable (fun v : Ω => v.2.1 i) := by fun_prop
  have hu (i : Fin n) : Measurable (fun v : Ω => v.2.2.1 i) := by fun_prop
  have hp (j : Fin N) : Measurable (fun v : Ω => v.1 j) := (measurable_pi_apply j).comp measurable_fst
  exact (π.asFinitePolicy N).measurable_selectedTag (π.asFinitePolicy_isMeasurable hπ N)
    measurable_snd.snd.snd (measurable_combinedValues_family _ hx _ hp)
    (measurable_combinedClocks_family _ hu _ hp) (hTag N)

lemma HybridRule.integrable_selectedAmplitude (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (B : FiniteIntensityHybridInstance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (tag : HybridTags n Seed) (hTag : tag.IsMeasurable) {D : ℝ} (hD : 0≤D)
    (hBound : ∀ v k, |tag v k|≤D) : Integrable (π.selectedAmplitude tag) (B.law ν) := by
  apply Integrable.of_bound (π.measurable_selectedAmplitude hπ tag hTag).aestronglyMeasurable D
  exact Eventually.of_forall (fun v => by
    rw [Real.norm_eq_abs]
    exact (π.asFinitePolicy v.1.1).selectedTag_abs_le _ _ _ _ hD (hBound v))

noncomputable def canonicalSelectedAmplitude (B : FiniteIntensityHybridInstance n)
    (w c : ℝ) (tag : HybridTags n Seed) (v : HybridWorld n Seed) : ℝ :=
  ((B.valueRule w c).asFinitePolicy v.1.1).selectedTag ()
    (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) (tag v)

lemma measurable_canonicalSelectedAmplitude (B : FiniteIntensityHybridInstance n)
    {w c : ℝ} (hw : 0≤w) (hc : 0≤c) (tag : HybridTags n Seed) (hTag : tag.IsMeasurable) :
    Measurable (canonicalSelectedAmplitude B w c tag) := by
  apply measurable_of_configuration_prod_branches
  intro N
  let Ω := (Fin N → Point) × Model.World n Seed
  have hx (i : Fin n) : Measurable (fun v : Ω => v.2.1 i) := by fun_prop
  have hu (i : Fin n) : Measurable (fun v : Ω => v.2.2.1 i) := by fun_prop
  have hp (j : Fin N) : Measurable (fun v : Ω => v.1 j) := (measurable_pi_apply j).comp measurable_fst
  exact ((B.valueRule w c).asFinitePolicy N).measurable_selectedTag
    ((B.valueRule w c).asFinitePolicy_isMeasurable (B.valueRule_isMeasurable hw hc) N)
    measurable_const (measurable_combinedValues_family _ hx _ hp)
    (measurable_combinedClocks_family _ hu _ hp) (hTag N)

lemma integrable_canonicalSelectedAmplitude (B : FiniteIntensityHybridInstance n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {w c D : ℝ} (hw : 0≤w) (hc : 0≤c)
    (tag : HybridTags n Seed) (hTag : tag.IsMeasurable) (hD : 0≤D)
    (hBound : ∀ v k, |tag v k|≤D) :
    Integrable (canonicalSelectedAmplitude B w c tag) (B.law ν) := by
  apply Integrable.of_bound (measurable_canonicalSelectedAmplitude B hw hc tag hTag).aestronglyMeasurable D
  exact Eventually.of_forall (fun v => by
    rw [Real.norm_eq_abs]
    exact ((B.valueRule w c).asFinitePolicy v.1.1).selectedTag_abs_le _ _ _ _ hD (hBound v))

noncomputable def canonicalChronologicalAmplitudeMean (B : FiniteIntensityHybridInstance n)
    (κ : Measure T) (A : ℝ × T → ℝ) (w c : ℝ) : ℝ :=
  ∫ v : HybridWorld n (Unit × (ℕ → T)),
    ((B.valueRule w c).asFinitePolicy v.1.1).selectedTag () (combinedValues v.2.1 v.1.2)
      (combinedClocks v.2.2.1 v.1.2) (chronologicalAmplitudeTag A v)
      ∂B.law ((Measure.dirac ()).prod (Measure.infinitePi (fun _ : ℕ => κ)))

lemma canonicalChronologicalAmplitudeMean_seed (B : FiniteIntensityHybridInstance n)
    (κ : Measure T) [IsProbabilityMeasure κ] (A : ℝ × T → ℝ) (hA : Measurable A)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0≤w) (hc : 0≤c) :
    (∫ v : HybridWorld n (Seed × (ℕ → T)),
      ((B.valueRule w c).asFinitePolicy v.1.1).selectedTag () (combinedValues v.2.1 v.1.2)
        (combinedClocks v.2.2.1 v.1.2) (chronologicalAmplitudeTag A v)
        ∂B.law (ν.prod (Measure.infinitePi (fun _ : ℕ => κ))))=
      canonicalChronologicalAmplitudeMean B κ A w c := by
  let K := Measure.infinitePi (fun _ : ℕ => κ)
  have hConst : MeasurePreserving (fun _ : Seed => ()) ν (Measure.dirac ()) :=
    ⟨measurable_const,by simp only [Measure.map_const,measure_univ,one_smul]⟩
  have hMP := (MeasurePreserving.id (configurationLaw B.intensity)).prod
    ((MeasurePreserving.id B.individuals.valuesLaw).prod
      ((MeasurePreserving.id (Model.Instance.clocksLaw n)).prod (hConst.prod (MeasurePreserving.id K))))
  let tag := chronologicalAmplitudeTag (n := n) (Seed := Unit) A
  have hm := measurable_canonicalSelectedAmplitude B hw hc tag (chronologicalAmplitudeTag_isMeasurable A hA)
  exact hMP.hasLaw.integral_comp hm.aestronglyMeasurable

end ProphetSecretary.Limiting
