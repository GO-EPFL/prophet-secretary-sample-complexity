import ProphetSecretary.Limiting.WeakRandomizedMarkMap
import ProphetSecretary.Probability.CenteredValueScore

/-!
# Actual offer laws under a randomized upper-mark replacement

Below the chosen old cutoff the value is retained. Above it an independent
tag is passed through the mark map. The law is a genuine pushforward of the
old mark and independent tag, and splits into unchanged lower mass and the
actual randomized image of the old upper mass.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal
namespace ProphetSecretary.Limiting
variable {T : Type*} [MeasurableSpace T]

noncomputable def cutoffPayloadDisplay (b : ℝ) (Φ : ℝ × T → ℝ) (z : ℝ × T) : ℝ :=
  if b<z.1 then Φ z else z.1

lemma measurable_cutoffPayloadDisplay (b : ℝ) {Φ : ℝ × T → ℝ} (hΦ : Measurable Φ) :
    Measurable (cutoffPayloadDisplay b Φ) :=
  hΦ.piecewise (measurableSet_Ioi.preimage measurable_fst) measurable_fst

lemma map_cutoffPayloadDisplay (μ : Measure ℝ) [SFinite μ] (κ : Measure T) [IsProbabilityMeasure κ]
    (b : ℝ) (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) :
    (μ.prod κ).map (cutoffPayloadDisplay b Φ)=
      μ.restrict (Iic b)+((μ.restrict (Ioi b)).prod κ).map Φ := by
  let S : Set (ℝ × T) := Ioi b ×ˢ univ
  have hS : MeasurableSet S := measurableSet_Ioi.prod MeasurableSet.univ
  have hHigh : ((μ.prod κ).restrict S).map (cutoffPayloadDisplay b Φ)=
      ((μ.restrict (Ioi b)).prod κ).map Φ := by
    rw [Measure.restrict_prod_eq_prod_univ]
    apply Measure.map_congr
    filter_upwards [ae_restrict_mem hS] with z hz
    exact if_pos hz.1
  have hLowMeasure : (μ.prod κ).restrict Sᶜ=(μ.restrict (Iic b)).prod κ := by
    rw [Measure.restrict_prod_eq_prod_univ]
    congr 1
    ext z
    simp only [S,mem_compl_iff,mem_prod,mem_univ,and_true,mem_Ioi,mem_Iic,not_lt]
  have hLow : ((μ.prod κ).restrict Sᶜ).map (cutoffPayloadDisplay b Φ)=μ.restrict (Iic b) := by
    calc
      _ = ((μ.prod κ).restrict Sᶜ).map Prod.fst := by
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem hS.compl] with z hz
        have hx : ¬b<z.1 := fun h => hz ⟨h,mem_univ _⟩
        exact if_neg hx
      _ = _ := by rw [hLowMeasure,Measure.map_fst_prod,measure_univ,one_smul]
  calc
    _ = ((μ.prod κ).restrict S+(μ.prod κ).restrict Sᶜ).map (cutoffPayloadDisplay b Φ) := by
      rw [Measure.restrict_add_restrict_compl hS]
    _ = _ := by
      rw [Measure.map_add _ _ (measurable_cutoffPayloadDisplay b hΦ),hHigh,hLow,add_comm]

noncomputable def cutoffPayloadLaw (q : ProbabilityMeasure ℝ) (κ : Measure T) [IsProbabilityMeasure κ]
    (b : ℝ) (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) : ProbabilityMeasure ℝ :=
  ⟨((q : Measure ℝ).prod κ).map (cutoffPayloadDisplay b Φ),
    Measure.isProbabilityMeasure_map (measurable_cutoffPayloadDisplay b hΦ).aemeasurable⟩

lemma cutoffPayloadLaw_supported (q : ProbabilityMeasure ℝ) (κ : Measure T) [IsProbabilityMeasure κ]
    (b : ℝ) (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) (H : ℝ≥0)
    (hOld : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) H)
    (hImage : ∀ᵐ z ∂(q : Measure ℝ).prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H) :
    ∀ᵐ x ∂(cutoffPayloadLaw q κ b Φ hΦ : Measure ℝ), x∈Icc (0 : ℝ) H := by
  apply (ae_map_iff (measurable_cutoffPayloadDisplay b hΦ).aemeasurable measurableSet_Icc).mpr
  have hMP : MeasurePreserving (Prod.fst : ℝ × T → ℝ) ((q : Measure ℝ).prod κ) (q : Measure ℝ) := measurePreserving_fst
  filter_upwards [hMP.quasiMeasurePreserving.ae hOld,hImage] with z hz hφ
  unfold cutoffPayloadDisplay
  split_ifs with h
  · exact hφ h
  · exact hz

omit [MeasurableSpace T] in
lemma cutoffPayloadDisplay_tail_preimage (b d : ℝ) (Φ : ℝ × T → ℝ) :
    cutoffPayloadDisplay b Φ ⁻¹' Ioi d⊆Prod.fst ⁻¹' Ioi (min b d) := by
  intro z hz
  change min b d<z.1
  change d<cutoffPayloadDisplay b Φ z at hz
  unfold cutoffPayloadDisplay at hz
  split_ifs at hz with h
  · exact (min_le_left _ _).trans_lt h
  · exact (min_le_right _ _).trans_lt hz

lemma displayedPayloadIntensity_add (μ ν : FiniteMeasure ℝ) (κ : Measure T) [IsProbabilityMeasure κ]
    (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) :
    displayedPayloadIntensity (μ+ν) κ Φ hΦ=
      displayedPayloadIntensity μ κ Φ hΦ+displayedPayloadIntensity ν κ Φ hΦ := by
  apply FiniteMeasure.toMeasure_injective
  rw [FiniteMeasure.toMeasure_add]
  simp_rw [displayedPayloadIntensity_toMeasure]
  rw [FiniteMeasure.toMeasure_add,Measure.add_prod,Measure.map_add _ _ hΦ]

noncomputable def payloadImageHom (κ : Measure T) [IsProbabilityMeasure κ]
    (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) : FiniteMeasure ℝ →+ FiniteMeasure ℝ where
  toFun μ := displayedPayloadIntensity μ κ Φ hΦ
  map_zero' := by
    apply FiniteMeasure.toMeasure_injective
    rw [displayedPayloadIntensity_toMeasure]
    simp
  map_add' μ ν := displayedPayloadIntensity_add μ ν κ Φ hΦ

end ProphetSecretary.Limiting
