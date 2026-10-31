import ProphetSecretary.Limiting.HybridValueBandForms

/-!
# Positive hybrid boundary probability from positive-level tails

Retained clock replacement and anonymous Campbell bounds combine into one
estimate. Its only instance dependence is through tails above b/4 and b/2;
in particular the total Poisson rate near zero does not enter the constant.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

omit [MeasurableSpace Seed] in
lemma FiniteIntensityHybridInstance.positiveValueBand_eq_union
    (B : FiniteIntensityHybridInstance n) {w : ℝ} (hw : 0 < w) (c b e : ℝ) :
    (B.positiveValueBand w c b e : Set (HybridWorld n Seed)) =
      (Prod.snd ⁻¹' {z : Model.World n Seed | ∃ i : Fin n, z ∈ B.retainedPositiveBand w c b e i}) ∪
        B.anonymousBandEvent w c b e (fun z : Model.World n Seed => z.2.1) := by
  ext v
  exact B.positiveValueBand_iff hw c b e v

lemma FiniteIntensityHybridInstance.measurableSet_positiveValueBand
    (B : FiniteIntensityHybridInstance n) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (b e : ℝ) :
    MeasurableSet (B.positiveValueBand w c b e : Set (HybridWorld n Seed)) := by
  rw [B.positiveValueBand_eq_union hw c b e]
  apply MeasurableSet.union
  · apply MeasurableSet.preimage _ measurable_snd
    rw [Set.setOf_exists]
    exact MeasurableSet.iUnion fun i => B.measurableSet_retainedPositiveBand hw.le hc b e i
  · exact B.measurableSet_anonymousBandEvent hw.le hc b e (measurable_fst.comp measurable_snd)

theorem FiniteIntensityHybridInstance.positiveValueBand_probability
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {H w c b L4 L2 e : ℝ}
    (hH : 0 ≤ H) (hCap : (B.cap : ℝ) ≤ H) (hw : 0 < w) (hc : 0 < c) (hb : 0 < b)
    (hL4 : B.tailCount (b/4) ≤ L4) (hL2 : B.tailCount (b/2) ≤ L2)
    (he0 : 0 ≤ e) (he : e ≤ w*b/4) :
    (B.law ν).real (B.positiveValueBand w c b e) ≤
      (2*L2/(c*Model.positiveBandDuration H w c b L4))*e := by
  let K := 2*e/(c*Model.positiveBandDuration H w c b L4)
  let R : Set (Model.World n Seed) := {z | ∃ i : Fin n, z ∈ B.retainedPositiveBand w c b e i}
  have hK : 0 ≤ K := by
    have := Model.positiveBandDuration_pos hH hw hc hb ((B.tailCount_nonnegative _).trans hL4)
    dsimp only [K]
    positivity
  have hR : MeasurableSet R := by
    dsimp only [R]
    rw [Set.setOf_exists]
    exact MeasurableSet.iUnion fun i => B.measurableSet_retainedPositiveBand hw.le hc.le b e i
  have hMP : MeasurePreserving (Prod.snd : HybridWorld n Seed → Model.World n Seed)
      (B.law ν) (B.individuals.worldLaw ν) := measurePreserving_snd
  have hMarg : (B.law ν).real (Prod.snd ⁻¹' R) = (B.individuals.worldLaw ν).real R :=
    congrArg ENNReal.toReal (hMP.measure_preimage hR.nullMeasurableSet)
  have hμTail : (B.intensity : Measure ℝ).real (Ici b) ≤ (B.intensity : Measure ℝ).real (Ioi (b/2)) := by
    apply ENNReal.toReal_mono (measure_ne_top _ _)
    apply measure_mono
    intro x hx
    change b/2 < x
    have hbx : b ≤ x := hx
    linarith
  have hAnon := B.anonymousBandEvent_probability ha (B.individuals.worldLaw ν)
    (measurable_fst.comp measurable_snd) hH hCap hw hc hb hL4 he0 he
  rw [B.positiveValueBand_eq_union hw c b e]
  calc
    _ ≤ (B.law ν).real (Prod.snd ⁻¹' R)+
        (B.law ν).real (B.anonymousBandEvent w c b e (fun z : Model.World n Seed => z.2.1)) := measureReal_union_le _ _
    _ ≤ K*B.individuals.tailCount (b/2)+K*(B.intensity : Measure ℝ).real (Ici b) := by
      rw [hMarg]
      exact add_le_add (B.any_retainedPositiveBand_probability ha ν hH hCap hw hc hb hL4 he0 he) hAnon
    _ ≤ K*B.tailCount (b/2) := by
      unfold FiniteIntensityHybridInstance.tailCount
      rw [mul_add]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hμTail hK)
    _ ≤ K*L2 := mul_le_mul_of_nonneg_left hL2 hK
    _ = _ := by dsimp only [K]; ring

end ProphetSecretary.Limiting
