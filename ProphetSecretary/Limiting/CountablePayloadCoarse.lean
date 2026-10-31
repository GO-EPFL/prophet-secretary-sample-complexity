import ProphetSecretary.Limiting.CountableCutoffPayload
import ProphetSecretary.Limiting.ResidualPayloadWeak
import ProphetSecretary.Limiting.OrderedResidualRestriction

/-!
# Coarse intensity limits for a randomized upper-mark replacement

The finite coarse premeasure retains every displayed affected mark, including
dominated ones. Restricting above the coarse level gives exactly the new
countable intensity there. Thus atoms at any strictly higher level agree
with those of the actual new limiting instance.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting

lemma positiveFiniteDifference_add_cancel (A μ : FiniteMeasure ℝ) :
    positiveFiniteDifference (A+μ) μ=A := by
  apply FiniteMeasure.toMeasure_injective
  exact Measure.add_sub_cancel

namespace CountableInstance
variable {T : Type*} [MeasurableSpace T]

lemma intensityAbove_difference (B : CountableInstance) {c b : ℝ}
    (hc : (B.terminal : ℝ)<c) (hb : (B.terminal : ℝ)<b) (hcb : c≤b) :
    positiveFiniteDifference (B.intensityAbove c hc) (B.intensityAbove b hb)=
      (B.intensityAbove c hc).restrict (Iic b) := by
  let A := (B.intensityAbove c hc).restrict (Iic b)
  have hSplit : A+B.intensityAbove b hb=B.intensityAbove c hc := by
    rw [← B.intensityAbove_restrict hc hb hcb]
    apply FiniteMeasure.toMeasure_injective
    change (B.intensityAbove c hc : Measure ℝ).restrict (Iic b)+
      (B.intensityAbove c hc : Measure ℝ).restrict (Ioi b)=(B.intensityAbove c hc : Measure ℝ)
    simpa only [compl_Ioi,add_comm] using
      Measure.restrict_add_restrict_compl (μ := (B.intensityAbove c hc : Measure ℝ)) (s := Ioi b) measurableSet_Ioi
  calc
    _ = positiveFiniteDifference (A+B.intensityAbove b hb) (B.intensityAbove b hb) :=
      congrArg (fun ν => positiveFiniteDifference ν (B.intensityAbove b hb)) hSplit.symm
    _ = A := positiveFiniteDifference_add_cancel A _

noncomputable def payloadCoarseIntensity (B : CountableInstance) (c : ℝ) (hc : (B.terminal : ℝ)<c)
    (b : ℝ) (hb : (B.terminal : ℝ)<b) (κ : Measure T) [IsProbabilityMeasure κ]
    (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) : FiniteMeasure ℝ :=
  positiveFiniteDifference (B.intensityAbove c hc) (B.intensityAbove b hb)+
    displayedPayloadIntensity (B.intensityAbove b hb) κ Φ hΦ

lemma payloadCoarseIntensity_restrict (B : CountableInstance) (b : ℝ) (hb : (B.terminal : ℝ)<b)
    (H : ℝ≥0) (hH : B.cap≤H) (κ : Measure T) [IsProbabilityMeasure κ]
    (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hImage : ∀ᵐ z ∂B.intensity.prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H)
    (c : ℝ) (hc : (B.terminal : ℝ)<c) (hcb : c≤b) (d : ℝ) (hcd : c≤d) :
    (B.payloadCoarseIntensity c hc b hb κ Φ hΦ).restrict (Ioi d)=
      (B.mapPoissonAbove b hb H hH κ Φ hΦ hImage).intensityAbove d (hc.trans_le hcd) := by
  apply FiniteMeasure.toMeasure_injective
  unfold payloadCoarseIntensity
  rw [B.intensityAbove_difference hc hb hcb]
  change (((B.intensityAbove c hc).restrict (Iic b)+
    displayedPayloadIntensity (B.intensityAbove b hb) κ Φ hΦ : FiniteMeasure ℝ) : Measure ℝ).restrict (Ioi d)=
    (B.mapPoissonAbove b hb H hH κ Φ hΦ hImage).intensity.restrict (Ioi d)
  rw [FiniteMeasure.toMeasure_add,FiniteMeasure.restrict_measure_eq,
    B.mapPoissonAbove_intensity b hb H hH κ Φ hΦ hImage]
  change (((B.intensity.restrict (Ioi c)).restrict (Iic b))+
    (displayedPayloadIntensity (B.intensityAbove b hb) κ Φ hΦ : Measure ℝ)).restrict (Ioi d)=
    (B.intensity.restrict (Iic b)+
      (displayedPayloadIntensity (B.intensityAbove b hb) κ Φ hΦ : Measure ℝ).restrict (Ioi (B.terminal : ℝ))).restrict (Ioi d)
  rw [Measure.restrict_add,Measure.restrict_add,
    Measure.restrict_restrict_of_subset (Ioi_subset_Ioi (hc.trans_le hcd).le)]
  congr 1
  ext E hE
  rw [Measure.restrict_apply hE,Measure.restrict_apply (hE.inter measurableSet_Ioi),
    Measure.restrict_apply ((hE.inter measurableSet_Ioi).inter measurableSet_Iic),
    Measure.restrict_apply hE,Measure.restrict_apply (hE.inter measurableSet_Ioi)]
  congr 1
  exact inter_eq_left.mpr (fun _ hx => hcd.trans_lt hx.1.2)

lemma payloadCoarseIntensity_atom (B : CountableInstance) (b : ℝ) (hb : (B.terminal : ℝ)<b)
    (H : ℝ≥0) (hH : B.cap≤H) (κ : Measure T) [IsProbabilityMeasure κ]
    (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hImage : ∀ᵐ z ∂B.intensity.prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H)
    (c : ℝ) (hc : (B.terminal : ℝ)<c) (hcb : c≤b) (d : ℝ) (hcd : c<d) :
    (B.payloadCoarseIntensity c hc b hb κ Φ hΦ : Measure ℝ) {d}=
      (B.mapPoissonAbove b hb H hH κ Φ hΦ hImage).intensity {d} := by
  have h := congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ) {d})
    (B.payloadCoarseIntensity_restrict b hb H hH κ Φ hΦ hImage c hc hcb c le_rfl)
  change (B.payloadCoarseIntensity c hc b hb κ Φ hΦ : Measure ℝ).restrict (Ioi c) {d}=
    (B.mapPoissonAbove b hb H hH κ Φ hΦ hImage).intensity.restrict (Ioi c) {d} at h
  rw [Measure.restrict_apply (measurableSet_singleton d),Measure.restrict_apply (measurableSet_singleton d)] at h
  have hSet : ({d} : Set ℝ)∩Ioi c={d} :=
    inter_eq_left.mpr (fun _ hx => by simpa only [mem_singleton_iff.mp hx,mem_Ioi] using hcd)
  simpa only [hSet] using h

end CountableInstance
end ProphetSecretary.Limiting
