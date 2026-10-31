import ProphetSecretary.Limiting.TruncatedIndividualScorePayoff
import ProphetSecretary.Limiting.TruncatedBandScorePayoff
import ProphetSecretary.Limiting.CountableTruncationScoreLimit

/-!
# Actual hybrid covariance limits along countable canonical truncations

Exact observer score transport identifies the finite-hybrid covariances with
full-world truncated execution covariances. The proved L² score stability
then passes to the full canonical execution along any cofinal prefix and
vanishing positive cutoff path.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology
namespace ProphetSecretary.Limiting
open CountableInstance ProphetSecretary.Probability

lemma CountableInstance.intensityAbove_real_upper (B : CountableInstance) {d : ℝ}
    (hd : (B.terminal:ℝ)<d) (b : ℝ) (hdb : d≤b) :
    (B.intensityAbove d hd:Measure ℝ).real (Ioi b)=B.intensity.real (Ioi b) := by
  unfold Measure.real
  change (B.intensity.restrict (Ioi d) (Ioi b)).toReal=_
  rw [Measure.restrict_apply measurableSet_Ioi,inter_eq_left.mpr (Ioi_subset_Ioi hdb)]

theorem CountableInstance.hybridTruncation_individual_score_tendsto (B : CountableInstance)
    (hZero : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (Ns : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ j, (B.terminal:ℝ)<bs j)
    (hNs : Tendsto Ns atTop atTop) (hbsLim : Tendsto bs atTop (𝓝 (B.terminal:ℝ)))
    (i : ℕ) (hi : ∀ j, i<Ns j) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun j => ∫ v : HybridWorld (Ns j) Unit,
      centeredBoundedScore (B.individuals i:Measure ℝ) f (v.2.1 ⟨i,hi j⟩)*
        ((B.truncation (Ns j) (bs j) (hbs j)).valueRule w c).realizedReward 0 v
      ∂(B.truncation (Ns j) (bs j) (hbs j)).law (Measure.dirac ())) atTop
      (𝓝 (∫ v, centeredBoundedScore (B.individuals i:Measure ℝ) f (v.2.1 i)*
        (B.valueRule w c).realizedReward 0 v ∂B.completeWorldLaw (Measure.dirac ()))) ∧
    Tendsto (fun j => ∫ v : HybridWorld (Ns j) Unit,
      centeredBoundedScore (B.individuals i:Measure ℝ) f (v.2.1 ⟨i,hi j⟩)*
        ((B.truncation (Ns j) (bs j) (hbs j)).valueRule w c).realizedDuration v
      ∂(B.truncation (Ns j) (bs j) (hbs j)).law (Measure.dirac ())) atTop
      (𝓝 (∫ v, centeredBoundedScore (B.individuals i:Measure ℝ) f (v.2.1 i)*
        (B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))) := by
  let Z : CompleteWorld Unit → ℝ := fun v => centeredBoundedScore (B.individuals i:Measure ℝ) f (v.2.1 i)
  have hZM : Measurable Z := (continuous_centeredBoundedScore (B.individuals i:Measure ℝ) f).measurable.comp
    ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  have hZ : MemLp Z 2 (B.completeWorldLaw (Measure.dirac ())) := MemLp.of_bound hZM.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (fun v => centeredBoundedScore_abs_le_one (B.individuals i:Measure ℝ) f (v.2.1 i)))
  obtain ⟨hR,hT⟩ := B.truncatedValueRule_scorePayoffs_tendsto hZero hw hc Ns bs hbs hNs hbsLim Z hZ
  have hEq (j) := ((B.truncation (Ns j) (bs j) (hbs j)).valueRule w c).integral_individualScorePayoffs_eq_extended
    ((B.truncation (Ns j) (bs j) (hbs j)).valueRule_isMeasurable hw.le hc.le)
    B (Measure.dirac ()) (hbs j) ⟨i,hi j⟩ f
  constructor
  · simpa only [hZero,NNReal.coe_zero] using hR.congr (fun j => (hEq j).1.symm)
  · exact hT.congr (fun j => (hEq j).2.symm)

theorem CountableInstance.hybridTruncation_band_score_tendsto (B : CountableInstance)
    (hZero : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (Ns : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ j, (B.terminal:ℝ)<bs j)
    (hNs : Tendsto Ns atTop atTop) (hbsLim : Tendsto bs atTop (𝓝 (B.terminal:ℝ)))
    (b : ℝ) (hb : (B.terminal:ℝ)<b) (hBelow : ∀ j, bs j≤b) :
    Tendsto (fun j => ∫ v : HybridWorld (Ns j) Unit,
      ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-B.intensity.real (Ioi b))*
        ((B.truncation (Ns j) (bs j) (hbs j)).valueRule w c).realizedReward 0 v
      ∂(B.truncation (Ns j) (bs j) (hbs j)).law (Measure.dirac ())) atTop
      (𝓝 (∫ v, B.bandScore (Ioi b) v*(B.valueRule w c).realizedReward 0 v ∂B.completeWorldLaw (Measure.dirac ()))) ∧
    Tendsto (fun j => ∫ v : HybridWorld (Ns j) Unit,
      ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-B.intensity.real (Ioi b))*
        ((B.truncation (Ns j) (bs j) (hbs j)).valueRule w c).realizedDuration v
      ∂(B.truncation (Ns j) (bs j) (hbs j)).law (Measure.dirac ())) atTop
      (𝓝 (∫ v, B.bandScore (Ioi b) v*(B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))) := by
  obtain ⟨hR,hT⟩ := B.truncatedValueRule_scorePayoffs_tendsto hZero hw hc Ns bs hbs hNs hbsLim
    (B.bandScore (Ioi b)) (B.bandScore_memLp_two measurableSet_Ioi hb (Subset.refl _) (Measure.dirac ()))
  have hEq (j) := ((B.truncation (Ns j) (bs j) (hbs j)).valueRule w c).integral_bandScorePayoffs_eq_extended
    ((B.truncation (Ns j) (bs j) (hbs j)).valueRule_isMeasurable hw.le hc.le)
    B (Measure.dirac ()) (hbs j) b (hBelow j)
  constructor
  · simpa only [hZero,NNReal.coe_zero] using hR.congr (fun j => (hEq j).1.symm)
  · exact hT.congr (fun j => (hEq j).2.symm)
end ProphetSecretary.Limiting
