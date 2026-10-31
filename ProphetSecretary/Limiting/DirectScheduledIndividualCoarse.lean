import ProphetSecretary.Limiting.DirectCoarseIndividualLimit
import ProphetSecretary.Limiting.DirectScheduledIndividualScores

/-!
# Retained-individual score comparison for the actual coarse execution

The score is centered under the same retained marginal law at every index.
All positive-level rarity and intensity conditions come from the actual
schedule, with no bound on its total first moment.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model ProphetSecretary.Probability

 theorem directScheduled_coarse_individual_score_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (K : ℕ) (d : ℝ) (hd : (B.terminal:ℝ)<d) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (i : Fin K) (f : ℝ →ᵇ ℝ) :
    let D := B.truncation K d hd
    let π := D.valueThresholdPolicy hw.le hc.le
    Tendsto (fun m => (directCoarsePolicy m (B.directVirtualCount hZero m) π d).expectedRewardScore
      (B.directFiniteApproximation hZero m)
      (directIndividualScore (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i.val f)) atTop
      (𝓝 (∫ v, centeredBoundedScore (B.individuals i.val:Measure ℝ) f (v.2.1 i)*
        (D.valueRule w c).realizedReward 0 v ∂D.law (Measure.dirac ()))) ∧
    Tendsto (fun m => (directCoarsePolicy m (B.directVirtualCount hZero m) π d).expectedDurationScore
      (B.directFiniteApproximation hZero m)
      (directIndividualScore (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i.val f)) atTop
      (𝓝 (∫ v, centeredBoundedScore (B.individuals i.val:Measure ℝ) f (v.2.1 i)*
        (D.valueRule w c).realizedDuration v ∂D.law (Measure.dirac ()))) := by
  let κ := fun m => (B.directVirtualOfferLaw hZero m:Measure ℝ)
  have hκ (m) : ∀ᵐ x ∂κ m, 0≤x := (B.directVirtualOfferLaw_bounds hZero m).mono (fun _ hx => hx.1)
  have hCap (m) : ∀ᵐ x ∂κ m, x≤(B.cap:ℝ) := (B.directVirtualOfferLaw_bounds hZero m).mono (fun _ hx => hx.2)
  have hdPos : 0<d := by simpa only [hZero,NNReal.coe_zero] using hd
  have hTail (m) : (B.directVirtualCount hZero m:ℝ)*(κ m).real (Ioi d)≤B.intensity.real (Ioi d) := by
    rw [B.directVirtualOfferLaw_upper_mass hZero m hdPos.le]
    have hMass : ((B.directTruncation m).intensity:Measure ℝ).real (Ioi d)≤B.intensity.real (Ioi d) :=
      ENNReal.toReal_mono (B.intensity_band_finite hd (subset_refl (Ioi d))).ne
        ((Measure.restrict_le_self : B.intensity.restrict (Ioi (B.markCutoff m))≤B.intensity) (Ioi d))
    have hNe : (B.directVirtualCount hZero m:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (B.directVirtualCount_positive hZero m))
    simpa only [mul_div_cancel₀ _ hNe] using hMass
  have h := B.direct_coarse_individual_score_tendsto hZero id (B.directVirtualCount hZero) tendsto_id
    (B.directVirtualCount_positive hZero) κ hκ hCap K d hdPos
    (B.directVirtualOfferLaw_threshold_tendsto hZero d hd) measureReal_nonneg hTail
    (B.directVirtualOfferLaw_square_sum_tendsto hZero d hdPos.le) hw hc i f
  constructor
  · exact h.1.congr (fun m => congrArg (fun P => (directCoarsePolicy m (B.directVirtualCount hZero m)
      ((B.truncation K d hd).valueThresholdPolicy hw.le hc.le) d).expectedRewardScore P
      (directIndividualScore (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i.val f))
      (B.directFiniteApproximation_eq_appendVirtual hZero m).symm)
  · exact h.2.congr (fun m => congrArg (fun P => (directCoarsePolicy m (B.directVirtualCount hZero m)
      ((B.truncation K d hd).valueThresholdPolicy hw.le hc.le) d).expectedDurationScore P
      (directIndividualScore (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i.val f))
      (B.directFiniteApproximation_eq_appendVirtual hZero m).symm)
end ProphetSecretary.Limiting.CountableInstance
