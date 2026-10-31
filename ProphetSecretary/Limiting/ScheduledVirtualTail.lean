import ProphetSecretary.Limiting.DirectVirtualOfferInstance
import ProphetSecretary.Limiting.DirectThresholdIntensity
import ProphetSecretary.Limiting.FixedCountDesignTilt
import ProphetSecretary.Limiting.TruncatedScoreLimits
import ProphetSecretary.Limiting.OrderedResidualRestriction

/-!
# Positive-band laws of the actual direct virtual schedule

The same base count gives exact finite restricted intensity. At each fixed
positive level the cutoff eventually lies below that level, so the intensity
is eventually equal to the limiting one. The explicit global squared-mass
schedule controls every positive-band square sum, without a first-moment bound.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal BigOperators
namespace ProphetSecretary.Limiting

lemma rareProbabilityLaw_threshold_sum (μ : FiniteMeasure ℝ) (N : ℕ) (hN : 0<N)
    (hm : μ.mass≤(N:ℝ≥0)) {d : ℝ} (hd : 0≤d) :
    (∑ _i : Fin N, thresholdMarkIntensity (rareProbabilityLaw μ (N:ℝ≥0) (by exact_mod_cast hN) hm:Measure ℝ) d)=
      μ.restrict (Ioi d) := by
  let p := rareParameter μ (N:ℝ≥0) (by exact_mod_cast hN) hm
  have hEach : thresholdMarkIntensity (rareProbabilityLaw μ (N:ℝ≥0) (by exact_mod_cast hN) hm:Measure ℝ) d=
      thresholdMarkIntensity (zeroInflatedLaw (normalizedMarkOrZero μ) p) d := by
    apply FiniteMeasure.toMeasure_injective
    exact congrArg (fun ν : Measure ℝ => ν.restrict (Ioi d)) (rareProbabilityLaw_eq_zeroInflated μ (N:ℝ≥0) (by exact_mod_cast hN) hm)
  calc
    _ = ∑ _i : Fin N, thresholdMarkIntensity (zeroInflatedLaw (normalizedMarkOrZero μ) p) d :=
      Finset.sum_congr rfl (fun _ _ => hEach)
    _ = _ := directPoissonMarginal_threshold_sum μ p N hN (rareParameter_coe_eq_mass_div μ N hN hm) hd

namespace CountableInstance

lemma directVirtualOfferLaw_threshold_sum (B : CountableInstance) (hZero : B.terminal=0)
    (m : ℕ) {d : ℝ} (hd : 0≤d) :
    (∑ _i : Fin (B.directVirtualCount hZero m), thresholdMarkIntensity (B.directVirtualOfferLaw hZero m:Measure ℝ) d)=
      (B.directTruncation m).intensity.restrict (Ioi d) :=
  rareProbabilityLaw_threshold_sum (B.directTruncation m).intensity (B.directVirtualCount hZero m)
    (B.directVirtualCount_positive hZero m) (B.directVirtualCount_rate_le hZero m) hd

theorem directVirtualOfferLaw_threshold_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (d : ℝ) (hd : (B.terminal:ℝ)<d) :
    Tendsto (fun m => ∑ _i : Fin (B.directVirtualCount hZero m),
      thresholdMarkIntensity (B.directVirtualOfferLaw hZero m:Measure ℝ) d) atTop (𝓝 (B.intensityAbove d hd)) := by
  have hBelow := B.markCutoff_tendsto.eventually (gt_mem_nhds hd)
  apply tendsto_const_nhds.congr'
  filter_upwards [hBelow] with m hm
  rw [B.directVirtualOfferLaw_threshold_sum hZero m (B.terminal.property.trans hd.le)]
  exact (B.intensityAbove_restrict (B.terminal_lt_markCutoff m) hd hm.le).symm

lemma directVirtualOfferLaw_upper_mass (B : CountableInstance) (hZero : B.terminal=0)
    (m : ℕ) {b : ℝ} (hb : 0≤b) :
    (B.directVirtualOfferLaw hZero m:Measure ℝ).real (Ioi b)=
      ((B.directTruncation m).intensity:Measure ℝ).real (Ioi b)/(B.directVirtualCount hZero m:ℝ) := by
  rw [directVirtualOfferLaw,rareProbabilityLaw_real_Ioi _ _ _ _ hb,NNReal.coe_natCast]
  ring

lemma directVirtualOfferLaw_upper_mass_of_cutoff_le (B : CountableInstance) (hZero : B.terminal=0)
    (m : ℕ) {b : ℝ} (hb : (B.terminal:ℝ)<b) (hm : B.markCutoff m≤b) :
    (B.directVirtualOfferLaw hZero m:Measure ℝ).real (Ioi b)=B.intensity.real (Ioi b)/(B.directVirtualCount hZero m:ℝ) := by
  rw [B.directVirtualOfferLaw_upper_mass hZero m (B.terminal.property.trans hb.le)]
  change (B.intensityAbove (B.markCutoff m) (B.terminal_lt_markCutoff m):Measure ℝ).real (Ioi b)/_=_
  rw [B.intensityAbove_real_upper (B.terminal_lt_markCutoff m) b hm]

theorem directVirtualOfferLaw_square_sum_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (d : ℝ) (hd : 0≤d) :
    Tendsto (fun m => (B.directVirtualCount hZero m:ℝ)*((B.directVirtualOfferLaw hZero m:Measure ℝ).real (Ioi d))^2)
      atTop (𝓝 (0:ℝ)) := by
  have hBound (m) : (B.directVirtualCount hZero m:ℝ)*((B.directVirtualOfferLaw hZero m:Measure ℝ).real (Ioi d))^2≤
      ((B.directTruncation m).intensity.mass:ℝ)^2/(B.directVirtualCount hZero m:ℝ) := by
    rw [B.directVirtualOfferLaw_upper_mass hZero m hd]
    have hTail : ((B.directTruncation m).intensity:Measure ℝ).real (Ioi d)≤((B.directTruncation m).intensity.mass:ℝ) :=
      measureReal_mono (subset_univ _)
    have hPow := pow_le_pow_left₀ measureReal_nonneg hTail 2
    have hN : (B.directVirtualCount hZero m:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt (B.directVirtualCount_positive hZero m))
    calc
      _ = (((B.directTruncation m).intensity:Measure ℝ).real (Ioi d))^2/(B.directVirtualCount hZero m:ℝ) := by field_simp [hN]
      _ ≤ _ := div_le_div_of_nonneg_right hPow (Nat.cast_nonneg _)
  exact squeeze_zero (fun _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hBound
    (B.directVirtualCount_square_error_tendsto hZero)
end CountableInstance
end ProphetSecretary.Limiting
