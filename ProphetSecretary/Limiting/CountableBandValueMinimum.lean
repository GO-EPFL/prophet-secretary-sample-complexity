import ProphetSecretary.Limiting.CountableFirstBandDeletionValue
import ProphetSecretary.Limiting.CountableBandEnvelope

/-!
# Zero-response deletion makes the scalar likelihood path stationary

Band intensity is ordered by its nonnegative scaling factor. Once deletion
preserves scalar value, every nonnegative scaling factor has value at least
the base value. The genuine optimized likelihood path thus has a local
minimum at zero. Its proved envelope derivative is zero by Fermat's theorem,
separately from the prophet derivative used in critical stationarity.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance

theorem scaleBand_value_mono (B : CountableInstance) (S : Set ℝ) {r s : ℝ≥0}
    (hrs : r≤s) {w c : ℝ} (hw : 0≤w) (hc : 0≤c) :
    (B.scaleBand S r).optimalScalarValue w c ≤ (B.scaleBand S s).optimalScalarValue w c := by
  have hIntensity : (B.scaleBand S r).intensity≤(B.scaleBand S s).intensity := by
    apply withDensity_mono
    apply Eventually.of_forall
    intro x
    apply ENNReal.ofReal_le_ofReal
    by_cases hx : x ∈ S
    · simpa only [bandScaleFactor,if_pos hx] using (show (r : ℝ)≤s by exact_mod_cast hrs)
    · simp only [bandScaleFactor,if_neg hx,le_refl]
  exact (B.scaleBand S r).optimalScalarValue_mono_intensity (B.scaleBand S s) rfl rfl rfl hIntensity hw hc

theorem bandLikelihood_value_isLocalMin_of_zeroBandValue (B : CountableInstance) (S : Set ℝ)
    {w c : ℝ} (hw : 0≤w) (hc : 0≤c)
    (hDeletion : (B.scaleBand S 0).optimalScalarValue w c=B.optimalScalarValue w c) :
    IsLocalMin (fun θ => (B.bandLikelihoodPath S θ).optimalScalarValue w c) 0 := by
  change ∀ᶠ θ in 𝓝 (0 : ℝ), (B.bandLikelihoodPath S 0).optimalScalarValue w c≤
    (B.bandLikelihoodPath S θ).optimalScalarValue w c
  rw [B.bandLikelihoodPath_zero]
  apply Eventually.of_forall
  intro θ
  by_cases hθ : |θ|≤1/4
  · rw [B.bandLikelihoodPath_of_mem S hθ,← hDeletion]
    exact B.scaleBand_value_mono S bot_le hw hc
  · simp only [bandLikelihoodPath,dif_neg hθ,le_refl]

theorem scalarBandLikelihoodDerivative_firstBandWindow_eq_zero_of_zero_durationScore
    (B : CountableInstance) (hTerminal : B.terminal=0) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (N : ℕ)
    (hZero : (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore (B.firstBandWindow N) v
      ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    (B.valuePolicy hw hc).scalarBandLikelihoodDerivative (B.firstBandWindow N) w c=0 := by
  have hValue := B.deleteFirstBands_value_eq_of_zero_durationScore hTerminal hw hc N hZero
  have hMin := B.bandLikelihood_value_isLocalMin_of_zeroBandValue (B.firstBandWindow N) hw.le hc.le hValue
  have hSub : B.firstBandWindow N ⊆ Ioi (B.markCutoff N) := by rw [B.firstBandWindow_eq_tail]
  exact hMin.hasDerivAt_eq_zero (B.hasDerivAt_optimalScalarValue_bandLikelihoodPath hTerminal hw hc
    (B.measurableSet_firstBandWindow N) (B.terminal_lt_markCutoff N) hSub)

theorem hasDerivAt_value_firstBandWindow_zero_of_zero_durationScore
    (B : CountableInstance) (hTerminal : B.terminal=0) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (N : ℕ)
    (hZero : (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore (B.firstBandWindow N) v
      ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    HasDerivAt (fun θ => (B.bandLikelihoodPath (B.firstBandWindow N) θ).optimalScalarValue w c) 0 0 := by
  have hSub : B.firstBandWindow N ⊆ Ioi (B.markCutoff N) := by rw [B.firstBandWindow_eq_tail]
  have h := B.hasDerivAt_optimalScalarValue_bandLikelihoodPath hTerminal hw hc
    (B.measurableSet_firstBandWindow N) (B.terminal_lt_markCutoff N) hSub
  rwa [B.scalarBandLikelihoodDerivative_firstBandWindow_eq_zero_of_zero_durationScore hTerminal hw hc N hZero] at h

end ProphetSecretary.Limiting.CountableInstance
