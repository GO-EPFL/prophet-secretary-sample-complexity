import ProphetSecretary.Limiting.CountablePoissonDurationScore
import ProphetSecretary.Limiting.CountableValuePolicy

/-!
# Actual canonical duration score in one Poisson construction band

Original-law admissibility identifies the analytical infimum with the actual
canonical duration. Thus the insertion identity applies to its fixed-policy
centered count score. A zero score forces the independently inserted-point
infimum to equal the original actual duration almost everywhere. No
admissibility on a fixed inserted-point slice is presumed.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Limiting.CountableInstance

theorem valueRule_durationScore_nonpositive (B : CountableInstance) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) (k : ℕ) :
    Integrable (fun v : CompleteWorld Unit => (B.valueRule w c).realizedDuration v*
        (((v.1 k).1 : ℝ)-(B.bandIntensity k).mass)) (B.completeWorldLaw (Measure.dirac ())) ∧
      (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*
        (((v.1 k).1 : ℝ)-(B.bandIntensity k).mass) ∂B.completeWorldLaw (Measure.dirac ())) ≤ 0 := by
  let accept := B.valueMarkovAcceptance w c
  have hMeas : (countableMarkovRule accept).IsMeasurable := by
    rw [← B.valueRule_eq_markovAcceptance]
    exact B.valueRule_isMeasurable hw.le hc.le
  have hRaw := countableMarkovRule_insertion_gain_integral accept hMeas B (Measure.dirac ()) k
  have hSign := countableMarkovRule_durationScore_nonpositive accept hMeas B (Measure.dirac ()) k
  rw [← B.valueRule_eq_markovAcceptance] at hRaw hSign
  have hDuration := (B.valueRule w c).infimumDuration_eq_actual B (Measure.dirac ()) (B.valueRule_admissible hw hc)
  have hScore : (fun v : CompleteWorld Unit => (B.valueRule w c).infimumDuration v*
      (((v.1 k).1 : ℝ)-(B.bandIntensity k).mass)) =ᵐ[B.completeWorldLaw (Measure.dirac ())]
      (fun v => (B.valueRule w c).realizedDuration v*(((v.1 k).1 : ℝ)-(B.bandIntensity k).mass)) := by
    filter_upwards [hDuration] with v hv
    rw [hv]
  exact ⟨hRaw.1.congr hScore,(integral_congr_ae hScore).symm.trans_le hSign⟩

theorem valueRule_insertionInfimum_eq_actual_of_durationScore_zero
    (B : CountableInstance) {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (k : ℕ)
    (hZero : (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*
      (((v.1 k).1 : ℝ)-(B.bandIntensity k).mass) ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    ∀ᵐ z : Point × CompleteWorld Unit
      ∂(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw (Measure.dirac ())),
      (B.valueRule w c).insertionInfimumKernel k z=(B.valueRule w c).realizedDuration z.2 := by
  let accept := B.valueMarkovAcceptance w c
  have hMeas : (countableMarkovRule accept).IsMeasurable := by
    rw [← B.valueRule_eq_markovAcceptance]
    exact B.valueRule_isMeasurable hw.le hc.le
  have hDuration := (B.valueRule w c).infimumDuration_eq_actual B (Measure.dirac ()) (B.valueRule_admissible hw hc)
  have hInfZero : (∫ v : CompleteWorld Unit, (B.valueRule w c).infimumDuration v*
      (((v.1 k).1 : ℝ)-(B.bandIntensity k).mass) ∂B.completeWorldLaw (Measure.dirac ()))=0 := by
    refine (integral_congr_ae ?_).trans hZero
    filter_upwards [hDuration] with v hv
    rw [hv]
  rw [B.valueRule_eq_markovAcceptance] at hInfZero
  have hInserted := countableMarkovRule_insertionInfimum_eq_of_durationScore_zero accept hMeas B (Measure.dirac ()) k hInfZero
  rw [← B.valueRule_eq_markovAcceptance] at hInserted
  have hBase := (Measure.quasiMeasurePreserving_snd
    (μ := ProphetSecretary.Limiting.intensity (B.bandIntensity k))
    (ν := B.completeWorldLaw (Measure.dirac ()))).ae hDuration
  filter_upwards [hInserted,hBase] with z hz hBaseZ
  exact hz.trans hBaseZ

end ProphetSecretary.Limiting.CountableInstance
