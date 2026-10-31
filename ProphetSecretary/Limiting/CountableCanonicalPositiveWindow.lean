import ProphetSecretary.Limiting.CountablePositiveWindowDuration
import ProphetSecretary.Limiting.CountableValuePolicy

/-!
# Actual canonical duration responses on positive mark windows

The complete centered count is the actual `bandScore` used in the likelihood
path. Original-law admissibility replaces the analytical infimum by actual
duration. A zero score makes insertion ineffective in the window, in every
construction band, with no counterfactual admissibility assumption.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance

lemma poissonRegionScore_eq_bandScore (B : CountableInstance) (S : Set ℝ)
    (v : CompleteWorld Unit) :
    (bandPointCount (univ ×ˢ S) v.1 : ℝ)-(Model.Instance.uniformClock.prod B.intensity).real (univ ×ˢ S)=
      B.bandScore S v := by
  rw [B.bandScore_eq]
  simp only [completeBandCount,measureReal_prod_prod,probReal_univ,one_mul]

theorem valueRule_positiveWindow_durationScore_nonpositive (B : CountableInstance) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S ⊆ Ioi b) :
    Integrable (fun v : CompleteWorld Unit => (B.valueRule w c).realizedDuration v*B.bandScore S v)
        (B.completeWorldLaw (Measure.dirac ())) ∧
      (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore S v
        ∂B.completeWorldLaw (Measure.dirac ())) ≤ 0 := by
  let accept := B.valueMarkovAcceptance w c
  have hMeas : (countableMarkovRule accept).IsMeasurable := by
    rw [← B.valueRule_eq_markovAcceptance]
    exact B.valueRule_isMeasurable hw.le hc.le
  have hPointSub : (univ : Set ℝ) ×ˢ S ⊆ (univ : Set ℝ) ×ˢ Ioi b := fun p hp => ⟨hp.1,hSub hp.2⟩
  have hInf := countableMarkovRule_poissonRegion_durationScore_nonpositive accept hMeas B (Measure.dirac ())
    hb (MeasurableSet.univ.prod hS) hPointSub
  rw [← B.valueRule_eq_markovAcceptance] at hInf
  have hDuration := (B.valueRule w c).infimumDuration_eq_actual B (Measure.dirac ()) (B.valueRule_admissible hw hc)
  have hAE : (fun v : CompleteWorld Unit => (B.valueRule w c).infimumDuration v*
      ((bandPointCount (univ ×ˢ S) v.1 : ℝ)-(Model.Instance.uniformClock.prod B.intensity).real (univ ×ˢ S)))
      =ᵐ[B.completeWorldLaw (Measure.dirac ())]
      (fun v => (B.valueRule w c).realizedDuration v*B.bandScore S v) := by
    filter_upwards [hDuration] with v hv
    rw [hv,B.poissonRegionScore_eq_bandScore S v]
  exact ⟨hInf.1.congr hAE,(integral_congr_ae hAE).symm.trans_le hInf.2⟩

theorem valueRule_positiveWindow_insertion_eq_actual_of_durationScore_zero
    (B : CountableInstance) {w c : ℝ} (hw : 0 < w) (hc : 0 < c)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S ⊆ Ioi b)
    (hZero : (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore S v
      ∂B.completeWorldLaw (Measure.dirac ()))=0) (k : ℕ) :
    ∀ᵐ z : Point × CompleteWorld Unit
      ∂(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw (Measure.dirac ())),
      z.1.2 ∈ S → (B.valueRule w c).insertionInfimumKernel k z=(B.valueRule w c).realizedDuration z.2 := by
  let accept := B.valueMarkovAcceptance w c
  have hMeas : (countableMarkovRule accept).IsMeasurable := by
    rw [← B.valueRule_eq_markovAcceptance]
    exact B.valueRule_isMeasurable hw.le hc.le
  have hPointSub : (univ : Set ℝ) ×ˢ S ⊆ (univ : Set ℝ) ×ˢ Ioi b := fun p hp => ⟨hp.1,hSub hp.2⟩
  have hDuration := (B.valueRule w c).infimumDuration_eq_actual B (Measure.dirac ()) (B.valueRule_admissible hw hc)
  have hInfZero : (∫ v : CompleteWorld Unit, (B.valueRule w c).infimumDuration v*
      ((bandPointCount (univ ×ˢ S) v.1 : ℝ)-(Model.Instance.uniformClock.prod B.intensity).real (univ ×ˢ S))
      ∂B.completeWorldLaw (Measure.dirac ()))=0 := by
    refine (integral_congr_ae ?_).trans hZero
    filter_upwards [hDuration] with v hv
    rw [hv,B.poissonRegionScore_eq_bandScore S v]
  rw [B.valueRule_eq_markovAcceptance] at hInfZero
  have hInserted := countableMarkovRule_poissonRegion_insertion_eq_of_durationScore_zero accept hMeas B (Measure.dirac ())
    hb (MeasurableSet.univ.prod hS) hPointSub hInfZero k
  rw [← B.valueRule_eq_markovAcceptance] at hInserted
  have hBase := (Measure.quasiMeasurePreserving_snd
    (μ := ProphetSecretary.Limiting.intensity (B.bandIntensity k))
    (ν := B.completeWorldLaw (Measure.dirac ()))).ae hDuration
  filter_upwards [hInserted,hBase] with z hz hBaseZ hPoint
  exact (hz ⟨trivial,hPoint⟩).trans hBaseZ

end ProphetSecretary.Limiting.CountableInstance
