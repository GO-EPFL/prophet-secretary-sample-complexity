import ProphetSecretary.Limiting.CountableFiniteBandScore
import ProphetSecretary.Limiting.CountableCanonicalPositiveWindow
import ProphetSecretary.Limiting.CountableCommonContinuityCutoffs

/-!
# Enlarging a nonzero positive-window response to an upper continuity band

Complete centered counts add over disjoint regions. Canonical duration
responses are nonpositive, so enlarging a positive window can only decrease
its response. A common continuity cutoff below the original window gives
the upper band required in `lem:nonzero` and `updual:scorelift`.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal
namespace ProphetSecretary.Limiting.CountableInstance

lemma bandScore_eq_add_sdiff_ae (B : CountableInstance) {S T : Set ℝ}
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hSub : S⊆T) (hFinite : B.intensity T<⊤)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ v ∂B.completeWorldLaw ν, B.bandScore T v=B.bandScore S v+B.bandScore (T\S) v := by
  have hFS : B.intensity S<⊤ := (measure_mono hSub).trans_lt hFinite
  have hFD : B.intensity (T\S)<⊤ := (measure_mono sdiff_subset).trans_lt hFinite
  have hMP : MeasurePreserving (Prod.fst : CompleteWorld Seed → BandConfigurations)
      (B.completeWorldLaw ν) B.bandConfigurationsLaw := measurePreserving_fst
  have hCount (U : Set ℝ) (hU : MeasurableSet U) (hF : B.intensity U<⊤) :
      ∀ᵐ v ∂B.completeWorldLaw ν,
        bandCountingMeasure v.1 (univ ×ˢ U)=(completeBandCount U v : ℝ≥0∞) :=
    hMP.quasiMeasurePreserving.ae ((B.finite_region_count_and_prefix_ae
      (MeasurableSet.univ.prod hU) (B.fullTime_region_finite hF)).mono (fun _ h => h.1))
  have hRate := measureReal_add_sdiff (μ:=B.intensity) hS hFS.ne hFinite.ne
  rw [union_eq_right.mpr hSub] at hRate
  filter_upwards [hCount S hS hFS,hCount T hT hFinite,hCount (T\S) (hT.diff hS) hFD]
    with v hCS hCT hCD
  have hDiff : (univ ×ˢ T)\(univ ×ˢ S)=(univ : Set ℝ) ×ˢ (T\S) := by ext p;simp
  have hRegionSub : (univ : Set ℝ) ×ˢ S⊆univ ×ˢ T := fun p hp => ⟨hp.1,hSub hp.2⟩
  have hMass := measureReal_add_sdiff (μ:=bandCountingMeasure v.1) (MeasurableSet.univ.prod hS)
    (by rw [hCS];simp) (by rw [hCT];simp)
  rw [union_eq_right.mpr hRegionSub,hDiff] at hMass
  simp only [Measure.real,hCS,hCT,hCD,ENNReal.toReal_natCast] at hMass
  rw [B.bandScore_eq,B.bandScore_eq,B.bandScore_eq]
  linarith only [hMass,hRate]

lemma bandScore_zero_ae_of_measure_zero (B : CountableInstance) {S : Set ℝ}
    (hS : MeasurableSet S) (hZero : B.intensity S=0)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ v ∂B.completeWorldLaw ν, B.bandScore S v=0 := by
  have hFinite : B.intensity S<⊤ := by rw [hZero];simp
  have hMP := B.completeBandCount_measurePreserving_of_finite hS hFinite ν
  simp only [bandRate,hZero,ENNReal.toNNReal_zero,ProphetSecretary.Probability.poissonMeasure_zero_eq_dirac] at hMP
  have hDirac : ∀ᵐ k ∂(Measure.dirac (0 : ℕ)), k=0 := by simp
  filter_upwards [hMP.quasiMeasurePreserving.ae hDirac] with v hv
  rw [B.bandScore_eq,hv,Measure.real,hZero,ENNReal.toReal_zero,Nat.cast_zero,sub_self]

lemma bandScore_upper_eq_capped_ae (B : CountableInstance) {b : ℝ}
    (hb : (B.terminal : ℝ)<b) {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ v ∂B.completeWorldLaw ν, B.bandScore (Ioi b) v=B.bandScore (Ioc b (B.cap : ℝ)) v := by
  have hSub : Ioc b (B.cap : ℝ)⊆Ioi b := fun _ hx => hx.1
  have hZero : B.intensity (Ioi b\Ioc b (B.cap : ℝ))=0 := by
    have hSubset : Ioi b\Ioc b (B.cap : ℝ)⊆(Ioc (B.terminal : ℝ) (B.cap : ℝ))ᶜ := by
      intro x hx hSupport
      exact hx.2 ⟨hx.1,hSupport.2⟩
    exact measure_mono_null hSubset (ae_iff.mp B.intensity_supported)

  filter_upwards [B.bandScore_eq_add_sdiff_ae measurableSet_Ioc measurableSet_Ioi hSub
    (B.intensity_tail_finite b hb) ν,
    B.bandScore_zero_ae_of_measure_zero (measurableSet_Ioi.diff measurableSet_Ioc) hZero ν] with v hAdd h0
  simpa only [h0,add_zero] using hAdd

lemma valueRule_durationScore_antitone_window (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hST : S⊆T) {b : ℝ} (hb : (B.terminal : ℝ)<b) (hTb : T⊆Ioi b) :
    (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore T v
      ∂B.completeWorldLaw (Measure.dirac ()))≤
    ∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore S v
      ∂B.completeWorldLaw (Measure.dirac ()) := by
  have hIS := B.valueRule_positiveWindow_durationScore_nonpositive hw hc hS hb (hST.trans hTb)
  have hID := B.valueRule_positiveWindow_durationScore_nonpositive hw hc (hT.diff hS) hb (sdiff_subset.trans hTb)
  have hScores := B.bandScore_eq_add_sdiff_ae hS hT hST
    ((measure_mono hTb).trans_lt (B.intensity_tail_finite b hb)) (Measure.dirac ())
  have hMean : (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore T v
      ∂B.completeWorldLaw (Measure.dirac ()))=
      (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore S v
        ∂B.completeWorldLaw (Measure.dirac ()))+
      ∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore (T\S) v
        ∂B.completeWorldLaw (Measure.dirac ()) := by
    calc
      _ = ∫ v : CompleteWorld Unit,
          ((B.valueRule w c).realizedDuration v*B.bandScore S v+
            (B.valueRule w c).realizedDuration v*B.bandScore (T\S) v)
          ∂B.completeWorldLaw (Measure.dirac ()) :=
        integral_congr_ae (hScores.mono (fun v hv => by rw [hv,mul_add]))
      _ = _ := integral_add hIS.1 hID.1
  linarith only [hMean,hID.2]

/-- Any nonzero positive-window duration response has a negative upper-band
response at a positive intensity-continuity level. Both presentations agree. -/
theorem exists_upperContinuityBand_durationScore_negative (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b)
    (hNonzero : (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore S v
      ∂B.completeWorldLaw (Measure.dirac ()))≠0) :
    ∃ d : ℝ, 0<d ∧ (B.terminal : ℝ)<d ∧ B.intensity {d}=0 ∧ (∀ i, (B.individuals i : Measure ℝ) {d}=0) ∧
      (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore (Ioi d) v
        ∂B.completeWorldLaw (Measure.dirac ()))<0 ∧
      (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore (Ioc d (B.cap : ℝ)) v
        ∂B.completeWorldLaw (Measure.dirac ()))<0 := by
  have hNegative := lt_of_le_of_ne (B.valueRule_positiveWindow_durationScore_nonpositive hw hc hS hb hSub).2 hNonzero
  obtain ⟨ds,_hAnti,hDs,hLimit,hContinuity⟩ := B.exists_common_continuity_cutoffs
  obtain ⟨j,hj⟩ := (hLimit.eventually (gt_mem_nhds hb)).exists
  have hSD : S⊆Ioi (ds j) := fun x hx => hj.trans (hSub hx)
  have hLarger := B.valueRule_durationScore_antitone_window hw hc hS measurableSet_Ioi hSD (hDs j).1 (fun _ hx => hx)
  have hUpper := hLarger.trans_lt hNegative
  have hEq : (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore (Ioi (ds j)) v
      ∂B.completeWorldLaw (Measure.dirac ()))=
      ∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore (Ioc (ds j) (B.cap : ℝ)) v
        ∂B.completeWorldLaw (Measure.dirac ()) :=
    integral_congr_ae ((B.bandScore_upper_eq_capped_ae (hDs j).1 (Measure.dirac ())).mono
      (fun v hv => congrArg ((B.valueRule w c).realizedDuration v*·) hv))
  exact ⟨ds j,B.terminal.coe_nonneg.trans_lt (hDs j).1,(hDs j).1,(hContinuity j).1,(hContinuity j).2,hUpper,hEq ▸ hUpper⟩

end ProphetSecretary.Limiting.CountableInstance
