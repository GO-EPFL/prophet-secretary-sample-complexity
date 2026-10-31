import ProphetSecretary.Limiting.DirectCoarseCloudLimit
import ProphetSecretary.Limiting.DirectCoarseRegret
import ProphetSecretary.Limiting.FiniteCanonicalScoreLimit
import ProphetSecretary.Limiting.CountableCommonContinuityCutoffs

/-!
# Actual canonical cloud-score limits for direct finite approximants

A uniform positive-level tail profile replaces a total-first-moment bound.
The actual zero-atom score has information at most twice its fixed band
intensity. The finite-array limit precedes refinement of the common coarse
policy; the proved score-stability comparison then identifies the canonical
finite and countable covariance limits.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
open CountableInstance ProphetSecretary.Probability

theorem CountableInstance.direct_canonical_cloud_score_limits (B : CountableInstance) (hZero : B.terminal=0)
    (ret N : ℕ → ℕ) (hRet : Tendsto ret atTop atTop) (hN : ∀ m, 0<N m)
    (hNLim : Tendsto (fun m => (N m:ℝ)) atTop atTop)
    (κ : ℕ → Measure ℝ) [∀ m, IsProbabilityMeasure (κ m)]
    (hκ : ∀ m, ∀ᵐ x ∂κ m, 0≤x) (hCap : ∀ m, ∀ᵐ x ∂κ m, x≤(B.cap:ℝ))
    (hμWeak : ∀ d (hd : (B.terminal:ℝ)<d), Tendsto (fun m => ∑ _i : Fin (N m), thresholdMarkIntensity (κ m) d)
      atTop (𝓝 (B.intensityAbove d hd)))
    (hSquares : ∀ d, 0<d → Tendsto (fun m => (N m:ℝ)*((κ m).real (Ioi d))^2) atTop (𝓝 (0:ℝ)))
    (L : ℝ → ℝ) (hL : ∀ d, 0<d → 0≤L d)
    (hTail : ∀ m d, 0<d → ((B.individualPrefix (ret m)).appendIndependent
      (Model.iidOfferInstance (κ m) (hκ m) (N m))).tailCount d≤L d)
    (b : ℝ) (hb : 0<b) (hAtom : B.intensity {b}=0) (hq : ∀ m, (1/2:ℝ)≤(κ m).real {0})
    (hp : ∀ m, (κ m).real (Ioi b)=B.intensity.real (Ioi b)/(N m:ℝ))
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (hNorm : w+c=1)
    (hV : Tendsto (fun m => Model.optimalScalarValue ((B.individualPrefix (ret m)).appendIndependent
      (Model.iidOfferInstance (κ m) (hκ m) (N m))) w c) atTop (𝓝 (B.optimalScalarValue w c))) :
    let Q := fun m => Model.iidOfferInstance (κ m) (hκ m) (N m)
    let P := fun m => (B.individualPrefix (ret m)).appendIndependent (Q m)
    let hP := fun m => (P m).integrable_maximum_of_bounded ((B.individualPrefix (ret m)).appendIndependent_bounded (Q m)
      (fun i => (B.individual_supported i.val).mono (fun _ hx => hx.2)) (fun _ => hCap m))
    let π := fun m => (P m).valuePolicy (hP m) hw.le hc.le
    Tendsto (fun m => (π m).expectedRewardScore (P m) (directCloudScore (ret m) (N m) (κ m) (Ioi b))) atTop
      (𝓝 (∫ v, B.bandScore (Ioi b) v*(B.valueRule w c).realizedReward 0 v ∂B.completeWorldLaw (Measure.dirac ()))) ∧
    Tendsto (fun m => (π m).expectedDurationScore (P m) (directCloudScore (ret m) (N m) (κ m) (Ioi b))) atTop
      (𝓝 (∫ v, B.bandScore (Ioi b) v*(B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))) := by
  let Q := fun m => Model.iidOfferInstance (κ m) (hκ m) (N m)
  let P := fun m => (B.individualPrefix (ret m)).appendIndependent (Q m)
  let sizes := fun m => ret m+N m
  have hCapP (m) : ∀ i, ∀ᵐ x ∂(P m).law i, x≤(B.cap:ℝ) :=
    (B.individualPrefix (ret m)).appendIndependent_bounded (Q m)
      (fun i => (B.individual_supported i.val).mono (fun _ hx => hx.2)) (fun _ => hCap m)
  have hVirtualTail (m d) (hd : 0<d) : (N m:ℝ)*(κ m).real (Ioi d)≤L d := by
    have hSum : (P m).tailCount d=(B.individualPrefix (ret m)).tailCount d+(N m:ℝ)*(κ m).real (Ioi d) := by
      simp only [P,Q,Model.Instance.tailCount,Model.Instance.appendIndependent,Model.iidOfferInstance,Fin.sum_univ_add,
        Fin.addCases_left,Fin.addCases_right,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Measure.real]
    have hNonneg : 0≤(B.individualPrefix (ret m)).tailCount d := (B.individualPrefix (ret m)).tailCount_nonnegative d
    linarith only [hSum,hNonneg,hTail m d hd]
  obtain ⟨ds,_hAnti,hdsBounds,hdsLim,_hdsAtoms⟩ := B.exists_common_continuity_cutoffs
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (hdsLim.eventually (Iio_mem_nhds (by simpa only [hZero,NNReal.coe_zero] using hb)))
  let bs := fun j : ℕ => ds (j+J)
  have hbs (j) : (B.terminal:ℝ)<bs j := (hdsBounds _).1
  have hbsPos (j) : 0<bs j := by simpa only [hZero,NNReal.coe_zero] using hbs j
  have hBelow (j) : bs j≤b := (hJ (j+J) (Nat.le_add_left J j)).le
  have hbsLim : Tendsto bs atTop (𝓝 (B.terminal:ℝ)) := hdsLim.comp (tendsto_add_atTop_nat J)
  let Ks := fun j : ℕ => j
  have hKs : Tendsto Ks atTop atTop := tendsto_id
  let D := fun j => B.truncation (Ks j) (bs j) (hbs j)
  let γ := fun j m => directCoarsePolicy (ret m) (N m) ((D j).valueThresholdPolicy hw.le hc.le) (bs j)
  let bR := fun j => ∫ v : HybridWorld (Ks j) Unit,
    ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-B.intensity.real (Ioi b))*
      ((D j).valueRule w c).realizedReward 0 v ∂(D j).law (Measure.dirac ())
  let bT := fun j => ∫ v : HybridWorld (Ks j) Unit,
    ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-B.intensity.real (Ioi b))*
      ((D j).valueRule w c).realizedDuration v ∂(D j).law (Measure.dirac ())
  let r := fun j => B.optimalScalarValue w c-(D j).optimalScalarValue w c
  have hCoarse (j) := B.direct_coarse_cloud_score_tendsto hZero ret N hRet hN hNLim κ hκ hCap (Ks j) (bs j) b
    (hbsPos j) (hBelow j) hAtom (hμWeak (bs j) (hbs j)) hq hp (hSquares (bs j) (hbsPos j)) hw hc
  have hbAbove : (B.terminal:ℝ)<b := by simpa only [hZero,NNReal.coe_zero] using hb
  have hTarget := B.hybridTruncation_band_score_tendsto hZero hw hc Ks bs hbs hKs hbsLim b hbAbove hBelow
  have hRegret (j) := B.direct_coarse_regret_tendsto hZero ret N hRet hN κ hκ hCap (Ks j) (bs j) (hbsPos j)
    (hμWeak (bs j) (hbs j)) (hL (bs j) (hbsPos j)) (fun m => hVirtualTail m (bs j) (hbsPos j))
    (hSquares (bs j) (hbsPos j)) hw hc hV
  have hRefine : Tendsto r atTop (𝓝 (0:ℝ)) := by
    have hConst : Tendsto (fun _ : ℕ => B.optimalScalarValue w c) atTop (𝓝 (B.optimalScalarValue w c)) := tendsto_const_nhds
    simpa only [r,D,sub_self] using hConst.sub (B.truncation_value_tendsto Ks bs hbs hKs hbsLim hw.le hc.le)
  let δ := min w c
  have hδ : 0<δ := lt_min hw hc
  have hProps (m) := directCloudScore_properties (B.individualPrefix (ret m)) (κ m) (hκ m)
    measurableSet_Ioi (not_lt.mpr hb.le) (hq m) (hN m) (hp m)
  exact finiteCanonical_score_tendsto_of_coarse sizes P B.cap.property hδ (by positivity : 0≤2*B.intensity.real (Ioi b)) hCapP
    L hL hTail (fun _ => w) (fun _ => c) (fun _ => min_le_left w c) (fun _ => min_le_right w c) (fun _ => hNorm)
    (fun m => directCloudScore (ret m) (N m) (κ m) (Ioi b)) (fun m => (hProps m).1)
    (fun m i => Filter.Eventually.of_forall ((hProps m).2.1 i)) (fun m => (hProps m).2.2.1) (fun m => (hProps m).2.2.2)
    γ bR bT r _ _ (fun j => (hCoarse j).1) (fun j => (hCoarse j).2) hTarget.1 hTarget.2 hRegret hRefine
end ProphetSecretary.Limiting
