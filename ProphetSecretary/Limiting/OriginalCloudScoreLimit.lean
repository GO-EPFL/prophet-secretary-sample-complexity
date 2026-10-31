import ProphetSecretary.Limiting.OriginalCoarseCloudScore
import ProphetSecretary.Limiting.OriginalCoarseRegret
import ProphetSecretary.Limiting.TruncatedScoreLimits
import ProphetSecretary.Limiting.FiniteCanonicalScoreLimit
import ProphetSecretary.Model.FirstMomentTailCount
import ProphetSecretary.Limiting.OrderedCloudScoreDiagonal

/-!
# Upper-band cloud score limits for original finite canonical policies

The original score compensates on the full complement of the band. One slow
residual schedule gives globally bounded components on every finite index,
with information at most 2S₀/b independently of the number of distributions.
The finite-array limit precedes the refinement limit.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
open CountableInstance ProphetSecretary.Probability

theorem OrderedBandConvergence.original_upperBand_score_limits
    {sizes : ℕ → ℕ} {P : ∀ m, Model.Instance (sizes m)} {wgt : ℝ →ᵇ ℝ} {B : CountableInstance}
    (h : OrderedBandConvergence sizes P wgt B) (hZero : B.terminal=0)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap:ℝ))
    {S0 δ lam : ℝ} (hS0 : 0≤S0) (hS : ∀ m, (P m).totalFirstMoment≤S0)
    (hδ : 0<δ) (hlam : lam∈Ioo (0:ℝ) 1) (lams : ℕ → ℝ)
    (hRange : ∀ m, lams m∈Icc δ (1-δ)) (hLam : Tendsto lams atTop (𝓝 lam))
    (hV : Tendsto (fun m => Model.optimalScalarValue (P m) (lams m) (1-lams m)) atTop
      (𝓝 (B.optimalScalarValue lam (1-lam)))) (b : ℝ) (hb : 0<b) (hAtom : B.intensity {b}=0) :
    ∃ Ns : ℕ → ℕ, Tendsto Ns atTop atTop ∧
      (∀ m, (∀ j, Measurable (weightedResidualScore (P m) wgt (Ns m) (Ioi b) j)) ∧
        (∀ j x, |weightedResidualScore (P m) wgt (Ns m) (Ioi b) j x|≤1) ∧
        (∀ j, (∫ x, weightedResidualScore (P m) wgt (Ns m) (Ioi b) j x ∂(P m).law j)=0) ∧
        information (P m).law (weightedResidualScore (P m) wgt (Ns m) (Ioi b))≤2*S0/b) ∧
      let ρ := fun m => (P m).valuePolicy ((P m).integrable_maximum_of_bounded (hCap m))
        (hδ.le.trans (hRange m).1) (show 0≤1-lams m from by linarith only [(hRange m).2,hδ.le])
      Tendsto (fun m => (ρ m).expectedRewardScore (P m) (weightedResidualScore (P m) wgt (Ns m) (Ioi b))) atTop
        (𝓝 (∫ v, B.bandScore (Ioi b) v*(B.valueRule lam (1-lam)).realizedReward 0 v
          ∂B.completeWorldLaw (Measure.dirac ()))) ∧
      Tendsto (fun m => (ρ m).expectedDurationScore (P m) (weightedResidualScore (P m) wgt (Ns m) (Ioi b))) atTop
        (𝓝 (∫ v, B.bandScore (Ioi b) v*(B.valueRule lam (1-lam)).realizedDuration v
          ∂B.completeWorldLaw (Measure.dirac ()))) := by
  have hw : 0<lam := hlam.1
  have hc : 0<1-lam := sub_pos.mpr hlam.2
  obtain ⟨ds,_hAnti,hdsBounds,hdsLim,hdsAtoms⟩ := B.exists_common_continuity_cutoffs
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (hdsLim.eventually (Iio_mem_nhds (by simpa only [hZero,NNReal.coe_zero] using hb)))
  let bs := fun j : ℕ => ds (j+J)
  have hbs (j) : (B.terminal:ℝ)<bs j := (hdsBounds _).1
  have hbsPos (j) : 0<bs j := by simpa only [hZero,NNReal.coe_zero] using hbs j
  have hBelow (j) : bs j≤b := (hJ (j+J) (Nat.le_add_left J j)).le
  have hbsLim : Tendsto bs atTop (𝓝 (B.terminal:ℝ)) := hdsLim.comp (tendsto_add_atTop_nat J)
  have hAtoms (j) : B.intensity {bs j}=0 := (hdsAtoms _).1
  have hbAbove : (B.terminal:ℝ)<b := by simpa only [hZero,NNReal.coe_zero] using hb
  obtain ⟨Ns,hNs,hWeak,hSup,hHalf⟩ := h.exists_cloud_score_diagonal b hbAbove
  let Ks := fun j : ℕ => j
  have hKs : Tendsto Ks atTop atTop := tendsto_id
  let D := fun j => B.truncation (Ks j) (bs j) (hbs j)
  let γ := fun j m => originalCoarsePolicy (P m) wgt (Ns m) ((D j).valueThresholdPolicy hw.le hc.le) (bs j)
  let bR := fun j => ∫ v : HybridWorld (Ks j) Unit,
    ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-B.intensity.real (Ioi b))*
      ((D j).valueRule lam (1-lam)).realizedReward 0 v ∂(D j).law (Measure.dirac ())
  let bT := fun j => ∫ v : HybridWorld (Ks j) Unit,
    ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-B.intensity.real (Ioi b))*
      ((D j).valueRule lam (1-lam)).realizedDuration v ∂(D j).law (Measure.dirac ())
  let r := fun j => B.optimalScalarValue lam (1-lam)-(D j).optimalScalarValue lam (1-lam)
  have hCoarse (j) := h.original_coarse_cloud_score_tendsto hZero hCap Ns hNs (Ks j) (bs j) b
    (hbsPos j) (hBelow j) (hAtoms j) hAtom (hWeak (bs j) (hbs j) (hAtoms j)) hHalf hw hc
  have hCoarseR (j) : Tendsto (fun m => (γ j m).expectedRewardScore (P m)
      (weightedResidualScore (P m) wgt (Ns m) (Ioi b))) atTop (𝓝 (bR j)) := by
    have hR := (hCoarse j).1
    have hCenter : ((B.truncation (Ks j) (bs j) (hbs j)).intensity:Measure ℝ).real (Ioi b)=B.intensity.real (Ioi b) :=
      B.intensityAbove_real_upper (hbs j) b (hBelow j)
    simpa only [hCenter] using hR
  have hCoarseT (j) : Tendsto (fun m => (γ j m).expectedDurationScore (P m)
      (weightedResidualScore (P m) wgt (Ns m) (Ioi b))) atTop (𝓝 (bT j)) := by
    have hT := (hCoarse j).2
    have hCenter : ((B.truncation (Ks j) (bs j) (hbs j)).intensity:Measure ℝ).real (Ioi b)=B.intensity.real (Ioi b) :=
      B.intensityAbove_real_upper (hbs j) b (hBelow j)
    simpa only [hCenter] using hT
  have hTarget := B.hybridTruncation_band_score_tendsto hZero hw hc Ks bs hbs hKs hbsLim b hbAbove hBelow
  have hRegret (j) := h.original_coarse_regret_tendsto hZero hCap Ns hNs (Ks j) (bs j) (hbsPos j)
    (hAtoms j) (hWeak (bs j) (hbs j) (hAtoms j)) hw hc lams (fun m => 1-lams m)
    hLam (tendsto_const_nhds.sub hLam) hV
  have hRefine : Tendsto r atTop (𝓝 (0:ℝ)) := by
    have hConst : Tendsto (fun _ : ℕ => B.optimalScalarValue lam (1-lam)) atTop
        (𝓝 (B.optimalScalarValue lam (1-lam))) := tendsto_const_nhds
    simpa only [r,D,sub_self] using
      (hConst.sub (B.truncation_value_tendsto Ks bs hbs hKs hbsLim hw.le hc.le))
  have hTail (m d) (hd : 0<d) : (P m).tailCount d≤S0/d :=
    ((P m).tailCount_le_totalFirstMoment_div ((P m).integrable_maximum_of_bounded (hCap m)) hd).trans
      (div_le_div_of_nonneg_right (hS m) hd.le)
  have hActiveHalf (m) := weightedResidualScore_half_of_sup (P m) wgt (Ns m) (Subset.refl (Ioi b)) (hSup m)
  have hBoundMean (m) := weightedResidualScore_centered_bounded (P m) wgt (Ns m) measurableSet_Ioi (hActiveHalf m)
  have hInfo (m) := weightedResidualScore_information_le_firstMoment (P m)
    ((P m).integrable_maximum_of_bounded (hCap m)) wgt (Ns m) measurableSet_Ioi hb
    (Subset.refl (Ioi b)) (hS m) (hActiveHalf m)
  refine ⟨Ns,hNs,(fun m => ⟨measurable_weightedResidualScore (P m) wgt (Ns m) measurableSet_Ioi,
    (hBoundMean m).1,(hBoundMean m).2,hInfo m⟩),?_⟩
  exact finiteCanonical_score_tendsto_of_coarse sizes P B.cap.property hδ (by positivity : 0≤2*S0/b) hCap
    (fun d => S0/d) (fun _ hd => div_nonneg hS0 hd.le) hTail lams (fun m => 1-lams m)
    (fun m => (hRange m).1) (fun m => by linarith only [(hRange m).2]) (fun _ => by ring)
    (fun m => weightedResidualScore (P m) wgt (Ns m) (Ioi b))
    (fun m => measurable_weightedResidualScore (P m) wgt (Ns m) measurableSet_Ioi)
    (fun m j => Filter.Eventually.of_forall ((hBoundMean m).1 j))
    (fun m => (hBoundMean m).2) hInfo γ bR bT r _ _ hCoarseR hCoarseT
    hTarget.1 hTarget.2 hRegret hRefine
end ProphetSecretary.Limiting
