import ProphetSecretary.Limiting.DirectCoarseIndividualLimit
import ProphetSecretary.Limiting.DirectCoarseRegret
import ProphetSecretary.Limiting.FiniteCanonicalScoreLimit
import ProphetSecretary.Limiting.CountableCommonContinuityCutoffs

/-!
# Actual canonical individual-score limits for direct finite approximants

A uniform positive-level tail profile replaces a total-first-moment bound.
The retained score has information at most one, with a fixed scaling of the bounded continuous observable. The finite-array limit precedes refinement of the common coarse
policy; the proved score-stability comparison then identifies the canonical
finite and countable covariance limits.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
open CountableInstance ProphetSecretary.Probability

theorem CountableInstance.direct_canonical_individual_score_limits (B : CountableInstance) (hZero : B.terminal=0)
    (ret N : ℕ → ℕ) (hRet : Tendsto ret atTop atTop) (hN : ∀ m, 0<N m)
    (κ : ℕ → Measure ℝ) [∀ m, IsProbabilityMeasure (κ m)]
    (hκ : ∀ m, ∀ᵐ x ∂κ m, 0≤x) (hCap : ∀ m, ∀ᵐ x ∂κ m, x≤(B.cap:ℝ))
    (hμWeak : ∀ d (hd : (B.terminal:ℝ)<d), Tendsto (fun m => ∑ _i : Fin (N m), thresholdMarkIntensity (κ m) d)
      atTop (𝓝 (B.intensityAbove d hd)))
    (hSquares : ∀ d, 0<d → Tendsto (fun m => (N m:ℝ)*((κ m).real (Ioi d))^2) atTop (𝓝 (0:ℝ)))
    (L : ℝ → ℝ) (hL : ∀ d, 0<d → 0≤L d)
    (hTail : ∀ m d, 0<d → ((B.individualPrefix (ret m)).appendIndependent
      (Model.iidOfferInstance (κ m) (hκ m) (N m))).tailCount d≤L d)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (hNorm : w+c=1)
    (hV : Tendsto (fun m => Model.optimalScalarValue ((B.individualPrefix (ret m)).appendIndependent
      (Model.iidOfferInstance (κ m) (hκ m) (N m))) w c) atTop (𝓝 (B.optimalScalarValue w c))) (i : ℕ) (f : ℝ →ᵇ ℝ) :
    let Q := fun m => Model.iidOfferInstance (κ m) (hκ m) (N m)
    let P := fun m => (B.individualPrefix (ret m)).appendIndependent (Q m)
    let hP := fun m => (P m).integrable_maximum_of_bounded ((B.individualPrefix (ret m)).appendIndependent_bounded (Q m)
      (fun i => (B.individual_supported i.val).mono (fun _ hx => hx.2)) (fun _ => hCap m))
    let π := fun m => (P m).valuePolicy (hP m) hw.le hc.le
    Tendsto (fun m => (π m).expectedRewardScore (P m) (directIndividualScore (B.individualPrefix (ret m)) (Q m) i f)) atTop
      (𝓝 (∫ v, centeredBoundedScore (B.individuals i:Measure ℝ) f (v.2.1 i)*(B.valueRule w c).realizedReward 0 v ∂B.completeWorldLaw (Measure.dirac ()))) ∧
    Tendsto (fun m => (π m).expectedDurationScore (P m) (directIndividualScore (B.individualPrefix (ret m)) (Q m) i f)) atTop
      (𝓝 (∫ v, centeredBoundedScore (B.individuals i:Measure ℝ) f (v.2.1 i)*(B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))) := by
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
  obtain ⟨bs,_hAnti,hbsBounds,hbsLim,_hbsAtoms⟩ := B.exists_common_continuity_cutoffs
  have hbs (j) : (B.terminal:ℝ)<bs j := (hbsBounds j).1
  have hbsPos (j) : 0<bs j := by simpa only [hZero,NNReal.coe_zero] using hbs j
  let Ks := fun j : ℕ => j+(i+1)
  have hKs : Tendsto Ks atTop atTop := tendsto_add_atTop_nat (i+1)
  have hi (j) : i<Ks j := by dsimp [Ks];omega
  let D := fun j => B.truncation (Ks j) (bs j) (hbs j)
  let γ := fun j m => directCoarsePolicy (ret m) (N m) ((D j).valueThresholdPolicy hw.le hc.le) (bs j)
  let bR := fun j => ∫ v : HybridWorld (Ks j) Unit,
    centeredBoundedScore (B.individuals i:Measure ℝ) f (v.2.1 ⟨i,hi j⟩)*
      ((D j).valueRule w c).realizedReward 0 v ∂(D j).law (Measure.dirac ())
  let bT := fun j => ∫ v : HybridWorld (Ks j) Unit,
    centeredBoundedScore (B.individuals i:Measure ℝ) f (v.2.1 ⟨i,hi j⟩)*
      ((D j).valueRule w c).realizedDuration v ∂(D j).law (Measure.dirac ())
  let r := fun j => B.optimalScalarValue w c-(D j).optimalScalarValue w c
  have hCoarse (j) := B.direct_coarse_individual_score_tendsto hZero ret N hRet hN κ hκ hCap (Ks j) (bs j)
    (hbsPos j) (hμWeak (bs j) (hbs j)) (hL (bs j) (hbsPos j))
    (fun m => hVirtualTail m (bs j) (hbsPos j)) (hSquares (bs j) (hbsPos j)) hw hc ⟨i,hi j⟩ f
  have hTarget := B.hybridTruncation_individual_score_tendsto hZero hw hc Ks bs hbs hKs hbsLim i hi f
  have hRegret (j) := B.direct_coarse_regret_tendsto hZero ret N hRet hN κ hκ hCap (Ks j) (bs j) (hbsPos j)
    (hμWeak (bs j) (hbs j)) (hL (bs j) (hbsPos j)) (fun m => hVirtualTail m (bs j) (hbsPos j))
    (hSquares (bs j) (hbsPos j)) hw hc hV
  have hRefine : Tendsto r atTop (𝓝 (0:ℝ)) := by
    have hConst : Tendsto (fun _ : ℕ => B.optimalScalarValue w c) atTop (𝓝 (B.optimalScalarValue w c)) := tendsto_const_nhds
    simpa only [r,D,sub_self] using hConst.sub (B.truncation_value_tendsto Ks bs hbs hKs hbsLim hw.le hc.le)
  let δ := min w c
  have hδ : 0<δ := lt_min hw hc
  have hProps (m) := directIndividualScore_properties (B.individualPrefix (ret m)) (Q m) i f
  exact finiteCanonical_score_tendsto_of_coarse sizes P B.cap.property hδ zero_le_one hCapP
    L hL hTail (fun _ => w) (fun _ => c) (fun _ => min_le_left w c) (fun _ => min_le_right w c) (fun _ => hNorm)
    (fun m => directIndividualScore (B.individualPrefix (ret m)) (Q m) i f) (fun m => (hProps m).1)
    (fun m i => Filter.Eventually.of_forall ((hProps m).2.1 i)) (fun m => (hProps m).2.2.1) (fun m => (hProps m).2.2.2)
    γ bR bT r _ _ (fun j => (hCoarse j).1) (fun j => (hCoarse j).2) hTarget.1 hTarget.2 hRegret hRefine
end ProphetSecretary.Limiting
