import ProphetSecretary.Limiting.OriginalCoarseIndividualScore
import ProphetSecretary.Limiting.OriginalCoarseRegret
import ProphetSecretary.Limiting.TruncatedScoreLimits
import ProphetSecretary.Limiting.FiniteCanonicalScoreLimit
import ProphetSecretary.Model.FirstMomentTailCount

/-!
# Individual score limits for the original finite canonical policies

The original score uses one statically ordered coordinate, centered under its
actual finite marginal. Its uniform information bound is one. A single slow
residual schedule is used at every coarse cutoff, with the finite-array limit
preceding the refinement limit. Scalar-value convergence is the value
convergence supplied by the same compact extraction.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
open CountableInstance ProphetSecretary.Probability

theorem OrderedBandConvergence.original_individual_score_limits
    {sizes : ℕ → ℕ} {P : ∀ m, Model.Instance (sizes m)} {wgt : ℝ →ᵇ ℝ} {B : CountableInstance}
    (h : OrderedBandConvergence sizes P wgt B) (hZero : B.terminal=0)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap:ℝ))
    {S0 δ lam : ℝ} (hS0 : 0≤S0) (hS : ∀ m, (P m).totalFirstMoment≤S0)
    (hδ : 0<δ) (hlam : lam∈Ioo (0:ℝ) 1) (lams : ℕ → ℝ)
    (hRange : ∀ m, lams m∈Icc δ (1-δ)) (hLam : Tendsto lams atTop (𝓝 lam))
    (hV : Tendsto (fun m => Model.optimalScalarValue (P m) (lams m) (1-lams m)) atTop
      (𝓝 (B.optimalScalarValue lam (1-lam)))) (i : ℕ) (f : ℝ →ᵇ ℝ) :
    let ρ := fun m => (P m).valuePolicy ((P m).integrable_maximum_of_bounded (hCap m))
      (hδ.le.trans (hRange m).1) (show 0≤1-lams m from by linarith only [(hRange m).2,hδ.le])
    Tendsto (fun m => (ρ m).expectedRewardScore (P m) (weightedIndividualScore (P m) wgt i f)) atTop
      (𝓝 (∫ v, centeredBoundedScore (B.individuals i:Measure ℝ) f (v.2.1 i)*
        (B.valueRule lam (1-lam)).realizedReward 0 v ∂B.completeWorldLaw (Measure.dirac ()))) ∧
    Tendsto (fun m => (ρ m).expectedDurationScore (P m) (weightedIndividualScore (P m) wgt i f)) atTop
      (𝓝 (∫ v, centeredBoundedScore (B.individuals i:Measure ℝ) f (v.2.1 i)*
        (B.valueRule lam (1-lam)).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))) := by
  have hw : 0<lam := hlam.1
  have hc : 0<1-lam := sub_pos.mpr hlam.2
  obtain ⟨bs,_hAnti,hbsBounds,hbsLim,hAtoms⟩ := B.exists_common_continuity_cutoffs
  have hbs (j) : (B.terminal:ℝ)<bs j := (hbsBounds j).1
  have hbsPos (j) : 0<bs j := by simpa only [hZero,NNReal.coe_zero] using hbs j
  obtain ⟨Ns,_hMono,_hLe,hNs,hWeak,_hRare⟩ := h.exists_all_continuity_residual_diagonal
  let Ks := fun j : ℕ => j+(i+1)
  have hKs : Tendsto Ks atTop atTop := tendsto_add_atTop_nat (i+1)
  have hi (j) : i<Ks j := by dsimp [Ks]; omega
  let D := fun j => B.truncation (Ks j) (bs j) (hbs j)
  let γ := fun j m => originalCoarsePolicy (P m) wgt (Ns m) ((D j).valueThresholdPolicy hw.le hc.le) (bs j)
  let bR := fun j => ∫ v : HybridWorld (Ks j) Unit,
    centeredBoundedScore (B.individuals i:Measure ℝ) f (v.2.1 ⟨i,hi j⟩)*
      ((D j).valueRule lam (1-lam)).realizedReward 0 v ∂(D j).law (Measure.dirac ())
  let bT := fun j => ∫ v : HybridWorld (Ks j) Unit,
    centeredBoundedScore (B.individuals i:Measure ℝ) f (v.2.1 ⟨i,hi j⟩)*
      ((D j).valueRule lam (1-lam)).realizedDuration v ∂(D j).law (Measure.dirac ())
  let r := fun j => B.optimalScalarValue lam (1-lam)-(D j).optimalScalarValue lam (1-lam)
  have hCoarse (j) := h.original_coarse_individual_score_tendsto hZero hCap Ns hNs (Ks j) (bs j)
    (hbsPos j) (hAtoms j).1 (hWeak (bs j) (hbs j) (hAtoms j).1) hw hc ⟨i,hi j⟩ f
  have hTarget := B.hybridTruncation_individual_score_tendsto hZero hw hc Ks bs hbs hKs hbsLim i hi f
  have hRegret (j) := h.original_coarse_regret_tendsto hZero hCap Ns hNs (Ks j) (bs j) (hbsPos j)
    (hAtoms j).1 (hWeak (bs j) (hbs j) (hAtoms j).1) hw hc lams (fun m => 1-lams m)
    hLam (tendsto_const_nhds.sub hLam) hV
  have hRefine : Tendsto r atTop (𝓝 (0:ℝ)) := by
    have hConst : Tendsto (fun _ : ℕ => B.optimalScalarValue lam (1-lam)) atTop
        (𝓝 (B.optimalScalarValue lam (1-lam))) := tendsto_const_nhds
    simpa only [r,D,sub_self] using
      (hConst.sub (B.truncation_value_tendsto Ks bs hbs hKs hbsLim hw.le hc.le))
  have hTail (m d) (hd : 0<d) : (P m).tailCount d≤S0/d :=
    ((P m).tailCount_le_totalFirstMoment_div ((P m).integrable_maximum_of_bounded (hCap m)) hd).trans
      (div_le_div_of_nonneg_right (hS m) hd.le)
  have hProps (m) := weightedIndividualScore_properties (P m) wgt i f
  exact finiteCanonical_score_tendsto_of_coarse sizes P B.cap.property hδ zero_le_one hCap
    (fun d => S0/d) (fun _ hd => div_nonneg hS0 hd.le) hTail lams (fun m => 1-lams m)
    (fun m => (hRange m).1) (fun m => by linarith only [(hRange m).2]) (fun _ => by ring)
    (fun m => weightedIndividualScore (P m) wgt i f) (fun m => (hProps m).1)
    (fun m j => Filter.Eventually.of_forall ((hProps m).2.1 j))
    (fun m => (hProps m).2.2.1) (fun m => (hProps m).2.2.2)
    γ bR bT r _ _ (fun j => (hCoarse j).1) (fun j => (hCoarse j).2)
    hTarget.1 hTarget.2 hRegret hRefine
end ProphetSecretary.Limiting
