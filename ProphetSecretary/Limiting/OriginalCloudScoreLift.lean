import ProphetSecretary.Limiting.OriginalCloudScoreLimit
import ProphetSecretary.Limiting.MaskedCanonicalScoreLimit
import ProphetSecretary.Analysis.EventualInteriorWeights
import ProphetSecretary.Limiting.CountableUpperBandResponse

/-!
# The Poisson upper-band score lift on the original finite sequence

This is the cloud case of `updual:scorelift`, including arbitrary initial
endpoint weights. Scores vanish at the exceptional indices where compact
interior replacement weights differ. The resulting actual likelihood laws
therefore have zero curvature at those indices; uniform regularity on the
remaining indices is supplied by `finite_score_likelihood_regularity_of_exceptional_weights`.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
open CountableInstance ProphetSecretary.Probability

theorem OrderedBandConvergence.original_upperBand_score_lift
    {sizes : ℕ → ℕ} {P : ∀ m, Model.Instance (sizes m)} {wgt : ℝ →ᵇ ℝ} {B : CountableInstance}
    (h : OrderedBandConvergence sizes P wgt B) (hZero : B.terminal=0)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap:ℝ))
    {S0 lam : ℝ} (hS0 : 0≤S0) (hS : ∀ m, (P m).totalFirstMoment≤S0)
    (hlam : lam∈Ioo (0:ℝ) 1) (lams : ℕ → ℝ) (hRange : ∀ m, lams m∈Icc (0:ℝ) 1)
    (hLam : Tendsto lams atTop (𝓝 lam))
    (hV : Tendsto (fun m => Model.optimalScalarValue (P m) (lams m) (1-lams m)) atTop
      (𝓝 (B.optimalScalarValue lam (1-lam)))) (b : ℝ) (hb : 0<b) (hAtom : B.intensity {b}=0) :
    ∃ (δ : ℝ) (ls : ℕ → ℝ) (score : ∀ m, Fin (sizes m) → ℝ → ℝ),
      0<δ ∧ (∀ m, ls m∈Icc δ (1-δ)) ∧ ls=ᶠ[atTop] lams ∧
      (∀ m, ls m≠lams m → ∀ j x, score m j x=0) ∧
      (∀ m, (∀ j, Measurable (score m j)) ∧ (∀ j x, |score m j x|≤1) ∧
        (∀ j, (∫ x, score m j x ∂(P m).law j)=0) ∧ information (P m).law (score m)≤2*S0/b) ∧
      let ρ := fun m => (P m).unitCanonicalPolicy ((P m).integrable_maximum_of_bounded (hCap m))
        (lams m) (hRange m)
      Tendsto (fun m => (ρ m).expectedRewardScore (P m) (score m)) atTop
        (𝓝 (∫ v, B.bandScore (Ioc b (B.cap:ℝ)) v*
          (B.valueRule lam (1-lam)).realizedReward 0 v ∂B.completeWorldLaw (Measure.dirac ()))) ∧
      Tendsto (fun m => (ρ m).expectedDurationScore (P m) (score m)) atTop
        (𝓝 (∫ v, B.bandScore (Ioc b (B.cap:ℝ)) v*
          (B.valueRule lam (1-lam)).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))) := by
  obtain ⟨δ,hδ,ls,hLs,hEq,hLim⟩ := ProphetSecretary.Analysis.exists_compact_interior_weight_sequence hlam lams hLam
  have hV' : Tendsto (fun m => Model.optimalScalarValue (P m) (ls m) (1-ls m)) atTop
      (𝓝 (B.optimalScalarValue lam (1-lam))) := by
    apply hV.congr'
    exact hEq.mono (fun m hm => congrArg (fun a => Model.optimalScalarValue (P m) a (1-a)) hm.symm)
  obtain ⟨Ns,_hNs,hProps,hCore⟩ := h.original_upperBand_score_limits hZero hCap hS0 hS hδ hlam ls hLs hLim hV' b hb hAtom
  let s := fun m => weightedResidualScore (P m) wgt (Ns m) (Ioi b)
  let score := maskedArrayScore (fun m => ls m=lams m) s
  have hMasked := maskedArrayScore_properties sizes P (fun m => ls m=lams m) s (by positivity : 0≤2*S0/b)
    (fun m => (hProps m).1) (fun m => (hProps m).2.1)
    (fun m => (hProps m).2.2.1) (fun m => (hProps m).2.2.2)
  refine ⟨δ,ls,score,hδ,hLs,hEq,?_,hMasked,?_⟩
  · intro m hm j x
    exact if_neg hm
  · have hCov := masked_finiteCanonical_score_limits sizes P hδ hCap ls lams hLs hRange hEq s hCore
    have hAbove : (B.terminal:ℝ)<b := by simpa only [hZero,NNReal.coe_zero] using hb
    have hScore := B.bandScore_upper_eq_capped_ae hAbove (Measure.dirac ())
    have hTR : (∫ v, B.bandScore (Ioi b) v*(B.valueRule lam (1-lam)).realizedReward 0 v
        ∂B.completeWorldLaw (Measure.dirac ()))=
        ∫ v, B.bandScore (Ioc b (B.cap:ℝ)) v*(B.valueRule lam (1-lam)).realizedReward 0 v
          ∂B.completeWorldLaw (Measure.dirac ()) :=
      integral_congr_ae (hScore.mono (fun v hv => congrArg (fun z => z*(B.valueRule lam (1-lam)).realizedReward 0 v) hv))
    have hTT : (∫ v, B.bandScore (Ioi b) v*(B.valueRule lam (1-lam)).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))=
        ∫ v, B.bandScore (Ioc b (B.cap:ℝ)) v*(B.valueRule lam (1-lam)).realizedDuration v
          ∂B.completeWorldLaw (Measure.dirac ()) :=
      integral_congr_ae (hScore.mono (fun v hv => congrArg (fun z => z*(B.valueRule lam (1-lam)).realizedDuration v) hv))
    exact ⟨hTR ▸ hCov.1,hTT ▸ hCov.2⟩
end ProphetSecretary.Limiting
