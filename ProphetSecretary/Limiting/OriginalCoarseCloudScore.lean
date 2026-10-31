import ProphetSecretary.Limiting.OriginalCoarseOutcomes
import ProphetSecretary.Limiting.CoarseFiniteCloudOutcomes
import ProphetSecretary.Limiting.WeightedCoarseExpectedScores
import ProphetSecretary.Limiting.WeightedResidualCoarseScore

/-!
# Original-array cloud-score expectations at a fixed coarse level

The residual score is indexed by the original labels. The pointwise complete
score identity, causal simulation and actual product laws identify its reward
and duration expectations with those of the residual finite evaluation.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical NNReal
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability

theorem OrderedBandConvergence.original_coarse_cloud_score_tendsto
    {sizes : ℕ → ℕ} {P : ∀ m, Model.Instance (sizes m)} {wgt : ℝ →ᵇ ℝ} {B : CountableInstance}
    (h : OrderedBandConvergence sizes P wgt B) (hZero : B.terminal=0)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap:ℝ))
    (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop) (K : ℕ)
    (d b : ℝ) (hd : 0<d) (hdb : d≤b) (hAtomD : B.intensity {d}=0) (hAtomB : B.intensity {b}=0)
    (hWeak : Tendsto (fun m => weightOrderedBandResidual (P m) wgt (Ns m) d)
      atTop (𝓝 (B.intensityAbove d (by simpa [hZero] using hd))))
    (hHalf : ∀ m i, ((weightOrderedRemainder (P m) wgt (Ns m)).law i).real (Ioi b)≤1/2)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) :
    let D := B.truncation K d (by simpa [hZero] using hd)
    let π := D.valueThresholdPolicy hw.le hc.le
    let s := fun m => weightedResidualScore (P m) wgt (Ns m) (Ioi b)
    Tendsto (fun m => (originalCoarsePolicy (P m) wgt (Ns m) π d).expectedRewardScore (P m) (s m)) atTop
      (𝓝 (∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(D.intensity:Measure ℝ).real (Ioi b))*
        (D.valueRule w c).realizedReward 0 v ∂D.law (Measure.dirac ()))) ∧
    Tendsto (fun m => (originalCoarsePolicy (P m) wgt (Ns m) π d).expectedDurationScore (P m) (s m)) atTop
      (𝓝 (∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-(D.intensity:Measure ℝ).real (Ioi b))*
        (D.valueRule w c).realizedDuration v ∂D.law (Measure.dirac ()))) := by
  let D := B.truncation K d (by simpa [hZero] using hd)
  let π := D.valueThresholdPolicy hw.le hc.le
  let Ps := fun m => weightOrderedPrefix (P m) wgt K
  let Q := fun m => weightOrderedRemainder (P m) wgt (Ns m)
  let δ := fun m => residualTailSup (fun j => weightOrderedPaddedLaw (P m) wgt j) (Ns m) d
  let s := fun m => completeScore (fun i => compensatedBandScore ((Q m).law i) (Ioi b))
  obtain ⟨hμWeak,⟨L,hL,hTail⟩,hδLim⟩ := h.residual_evaluation_inputs hZero Ns hNs d hd hAtomD hWeak
  have hAtom : (D.intensity:Measure ℝ) {b}=0 := by
    change B.intensity.restrict (Ioi d) {b}=0
    rw [Measure.restrict_apply (measurableSet_singleton b)]
    exact measure_mono_null inter_subset_left hAtomB
  have hLim := D.coarse_finite_cloud_outcomes_tendsto hZero hw hc Ps sizes Q d b hd.le hdb B.cap (le_refl _)
    (fun m => weightOrderedPrefix_bounded (P m) wgt K B.cap.property (hCap m))
    (fun m => weightOrderedRemainder_bounded (P m) wgt (Ns m) B.cap.property (hCap m))
    (h.prefix_marginal_tendsto K) hμWeak hAtom hHalf hL δ
    (fun _ => residualTailSup_nonneg _ _ _) hδLim hTail
    (fun m i => weightOrderedRemainder_tail_le_sup (P m) wgt (Ns m) d i)
  have hs (m) : Measurable (s m) := measurable_completeScore
    (fun i => measurable_compensatedBandScore ((Q m).law i) measurableSet_Ioi)
  have hsInt (m) : Integrable (s m) (Q m).valuesLaw := by
    simpa only [s,Model.Instance.valuesLaw,pow_one] using completeScore_integrable_pow (Q m).law
      (fun i => compensatedBandScore ((Q m).law i) (Ioi b))
      (fun i => measurable_compensatedBandScore ((Q m).law i) measurableSet_Ioi)
      (fun i => Filter.Eventually.of_forall (compensatedBandScore_abs_le_one ((Q m).law i) (hHalf m i))) 1
  have hExec (m) := π.finiteCutoffEvaluation_score_coordinate_tests (Ps m) (Q m) d B.cap
    (weightOrderedPrefix_bounded (P m) wgt K B.cap.property (hCap m))
    (weightOrderedRemainder_bounded (P m) wgt (Ns m) B.cap.property (hCap m)) (s m) (hs m) (hsInt m)
  have hEq (m) (hm : K≤Ns m) := weightedCanonicalCoarsePolicy_expectedScores_of_pullback
    (P m) wgt (Ns m) hm D hw hc d
    (fun y : Fin (K+sizes m) → ℝ => s m (fun j => y (j.natAdd K)))
    ((hs m).comp (measurable_pi_lambda _ (fun j => measurable_pi_apply (j.natAdd K))))
    (weightedResidualScore (P m) wgt (Ns m) (Ioi b))
    (weightedCoarseScore_residual_eq_completeScore (P m) wgt (Ns m) hm measurableSet_Ioi
      (not_lt.mpr (hd.le.trans hdb))) (hExec m).1.1 (hExec m).2.1
  constructor
  · apply hLim.1.congr'
    filter_upwards [hNs (eventually_ge_atTop K)] with m hm
    have hm' : K≤Ns m := hm
    have hγ : originalCoarsePolicy (P m) wgt (Ns m) π d=weightedCoarsePolicy (P m) wgt (Ns m) hm' π d := by
      unfold originalCoarsePolicy
      exact dif_pos hm'
    exact (hEq m hm').1.symm.trans ((congrArg
      (fun ρ : Model.RandomizedPolicy (sizes m) => ρ.expectedRewardScore (P m) (weightedResidualScore (P m) wgt (Ns m) (Ioi b))) hγ).symm)
  · apply hLim.2.congr'
    filter_upwards [hNs (eventually_ge_atTop K)] with m hm
    have hm' : K≤Ns m := hm
    have hγ : originalCoarsePolicy (P m) wgt (Ns m) π d=weightedCoarsePolicy (P m) wgt (Ns m) hm' π d := by
      unfold originalCoarsePolicy
      exact dif_pos hm'
    exact (hEq m hm').2.symm.trans ((congrArg
      (fun ρ : Model.RandomizedPolicy (sizes m) => ρ.expectedDurationScore (P m) (weightedResidualScore (P m) wgt (Ns m) (Ioi b))) hγ).symm)
end ProphetSecretary.Limiting
