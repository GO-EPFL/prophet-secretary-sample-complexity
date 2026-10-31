import ProphetSecretary.Limiting.OriginalCoarseOutcomes
import ProphetSecretary.Limiting.CoarseFiniteIndividualOutcomes
import ProphetSecretary.Limiting.WeightedCoarseExpectedScores
import ProphetSecretary.Limiting.WeightedIndividualCoarseScore

/-!
# Original-array individual-score expectations at a fixed coarse level

The retained-individual score is indexed by the original labels. The pointwise complete
score identity, causal simulation and actual product laws identify its reward
and duration expectations with those of the residual finite evaluation.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology Classical NNReal
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability

theorem OrderedBandConvergence.original_coarse_individual_score_tendsto
    {sizes : ℕ → ℕ} {P : ∀ m, Model.Instance (sizes m)} {wgt : ℝ →ᵇ ℝ} {B : CountableInstance}
    (h : OrderedBandConvergence sizes P wgt B) (hZero : B.terminal=0)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap:ℝ))
    (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop) (K : ℕ)
    (d : ℝ) (hd : 0<d) (hAtomD : B.intensity {d}=0)
    (hWeak : Tendsto (fun m => weightOrderedBandResidual (P m) wgt (Ns m) d)
      atTop (𝓝 (B.intensityAbove d (by simpa [hZero] using hd))))
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (i : Fin K) (f : ℝ →ᵇ ℝ) :
    let D := B.truncation K d (by simpa [hZero] using hd)
    let π := D.valueThresholdPolicy hw.le hc.le
    let s := fun m => weightedIndividualScore (P m) wgt i.val f
    Tendsto (fun m => (originalCoarsePolicy (P m) wgt (Ns m) π d).expectedRewardScore (P m) (s m)) atTop
      (𝓝 (∫ v, centeredBoundedScore (D.individuals.law i) f (v.2.1 i)*
        (D.valueRule w c).realizedReward 0 v ∂D.law (Measure.dirac ()))) ∧
    Tendsto (fun m => (originalCoarsePolicy (P m) wgt (Ns m) π d).expectedDurationScore (P m) (s m)) atTop
      (𝓝 (∫ v, centeredBoundedScore (D.individuals.law i) f (v.2.1 i)*
        (D.valueRule w c).realizedDuration v ∂D.law (Measure.dirac ()))) := by
  let D := B.truncation K d (by simpa [hZero] using hd)
  let π := D.valueThresholdPolicy hw.le hc.le
  let Ps := fun m => weightOrderedPrefix (P m) wgt K
  let Q := fun m => weightOrderedRemainder (P m) wgt (Ns m)
  let δ := fun m => residualTailSup (fun j => weightOrderedPaddedLaw (P m) wgt j) (Ns m) d
  obtain ⟨hμWeak,⟨L,hL,hTail⟩,hδLim⟩ := h.residual_evaluation_inputs hZero Ns hNs d hd hAtomD hWeak
  have hLim := D.coarse_finite_individual_outcomes_tendsto hZero hw hc Ps sizes Q d hd.le B.cap (le_refl _)
    (fun m => weightOrderedPrefix_bounded (P m) wgt K B.cap.property (hCap m))
    (fun m => weightOrderedRemainder_bounded (P m) wgt (Ns m) B.cap.property (hCap m))
    (h.prefix_marginal_tendsto K) hμWeak hL δ
    (fun _ => residualTailSup_nonneg _ _ _) hδLim hTail
    (fun m j => weightOrderedRemainder_tail_le_sup (P m) wgt (Ns m) d j) i f
  let g := fun m (v : Model.World K π.Seed) => centeredBoundedScore ((Ps m).law i) f (v.1 i)
  have hg (m) : Measurable (g m) :=
    (continuous_centeredBoundedScore ((Ps m).law i) f).measurable.comp ((measurable_pi_apply i).comp measurable_fst)
  have hgb (m v) : ‖g m v‖≤1 := centeredBoundedScore_abs_le_one ((Ps m).law i) f (v.1 i)
  have hExec (m) := π.finiteCutoffEvaluation_retained_score_coordinate_tests (Ps m) (Q m) d B.cap
    (weightOrderedPrefix_bounded (P m) wgt K B.cap.property (hCap m))
    (weightOrderedRemainder_bounded (P m) wgt (Ns m) B.cap.property (hCap m)) (g m) (hg m) (hgb m)
  have hs (m) : Measurable (fun y : Fin (K+sizes m) → ℝ => centeredBoundedScore ((Ps m).law i) f (y (i.castAdd (sizes m)))) :=
    (continuous_centeredBoundedScore ((Ps m).law i) f).measurable.comp (measurable_pi_apply (i.castAdd (sizes m)))
  have hEq (m) (hm : K≤Ns m) := weightedCanonicalCoarsePolicy_expectedScores_of_pullback
    (P m) wgt (Ns m) hm D hw hc d
    (fun y : Fin (K+sizes m) → ℝ => centeredBoundedScore ((Ps m).law i) f (y (i.castAdd (sizes m))))
    (hs m) (weightedIndividualScore (P m) wgt i.val f)
    (weightedCoarseScore_individual_eq_completeScore (P m) wgt (Ns m) hm i f)
    (hExec m).1.1 (hExec m).2.1
  constructor
  · apply hLim.1.congr'
    filter_upwards [hNs (eventually_ge_atTop K)] with m hm
    have hm' : K≤Ns m := hm
    have hγ : originalCoarsePolicy (P m) wgt (Ns m) π d=weightedCoarsePolicy (P m) wgt (Ns m) hm' π d := by
      unfold originalCoarsePolicy
      exact dif_pos hm'
    exact (hEq m hm').1.symm.trans ((congrArg
      (fun ρ : Model.RandomizedPolicy (sizes m) => ρ.expectedRewardScore (P m) (weightedIndividualScore (P m) wgt i.val f)) hγ).symm)
  · apply hLim.2.congr'
    filter_upwards [hNs (eventually_ge_atTop K)] with m hm
    have hm' : K≤Ns m := hm
    have hγ : originalCoarsePolicy (P m) wgt (Ns m) π d=weightedCoarsePolicy (P m) wgt (Ns m) hm' π d := by
      unfold originalCoarsePolicy
      exact dif_pos hm'
    exact (hEq m hm').2.symm.trans ((congrArg
      (fun ρ : Model.RandomizedPolicy (sizes m) => ρ.expectedDurationScore (P m) (weightedIndividualScore (P m) wgt i.val f)) hγ).symm)
end ProphetSecretary.Limiting
