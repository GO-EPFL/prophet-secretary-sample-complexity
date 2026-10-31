import ProphetSecretary.Limiting.DirectCoarsePolicy
import ProphetSecretary.Limiting.CoarseFiniteOutcomes
import ProphetSecretary.Limiting.IidSquareRarity
import ProphetSecretary.Limiting.CountableInstance
import ProphetSecretary.Model.StandbyIidReward

/-!
# Actual direct-approximation coarse reward and duration limits

The retained prefix and the virtual count may grow independently. A common
positive-level tail bound and the actual iid square-sum estimate control the
fixed coarse execution. Zero-valued retained observations remain present.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
open CountableInstance

theorem CountableInstance.direct_coarse_outcomes_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (ret N : ℕ → ℕ) (hRet : Tendsto ret atTop atTop) (hN : ∀ m, 0<N m)
    (κ : ℕ → Measure ℝ) [∀ m, IsProbabilityMeasure (κ m)]
    (hκ : ∀ m, ∀ᵐ x ∂κ m, 0≤x) (hCap : ∀ m, ∀ᵐ x ∂κ m, x≤(B.cap:ℝ))
    (K : ℕ) (d : ℝ) (hd : 0<d)
    (hμWeak : Tendsto (fun m => ∑ _i : Fin (N m), thresholdMarkIntensity (κ m) d) atTop
      (𝓝 (B.intensityAbove d (by simpa only [hZero,NNReal.coe_zero] using hd))))
    {L : ℝ} (hL : 0≤L) (hTail : ∀ m, (N m:ℝ)*(κ m).real (Ioi d)≤L)
    (hSquares : Tendsto (fun m => (N m:ℝ)*((κ m).real (Ioi d))^2) atTop (𝓝 (0:ℝ)))
    {w c : ℝ} (hw : 0<w) (hc : 0<c) :
    let D := B.truncation K d (by simpa only [hZero,NNReal.coe_zero] using hd)
    let π := D.valueThresholdPolicy hw.le hc.le
    let Q := fun m => Model.iidOfferInstance (κ m) (hκ m) (N m)
    let P := fun m => (B.individualPrefix (ret m)).appendIndependent (Q m)
    Tendsto (fun m => (directCoarsePolicy (ret m) (N m) π d).expectedReward (P m)) atTop
      (𝓝 (∫ v, (D.valueRule w c).realizedReward 0 v ∂D.law (Measure.dirac ()))) ∧
    Tendsto (fun m => (directCoarsePolicy (ret m) (N m) π d).expectedDuration (P m)) atTop
      (𝓝 (∫ v, (D.valueRule w c).realizedDuration v ∂D.law (Measure.dirac ()))) := by
  have hdAbove : (B.terminal:ℝ)<d := by simpa only [hZero,NNReal.coe_zero] using hd
  let D := B.truncation K d hdAbove
  let π := D.valueThresholdPolicy hw.le hc.le
  let Ps := B.individualPrefix K
  let Q := fun m => Model.iidOfferInstance (κ m) (hκ m) (N m)
  let δ := fun m => (κ m).real (Ioi d)
  have hPs (i) : ∀ᵐ x ∂Ps.law i, x≤(B.cap:ℝ) := (B.individual_supported i.val).mono (fun _ hx => hx.2)
  have hTailQ (m) : (Q m).tailCount d≤L := by
    simpa only [Q,Model.Instance.tailCount,Model.iidOfferInstance,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,nsmul_eq_mul,Measure.real] using hTail m
  have hLim := D.coarse_finite_outcomes_tendsto hZero hw hc (fun _ => Ps) N Q d hd.le B.cap (le_refl _)
    (fun _ => hPs) (fun m _ => hCap m) (fun _ => tendsto_const_nhds) hμWeak hL δ
    (fun _ => measureReal_nonneg) (iid_band_probability_tendsto_zero N hN κ (Ioi d) hSquares)
    hTailQ (fun _ _ => le_refl _)
  have hSplit (m) (hm : K≤ret m) : (B.individualPrefix (ret m)).restrictBy (Fin.castLEEmb hm)=Ps := by
    apply Model.Instance.eq_of_law_eq
    rfl
  constructor
  · apply hLim.1.congr'
    filter_upwards [hRet (eventually_ge_atTop K)] with m hm
    have hEq := directCoarsePolicy_expectedReward (B.individualPrefix (ret m)) (Q m) π d hm
    rw [hSplit m hm] at hEq
    exact hEq.symm
  · apply hLim.2.congr'
    filter_upwards [hRet (eventually_ge_atTop K)] with m hm
    have hEq := directCoarsePolicy_expectedDuration (B.individualPrefix (ret m)) (Q m) π d hm
    rw [hSplit m hm] at hEq
    exact hEq.symm
end ProphetSecretary.Limiting
