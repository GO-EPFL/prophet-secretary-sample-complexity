import ProphetSecretary.Limiting.ExactCoarseEvaluation
import ProphetSecretary.Limiting.ScheduledVirtualTail
import ProphetSecretary.Limiting.DirectCoarsePolicy
import ProphetSecretary.Limiting.DirectApproximationBenchmark
import ProphetSecretary.Limiting.CountableTruncationLower

/-!
# Fixed coarse callbacks on prescribed-count direct approximants

Both the cutoff and finite retained set of the comparator stay fixed before
the array limit. Above that cutoff the prescribed finite intensity is
eventually exact. Thus arbitrary bounded measurable observations, including
those arising from a likelihood perturbation, require no continuity of the
callback at the boundary of the scored set.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability CountableInstance

lemma rareProbabilityLaw_tail_square_le (μ : FiniteMeasure ℝ) (k : ℕ) (hk : 0<k)
    (hm : μ.mass≤(k:ℝ≥0)) {d : ℝ} (hd : 0≤d) :
    (k:ℝ)*((rareProbabilityLaw μ (k:ℝ≥0) (by exact_mod_cast hk) hm:Measure ℝ).real (Ioi d))^2≤
      (μ.mass:ℝ)^2/(k:ℝ) := by
  rw [rareProbabilityLaw_real_Ioi _ _ _ _ hd,NNReal.coe_natCast]
  have hTail : (μ:Measure ℝ).real (Ioi d)≤(μ.mass:ℝ) := measureReal_mono (subset_univ _)
  have hPow := pow_le_pow_left₀ measureReal_nonneg hTail 2
  have hNe : (k:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  calc
    _ = ((μ:Measure ℝ).real (Ioi d))^2/(k:ℝ) := by field_simp [hNe]
    _ ≤ _ := div_le_div_of_nonneg_right hPow (Nat.cast_nonneg _)

 theorem CountableInstance.directPrescribed_coarse_payoffs_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (Ns ks : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ m, (B.terminal:ℝ)<bs m)
    (hk : ∀ m, 0<ks m) (hm : ∀ m, (B.intensityAbove (bs m) (hbs m)).mass≤(ks m:ℝ≥0))
    (hNs : Tendsto Ns atTop atTop) (hCut : Tendsto bs atTop (𝓝 (B.terminal:ℝ)))
    (hSquare : Tendsto (fun m => ((B.intensityAbove (bs m) (hbs m)).mass:ℝ)^2/(ks m:ℝ)) atTop (𝓝 (0:ℝ)))
    {K : ℕ} (π : RandomizedHybridPolicy K) (d : ℝ) (hd : (B.terminal:ℝ)<d) :
    let A := fun m => B.finiteDirectApproximationAt (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m)
    Tendsto (fun m => (directCoarsePolicy (Ns m) (ks m) π d).expectedReward (A m)) atTop
      (𝓝 ((π.extendToCountable B hd).expectedReward)) ∧
    Tendsto (fun m => (directCoarsePolicy (Ns m) (ks m) π d).expectedDuration (A m)) atTop
      (𝓝 ((π.extendToCountable B hd).expectedDuration)) := by
  let μ := fun m => B.intensityAbove (bs m) (hbs m)
  let κ := fun m => (rareProbabilityLaw (μ m) (ks m:ℝ≥0) (by exact_mod_cast hk m) (hm m):Measure ℝ)
  have hκBound (m) : ∀ᵐ x ∂κ m, x∈Icc (0:ℝ) B.cap :=
    rareProbabilityLaw_bounds (μ m) B.cap ((B.truncation (Ns m) (bs m) (hbs m)).intensity_supported.mono
      (fun _ hx => ⟨hx.1.le,hx.2⟩)) (ks m) (by exact_mod_cast hk m) (hm m)
  let Q := fun m => Model.iidOfferInstance (κ m) ((hκBound m).mono (fun _ hx => hx.1)) (ks m)
  let D := B.truncation K d hd
  have hExact : ∀ᶠ m in atTop, (∑ i, thresholdMarkIntensity ((Q m).law i) d)=D.intensity := by
    filter_upwards [hCut.eventually (gt_mem_nhds hd)] with m hmCut
    change (∑ _i : Fin (ks m), thresholdMarkIntensity (κ m) d)=_
    rw [rareProbabilityLaw_threshold_sum (μ m) (ks m) (hk m) (hm m) (B.terminal.property.trans hd.le)]
    exact B.intensityAbove_restrict (hbs m) hd hmCut.le
  have hSquares : Tendsto (fun m => ∑ i, (((Q m).law i).real (Ioi d))^2) atTop (𝓝 (0:ℝ)) := by
    have hEq (m) : (∑ i, (((Q m).law i).real (Ioi d))^2)=(ks m:ℝ)*((κ m).real (Ioi d))^2 := by
      simp only [Q,Model.iidOfferInstance,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    apply squeeze_zero (fun m => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) _ hSquare
    intro m
    rw [hEq m]
    exact rareProbabilityLaw_tail_square_le (μ m) (ks m) (hk m) (hm m) (B.terminal.property.trans hd.le)
  have hLim := π.finiteCutoffEvaluation_exactIntensity_tendsto D hZero ks Q d
    (fun m _ => (hκBound m).mono (fun _ hx => hx.2)) hExact hSquares
  have hSplit (m) (hmK : K≤Ns m) : (B.individualPrefix (Ns m)).restrictBy (Fin.castLEEmb hmK)=D.individuals := by
    apply Model.Instance.eq_of_law_eq
    rfl
  have hA (m) : B.finiteDirectApproximationAt (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m)=
      (B.individualPrefix (Ns m)).appendIndependent (Q m) := by
    apply Model.Instance.eq_of_law_eq
    rfl
  have hREq (m) (hmK : K≤Ns m) : (directCoarsePolicy (Ns m) (ks m) π d).expectedReward
      (B.finiteDirectApproximationAt (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m))=
      (π.finiteCutoffEvaluation (ks m) d).expectedReward (D.individuals.appendIndependent (Q m)) := by
    rw [hA m,directCoarsePolicy_expectedReward _ _ π d hmK,hSplit m hmK]
  have hTEq (m) (hmK : K≤Ns m) : (directCoarsePolicy (Ns m) (ks m) π d).expectedDuration
      (B.finiteDirectApproximationAt (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m))=
      (π.finiteCutoffEvaluation (ks m) d).expectedDuration (D.individuals.appendIndependent (Q m)) := by
    rw [hA m,directCoarsePolicy_expectedDuration _ _ π d hmK,hSplit m hmK]
  dsimp only
  rw [π.extendToCountable_expectedReward B hd,π.extendToCountable_expectedDuration B hd]
  constructor
  · apply hLim.1.congr'
    filter_upwards [hNs (eventually_ge_atTop K)] with m hmK
    exact (hREq m hmK).symm
  · apply hLim.2.congr'
    filter_upwards [hNs (eventually_ge_atTop K)] with m hmK
    exact (hTEq m hmK).symm
end ProphetSecretary.Limiting
