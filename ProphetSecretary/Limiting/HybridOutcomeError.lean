import ProphetSecretary.Limiting.HybridFirstDisagreement
import ProphetSecretary.Limiting.HybridTerminalWindow

/-!
# Coupled outcome error for finite-intensity hybrid policies

Both policies use the same complete offers and clocks. At zero terminal reward,
the finite-adapter expression is exactly the difference of the actual selected
rewards and durations. It neither conditions on survival nor reveals the
complete vectors to a policy.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*}

noncomputable def HybridRule.coupledValueOutcomeError (π : HybridRule n Seed)
    (B : FiniteIntensityHybridInstance n) (w c : ℝ) (v : HybridWorld n Seed) : ℝ :=
  let x := combinedValues v.2.1 v.1.2
  let u := combinedClocks v.2.2.1 v.1.2
  |(π.asFinitePolicy v.1.1).reward v.2.2.2 Finset.univ x u-
    ((B.valueRule w c).asFinitePolicy v.1.1).reward () Finset.univ x u|+
  |(π.asFinitePolicy v.1.1).stoppingTime v.2.2.2 Finset.univ x u-
    ((B.valueRule w c).asFinitePolicy v.1.1).stoppingTime () Finset.univ x u|

lemma HybridRule.coupledValueOutcomeError_eq_actual (π : HybridRule n Seed)
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (w c : ℝ) (v : HybridWorld n Seed) :
    π.coupledValueOutcomeError B w c v =
      |π.realizedReward B.terminal v-
        (B.valueRule w c).reward B.terminal () v.2.1 v.2.2.1 v.1|+
      |π.realizedDuration v-(B.valueRule w c).stoppingTime () v.2.1 v.2.2.1 v.1| := by
  rw [ha]
  simp only [NNReal.coe_zero,HybridRule.realizedReward,HybridZeroSimulation.reward_zero_eq_finite]
  rfl

lemma HybridRule.coupledValueOutcomeError_nonnegative (π : HybridRule n Seed)
    (B : FiniteIntensityHybridInstance n) (w c : ℝ) (v : HybridWorld n Seed) :
    0 ≤ π.coupledValueOutcomeError B w c v := add_nonneg (abs_nonneg _) (abs_nonneg _)

lemma HybridRule.coupledValueOutcomeError_le_bound (π : HybridRule n Seed)
    (B : FiniteIntensityHybridInstance n) (w c : ℝ) (v : HybridWorld n Seed) {H : ℝ}
    (hH : 0 ≤ H) (hx0 : ∀ k, 0 ≤ combinedValues v.2.1 v.1.2 k)
    (hxH : ∀ k, combinedValues v.2.1 v.1.2 k ≤ H)
    (hu0 : ∀ k, 0 ≤ combinedClocks v.2.2.1 v.1.2 k) :
    π.coupledValueOutcomeError B w c v ≤ H+1 := by
  let x := combinedValues v.2.1 v.1.2
  let u := combinedClocks v.2.2.1 v.1.2
  let ρ := (B.valueRule w c).asFinitePolicy v.1.1
  let σ := π.asFinitePolicy v.1.1
  have hM := Model.Instance.maximum_le x hH hxH
  have hp0 := σ.reward_nonnegative v.2.2.2 Finset.univ x u hx0
  have hr0 := ρ.reward_nonnegative () Finset.univ x u hx0
  have hpH := (σ.reward_le_maximum v.2.2.2 Finset.univ x u).trans hM
  have hrH := (ρ.reward_le_maximum () Finset.univ x u).trans hM
  have hpT0 := σ.stoppingTime_nonneg v.2.2.2 Finset.univ x u hu0
  have hrT0 := ρ.stoppingTime_nonneg () Finset.univ x u hu0
  have hpT1 := σ.stoppingTime_le_one v.2.2.2 Finset.univ x u
  have hrT1 := ρ.stoppingTime_le_one () Finset.univ x u
  have hR : |σ.reward v.2.2.2 Finset.univ x u-ρ.reward () Finset.univ x u| ≤ H := by
    rw [abs_le]
    constructor <;> linarith
  have hT : |σ.stoppingTime v.2.2.2 Finset.univ x u-ρ.stoppingTime () Finset.univ x u| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  exact add_le_add hR hT

lemma HybridRule.coupledValueOutcomeError_le_window (π : HybridRule n Seed)
    (B : FiniteIntensityHybridInstance n) (w c : ℝ) (v : HybridWorld n Seed) {H window : ℝ}
    (hH : 0 ≤ H) (hw0 : 0 ≤ window)
    (hx0 : ∀ k, 0 ≤ combinedValues v.2.1 v.1.2 k)
    (hxH : ∀ k, combinedValues v.2.1 v.1.2 k ≤ H)
    (hu0 : ∀ k, 0 ≤ combinedClocks v.2.2.1 v.1.2 k) :
    π.coupledValueOutcomeError B w c v ≤ window+
      (H+1)*(if v ∈ π.earlyValueDifference B w c window then 1 else 0)+hybridLateMaximum (1-window) v := by
  have hR := (π.asFinitePolicy v.1.1).reward_difference_le_window
    ((B.valueRule w c).asFinitePolicy v.1.1) v.2.2.2 ()
    (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) hH hx0 hxH (cut := 1-window)
  have hT := (π.asFinitePolicy v.1.1).duration_difference_le_window
    ((B.valueRule w c).asFinitePolicy v.1.1) v.2.2.2 ()
    (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) hu0 hw0
  change |(π.asFinitePolicy v.1.1).reward v.2.2.2 Finset.univ _ _-_|+
    |(π.asFinitePolicy v.1.1).stoppingTime v.2.2.2 Finset.univ _ _-_| ≤ _
  change _ ≤ window+(H+1)*(if (π.asFinitePolicy v.1.1).EarlyOutcomeDifference
    ((B.valueRule w c).asFinitePolicy v.1.1) v.2.2.2 () _ _ (1-window) then 1 else 0)+_ 
  unfold hybridLateMaximum
  nlinarith only [hR,hT]

variable [MeasurableSpace Seed]

lemma HybridRule.measurable_coupledValueOutcomeError (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (B : FiniteIntensityHybridInstance n) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Measurable (π.coupledValueOutcomeError B w c) := by
  apply measurable_of_configuration_prod_branches
  intro N
  let Ω := (Fin N → Point) × Model.World n Seed
  have hr : Measurable (fun v : Ω => v.2.2.2) := by fun_prop
  have hx (i : Fin n) : Measurable (fun v : Ω => v.2.1 i) := by fun_prop
  have hu (i : Fin n) : Measurable (fun v : Ω => v.2.2.1 i) := by fun_prop
  have hv (j : Fin N) : Measurable (fun v : Ω => v.1 j) := (measurable_pi_apply j).comp measurable_fst
  have hX (k : Fin (n+N)) := measurable_combinedValues_family _ hx _ hv k
  have hU (k : Fin (n+N)) := measurable_combinedClocks_family _ hu _ hv k
  have hσ := π.asFinitePolicy_isMeasurable hπ N
  have hρ := (B.valueRule w c).asFinitePolicy_isMeasurable (B.valueRule_isMeasurable hw hc) N
  exact (continuous_abs.measurable.comp
    (((π.asFinitePolicy N).measurable_reward hσ hr hX hU Finset.univ).sub
      (((B.valueRule w c).asFinitePolicy N).measurable_reward hρ measurable_const hX hU Finset.univ))).add
    (continuous_abs.measurable.comp
      (((π.asFinitePolicy N).measurable_stoppingTime hσ hr hX hU Finset.univ).sub
        (((B.valueRule w c).asFinitePolicy N).measurable_stoppingTime hρ measurable_const hX hU Finset.univ)))

lemma HybridRule.integrable_coupledValueOutcomeError (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (B : FiniteIntensityHybridInstance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Integrable (π.coupledValueOutcomeError B w c) (B.law ν) := by
  apply Integrable.of_bound (π.measurable_coupledValueOutcomeError hπ B hw hc).aestronglyMeasurable ((B.cap : ℝ)+1)
  filter_upwards [realized_values_bounds B.individuals B.intensity ν B.individual_bounded B.intensity_supported,
    hybrid_combined_clocks_regular B.individuals B.intensity ν] with v hx ht
  rw [Real.norm_eq_abs,abs_of_nonneg (π.coupledValueOutcomeError_nonnegative B w c v)]
  exact π.coupledValueOutcomeError_le_bound B w c v B.cap.property (fun k => (hx k).1)
    (fun k => (hx k).2) (fun k => (ht.2 k).1.le)

noncomputable def RandomizedHybridPolicy.expectedValueOutcomeError (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (w c : ℝ) : ℝ :=
  ∫ v, π.rule.coupledValueOutcomeError B w c v ∂B.law π.seedLaw

end ProphetSecretary.Limiting
