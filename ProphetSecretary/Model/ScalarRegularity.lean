import ProphetSecretary.Model.ThresholdVariation
import ProphetSecretary.Model.ScalarBands
import ProphetSecretary.Model.BellmanLossProbability

/-!
# Finite scalar policy regret under a changed weight

The threshold error is proportional to the remaining horizon. Integrating it
against the actual independent candidate clock makes regret quadratic, with an
explicit finite-cardinality constant and no offer-cap dependence.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.weightLocalLoss (P : Instance n) (lam rho u : ℝ) (i : Fin n)
    (ω : World n Unit) : ℝ :=
  (thresholdPolicy (fun (_ : Unit) A t j ↦ P.valueThreshold lam ((1 - lam) * u) A t j)).arrivalBellmanLoss
    P rho ((1 - rho) * u) () ω.1 ω.2.1 i

lemma Instance.measurable_weightLocalLoss (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam rho u : ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) 1) (hrho : rho ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u) (i : Fin n) :
    Measurable (P.weightLocalLoss lam rho u i) := by
  exact Policy.measurable_arrivalBellmanLoss _
    (P.valueThreshold_policy_isMeasurable hP hlam.1.le (mul_nonneg (sub_nonneg.mpr hlam.2.le) hu))
    P hP hrho.1 (mul_nonneg (sub_nonneg.mpr hrho.2.le) hu) measurable_const
    (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
    (fun j ↦ (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i

lemma Instance.weightLocalLoss_nonnegative (P : Instance n) (lam rho u : ℝ) (i : Fin n)
    (ω : World n Unit) : 0 ≤ P.weightLocalLoss lam rho u i ω :=
  Policy.arrivalBellmanLoss_nonnegative _ _ _ _ _ _ _ _

lemma Instance.integrable_weightLocalLoss (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam rho u : ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) 1) (hrho : rho ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u) (i : Fin n) :
    Integrable (P.weightLocalLoss lam rho u i) (P.worldLaw (Measure.dirac ())) := by
  let δ := u * |lam - rho| / lam
  have hδ : 0 ≤ δ := div_nonneg (mul_nonneg hu (abs_nonneg _)) hlam.1.le
  apply Integrable.of_bound (P.measurable_weightLocalLoss hP hlam hrho hu i).aestronglyMeasurable δ
  filter_upwards [P.world_clocks_mem_unitInterval (Measure.dirac ())] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (P.weightLocalLoss_nonnegative lam rho u i ω)]
  have h := P.oldPolicy_localLoss_le_band hP hlam hrho hu ω.1 ω.2.1 i (hω i).1
  change P.weightLocalLoss lam rho u i ω ≤ if
    |rho * ω.1 i - P.continuationAtArrival rho ((1 - rho) * u) ω.1 ω.2.1 i| ≤ δ then δ else 0 at h
  split_ifs at h
  · exact h
  · exact h.trans hδ

/-- A single candidate contributes at most the displayed quadratic regret.
The estimate retains a factor `u`, making it uniform down to horizon zero. -/
theorem Instance.expected_weightLocalLoss_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam rho u : ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) 1) (hrho : rho ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u) (i : Fin n) :
    (∫ ω : World n Unit, P.weightLocalLoss lam rho u i ω ∂P.worldLaw (Measure.dirac ())) ≤
      8 * (1 + (n : ℝ)) * u * (lam - rho) ^ 2 / (lam ^ 2 * (1 - rho)) := by
  let μ := P.worldLaw (Measure.dirac ())
  let δ := u * |lam - rho| / lam
  let E : Set (World n Unit) := {ω | |rho * ω.1 i - P.continuationAtArrival rho ((1 - rho) * u) ω.1 ω.2.1 i| ≤ δ}
  have hδ : 0 ≤ δ := div_nonneg (mul_nonneg hu (abs_nonneg _)) hlam.1.le
  have hcNew : 0 ≤ (1 - rho) * u := mul_nonneg (sub_nonneg.mpr hrho.2.le) hu
  have hV : Measurable (fun ω : World n Unit ↦ P.continuationAtArrival rho ((1 - rho) * u) ω.1 ω.2.1 i) :=
    P.measurable_continuationAtArrival hP hrho.1 hcNew
      (fun j ↦ (measurable_pi_apply j).comp measurable_fst)
      (fun j ↦ (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  have hgap : Measurable (fun ω : World n Unit ↦ rho * ω.1 i -
      P.continuationAtArrival rho ((1 - rho) * u) ω.1 ω.2.1 i) :=
    (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst)).sub hV
  have hE : MeasurableSet E := measurableSet_le (continuous_abs.measurable.comp hgap) measurable_const
  have hband : ∀ᵐ ω : World n Unit ∂μ,
      P.weightLocalLoss lam rho u i ω ≤ E.indicator (fun _ ↦ δ) ω := by
    filter_upwards [P.world_clocks_mem_unitInterval (Measure.dirac ())] with ω hω
    have h := P.oldPolicy_localLoss_le_band hP hlam hrho hu ω.1 ω.2.1 i (hω i).1
    change P.weightLocalLoss lam rho u i ω ≤
      if |rho * ω.1 i - P.continuationAtArrival rho ((1 - rho) * u) ω.1 ω.2.1 i| ≤ δ then δ else 0 at h
    by_cases he : ω ∈ E
    · rw [Set.indicator_of_mem he]
      have he' : |rho * ω.1 i - P.continuationAtArrival rho ((1 - rho) * u) ω.1 ω.2.1 i| ≤ δ := he
      simpa only [if_pos he'] using h
    · rw [Set.indicator_of_notMem he]
      have he' : ¬ |rho * ω.1 i - P.continuationAtArrival rho ((1 - rho) * u) ω.1 ω.2.1 i| ≤ δ := he
      simpa only [if_neg he'] using h
  have hbound : ∀ᵐ ω : World n Unit ∂μ, P.weightLocalLoss lam rho u i ω ≤ δ := by
    filter_upwards [hband] with ω hω
    apply hω.trans
    by_cases he : ω ∈ E
    · rw [Set.indicator_of_mem he]
    · rw [Set.indicator_of_notMem he]
      exact hδ
  have hInt : Integrable (P.weightLocalLoss lam rho u i) μ := by
    apply Integrable.of_bound (P.measurable_weightLocalLoss hP hlam hrho hu i).aestronglyMeasurable δ
    filter_upwards [hbound] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (P.weightLocalLoss_nonnegative lam rho u i ω)]
    exact hω
  by_cases hu0 : u = 0
  · have h := integral_mono_ae hInt (integrable_const δ) hbound
    simp only [integral_const, probReal_univ, one_smul] at h
    have hz : δ = 0 := by simp [δ, hu0]
    rw [hz] at h
    simpa only [hu0, mul_zero, zero_mul, zero_div] using h
  · have huPos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
    have hcPos : 0 < (1 - rho) * u := mul_pos (sub_pos.mpr hrho.2) huPos
    have hprob := P.acceptanceBand_probability hP (Measure.dirac ()) hrho.1 hcPos hδ i
    change μ.real E ≤ 2 * δ / (((1 - rho) * u) / (4 * (1 + (n : ℝ)))) at hprob
    have h := integral_mono_ae hInt ((integrable_const δ).indicator hE) hband
    rw [integral_indicator_const δ hE, smul_eq_mul] at h
    calc
      _ ≤ μ.real E * δ := h
      _ ≤ (2 * δ / (((1 - rho) * u) / (4 * (1 + (n : ℝ))))) * δ :=
        mul_le_mul_of_nonneg_right hprob hδ
      _ = _ := by
        dsimp [δ]
        rw [← sq_abs (lam - rho)]
        field_simp [hlam.1.ne', huPos.ne', (sub_pos.mpr hrho.2).ne',
          (show (4 : ℝ) * (1 + (n : ℝ)) ≠ 0 by positivity)]
        ring

/-- Finite scalar regret of the old canonical policy at a new weight. The
constant is independent of the distributions and all remaining horizons `u≤1`. -/
theorem Instance.scalarPolicy_regret_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam rho u : ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) 1) (hrho : rho ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u) :
    let π := P.scalarStatePolicy hP hlam hu
    optimalScalarValue P rho ((1 - rho) * u) - π.scalarObjective P rho ((1 - rho) * u) ≤
      8 * (n : ℝ) * (1 + (n : ℝ)) * u * (lam - rho) ^ 2 / (lam ^ 2 * (1 - rho)) := by
  let π := P.scalarStatePolicy hP hlam hu
  have hcNew : 0 ≤ (1 - rho) * u := mul_nonneg (sub_nonneg.mpr hrho.2.le) hu
  change optimalScalarValue P rho ((1 - rho) * u) - π.scalarObjective P rho ((1 - rho) * u) ≤ _
  rw [π.bellman_performanceDifference P hP hrho.1 hcNew]
  change (∫ ω : World n Unit, π.rule.reachedBellmanLoss P rho ((1 - rho) * u) ω.2.2 ω.1 ω.2.1
    ∂P.worldLaw (Measure.dirac ())) ≤ _
  have hpoint (ω : World n Unit) : π.rule.reachedBellmanLoss P rho ((1 - rho) * u) ω.2.2 ω.1 ω.2.1 ≤
      ∑ i : Fin n, P.weightLocalLoss lam rho u i ω := by
    unfold Policy.reachedBellmanLoss
    apply Finset.sum_le_sum
    intro i _hi
    split_ifs
    · exact le_of_eq (by rfl)
    · exact P.weightLocalLoss_nonnegative lam rho u i ω
  have hsum : Integrable (fun ω : World n Unit ↦ ∑ i : Fin n, P.weightLocalLoss lam rho u i ω)
      (P.worldLaw (Measure.dirac ())) :=
    integrable_finsetSum _ (fun i _hi ↦ P.integrable_weightLocalLoss hP hlam hrho hu i)
  have hInt := integral_mono (π.rule.integrable_reachedBellmanLoss π.measurable_rule P hP π.seedLaw hrho.1 hcNew) hsum hpoint
  change (∫ ω : World n Unit, π.rule.reachedBellmanLoss P rho ((1 - rho) * u) ω.2.2 ω.1 ω.2.1
    ∂P.worldLaw (Measure.dirac ())) ≤
      ∫ ω : World n Unit, ∑ i : Fin n, P.weightLocalLoss lam rho u i ω ∂P.worldLaw (Measure.dirac ()) at hInt
  rw [integral_finsetSum Finset.univ (fun i _hi ↦ P.integrable_weightLocalLoss hP hlam hrho hu i)] at hInt
  calc
    _ ≤ ∑ i : Fin n, ∫ ω : World n Unit, P.weightLocalLoss lam rho u i ω ∂P.worldLaw (Measure.dirac ()) := hInt
    _ ≤ ∑ _i : Fin n, (8 * (1 + (n : ℝ)) * u * (lam - rho) ^ 2 / (lam ^ 2 * (1 - rho))) :=
      Finset.sum_le_sum (fun i _hi ↦ P.expected_weightLocalLoss_le hP hlam hrho hu i)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Quadratic supporting-payoff error at every finite state. The slope is
that of the fixed base optimizer, not a derivative of a reoptimized policy. -/
theorem Instance.scalarState_quadraticGap (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam rho u : ℝ}
    (hlam : lam ∈ Ioo (0 : ℝ) 1) (hrho : rho ∈ Ioo (0 : ℝ) 1) (hu : 0 ≤ u) :
    let π := P.scalarStatePolicy hP hlam hu
    let gap := optimalScalarValue P rho ((1 - rho) * u) - optimalScalarValue P lam ((1 - lam) * u) -
      (rho - lam) * (π.expectedReward P - u * π.expectedDuration P)
    0 ≤ gap ∧ gap ≤ 8 * (n : ℝ) * (1 + (n : ℝ)) * u * (lam - rho) ^ 2 / (lam ^ 2 * (1 - rho)) := by
  let π := P.scalarStatePolicy hP hlam hu
  have hopt : π.scalarObjective P lam ((1 - lam) * u) = optimalScalarValue P lam ((1 - lam) * u) :=
    P.valuePolicy_optimal hP hlam.1 (mul_nonneg (sub_nonneg.mpr hlam.2.le) hu)
  have heq : optimalScalarValue P rho ((1 - rho) * u) - optimalScalarValue P lam ((1 - lam) * u) -
      (rho - lam) * (π.expectedReward P - u * π.expectedDuration P) =
      optimalScalarValue P rho ((1 - rho) * u) - π.scalarObjective P rho ((1 - rho) * u) := by
    rw [← hopt, π.scalarObjective_eq P hP, π.scalarObjective_eq P hP]
    ring
  change (0 ≤ optimalScalarValue P rho ((1 - rho) * u) - optimalScalarValue P lam ((1 - lam) * u) -
      (rho - lam) * (π.expectedReward P - u * π.expectedDuration P)) ∧ _
  rw [heq]
  exact ⟨sub_nonneg.mpr (scalarObjective_le_optimal π P hP hrho.1.le
    (mul_nonneg (sub_nonneg.mpr hrho.2.le) hu)), P.scalarPolicy_regret_le hP hlam hrho hu⟩

/-- Explicit preliminary finite curvature constant on `[a,b]⊂(0,1)`. It is
uniform over all offer laws and every remaining horizon in `[0,1]`. -/
noncomputable def finiteScalarConstant (n : ℕ) (a b : ℝ) : ℝ :=
  8 * (n : ℝ) * (1 + (n : ℝ)) / (a ^ 2 * (1 - b))

theorem Instance.scalarState_quadraticGap_uniform (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {a b lam rho u : ℝ}
    (ha : 0 < a) (hb : b < 1) (hlam : lam ∈ Icc a b) (hrho : rho ∈ Icc a b)
    (hu : u ∈ Icc (0 : ℝ) 1) :
    let π := P.scalarStatePolicy hP ⟨ha.trans_le hlam.1, hlam.2.trans_lt hb⟩ hu.1
    let gap := optimalScalarValue P rho ((1 - rho) * u) - optimalScalarValue P lam ((1 - lam) * u) -
      (rho - lam) * (π.expectedReward P - u * π.expectedDuration P)
    0 ≤ gap ∧ gap ≤ finiteScalarConstant n a b * (rho - lam) ^ 2 := by
  have hl0 : lam ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans_le hlam.1, hlam.2.trans_lt hb⟩
  have hr0 : rho ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans_le hrho.1, hrho.2.trans_lt hb⟩
  have h := P.scalarState_quadraticGap hP hl0 hr0 hu.1
  refine ⟨h.1, h.2.trans ?_⟩
  let C := 8 * (n : ℝ) * (1 + (n : ℝ))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hN : C * u * (lam - rho) ^ 2 ≤ C * (lam - rho) ^ 2 := by
    have ht := mul_le_mul_of_nonneg_left hu.2 (mul_nonneg hC (sq_nonneg (lam - rho)))
    nlinarith
  have hSq : a ^ 2 ≤ lam ^ 2 := by nlinarith [ha, hlam.1]
  have hD : a ^ 2 * (1 - b) ≤ lam ^ 2 * (1 - rho) :=
    mul_le_mul hSq (by linarith [hrho.2]) (sub_pos.mpr hb).le (sq_nonneg lam)
  have hSmall : 0 < a ^ 2 * (1 - b) := mul_pos (sq_pos_of_pos ha) (sub_pos.mpr hb)
  have hInv := mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hSmall hD)
    (mul_nonneg hC (sq_nonneg (lam - rho)))
  calc
    _ ≤ (C * (lam - rho) ^ 2) / (lam ^ 2 * (1 - rho)) :=
      div_le_div_of_nonneg_right hN (mul_nonneg (sq_nonneg lam) (sub_nonneg.mpr hr0.2.le))
    _ ≤ (C * (lam - rho) ^ 2) / (a ^ 2 * (1 - b)) := by
      simpa only [div_eq_mul_inv, one_div, one_mul] using hInv
    _ = _ := by
      dsimp [C, finiteScalarConstant]
      ring

end ProphetSecretary.Model
