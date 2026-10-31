import ProphetSecretary.Stability.TerminalWindow
import ProphetSecretary.Model.StabilityBands

/-!
# Explicit outcome-stability estimates

First disagreement is charged either to a reached Bellman loss or to an unconditioned
positive acceptance-boundary event. Terminal rewards are bounded without conditioning
on survival. Paper labels: `eq:ps-first-disagreement`, `eq:ps-duration-stability-explicit`,
and `eq:ps-reward-stability-explicit`.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

/-- The quotient form is used only with a positive reward coefficient. -/
noncomputable def Instance.canonicalRule (P : Instance n) (w c : ℝ) : Policy Unit n :=
  thresholdPolicy (fun (_ : Unit) A t i => P.valueThreshold w c A t i)

def Policy.earlyCanonicalDifference (π : Policy Seed n) (P : Instance n)
    (w c window : ℝ) : Set (World n Seed) :=
  {ω | π.EarlyOutcomeDifference (P.canonicalRule w c) ω.2.2 () ω.1 ω.2.1 (1 - window)}

lemma Policy.earlyCanonicalDifference_loss_or_boundary (π : Policy Seed n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c b e : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hb : 0 < b) (he : e ≤ w * b / 4)
    (ω : World n Seed) (hclock : Function.Injective ω.2.1)
    (hEarly : ω ∈ π.earlyCanonicalDifference P w c (2 * w * b / c)) :
    ω ∈ π.reachedLossEvent P w c e ∪
      {ω : World n Seed | ∃ i, b ≤ ω.1 i ∧ |w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i| ≤ e} := by
  let window := 2 * w * b / c
  have hwindow : 0 ≤ window := by dsimp [window]; positivity
  obtain ⟨i, hui, hr, _hρr, hact⟩ := π.earlyOutcomeDifference_witness (P.canonicalRule w c)
    ω.2.2 () ω.1 ω.2.1 hclock (show 1 - window ≤ 1 by linarith) hEarly
  have hloss := π.disagreementLoss_eq_absGap P hw c ω.2.2 ω.1 ω.2.1 i hact
  by_cases hx : b ≤ ω.1 i
  · by_cases hg : |w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i| ≤ e
    · exact Or.inr ⟨i, hx, hg⟩
    · exact Or.inl ⟨i, hr, (le_of_lt (lt_of_not_ge hg)).trans_eq hloss.symm⟩
  · have hsmall : w * ω.1 i < w * b := mul_lt_mul_of_pos_left (lt_of_not_ge hx) hw
    have hwait : c * max 0 (1 - ω.2.1 i) ≤ P.continuationAtArrival w c ω.1 ω.2.1 i :=
      P.durationWeight_le_continuationValue hP _ (le_max_left _ _) hw.le hc.le
    have hphysical : window < 1 - ω.2.1 i := by linarith
    have hmul := mul_lt_mul_of_pos_left hphysical hc
    have heq : c * window = 2 * w * b := by dsimp [window]; field_simp
    rw [heq] at hmul
    have hmax := mul_le_mul_of_nonneg_left (le_max_right (0 : ℝ) (1 - ω.2.1 i)) hc.le
    have hcont : 2 * w * b < P.continuationAtArrival w c ω.1 ω.2.1 i :=
      hmul.trans_le (hmax.trans hwait)
    have hgapneg : w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i < 0 := by nlinarith
    have hlarge : e ≤ |w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i| := by
      rw [abs_of_neg hgapneg]
      nlinarith [mul_pos hw hb]
    exact Or.inl ⟨i, hr, hlarge.trans_eq hloss.symm⟩

variable [MeasurableSpace Seed]

lemma Policy.measurableSet_earlyCanonicalDifference (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (window : ℝ) :
    MeasurableSet (π.earlyCanonicalDifference P w c window) :=
  π.measurableSet_earlyOutcomeDifference hπ (P.canonicalRule w c)
    (P.valueThreshold_policy_isMeasurable hP hw.le hc)
    (measurable_snd.comp measurable_snd) measurable_const
    (fun i => (measurable_pi_apply i).comp measurable_fst)
    (fun i => (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)) measurable_const

/-- Raw first-disagreement bound, before substituting the proved boundary probability. -/
theorem RandomizedPolicy.earlyCanonicalDifference_probability (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c b e : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hb : 0 < b) (he0 : 0 < e) (he : e ≤ w * b / 4) :
    (P.worldLaw π.seedLaw).real (π.rule.earlyCanonicalDifference P w c (2 * w * b / c)) ≤
      (optimalScalarValue P w c - π.scalarObjective P w c) / e +
        (P.worldLaw π.seedLaw).real {ω : π.World | ∃ i,
          b ≤ ω.1 i ∧ |w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i| ≤ e} := by
  let μ := P.worldLaw π.seedLaw
  let L : Set π.World := π.rule.reachedLossEvent P w c e
  let B : Set π.World := {ω | ∃ i, b ≤ ω.1 i ∧ |w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i| ≤ e}
  have hsub : ∀ᵐ ω : π.World ∂μ,
      ω ∈ π.rule.earlyCanonicalDifference P w c (2 * w * b / c) → ω ∈ (L ∪ B : Set π.World) := by
    filter_upwards [P.world_clocks_distinct π.seedLaw] with ω hω hE
    exact π.rule.earlyCanonicalDifference_loss_or_boundary P hP hw hc hb he ω hω hE
  have hmono : μ.real (π.rule.earlyCanonicalDifference P w c (2 * w * b / c)) ≤ μ.real (L ∪ B) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  calc
    _ ≤ μ.real L + μ.real B := hmono.trans (measureReal_union_le L B)
    _ ≤ _ := add_le_add (π.reachedLoss_probability_le_regret P hP hw hc.le he0) le_rfl

/-- Coupled reward/time error under the same complete offers and clocks. -/
noncomputable def RandomizedPolicy.coupledOutcomeError (π : RandomizedPolicy n) (P : Instance n)
    (w c : ℝ) (ω : π.World) : ℝ :=
  |π.realizedReward ω - (P.canonicalRule w c).reward () Finset.univ ω.1 ω.2.1| +
    |π.realizedDuration ω - (P.canonicalRule w c).stoppingTime () Finset.univ ω.1 ω.2.1|

noncomputable def RandomizedPolicy.expectedOutcomeError (π : RandomizedPolicy n) (P : Instance n)
    (w c : ℝ) : ℝ := ∫ ω, π.coupledOutcomeError P w c ω ∂P.worldLaw π.seedLaw

lemma RandomizedPolicy.coupledOutcomeError_nonnegative (π : RandomizedPolicy n) (P : Instance n)
    (w c : ℝ) (ω : π.World) : 0 ≤ π.coupledOutcomeError P w c ω :=
  add_nonneg (abs_nonneg _) (abs_nonneg _)

lemma RandomizedPolicy.coupledOutcomeError_le_bound (π : RandomizedPolicy n) (P : Instance n)
    (w c : ℝ) (ω : π.World) {H : ℝ} (hH : 0 ≤ H)
    (hx0 : ∀ i, 0 ≤ ω.1 i) (hxH : ∀ i, ω.1 i ≤ H) (hu0 : ∀ i, 0 ≤ ω.2.1 i) :
    π.coupledOutcomeError P w c ω ≤ H + 1 := by
  let ρ := P.canonicalRule w c
  have hM := Instance.maximum_le ω.1 hH hxH
  have hp0 := π.rule.reward_nonnegative ω.2.2 Finset.univ ω.1 ω.2.1 hx0
  have hr0 := ρ.reward_nonnegative () Finset.univ ω.1 ω.2.1 hx0
  have hpH := (π.rule.reward_le_maximum ω.2.2 Finset.univ ω.1 ω.2.1).trans hM
  have hrH := (ρ.reward_le_maximum () Finset.univ ω.1 ω.2.1).trans hM
  have hpT0 := π.rule.stoppingTime_nonneg ω.2.2 Finset.univ ω.1 ω.2.1 hu0
  have hrT0 := ρ.stoppingTime_nonneg () Finset.univ ω.1 ω.2.1 hu0
  have hpT1 := π.rule.stoppingTime_le_one ω.2.2 Finset.univ ω.1 ω.2.1
  have hrT1 := ρ.stoppingTime_le_one () Finset.univ ω.1 ω.2.1
  have hR : |π.rule.reward ω.2.2 Finset.univ ω.1 ω.2.1 - ρ.reward () Finset.univ ω.1 ω.2.1| ≤ H := by
    rw [abs_le]
    constructor <;> linarith
  have hT : |π.rule.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 - ρ.stoppingTime () Finset.univ ω.1 ω.2.1| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  exact add_le_add hR hT

lemma RandomizedPolicy.measurable_coupledOutcomeError (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Measurable (π.coupledOutcomeError P w c) := by
  let ρ := P.canonicalRule w c
  have hρ : ρ.IsMeasurable := P.valueThreshold_policy_isMeasurable hP hw.le hc
  have hx (i : Fin n) : Measurable (fun ω : π.World => ω.1 i) := (measurable_pi_apply i).comp measurable_fst
  have hu (i : Fin n) : Measurable (fun ω : π.World => ω.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  have hR := ρ.measurable_reward hρ (measurable_const : Measurable fun _ : π.World => ()) hx hu Finset.univ
  have hT := ρ.measurable_stoppingTime hρ (measurable_const : Measurable fun _ : π.World => ()) hx hu Finset.univ
  exact (continuous_abs.measurable.comp (π.measurable_realizedReward.sub hR)).add
    (continuous_abs.measurable.comp (π.measurable_realizedDuration.sub hT))

lemma RandomizedPolicy.integrable_coupledOutcomeError (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Integrable (π.coupledOutcomeError P w c) (P.worldLaw π.seedLaw) := by
  have hv : MeasurePreserving (fun ω : π.World => ω.1) (P.worldLaw π.seedLaw) P.valuesLaw := measurePreserving_fst
  have hmax := hv.integrable_comp_of_integrable hP
  apply (hmax.add (integrable_const 1)).mono' (π.measurable_coupledOutcomeError P hP hw hc).aestronglyMeasurable
  filter_upwards [hv.quasiMeasurePreserving.ae P.ae_nonnegative,
    P.world_clocks_mem_unitInterval π.seedLaw] with ω hx hu
  rw [Real.norm_eq_abs, abs_of_nonneg (π.coupledOutcomeError_nonnegative P w c ω)]
  exact π.coupledOutcomeError_le_bound P w c ω (Instance.maximum_nonnegative ω.1)
    hx (fun i => Instance.le_maximum ω.1 i) (fun i => (hu i).1)

lemma RandomizedPolicy.expectedOutcomeError_nonnegative (π : RandomizedPolicy n) (P : Instance n)
    (w c : ℝ) : 0 ≤ π.expectedOutcomeError P w c :=
  integral_nonneg (π.coupledOutcomeError_nonnegative P w c)

lemma RandomizedPolicy.expectedOutcomeError_le_bound (π : RandomizedPolicy n) (P : Instance n)
    {H w c : ℝ} (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) (hw : 0 < w) (hc : 0 ≤ c) :
    π.expectedOutcomeError P w c ≤ H + 1 := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hv : MeasurePreserving (fun ω : π.World => ω.1) (P.worldLaw π.seedLaw) P.valuesLaw := measurePreserving_fst
  have hvalsH : ∀ᵐ x ∂P.valuesLaw, ∀ i, x i ≤ H := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hbound i)
  have h := integral_mono_ae (π.integrable_coupledOutcomeError P hP hw hc) (integrable_const (H + 1)) (by
    filter_upwards [hv.quasiMeasurePreserving.ae P.ae_nonnegative,
      hv.quasiMeasurePreserving.ae hvalsH, P.world_clocks_mem_unitInterval π.seedLaw] with ω hx0 hxH hu
    exact π.coupledOutcomeError_le_bound P w c ω hH hx0 hxH (fun i => (hu i).1))
  simpa only [RandomizedPolicy.expectedOutcomeError, integral_const, probReal_univ, one_smul] using h

/-- Explicit outcome estimate with the actual boundary probability retained. -/
lemma RandomizedPolicy.expectedOutcomeError_le_window (π : RandomizedPolicy n) (P : Instance n)
    {H w c b d e : ℝ} (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H)
    (hw : 0 < w) (hc : 0 < c) (hb : 0 < b) (hd : 0 ≤ d)
    (he0 : 0 < e) (he : e ≤ w * b / 4) (hwindow : 2 * w * b / c ≤ 1) :
    π.expectedOutcomeError P w c ≤ 2 * w * b / c +
      (H + 1) * ((optimalScalarValue P w c - π.scalarObjective P w c) / e +
        (P.worldLaw π.seedLaw).real {ω : π.World | ∃ i,
          b ≤ ω.1 i ∧ |w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i| ≤ e}) +
      d + H * (2 * w * b / c) * P.tailCount d := by
  classical
  let μ := P.worldLaw π.seedLaw
  let ρ := P.canonicalRule w c
  let window := 2 * w * b / c
  let E := π.rule.earlyCanonicalDifference P w c window
  let I : π.World → ℝ := fun ω => if ω ∈ E then 1 else 0
  have hP := P.integrable_maximum_of_bounded hbound
  have hw0 : 0 ≤ window := by dsimp [window]; positivity
  have hEm : MeasurableSet E := π.rule.measurableSet_earlyCanonicalDifference π.measurable_rule P hP hw hc.le window
  have hII : Integrable I μ := by
    apply Integrable.of_bound (Measurable.ite hEm measurable_const measurable_const).aestronglyMeasurable 1
    filter_upwards [] with ω
    dsimp [I]
    split_ifs <;> norm_num
  have hIeq : (∫ ω, I ω ∂μ) = μ.real E := by
    simpa only [I, Set.indicator_apply, Pi.one_apply] using (integral_indicator_one (μ := μ) hEm)
  have hlate := P.integrable_lateMaximum π.seedLaw (cut := 1 - window) hH hbound
  have hRHS : Integrable (fun ω : π.World => window + (H + 1) * I ω + lateMaximum ω.1 ω.2.1 (1 - window)) μ :=
    ((integrable_const window).add (hII.const_mul (H + 1))).add hlate
  have hv : MeasurePreserving (fun ω : π.World => ω.1) μ P.valuesLaw := measurePreserving_fst
  have hvalsH : ∀ᵐ x ∂P.valuesLaw, ∀ i, x i ≤ H := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hbound i)
  have hpoint : ∀ᵐ ω : π.World ∂μ, π.coupledOutcomeError P w c ω ≤
      window + (H + 1) * I ω + lateMaximum ω.1 ω.2.1 (1 - window) := by
    filter_upwards [hv.quasiMeasurePreserving.ae P.ae_nonnegative,
      hv.quasiMeasurePreserving.ae hvalsH, P.world_clocks_mem_unitInterval π.seedLaw] with ω hx0 hxH hu
    have hR := π.rule.reward_difference_le_window ρ ω.2.2 () ω.1 ω.2.1 hH hx0 hxH (cut := 1 - window)
    have hT := π.rule.duration_difference_le_window ρ ω.2.2 () ω.1 ω.2.1 (fun i => (hu i).1) hw0
    have hInd : (if π.rule.EarlyOutcomeDifference ρ ω.2.2 () ω.1 ω.2.1 (1 - window) then (1 : ℝ) else 0) = I ω := by
      rfl
    rw [hInd] at hR hT
    change |π.rule.reward ω.2.2 Finset.univ ω.1 ω.2.1 - ρ.reward () Finset.univ ω.1 ω.2.1| +
      |π.rule.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 - ρ.stoppingTime () Finset.univ ω.1 ω.2.1| ≤ _
    linarith
  have h := integral_mono_ae (π.integrable_coupledOutcomeError P hP hw hc.le) hRHS hpoint
  change (∫ ω : π.World, π.coupledOutcomeError P w c ω ∂μ) ≤
    ∫ ω : π.World, (window + (H + 1) * I ω) + lateMaximum ω.1 ω.2.1 (1 - window) ∂μ at h
  rw [integral_add (μ := μ)
      (f := fun ω : π.World => window + (H + 1) * I ω)
      (g := fun ω : π.World => lateMaximum ω.1 ω.2.1 (1 - window))
      ((integrable_const window).add (hII.const_mul (H + 1))) hlate,
    integral_add (μ := μ) (f := fun _ : π.World => window)
      (g := fun ω : π.World => (H + 1) * I ω)
      (integrable_const window) (hII.const_mul (H + 1)), integral_const_mul, hIeq] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  have hEarly := π.earlyCanonicalDifference_probability P hP hw hc hb he0 he
  have hmul := mul_le_mul_of_nonneg_left hEarly (show 0 ≤ H + 1 by linarith)
  have hL := P.integral_lateMaximum_le π.seedLaw hH hd hw0 hwindow hbound
  change (H + 1) * μ.real E ≤ (H + 1) *
    ((optimalScalarValue P w c - π.scalarObjective P w c) / e +
      μ.real {ω : π.World | ∃ i, b ≤ ω.1 i ∧ |w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i| ≤ e}) at hmul
  change (∫ ω : π.World, lateMaximum ω.1 ω.2.1 (1 - window) ∂μ) ≤ d + H * window * P.tailCount d at hL
  change π.expectedOutcomeError P w c ≤ _
  change π.expectedOutcomeError P w c ≤ window + (H + 1) * μ.real E +
    (∫ ω : π.World, lateMaximum ω.1 ω.2.1 (1 - window) ∂μ) at h
  linarith

/-- Dimension-independent finite estimate used to construct the uniform modulus.
All cap, weight and tail-count dependencies are explicit. -/
theorem RandomizedPolicy.expectedOutcomeError_le_uniform (π : RandomizedPolicy n) (P : Instance n)
    {H δ w c b d e L4 L2 Ld : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H)
    (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1)
    (hb : 0 < b) (hbsmall : b < δ / 2) (hd : 0 ≤ d) (he0 : 0 < e) (he : e ≤ δ * b / 4)
    (hL4 : P.tailCount (b / 4) ≤ L4) (hL2 : P.tailCount (b / 2) ≤ L2) (hLd : P.tailCount d ≤ Ld) :
    π.expectedOutcomeError P w c ≤
      (H + 1) * ((optimalScalarValue P w c - π.scalarObjective P w c) / e +
        uniformStabilityBandConstant H δ b L4 L2 * e) +
      2 * b / δ + d + (2 * H * b / δ) * Ld := by
  have hw : 0 < w := hδ.trans_le hwδ
  have hc : 0 < c := hδ.trans_le hcδ
  have hw1 : w ≤ 1 := by linarith
  let window := 2 * w * b / c
  have hw0 : 0 ≤ window := by dsimp [window]; positivity
  have hδw : δ * w ≤ c := by
    have h := mul_le_mul_of_nonneg_left hw1 hδ.le
    nlinarith
  have hwBound : window ≤ 2 * b / δ := by
    apply (div_le_div_iff₀ hc hδ).mpr
    nlinarith [mul_le_mul_of_nonneg_left hδw (show 0 ≤ 2 * b by positivity)]
  have hw1Window : window ≤ 1 :=
    hwBound.trans ((div_lt_one hδ).mpr (by linarith)).le
  have heActual : e ≤ w * b / 4 :=
    he.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hwδ hb.le) (by norm_num))
  have hraw := π.expectedOutcomeError_le_window P hH hbound hw hc hb hd he0 heActual hw1Window
  have hband := P.any_positiveAcceptanceBand_probability_uniform π.seedLaw hH hbound hδ hwδ hcδ hsum hb hL4 hL2 he0.le
  have hbandTerm := mul_le_mul_of_nonneg_left
    (add_le_add_left hband ((optimalScalarValue P w c - π.scalarObjective P w c) / e))
    (show 0 ≤ H + 1 by linarith)
  have hLd0 : 0 ≤ Ld := (P.tailCount_nonnegative d).trans hLd
  have htail0 := mul_le_mul_of_nonneg_left hLd (mul_nonneg hH hw0)
  have htail1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hwBound hH) hLd0
  change H * window * P.tailCount d ≤ H * window * Ld at htail0
  change H * window * Ld ≤ H * (2 * b / δ) * Ld at htail1
  have hcoef : H * (2 * b / δ) * Ld = (2 * H * b / δ) * Ld := by ring
  rw [hcoef] at htail1
  change π.expectedOutcomeError P w c ≤ window +
    (H + 1) * ((optimalScalarValue P w c - π.scalarObjective P w c) / e +
      (P.worldLaw π.seedLaw).real {ω : π.World | ∃ i,
        b ≤ ω.1 i ∧ |w * ω.1 i - P.continuationAtArrival w c ω.1 ω.2.1 i| ≤ e}) +
    d + H * window * P.tailCount d at hraw
  nlinarith

end ProphetSecretary.Model


