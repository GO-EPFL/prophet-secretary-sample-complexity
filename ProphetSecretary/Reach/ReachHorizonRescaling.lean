import ProphetSecretary.Reach.FiniteStrictReach

/-!
# Remaining horizons

A physical execution on `[0,h]` observes physical timestamps and uses terminal
time `h`. Scaling the complete history and the current timestamp converts it to
the unit-horizon policy class without dropping observations.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

/-- The scaled clock law is normalized Lebesgue measure on `[0,h]`. -/
theorem scaled_uniformClock_eq {h : ℝ} (hh : 0 < h) :
    Instance.uniformClock.map (fun t : ℝ ↦ h * t) =
      ENNReal.ofReal h⁻¹ • volume.restrict (Icc (0 : ℝ) h) := by
  have hpre : (fun t : ℝ ↦ h * t) ⁻¹' Icc (0 : ℝ) h = Icc (0 : ℝ) 1 := by
    ext t
    simp only [mem_preimage, mem_Icc]
    constructor
    · rintro ⟨h0, h1⟩
      constructor <;> nlinarith
    · rintro ⟨h0, h1⟩
      exact ⟨mul_nonneg hh.le h0, by nlinarith⟩
  unfold Instance.uniformClock
  rw [← hpre, ← Measure.restrict_map (f := fun t : ℝ ↦ h * t) (measurable_const.mul measurable_id) measurableSet_Icc,
    Real.map_volume_mul_left hh.ne', Measure.restrict_smul, abs_of_pos (inv_pos.mpr hh)]

/-- Multiply the timestamp of an observed offer, retaining its value and identity. -/
def scaleObservation (h : ℝ) : Option (ℝ × ℝ) → Option (ℝ × ℝ) :=
  Option.map (fun p ↦ (h * p.1, p.2))

def scaleHistory (h : ℝ) (H : History n) : History n :=
  fun j ↦ scaleObservation h (H j)

/-- A physical policy transported to a unit horizon. It sees scaled current
and historical times, and retains the complete seed and observed values. -/
def Policy.onUnitHorizon (π : Policy Seed n) (h : ℝ) : Policy Seed n where
  decide r t i x H := π.decide r (h * t) i x (scaleHistory h H)

/-- An execution whose terminal convention is the physical horizon `h`. -/
noncomputable def Policy.stoppingTimeAt (π : Policy Seed n) (h : ℝ) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) : ℝ :=
  (insert h ((π.accepted r D x u).image u)).min' ⟨h, Finset.mem_insert_self _ _⟩

theorem scaleHistory_history {h : ℝ} (hh : 0 < h)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (t : ℝ) :
    scaleHistory h (history D x u t) = history D x (fun j ↦ h * u j) (h * t) := by
  funext j
  simp only [scaleHistory, scaleObservation, history, mul_lt_mul_iff_right₀ hh]
  split_ifs <;> rfl

theorem Policy.action_onUnitHorizon (π : Policy Seed n) {h : ℝ} (hh : 0 < h)
    (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) (j : Fin n) :
    (π.onUnitHorizon h).action r D x u j = π.action r D x (fun j ↦ h * u j) j := by
  simp only [Policy.action, Policy.onUnitHorizon, scaleHistory_history hh]

theorem Policy.accepted_onUnitHorizon (π : Policy Seed n) {h : ℝ} (hh : 0 < h)
    (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    (π.onUnitHorizon h).accepted r D x u = π.accepted r D x (fun j ↦ h * u j) := by
  ext j
  simp only [Policy.mem_accepted, π.action_onUnitHorizon hh]

theorem Policy.stoppingTimeAt_scale (π : Policy Seed n) {h : ℝ} (hh : 0 < h)
    (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    π.stoppingTimeAt h r D x (fun j ↦ h * u j) =
      h * (π.onUnitHorizon h).stoppingTime r D x u := by
  have hset : insert h ((π.accepted r D x (fun j ↦ h * u j)).image (fun j ↦ h * u j)) =
      ((π.onUnitHorizon h).stopTimes r D x u).image (fun t ↦ h * t) := by
    rw [Policy.stopTimes, Finset.image_insert, Finset.image_image,
      π.accepted_onUnitHorizon hh]
    simp only [mul_one, Function.comp_def]
  unfold Policy.stoppingTimeAt Policy.stoppingTime
  simp only [hset]
  exact Finset.min'_image (fun a b hab ↦ mul_le_mul_of_nonneg_left hab hh.le) _ _

/-- The absent observation stays absent under time scaling. -/
@[simp] theorem scaleObservation_eq_none (h : ℝ) (o : Option (ℝ × ℝ)) :
    scaleObservation h o = none ↔ o = none := by
  cases o <;> simp [scaleObservation]

theorem unseen_scaleHistory (h : ℝ) (H : History n) :
    unseen (scaleHistory h H) = unseen H := by
  ext j
  simp [unseen, scaleHistory]

theorem thresholdPolicy_onUnitHorizon
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → ℝ) (h : ℝ) :
    (thresholdPolicy θ).onUnitHorizon h = thresholdPolicy (fun r A t i ↦ θ r A (h * t) i) := by
  unfold Policy.onUnitHorizon thresholdPolicy
  congr 1
  funext r t i x H
  simp only [unseen_scaleHistory]

/-- Physical-horizon reach; the terminal convention is `h`. -/
def Policy.ReachesAt (π : Policy Seed n) (h : ℝ) (r : Seed)
    (x u : Fin n → ℝ) (i : Fin n) : Prop :=
  u i ≤ π.stoppingTimeAt h r Finset.univ x u

def Policy.SelectsAt (π : Policy Seed n) (h : ℝ) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (i : Fin n) : Prop :=
  i ∈ π.accepted r D x u ∧ u i = π.stoppingTimeAt h r D x u

def Policy.ActualSelectsAt (π : Policy Seed n) (h : ℝ) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (i : Fin n) : Prop :=
  π.SelectsAt h r D x u i ∧ ∀ j, π.SelectsAt h r D x u j → i ≤ j

theorem Policy.reachesAt_scale (π : Policy Seed n) {h : ℝ} (hh : 0 < h)
    (r : Seed) (x u : Fin n → ℝ) (i : Fin n) :
    π.ReachesAt h r x (fun j ↦ h * u j) i ↔ (π.onUnitHorizon h).Reaches r x u i := by
  simp only [Policy.ReachesAt, Policy.Reaches, π.stoppingTimeAt_scale hh,
    mul_le_mul_iff_right₀ hh]

theorem Policy.selectsAt_scale (π : Policy Seed n) {h : ℝ} (hh : 0 < h)
    (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) (i : Fin n) :
    π.SelectsAt h r D x (fun j ↦ h * u j) i ↔ (π.onUnitHorizon h).Selects r D x u i := by
  simp only [Policy.SelectsAt, Policy.Selects, π.stoppingTimeAt_scale hh,
    ← π.accepted_onUnitHorizon hh, mul_right_inj' hh.ne']

theorem Policy.actualSelectsAt_scale (π : Policy Seed n) {h : ℝ} (hh : 0 < h)
    (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) (i : Fin n) :
    π.ActualSelectsAt h r D x (fun j ↦ h * u j) i ↔
      (π.onUnitHorizon h).ActualSelects r D x u i := by
  simp only [Policy.ActualSelectsAt, Policy.ActualSelects, π.selectsAt_scale hh]

section Measurability

variable [MeasurableSpace Seed]

theorem measurable_scaleObservation (h : ℝ) : Measurable (scaleObservation h) := by
  let code : Option (ℝ × ℝ) → Unit ⊕ (ℝ × ℝ) :=
    fun o ↦ match o with | none => Sum.inl () | some p => Sum.inr p
  have hc : Measurable code := by
    exact Measurable.of_comap_le le_rfl
  have hm : Measurable (Sum.map (id : Unit → Unit) (fun p : ℝ × ℝ ↦ (h * p.1, p.2))) :=
    measurable_id.sumMap ((measurable_const.mul measurable_fst).prodMk measurable_snd)
  rw [measurable_comap_iff]
  convert hm.comp hc using 1
  funext o
  cases o <;> rfl

theorem measurable_scaleHistory (h : ℝ) : Measurable (scaleHistory (n := n) h) := by
  apply measurable_pi_lambda
  intro j
  exact (measurable_scaleObservation h).comp (measurable_pi_apply j)

theorem Policy.onUnitHorizon_isMeasurable (π : Policy Seed n) (hπ : π.IsMeasurable)
    (h : ℝ) : (π.onUnitHorizon h).IsMeasurable := by
  unfold Policy.IsMeasurable Policy.onUnitHorizon
  exact hπ.comp (measurable_fst.prodMk
    ((measurable_const.mul (measurable_fst.comp measurable_snd)).prodMk
      ((measurable_fst.comp (measurable_snd.comp measurable_snd)).prodMk
        ((measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))).prodMk
          ((measurable_scaleHistory h).comp
            (measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))))))))

/-- A scaled arrival coordinate has the physical uniform law. Independence
of all clocks is retained by applying this deterministic map separately. -/
theorem Instance.world_physical_clock_map (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] {h : ℝ} (hh : 0 < h) (i : Fin n) :
    (P.worldLaw ν).map (fun ω : World n Seed ↦ h * ω.2.1 i) =
      ENNReal.ofReal h⁻¹ • volume.restrict (Icc (0 : ℝ) h) := by
  have hm : Measurable (fun ω : World n Seed ↦ ω.2.1 i) :=
    (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)
  rw [← Function.comp_def, ← Measure.map_map (g := fun t : ℝ ↦ h * t) (measurable_const.mul measurable_id) hm,
    P.world_clock_map ν i, scaled_uniformClock_eq hh]

/-- The physical experiment uses independent unit clocks multiplied by `h`.
Thus each clock is a uniform on `[0,h]`, with every observed timestamp retained. -/
noncomputable def Policy.reachProbabilityAt (π : Policy Seed n) (h : ℝ)
    (P : Instance n) (ν : Measure Seed) (i : Fin n) : ℝ :=
  (P.worldLaw ν).real {ω : World n Seed |
    π.ReachesAt h ω.2.2 ω.1 (fun j ↦ h * ω.2.1 j) i}

noncomputable def Policy.selectionProbabilityAt (π : Policy Seed n) (h : ℝ)
    (P : Instance n) (ν : Measure Seed) (i : Fin n) : ℝ :=
  (P.worldLaw ν).real {ω : World n Seed |
    π.ActualSelectsAt h ω.2.2 Finset.univ ω.1 (fun j ↦ h * ω.2.1 j) i}

/-- Additional stopping time from the state's start, with default value `h`. -/
noncomputable def Policy.meanDurationAt (π : Policy Seed n) (h : ℝ)
    (P : Instance n) (ν : Measure Seed) : ℝ :=
  ∫ ω : World n Seed,
    π.stoppingTimeAt h ω.2.2 Finset.univ ω.1 (fun j ↦ h * ω.2.1 j) ∂P.worldLaw ν

theorem Policy.reachProbabilityAt_eq (π : Policy Seed n) {h : ℝ} (hh : 0 < h)
    (P : Instance n) (ν : Measure Seed) (i : Fin n) :
    π.reachProbabilityAt h P ν i = (π.onUnitHorizon h).reachProbability P ν i := by
  simp only [Policy.reachProbabilityAt, Policy.reachProbability, π.reachesAt_scale hh]

theorem Policy.selectionProbabilityAt_eq (π : Policy Seed n) {h : ℝ} (hh : 0 < h)
    (P : Instance n) (ν : Measure Seed) (i : Fin n) :
    π.selectionProbabilityAt h P ν i = (π.onUnitHorizon h).selectionProbability P ν i := by
  simp only [Policy.selectionProbabilityAt, Policy.selectionProbability, π.actualSelectsAt_scale hh]

theorem Policy.meanDurationAt_eq_mul (π : Policy Seed n) {h : ℝ} (hh : 0 < h)
    (P : Instance n) (ν : Measure Seed) :
    π.meanDurationAt h P ν = h * (π.onUnitHorizon h).meanDuration P ν := by
  simp only [Policy.meanDurationAt, π.stoppingTimeAt_scale hh, integral_const_mul,
    Policy.meanDuration]

theorem Policy.meanDurationAt_div_eq (π : Policy Seed n) {h : ℝ} (hh : 0 < h)
    (P : Instance n) (ν : Measure Seed) :
    π.meanDurationAt h P ν / h = (π.onUnitHorizon h).meanDuration P ν := by
  rw [π.meanDurationAt_eq_mul hh]
  exact mul_div_cancel_left₀ _ hh.ne'

/-- The universal finite comparison on a remaining horizon `h>0`, with
expected duration divided by `h` as in `lem:monotone-reach`. -/
theorem Policy.reachProbabilityAt_le_twice_normalized_duration (π : Policy Seed n)
    (hπ : π.IsMeasurable) {h : ℝ} (hh : 0 < h)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    π.reachProbabilityAt h P ν i ≤ 2 * (π.meanDurationAt h P ν / h) := by
  rw [π.reachProbabilityAt_eq hh, π.meanDurationAt_div_eq hh]
  exact (π.onUnitHorizon h).reachProbability_le_twice_meanDuration
    (π.onUnitHorizon_isMeasurable hπ h) P ν i

omit [MeasurableSpace Seed] in
/-- Threshold monotonicity is retained by changing the time unit. -/
theorem monotoneThresholds_timeScale
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → ℝ) (hθ : MonotoneThresholds θ) (h : ℝ) :
    MonotoneThresholds (fun r A t i ↦ θ r A (h * t) i) := by
  intro r t i A B hi hAB
  exact hθ r (h * t) i A B hi hAB

/-- The strict finite comparison on a remaining horizon, derived from the
execution equivalence with the unit horizon rather than assumed normalization. -/
theorem thresholdPolicy.strict_reachAt
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → ℝ)
    (hθ : MonotoneThresholds θ) (hπ : (thresholdPolicy θ).IsMeasurable)
    {h : ℝ} (hh : 0 < h) (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin n) :
    (thresholdPolicy θ).reachProbabilityAt h P ν i -
      (thresholdPolicy θ).meanDurationAt h P ν / h ≥
      ((thresholdPolicy θ).selectionProbabilityAt h P ν i) ^ 2 / 2 := by
  rw [(thresholdPolicy θ).reachProbabilityAt_eq hh,
    (thresholdPolicy θ).meanDurationAt_div_eq hh,
    (thresholdPolicy θ).selectionProbabilityAt_eq hh]
  have hm := (thresholdPolicy θ).onUnitHorizon_isMeasurable hπ h
  rw [thresholdPolicy_onUnitHorizon] at hm ⊢
  exact thresholdPolicy.strict_reach _ (monotoneThresholds_timeScale θ hθ h) hm P ν i

end Measurability

end ProphetSecretary.Model
