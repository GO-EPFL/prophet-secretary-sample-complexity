import ProphetSecretary.Model.BellmanBase
import ProphetSecretary.Model.ContinuationTransport
import ProphetSecretary.Model.FirstArrival
import ProphetSecretary.Model.Reindex

/-!
# Finite Bellman continuation correspondence

A reached, rejected prefix determines an admissible policy on the remaining
independent instance. Value thresholds themselves transport to the child state's
value thresholds after changing duration's coefficient by the remaining horizon.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

lemma unseen_continuationHistory (A : Finset (Fin n)) (s : ℝ) (H : History n)
    (hH : ValidPrefix A s H) (K : History A.card) :
    unseen (continuationHistory A s H K) = (unseen K).map (stateEmbedding A) := by
  ext i
  by_cases hi : i ∈ A
  · let j := stateIndex A i hi
    have hej : stateEmbedding A j = i := stateEmbedding_stateIndex A i hi
    have hmem : i ∈ unseen (continuationHistory A s H K) ↔ j ∈ unseen K := by
      simp only [unseen, Finset.mem_filter, Finset.mem_univ, true_and,
        continuationHistory, dif_pos hi]
      cases K j <;> simp [continuationObservation]
    constructor
    · intro h
      exact Finset.mem_map.mpr ⟨j, hmem.mp h, hej⟩
    · intro h
      obtain ⟨k, hk, hki⟩ := Finset.mem_map.mp h
      have hkj : k = j := (stateEmbedding A).injective (hki.trans hej.symm)
      exact hmem.mpr (hkj ▸ hk)
  · obtain ⟨t, x, hobs, _ht⟩ := hH.2 i hi
    constructor
    · intro h
      simp only [unseen, Finset.mem_filter, Finset.mem_univ, true_and,
        continuationHistory, dif_neg hi, hobs, Option.some_ne_none] at h
    · intro h
      obtain ⟨j, _hj, hej⟩ := Finset.mem_map.mp h
      exact False.elim (hi (hej ▸ stateEmbedding_mem A j))

/-- Fix the original random seed and the observed prefix when comparing the
future policy with the child instance's full admissible policy class. -/
noncomputable def Policy.fixedContinuation (π : Policy Seed n) (A : Finset (Fin n))
    (r : Seed) (s : ℝ) (H : History n) : Policy Unit A.card where
  decide _ t j x K := (π.continuationRule A).decide (r, s, H) t j x K

lemma Policy.fixedContinuation_isMeasurable [MeasurableSpace Seed]
    (π : Policy Seed n) (hπ : π.IsMeasurable) (A : Finset (Fin n))
    (r : Seed) (s : ℝ) (H : History n) : (π.fixedContinuation A r s H).IsMeasurable := by
  exact (π.continuationRule_isMeasurable hπ A).comp
    (measurable_const.prodMk measurable_snd)

noncomputable def Policy.fixedContinuationPolicy [MeasurableSpace Seed]
    (π : Policy Seed n) (hπ : π.IsMeasurable) (A : Finset (Fin n))
    (r : Seed) (s : ℝ) (H : History n) : RandomizedPolicy A.card where
  Seed := Unit
  seedLaw := Measure.dirac ()
  rule := π.fixedContinuation A r s H
  measurable_rule := π.fixedContinuation_isMeasurable hπ A r s H

/-- Transported value thresholds are exactly the child instance's value
thresholds, with the duration coefficient multiplied by remaining time. This
identity concerns the decision rule and does not assume its optimality. -/
lemma Instance.valueThreshold_fixedContinuation (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c s : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (hs : s ≤ 1) (A : Finset (Fin n))
    (H : History n) (hH : ValidPrefix A s H) :
    (thresholdPolicy (fun (_ : Unit) B t i ↦ P.valueThreshold w c B t i)).fixedContinuation A () s H =
      thresholdPolicy (fun (_ : Unit) B t i ↦
        (P.restrictTo A).valueThreshold w (c * (1 - s)) B t i) := by
  unfold Policy.fixedContinuation Policy.continuationRule thresholdPolicy
  congr 1
  funext r t j x K
  have hth := P.valueThreshold_restrictBy (A.orderEmbOfFin rfl) (unseen K) j hP hw
    (mul_nonneg hc (sub_nonneg.mpr hs)) t
  have he : P.valueThreshold w c (unseen (continuationHistory A s H K))
      (s + (1 - s) * t) (stateEmbedding A j) =
      (P.restrictTo A).valueThreshold w (c * (1 - s)) (unseen K) t j := by
    rw [unseen_continuationHistory A s H hH K, P.valueThreshold_after_elapsed _ _ _ _ _ _ hs]
    exact hth.symm
  change decide (P.valueThreshold w c (unseen (continuationHistory A s H K))
    (s + (1 - s) * t) (stateEmbedding A j) ≤ x) =
    decide ((P.restrictTo A).valueThreshold w (c * (1 - s)) (unseen K) t j ≤ x)
  rw [he]

/-- Every finite independent clock is strictly positive almost surely. -/
lemma Instance.world_clocks_positive {m : ℕ} {S : Type*} [MeasurableSpace S]
    (Q : Instance m) (ν : Measure S) [IsProbabilityMeasure ν] :
    ∀ᵐ ω : World m S ∂Q.worldLaw ν, ∀ j, 0 < ω.2.1 j := by
  rw [ae_all_iff]
  intro j
  have hn := (Q.world_clock_measurePreserving ν j).quasiMeasurePreserving.ae
    (Instance.uniformClock.ae_ne 0)
  filter_upwards [Q.world_clocks_mem_unitInterval ν, hn] with ω h01 hne
  exact lt_of_le_of_ne (h01 j).1 hne.symm

/-- Equality of the actual additional scalar payoff and the transported child's
objective under independent future offers and clocks. The reached prefix remains
fixed throughout the future experiment. -/
lemma Policy.continuationObjective_eq [MeasurableSpace Seed]
    (π : Policy Seed n) (hπ : π.IsMeasurable) (P : Instance n)
    (A : Finset (Fin n)) (r : Seed) {s : ℝ} (hs : s < 1)
    (H : History n) (hH : ValidPrefix A s H) (hReject : PrefixRejected π r A H) (w c : ℝ) :
    (∫ ω : World A.card Unit,
      (w * π.reward r Finset.univ (extendValues A H ω.1) (extendClocks A s H ω.2.1) +
        c * (π.stoppingTime r Finset.univ (extendValues A H ω.1)
          (extendClocks A s H ω.2.1) - s)) ∂(P.restrictTo A).worldLaw (Measure.dirac ())) =
      (π.fixedContinuationPolicy hπ A r s H).scalarObjective (P.restrictTo A) w (c * (1 - s)) := by
  apply integral_congr_ae
  filter_upwards [(P.restrictTo A).world_clocks_positive (Measure.dirac ())] with ω hω
  exact π.scalarPayoff_extend A hs H hH r ω.1 ω.2.1 hω hReject w c

lemma Policy.integrable_continuationPayoff [MeasurableSpace Seed]
    (π : Policy Seed n) (hπ : π.IsMeasurable) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    (A : Finset (Fin n)) (r : Seed) {s : ℝ} (hs : s < 1)
    (H : History n) (hH : ValidPrefix A s H) (hReject : PrefixRejected π r A H) (w c : ℝ) :
    Integrable (fun ω : World A.card Unit ↦
      w * π.reward r Finset.univ (extendValues A H ω.1) (extendClocks A s H ω.2.1) +
        c * (π.stoppingTime r Finset.univ (extendValues A H ω.1)
          (extendClocks A s H ω.2.1) - s)) ((P.restrictTo A).worldLaw (Measure.dirac ())) := by
  let C := π.fixedContinuationPolicy hπ A r s H
  have hInt := ((C.integrable_realizedReward (P.restrictTo A)
    (P.restrictTo_integrable_maximum A hP)).const_mul w).add
      ((C.integrable_realizedDuration (P.restrictTo A)).const_mul (c * (1 - s)))
  apply hInt.congr
  filter_upwards [(P.restrictTo A).world_clocks_positive (Measure.dirac ())] with ω hω
  exact (π.scalarPayoff_extend A hs H hH r ω.1 ω.2.1 hω hReject w c).symm

/-- Every original history-dependent randomized competitor has continuation
value at most the child optimum. The original seed is held fixed here; first-arrival
law transport justifies averaging this bound over the observed prefix afterwards. -/
lemma Policy.continuationObjective_le_optimal [MeasurableSpace Seed]
    (π : Policy Seed n) (hπ : π.IsMeasurable) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    (A : Finset (Fin n)) (r : Seed) {s : ℝ} (hs : s < 1)
    (H : History n) (hH : ValidPrefix A s H) (hReject : PrefixRejected π r A H)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (∫ ω : World A.card Unit,
      (w * π.reward r Finset.univ (extendValues A H ω.1) (extendClocks A s H ω.2.1) +
        c * (π.stoppingTime r Finset.univ (extendValues A H ω.1)
          (extendClocks A s H ω.2.1) - s)) ∂(P.restrictTo A).worldLaw (Measure.dirac ())) ≤
      optimalScalarValue (P.restrictTo A) w (c * (1 - s)) := by
  rw [π.continuationObjective_eq hπ P A r hs H hH hReject w c]
  exact scalarObjective_le_optimal _ (P.restrictTo A)
    (P.restrictTo_integrable_maximum A hP) hw (mul_nonneg hc (sub_nonneg.mpr hs.le))

/-- Before invoking induction, the canonical continuation's objective is exactly
the child value-policy objective. This does not postulate the child's optimality. -/
lemma Instance.valuePolicy_continuationObjective (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c s : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (hs : s ≤ 1)
    (A : Finset (Fin n)) (H : History n) (hH : ValidPrefix A s H) :
    ((P.valuePolicy hP hw hc).rule.fixedContinuationPolicy
      (P.valuePolicy hP hw hc).measurable_rule A () s H).scalarObjective
      (P.restrictTo A) w (c * (1 - s)) =
      ((P.restrictTo A).valuePolicy (P.restrictTo_integrable_maximum A hP) hw
        (mul_nonneg hc (sub_nonneg.mpr hs))).scalarObjective (P.restrictTo A) w (c * (1 - s)) := by
  simp only [Policy.fixedContinuationPolicy, Instance.valuePolicy,
    RandomizedPolicy.scalarObjective, RandomizedPolicy.realizedReward, RandomizedPolicy.realizedDuration]
  rw [P.valueThreshold_fixedContinuation hP hw hc hs A H hH]
  rfl

end ProphetSecretary.Model
