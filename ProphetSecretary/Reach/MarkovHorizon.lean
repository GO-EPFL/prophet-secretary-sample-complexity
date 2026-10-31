import ProphetSecretary.Reach.ReachHorizonRescaling
import ProphetSecretary.Reach.MarkovStrict

/-!
# Extended Markov comparisons on a remaining horizon

The physical-time acceptance rule is required to be deletion monotone only on `[0,h]`.
The existing complete-history rescaling derives the unit-horizon rule, so the normalized
duration is `E[τ]/h`. Infinite thresholds and arbitrary future observations are retained.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

def DeletionMonotoneAcceptanceAt
    (accept : Seed → Finset (Fin n) → ℝ → Fin n → ℝ → Bool) (h : ℝ) : Prop :=
  ∀ r t, t ∈ Icc (0 : ℝ) h → ∀ i x, 0 ≤ x → ∀ A B,
    i ∈ A → A ⊆ B → accept r B t i x = true → accept r A t i x = true

lemma markovPolicy_onUnitHorizon
    (accept : Seed → Finset (Fin n) → ℝ → Fin n → ℝ → Bool) (h : ℝ) :
    (markovPolicy accept).onUnitHorizon h =
      markovPolicy (fun r A t i x => accept r A (h * t) i x) := by
  unfold Policy.onUnitHorizon markovPolicy
  congr 1
  funext r t i x H
  simp only [unseen_scaleHistory]

lemma DeletionMonotoneAcceptanceAt.timeScale
    (accept : Seed → Finset (Fin n) → ℝ → Fin n → ℝ → Bool) {h : ℝ}
    (ha : DeletionMonotoneAcceptanceAt accept h) (hh : 0 < h) :
    DeletionMonotoneAcceptance (fun r A t i x => accept r A (h * t) i x) := by
  intro r t ht i x hx A B hi hAB hacc
  have htime : h * t ∈ Icc (0 : ℝ) h := by
    refine ⟨mul_nonneg hh.le ht.1, ?_⟩
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht.2 hh.le
  exact ha r (h * t) htime i x hx A B hi hAB hacc

def MonotoneExtendedThresholdsAt
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → EReal) (h : ℝ) : Prop :=
  ∀ r t, t ∈ Icc (0 : ℝ) h → ∀ i A B, i ∈ A → A ⊆ B → θ r A t i ≤ θ r B t i

lemma extendedThresholdPolicy.deletionMonotoneAt
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → EReal) {h : ℝ} (hθ : MonotoneExtendedThresholdsAt θ h) :
    DeletionMonotoneAcceptanceAt (fun r A t i x => decide (θ r A t i ≤ (x : EReal))) h := by
  intro r t ht i x _hx A B hi hAB hacc
  simp only [decide_eq_true_eq] at hacc ⊢
  exact (hθ r t ht i A B hi hAB).trans hacc

variable [MeasurableSpace Seed]

theorem markovPolicy.strict_reachAt
    (accept : Seed → Finset (Fin n) → ℝ → Fin n → ℝ → Bool) {h : ℝ}
    (ha : DeletionMonotoneAcceptanceAt accept h) (hπ : (markovPolicy accept).IsMeasurable)
    (hh : 0 < h) (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    (markovPolicy accept).reachProbabilityAt h P ν i -
      (markovPolicy accept).meanDurationAt h P ν / h ≥
      ((markovPolicy accept).selectionProbabilityAt h P ν i) ^ 2 / 2 := by
  rw [(markovPolicy accept).reachProbabilityAt_eq hh,
    (markovPolicy accept).meanDurationAt_div_eq hh,
    (markovPolicy accept).selectionProbabilityAt_eq hh]
  have hm := (markovPolicy accept).onUnitHorizon_isMeasurable hπ h
  rw [markovPolicy_onUnitHorizon] at hm ⊢
  exact markovPolicy.strict_reach _ (DeletionMonotoneAcceptanceAt.timeScale accept ha hh) hm P ν i

theorem extendedThresholdPolicy.strict_reachAt
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → EReal) {h : ℝ}
    (hθ : MonotoneExtendedThresholdsAt θ h) (hπ : (extendedThresholdPolicy θ).IsMeasurable)
    (hh : 0 < h) (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    (extendedThresholdPolicy θ).reachProbabilityAt h P ν i -
      (extendedThresholdPolicy θ).meanDurationAt h P ν / h ≥
      ((extendedThresholdPolicy θ).selectionProbabilityAt h P ν i) ^ 2 / 2 :=
  markovPolicy.strict_reachAt _ (extendedThresholdPolicy.deletionMonotoneAt θ hθ) hπ hh P ν i

theorem extendedThresholdPolicy.normalizedDuration_le_reachProbabilityAt
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → EReal) {h : ℝ}
    (hθ : MonotoneExtendedThresholdsAt θ h) (hπ : (extendedThresholdPolicy θ).IsMeasurable)
    (hh : 0 < h) (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    (extendedThresholdPolicy θ).meanDurationAt h P ν / h ≤
      (extendedThresholdPolicy θ).reachProbabilityAt h P ν i := by
  have hs := extendedThresholdPolicy.strict_reachAt θ hθ hπ hh P ν i
  nlinarith [sq_nonneg ((extendedThresholdPolicy θ).selectionProbabilityAt h P ν i)]

end ProphetSecretary.Model
