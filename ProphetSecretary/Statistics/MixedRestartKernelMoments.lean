import ProphetSecretary.Statistics.RestrictedTrainingState
import ProphetSecretary.Statistics.MixedEmpiricalFutureError

/-!
# Genuine fresh-state kernel moments for mixed laws

Restricted training and normalized refreshed pending clocks have the constructed
child-state product law. Known labels restrict along the same identity embedding.
The actual localized mixed all-future moments transfer with unchanged constants
for every fixed prefix; no random-entrance independence is assumed.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def Instance.mixedRestartedFutureError (P : Instance n) (known : Finset (Fin n)) (k : ℕ) [NeZero k]
    (lo hi t : ℝ) (u : Fin n → ℝ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) : ℝ :=
  let A := ProphetSecretary.Probability.pendingClockSet t u
  (P.restrictTo A).mixedFutureError (knownInState known A) k (lo*(1-t)) (hi*(1-t))
    (normalizedRefreshedStateCoordinates t u q)

lemma Instance.measurable_mixedRestartedFutureError (P : Instance n) (known : Finset (Fin n)) (lo hi : ℝ)
    {t : ℝ} (ht : t < 1) (u : Fin n → ℝ) : Measurable (P.mixedRestartedFutureError known k lo hi t u) :=
  ((P.restrictTo (ProphetSecretary.Probability.pendingClockSet t u)).measurable_mixedFutureError
    (knownInState known (ProphetSecretary.Probability.pendingClockSet t u)) _ _).comp
    (P.normalizedRefreshedStateCoordinates_measurePreserving ht u).measurable

/-- The second moment uses genuine restricted samples and fresh pending clocks. -/
theorem Instance.mixedRestartedFutureError_secondMoment (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi t a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (u : Fin n → ℝ)
    (hValue : P.continuationValue (ProphetSecretary.Probability.pendingClockSet t u) (1-t) 1 hi ≤ a) :
    Integrable (fun q => P.mixedRestartedFutureError known k lo hi t u q ^ 2)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
    (∫ q, P.mixedRestartedFutureError known k lo hi t u q ^ 2
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      (16 * (18 * (128 + 4 * (hi-lo)^2 / hi))) * (a / (k : ℝ) + 1 / (k : ℝ)^2) := by
  let A := ProphetSecretary.Probability.pendingClockSet t u
  have hA : ∀ j, ∀ᵐ x ∂(P.restrictTo A).law j, x ≤ 1 := fun j => hbound (stateEmbedding A j)
  have hm := (P.restrictTo A).mixedFutureError_secondMoment_localized (k := k) (knownInState known A) hA hlo hlohi hhi
    (sub_nonneg.mpr ht1.le) (by linarith : 1-t ≤ 1) hValue
  have hp := P.normalizedRefreshedStateCoordinates_measurePreserving (k := k) ht1 u
  have hEq := integral_map (μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))
    hp.measurable.aemeasurable
    (((P.restrictTo A).measurable_mixedFutureError (knownInState known A) (lo*(1-t)) (hi*(1-t))).pow_const 2).aestronglyMeasurable
  rw [hp.map_eq] at hEq
  exact ⟨hp.integrable_comp_of_integrable hm.1, hEq.symm.trans_le hm.2⟩

/-- The sixth moment transfers through exactly the same reset kernel. -/
theorem Instance.mixedRestartedFutureError_sixthMoment (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi t a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi) (ht0 : 0 ≤ t) (ht1 : t < 1)
    (u : Fin n → ℝ)
    (hValue : P.continuationValue (ProphetSecretary.Probability.pendingClockSet t u) (1-t) 1 hi ≤ a) :
    Integrable (fun q => P.mixedRestartedFutureError known k lo hi t u q ^ 6)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
    (∫ q, P.mixedRestartedFutureError known k lo hi t u q ^ 6
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      (832 * (23328 * (2 * (6672000000000 ^ 2 + 13348000000000) +
        (106000000000 ^ 2 + 212000000000) * (hi-lo)^6 / hi^3))) *
        (a^3 / (k : ℝ)^3 + 1 / (k : ℝ)^6) := by
  let A := ProphetSecretary.Probability.pendingClockSet t u
  have hA : ∀ j, ∀ᵐ x ∂(P.restrictTo A).law j, x ≤ 1 := fun j => hbound (stateEmbedding A j)
  have hm := (P.restrictTo A).mixedFutureError_sixthMoment_localized (k := k) (knownInState known A) hA hlo hlohi hhi
    (sub_nonneg.mpr ht1.le) (by linarith : 1-t ≤ 1) hValue
  have hp := P.normalizedRefreshedStateCoordinates_measurePreserving (k := k) ht1 u
  have hEq := integral_map (μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))
    hp.measurable.aemeasurable
    (((P.restrictTo A).measurable_mixedFutureError (knownInState known A) (lo*(1-t)) (hi*(1-t))).pow_const 6).aestronglyMeasurable
  rw [hp.map_eq] at hEq
  exact ⟨hp.integrable_comp_of_integrable hm.1, hEq.symm.trans_le hm.2⟩

end ProphetSecretary.Model
