import ProphetSecretary.Statistics.StateFutureError

/-!
# Integrability of the actual state error

The bound by twice the finite number of identities serves only integrability.
It is proved under the actual reset law and transferred back by measure
preservation; statistical moment constants do not use this dimension bound.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma Instance.empiricalFutureError_bounded (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (lo hi : ℝ) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      P.empiricalFutureError k lo hi q ≤ 2 * (n : ℝ) := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  let ℱ := ProphetSecretary.Probability.dataClockHistoryFiltration ((Fin n × Fin k) → ℝ) n
  let E := P.empiricalUniformResidualEnvelope k lo hi
  have hb : ∀ᵐ q ∂μ, ‖E q‖ ≤ (n : ℝ) := by
    filter_upwards [P.empiricalUniformResidualEnvelope_bounded (k := k) hbound lo hi] with q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (P.empiricalUniformResidualEnvelope_nonnegative lo hi q)]
    exact hq
  have h := ProphetSecretary.Probability.countableConditionalMaximum_bounded μ ℱ E
    ProphetSecretary.Probability.rationalObservationTime (Nat.cast_nonneg n) hb
  exact h.mono fun q hq => mul_le_mul_of_nonneg_left hq (by norm_num)

lemma Instance.restartedFutureError_bounded (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (lo hi : ℝ) {t : ℝ} (ht : t < 1) (u : Fin n → ℝ) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      P.restartedFutureError k lo hi t u q ≤ 2 * (n : ℝ) := by
  let A := ProphetSecretary.Probability.pendingClockSet t u
  have hA : ∀ j, ∀ᵐ x ∂(P.restrictTo A).law j, x ≤ 1 := fun j => hbound (stateEmbedding A j)
  have hp := P.normalizedRefreshedStateCoordinates_measurePreserving (k := k) ht u
  have hb := hp.quasiMeasurePreserving.ae ((P.restrictTo A).empiricalFutureError_bounded (k := k) hA
    (lo*(1-t)) (hi*(1-t)))
  have hcard : (A.card : ℝ) ≤ n := by
    have hn : A.card ≤ n := by simpa only [Fintype.card_fin] using Finset.card_le_univ A
    exact_mod_cast hn
  exact hb.mono fun q hq => hq.trans (by nlinarith only [hcard])

lemma Instance.stateFutureError_bounded (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (lo hi : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      P.stateFutureError k lo hi t q ≤ 2 * (n : ℝ) := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  have hp := ProphetSecretary.Probability.restartTrainingClocks_measurePreserving (n := n)
    (P.trainingCoordinateLaw k) ht0 ht1
  have hs : MeasurableSet {q | P.stateFutureError k lo hi t q ≤ 2*(n : ℝ)} :=
    measurableSet_le (P.measurable_stateFutureError lo hi t) measurable_const
  have hprod : ∀ᵐ qr ∂μ.prod μ,
      P.stateFutureError k lo hi t (ProphetSecretary.Probability.restartTrainingClocks t qr) ≤ 2*(n : ℝ) := by
    apply (Measure.ae_prod_iff_ae_ae (hp.measurable hs)).mpr
    exact Eventually.of_forall fun q => by
      have hv : ∀ᵐ r ∂μ, ∀ i, 0 ≤ r.2 i :=
        (measurePreserving_snd (μ := P.trainingCoordinateLaw k) (ν := Instance.clocksLaw n)).quasiMeasurePreserving.ae
          ((Instance.clocks_mem_unitInterval (n := n)).mono fun _ h => fun i => (h i).1)
      filter_upwards [hv, P.restartedFutureError_bounded (k := k) hbound lo hi ht1 q.2] with r hr hb
      rw [P.stateFutureError_restart lo hi ht1 q r hr]
      exact hb
  have he := ae_map_iff (μ := μ.prod μ) hp.measurable.aemeasurable hs
  have hmap : Measure.map (ProphetSecretary.Probability.restartTrainingClocks t) (μ.prod μ) = μ := hp.map_eq
  rw [hmap] at he
  exact he.mpr hprod

lemma Instance.integrable_stateFutureError_pow (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (lo hi : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) (p : ℕ) :
    Integrable (fun q => P.stateFutureError k lo hi t q ^ p)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
  apply Integrable.of_bound ((P.measurable_stateFutureError lo hi t).pow_const p).aestronglyMeasurable ((2*(n : ℝ))^p)
  filter_upwards [P.stateFutureError_bounded (k := k) hbound lo hi ht0 ht1] with q hq
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (P.stateFutureError_nonnegative lo hi t q) p)]
  exact pow_le_pow_left₀ (P.stateFutureError_nonnegative lo hi t q) hq p

end ProphetSecretary.Model
