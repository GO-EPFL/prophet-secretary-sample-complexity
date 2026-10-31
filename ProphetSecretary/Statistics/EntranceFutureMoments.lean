import ProphetSecretary.Statistics.EntranceFutureError
import ProphetSecretary.Statistics.GridEntranceUnweightedMoments
import ProphetSecretary.Statistics.PostRemainingSizeMeasurability
import ProphetSecretary.Probability.WeightedEnvelopeFatou

/-!
# Actual critical-entrance envelope moments

The concrete lower-limit envelope has both the localized moments and the
remaining-size weighted moments needed by the loss integrals. Every ingredient
is from the actual training/clock product law: uniform grid moments, no-atom
state stabilization, and the verified weighted Fatou theorem. No independence
between the entrance error and remaining size is assumed.
-/

open MeasureTheory Set Filter
open scoped Classical Topology BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

/-- The paper's post-arrival B_a, determined by true laws and clocks only. -/
noncomputable def Instance.entranceRemainingSize (P : Instance n) (hi a : ℝ) (u : Fin n → ℝ) : ℝ :=
  P.postRemainingSize (P.trueCriticalEntrance hi a u) u

omit [NeZero k] in
lemma Instance.measurable_entranceRemainingSize (P : Instance n) (hi a : ℝ) :
    Measurable (P.entranceRemainingSize hi a) := P.measurable_trueEntrance_postSize hi a

omit [NeZero k] in
lemma Instance.entranceRemainingSize_mem (P : Instance n) (hi a : ℝ) (u : Fin n → ℝ) :
    P.entranceRemainingSize hi a u ∈ Icc (0 : ℝ) (P.totalFirstMoment+1) :=
  P.postRemainingSize_mem (P.trueCriticalEntrance_mem hi a u).1 (P.trueCriticalEntrance_mem hi a u).2 u

/-- Unweighted localized moments of E_a at the actual true entrance. -/
theorem Instance.entranceFutureError_moment (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a : ℝ}
    (hlo : 0≤lo) (hlohi : lo≤hi) (hhi : 0<hi) (ha : 0≤a) {p : ℕ} (hp : p=2 ∨ p=6) :
    Integrable (fun q => P.entranceFutureError k lo hi a q^p)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
    (∫ q, P.entranceFutureError k lo hi a q^p ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalRestartMomentBound k lo hi a p := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  let E : ℕ → (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ := fun m =>
    P.gridEntranceError k (ProphetSecretary.Statistics.dyadicEntranceGrid m) lo hi a (2^m)
  have hEm (m) : Measurable (E m) := P.measurable_gridEntranceError _
    (ProphetSecretary.Statistics.dyadicEntranceGrid_monotone m) lo hi a _
  have hE0 (m q) : 0≤E m q := P.gridEntranceError_nonnegative _ lo hi a _ q
  have hEB (m) : ∀ᵐ q ∂μ, E m q ≤ 2*(n:ℝ) := P.gridEntranceError_bounded hbound _ lo hi a _
    (fun j _ => ProphetSecretary.Statistics.dyadicEntranceGrid_mem m j)
  have hGrid (m) := P.gridEntranceError_moment (k:=k) hbound hlo hlohi hhi ha _
    (ProphetSecretary.Statistics.dyadicEntranceGrid_monotone m) (2^m)
    (fun j _ => ProphetSecretary.Statistics.dyadicEntranceGrid_mem m j) hp
  have hp0 : 0<p := by rcases hp with rfl|rfl <;> omega
  have hK := empiricalRestartMomentBound_nonnegative k (lo:=lo) hhi ha p
  have h := ProphetSecretary.Probability.weighted_lowerLimitEnvelope_moment μ
    (E:=E) (W:=fun _ _ => (1:ℝ)) (w:=fun _ => (1:ℝ))
    hEm (fun _ => measurable_const) measurable_const hE0 (fun _ _ => zero_le_one) (fun _ => zero_le_one)
    (D:=2*(n:ℝ)) (C:=1) (K:=empiricalRestartMomentBound k lo hi a p)
    (by positivity) zero_le_one hK hEB (Eventually.of_forall fun _ => le_rfl)
    (Eventually.of_forall fun _ => tendsto_const_nhds) hp0
    (fun m => by simpa only [one_mul] using (hGrid m).1)
    (fun m => by simpa only [one_mul] using (hGrid m).2)
  change Integrable (fun q => ProphetSecretary.Probability.lowerLimitEnvelope E q^p) μ ∧
    (∫ q, ProphetSecretary.Probability.lowerLimitEnvelope E q^p ∂μ) ≤ _
  simpa only [one_mul] using h

/-- Weighted moments pass to the actual POST-arrival remaining size B_a. -/
theorem Instance.entranceFutureError_weighted_moment (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a : ℝ}
    (hlo : 0≤lo) (hlohi : lo≤hi) (hhi : 0<hi) (ha : 0≤a) {p : ℕ} (hp : p=2 ∨ p=6) :
    Integrable (fun q => P.entranceRemainingSize hi a q.2 * P.entranceFutureError k lo hi a q^p)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
    (∫ q, P.entranceRemainingSize hi a q.2 * P.entranceFutureError k lo hi a q^p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalRestartMomentBound k lo hi a p * (a*(1+P.totalFirstMoment)/hi) := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  let E : ℕ → (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ := fun m =>
    P.gridEntranceError k (ProphetSecretary.Statistics.dyadicEntranceGrid m) lo hi a (2^m)
  let W : ℕ → (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ := fun m =>
    P.gridEntranceSize k (ProphetSecretary.Statistics.dyadicEntranceGrid m) hi a (2^m)
  let w : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ := fun q => P.entranceRemainingSize hi a q.2
  have hP := P.integrable_maximum_of_bounded hbound
  have hEm (m) : Measurable (E m) := P.measurable_gridEntranceError _
    (ProphetSecretary.Statistics.dyadicEntranceGrid_monotone m) lo hi a _
  have hWm (m) : Measurable (W m) := by
    apply Finset.measurable_sum
    intro j _
    exact ((P.stronglyMeasurable_gridEntranceSizeMultiplier (k:=k) _
      (ProphetSecretary.Statistics.dyadicEntranceGrid_monotone m) hi a j).mono
      (ProphetSecretary.Probability.observedClockSigma_le _)).measurable
  have hwm : Measurable w := (P.measurable_entranceRemainingSize hi a).comp measurable_snd
  have hE0 (m q) : 0≤E m q := P.gridEntranceError_nonnegative _ lo hi a _ q
  have hW0 (m q) : 0≤W m q := by
    apply Finset.sum_nonneg
    intro j _
    exact (P.gridEntranceSizeMultiplier_mem (k:=k) _ hi a j
      (ProphetSecretary.Statistics.dyadicEntranceGrid_mem m j).1
      (ProphetSecretary.Statistics.dyadicEntranceGrid_mem m j).2.le q).1
  have hw0 (q) : 0≤w q := (P.entranceRemainingSize_mem hi a q.2).1
  have hEB (m) : ∀ᵐ q ∂μ, E m q ≤ 2*(n:ℝ) := P.gridEntranceError_bounded hbound _ lo hi a _
    (fun j _ => ProphetSecretary.Statistics.dyadicEntranceGrid_mem m j)
  have hwB : ∀ᵐ q ∂μ, w q≤P.totalFirstMoment+1 :=
    Eventually.of_forall fun q => (P.entranceRemainingSize_mem hi a q.2).2
  have hWL : ∀ᵐ q ∂μ, Tendsto (fun m => W m q) atTop (𝓝 (w q)) := by
    have hp : MeasurePreserving (Prod.snd : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ)) μ
      (Instance.clocksLaw n) := measurePreserving_snd
    have h := hp.quasiMeasurePreserving.ae (P.dyadic_gridEntranceSize_tendsto_post (k:=k) (a:=a) hP hhi.le)
    exact h.mono fun q hq => hq q.1
  have hGrid (m) := P.gridEntrance_weightedError_moment (k:=k) hbound hlo hlohi hhi ha _
    (ProphetSecretary.Statistics.dyadicEntranceGrid_monotone m) (2^m)
    (fun j _ => ProphetSecretary.Statistics.dyadicEntranceGrid_mem m j) hp
  have hp0 : 0<p := by rcases hp with rfl|rfl <;> omega
  have hK : 0 ≤ empiricalRestartMomentBound k lo hi a p * (a*(1+P.totalFirstMoment)/hi) :=
    mul_nonneg (empiricalRestartMomentBound_nonnegative k (lo:=lo) hhi ha p)
      (div_nonneg (mul_nonneg ha (by linarith [P.totalFirstMoment_nonnegative])) hhi.le)
  have h := ProphetSecretary.Probability.weighted_lowerLimitEnvelope_moment μ
    (E:=E) (W:=W) (w:=w) hEm hWm hwm hE0 hW0 hw0
    (D:=2*(n:ℝ)) (C:=P.totalFirstMoment+1)
    (K:=empiricalRestartMomentBound k lo hi a p * (a*(1+P.totalFirstMoment)/hi))
    (by positivity) (by linarith [P.totalFirstMoment_nonnegative]) hK hEB hwB hWL hp0
    (fun m => (hGrid m).1) (fun m => (hGrid m).2)
  exact h

end ProphetSecretary.Model
