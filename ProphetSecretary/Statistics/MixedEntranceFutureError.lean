import ProphetSecretary.Statistics.MixedGridEntranceDomination
import ProphetSecretary.Statistics.TrueCriticalEntrance
import ProphetSecretary.Statistics.GridEntranceTime
import ProphetSecretary.Probability.LowerLimitEnvelope

/-!
# Actual mixed envelope after the true critical entrance

The lower limit of constructed mixed grid errors bounds all interval scalars
and times strictly after the actual true-law entrance. Proved right limits
recover its post-arrival state. No independence or restart rule at the random
entrance is assumed in this construction.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def Instance.mixedEntranceFutureError (P : Instance n) (known : Finset (Fin n)) (k : ℕ) [NeZero k]
    (lo hi a : ℝ) : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ :=
  ProphetSecretary.Probability.lowerLimitEnvelope (fun m =>
    P.mixedGridEntranceError known k (ProphetSecretary.Statistics.dyadicEntranceGrid m) lo hi a (2^m))

lemma Instance.measurable_mixedEntranceFutureError (P : Instance n) (known : Finset (Fin n)) (lo hi a : ℝ) :
    Measurable (P.mixedEntranceFutureError known k lo hi a) :=
  ProphetSecretary.Probability.measurable_lowerLimitEnvelope (fun m =>
    P.measurable_mixedGridEntranceError known _ (ProphetSecretary.Statistics.dyadicEntranceGrid_monotone m) lo hi a _)

lemma Instance.mixedEntranceFutureError_nonnegative (P : Instance n) (known : Finset (Fin n)) (lo hi a : ℝ)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) : 0 ≤ P.mixedEntranceFutureError known k lo hi a q :=
  ProphetSecretary.Probability.lowerLimitEnvelope_nonnegative _ _

lemma Instance.mixedEntranceFutureError_bounded (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (lo hi a : ℝ) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n), P.mixedEntranceFutureError known k lo hi a q ≤ 2*(n:ℝ) := by
  have hb : ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      ∀ m, P.mixedGridEntranceError known k (ProphetSecretary.Statistics.dyadicEntranceGrid m) lo hi a (2^m) q ≤ 2*(n:ℝ) :=
    ae_all_iff.mpr fun m => P.mixedGridEntranceError_bounded known hbound _ lo hi a _
      (fun j _ => ProphetSecretary.Statistics.dyadicEntranceGrid_mem m j)
  exact hb.mono fun q hq => ProphetSecretary.Probability.lowerLimitEnvelope_le _ q (by positivity) hq

/-- Common all-weight domination strictly after the actual critical entrance. -/
theorem Instance.mixedEntranceFutureError_dominates_later (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a : ℝ} (hlo : 0 ≤ lo) (hlohi : lo≤hi) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      ∀ t ∈ Ioc (P.trueCriticalEntrance hi a q.2) 1, ∀ z ∈ Icc lo hi,
      |(mixedEmpiricalInstance P known (reservoirCoordinates.symm q.1)).continuationValue
          (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z| ≤
      P.mixedEntranceFutureError known k lo hi a q := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  have hP := P.integrable_maximum_of_bounded hbound
  have hDom : ∀ᵐ q ∂μ, ∀ m, ∀ j<2^m,
      P.firstCriticalGridEvent (ProphetSecretary.Statistics.dyadicEntranceGrid m) hi a j q.2 →
      ∀ t∈Icc (ProphetSecretary.Statistics.dyadicEntranceGrid m j) 1, ∀ z∈Icc lo hi,
      |(mixedEmpiricalInstance P known (reservoirCoordinates.symm q.1)).continuationValue
          (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z| ≤
      P.mixedGridEntranceError known k (ProphetSecretary.Statistics.dyadicEntranceGrid m) lo hi a (2^m) q :=
    ae_all_iff.mpr fun m => P.mixedGridEntranceError_dominates_after_event known hbound hlo hlohi _ _
      (fun j _ => ProphetSecretary.Statistics.dyadicEntranceGrid_mem m j)
  have hBound : ∀ᵐ q ∂μ, ∀ m,
      P.mixedGridEntranceError known k (ProphetSecretary.Statistics.dyadicEntranceGrid m) lo hi a (2^m) q ≤ 2*(n:ℝ) :=
    ae_all_iff.mpr fun m => P.mixedGridEntranceError_bounded known hbound _ lo hi a _
      (fun j _ => ProphetSecretary.Statistics.dyadicEntranceGrid_mem m j)
  filter_upwards [hDom,hBound] with q hq hqB
  intro t ht z hz
  have hlim := P.dyadic_gridEntranceTime_tendsto (a:=a) hP (hlo.trans hlohi) q.2
  have hNear : ∀ᶠ m in atTop,
      P.gridEntranceTime (ProphetSecretary.Statistics.dyadicEntranceGrid m) hi a (2^m) q.2 < t :=
    hlim.eventually (isOpen_Iio.mem_nhds ht.1)
  have hErr : ∀ᶠ m in atTop,
      |(mixedEmpiricalInstance P known (reservoirCoordinates.symm q.1)).continuationValue
          (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z| ≤
      P.mixedGridEntranceError known k (ProphetSecretary.Statistics.dyadicEntranceGrid m) lo hi a (2^m) q := by
    filter_upwards [hNear] with m hm
    by_cases hex : ∃ j<2^m, P.firstCriticalGridEvent (ProphetSecretary.Statistics.dyadicEntranceGrid m) hi a j q.2
    · obtain ⟨j,hj,hE⟩ := hex
      rw [P.gridEntranceTime_eq_of_event _ hi a hj q.2 hE] at hm
      exact hq m j hj hE t ⟨hm.le,ht.2⟩ z hz
    · rw [P.gridEntranceTime_eq_one_of_no_event _ hi a _ q.2 hex] at hm
      exact False.elim ((not_lt_of_ge ht.2) hm)
  exact ProphetSecretary.Probability.le_lowerLimitEnvelope_of_eventual _ q (abs_nonneg _) hqB hErr

/-- The envelope also controls the actual post-jump state at the entrance. -/
theorem Instance.mixedEntranceFutureError_dominates_postEntrance (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a : ℝ} (hlo : 0 ≤ lo) (hlohi : lo≤hi) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      P.trueCriticalEntrance hi a q.2 < 1 → ∀ z∈Icc lo hi,
      let σ := P.trueCriticalEntrance hi a q.2
      |(mixedEmpiricalInstance P known (reservoirCoordinates.symm q.1)).continuationValue
          (ProphetSecretary.Probability.strictPendingClockSet σ q.2) (1-σ) 1 z -
        P.continuationValue (ProphetSecretary.Probability.strictPendingClockSet σ q.2) (1-σ) 1 z| ≤
      P.mixedEntranceFutureError known k lo hi a q := by
  have hP := P.integrable_maximum_of_bounded hbound
  filter_upwards [P.mixedEntranceFutureError_dominates_later (k:=k) known hbound hlo hlohi] with q hq
  intro hσ1 z hz
  let σ := P.trueCriticalEntrance hi a q.2
  let Q := mixedEmpiricalInstance P known (reservoirCoordinates.symm q.1)
  have hQ := mixedEmpiricalInstance_integrable P hP known (reservoirCoordinates.symm q.1)
  have hz0 : 0≤z := hlo.trans hz.1
  have hlim := continuous_abs.continuousAt.tendsto.comp
    ((ProphetSecretary.Probability.pendingContinuationValue_tendsto_right Q hQ hz0 q.2 σ).sub
      (ProphetSecretary.Probability.pendingContinuationValue_tendsto_right P hP hz0 q.2 σ))
  have hNear : ∀ᶠ t in 𝓝[>] σ, σ<t ∧ t≤1 := by
    have h1 : ∀ᶠ t in 𝓝 σ, t<1 := isOpen_Iio.mem_nhds hσ1
    filter_upwards [self_mem_nhdsWithin (a:=σ) (s:=Ioi σ),h1.filter_mono nhdsWithin_le_nhds] with t ht ht1
    exact ⟨ht,ht1.le⟩
  have hB : ∀ᶠ t in 𝓝[>] σ,
      |Q.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (max 0 (1-t)) 1 z -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (max 0 (1-t)) 1 z| ≤
      P.mixedEntranceFutureError known k lo hi a q := by
    filter_upwards [hNear] with t ht
    rw [max_eq_right (sub_nonneg.mpr ht.2)]
    exact hq t ht z hz
  have h := le_of_tendsto hlim hB
  have hσ : σ≤1 := hσ1.le
  rw [max_eq_right (sub_nonneg.mpr hσ)] at h
  exact h

end ProphetSecretary.Model
