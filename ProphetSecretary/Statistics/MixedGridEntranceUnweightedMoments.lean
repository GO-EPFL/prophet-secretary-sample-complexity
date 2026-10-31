import ProphetSecretary.Statistics.MixedGridEntranceDomination
import ProphetSecretary.Statistics.GridEntranceUnweightedMoments

/-!
# Unweighted actual mixed grid-error moments

Observable first-entrance indicators weight the proved mixed conditional moments.
Their disjointness bounds the total event probability by one. The concrete mixed
grid envelope therefore has no grid-cardinality or instance-size factor in its
localized second/sixth moment profile.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

lemma Instance.mixedGridEntrance_eventMoment_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi)
    (τ : ℕ → ℝ) (hτ : Monotone τ) (j : ℕ) (ht0 : 0 ≤ τ j) (ht1 : τ j < 1)
    {p : ℕ} (hp : p=2 ∨ p=6) :
    (∫ q, if P.firstCriticalGridEvent τ hi a j q.2 then P.mixedStateFutureError known k lo hi (τ j) q^p else 0
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalRestartMomentBound k lo hi a p *
        ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)).real
          {q | P.firstCriticalGridEvent τ hi a j q.2} := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  let E : Set (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) := {q | P.firstCriticalGridEvent τ hi a j q.2}
  let H := E.indicator (fun _ => (1 : ℝ))
  have hE := P.measurableSet_firstCriticalGridEvent (k := k) τ hτ hi a j
  have hm : StronglyMeasurable[ProphetSecretary.Probability.observedClockSigma ((Fin n × Fin k) → ℝ) n (τ j)] H :=
    (Measurable.ite hE measurable_const measurable_const).stronglyMeasurable
  have hb : ∀ᵐ q ∂μ, 0≤H q ∧ H q≤1 := Eventually.of_forall fun q => by
    simp only [H,Set.indicator_apply]
    split_ifs <;> norm_num
  have hM := P.weighted_critical_mixedStateFutureError_moment known hbound hlo hlohi hhi ht0 ht1 hp H hm zero_le_one hb (by
    intro q hne
    by_cases hEq : P.firstCriticalGridEvent τ hi a j q.2
    · exact hEq.1
    · exact False.elim (hne (by simp only [H,E,Set.indicator_apply,Set.mem_setOf_eq,if_neg hEq])))
  have hEg : MeasurableSet E := (ProphetSecretary.Probability.observedClockSigma_le (n := n)
    (D := (Fin n × Fin k) → ℝ) (τ j)) _ hE
  have hHmean : (∫ q, H q ∂μ) = μ.real E := integral_indicator_one hEg
  have hfun : (fun q => H q * P.mixedStateFutureError known k lo hi (τ j) q^p) =
      fun q => if P.firstCriticalGridEvent τ hi a j q.2 then P.mixedStateFutureError known k lo hi (τ j) q^p else 0 := by
    funext q
    simp only [H,E,Set.indicator_apply,Set.mem_setOf_eq]
    split_ifs <;> simp
  rw [hfun,hHmean] at hM
  exact hM

/-- The concrete grid error has the full localized moment profile. -/
theorem Instance.mixedGridEntranceError_moment (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi) (ha : 0 ≤ a)
    (τ : ℕ → ℝ) (hτ : Monotone τ) (N : ℕ) (hTimes : ∀ j<N, τ j∈Ico (0:ℝ) 1)
    {p : ℕ} (hp : p=2 ∨ p=6) :
    Integrable (fun q => P.mixedGridEntranceError known k τ lo hi a N q^p)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
    (∫ q, P.mixedGridEntranceError known k τ lo hi a N q^p ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalRestartMomentBound k lo hi a p := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  have hp0 : 0<p := by rcases hp with rfl|rfl <;> omega
  have hI : Integrable (fun q => P.mixedGridEntranceError known k τ lo hi a N q^p) μ := by
    apply Integrable.of_bound ((P.measurable_mixedGridEntranceError known τ hτ lo hi a N).pow_const p).aestronglyMeasurable ((2*(n:ℝ))^p)
    filter_upwards [P.mixedGridEntranceError_bounded (k := k) known hbound τ lo hi a N hTimes] with q hq
    change ‖P.mixedGridEntranceError known k τ lo hi a N q^p‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (P.mixedGridEntranceError_nonnegative known τ lo hi a N q) p)]
    exact pow_le_pow_left₀ (P.mixedGridEntranceError_nonnegative known τ lo hi a N q) hq p
  refine ⟨hI,?_⟩
  have hfun : (fun q => P.mixedGridEntranceError known k τ lo hi a N q^p) =
      (fun q => ∑ j∈Finset.range N, if P.firstCriticalGridEvent τ hi a j q.2 then P.mixedStateFutureError known k lo hi (τ j) q^p else 0) := by
    funext q
    exact ProphetSecretary.Statistics.pow_sum_one_active (Finset.range N)
      (fun j => P.firstCriticalGridEvent τ hi a j q.2)
      (fun i _ j _ hEi hEj => P.firstCriticalGridEvent_unique τ hi a q.2 hEi hEj)
      (fun j => P.mixedStateFutureError known k lo hi (τ j) q) hp0
  have hterms (j : ℕ) (hj : j∈Finset.range N) : Integrable
      (fun q => if P.firstCriticalGridEvent τ hi a j q.2 then P.mixedStateFutureError known k lo hi (τ j) q^p else 0) μ :=
    (P.integrable_mixedStateFutureError_pow known hbound lo hi (hTimes j (Finset.mem_range.mp hj)).1 (hTimes j (Finset.mem_range.mp hj)).2 p).indicator
      ((ProphetSecretary.Probability.observedClockSigma_le (n := n) (D := (Fin n × Fin k) → ℝ) (τ j)) _
        (P.measurableSet_firstCriticalGridEvent τ hτ hi a j))
  rw [hfun,integral_finsetSum _ hterms]
  have hsum := Finset.sum_le_sum (s:=Finset.range N) fun j hj =>
    P.mixedGridEntrance_eventMoment_le (k:=k) (a:=a) known hbound hlo hlohi hhi τ hτ j
      (hTimes j (Finset.mem_range.mp hj)).1 (hTimes j (Finset.mem_range.mp hj)).2 hp
  apply hsum.trans
  rw [← Finset.mul_sum]
  have hK := empiricalRestartMomentBound_nonnegative k (lo:=lo) hhi ha p
  have hb := mul_le_mul_of_nonneg_left (P.gridEntrance_eventProbability_sum_le (k:=k) τ hτ hi a N) hK
  simpa only [mul_one] using hb

end ProphetSecretary.Model
