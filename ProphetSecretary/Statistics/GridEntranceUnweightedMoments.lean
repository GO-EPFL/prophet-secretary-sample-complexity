import ProphetSecretary.Statistics.GridEntranceDomination

/-!
# Unweighted localized grid entrance moments

Observable first-entrance indicators multiply the actual conditional moments.
They are pairwise disjoint, so their total probability is at most one. Thus
the concrete grid error has the localized moment profile without a factor
from the number of grid points or identities.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics

lemma pow_sum_one_active {α : Type*} [DecidableEq α] (s : Finset α) (E : α → Prop)
    (hUnique : ∀ i ∈ s, ∀ j ∈ s, E i → E j → i=j) (G : α → ℝ) {p : ℕ} (hp : 0<p) :
    (∑ i ∈ s, if E i then G i else 0)^p = ∑ i ∈ s, if E i then G i^p else 0 := by
  by_cases hex : ∃ i ∈ s, E i
  · obtain ⟨i,hi,hE⟩ := hex
    have hsum (f : α → ℝ) : (∑ j ∈ s, if E j then f j else 0) = f i := by
      rw [Finset.sum_eq_single i]
      · exact if_pos hE
      · intro j hj hji
        exact if_neg (fun hjE => hji (hUnique j hj i hi hjE hE))
      · intro hn
        exact False.elim (hn hi)
    rw [hsum G,hsum (fun i => G i^p)]
  · have hsum (f : α → ℝ) : (∑ j ∈ s, if E j then f j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact if_neg (fun he => hex ⟨j,hj,he⟩)
    rw [hsum G,hsum (fun i => G i^p),zero_pow hp.ne']

end ProphetSecretary.Statistics

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma Instance.gridEntrance_eventMoment_le (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi)
    (τ : ℕ → ℝ) (hτ : Monotone τ) (j : ℕ) (ht0 : 0 ≤ τ j) (ht1 : τ j < 1)
    {p : ℕ} (hp : p=2 ∨ p=6) :
    (∫ q, if P.firstCriticalGridEvent τ hi a j q.2 then P.stateFutureError k lo hi (τ j) q^p else 0
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
  have hM := P.weighted_critical_stateFutureError_moment hbound hlo hlohi hhi ht0 ht1 hp H hm zero_le_one hb (by
    intro q hne
    by_cases hEq : P.firstCriticalGridEvent τ hi a j q.2
    · exact hEq.1
    · exact False.elim (hne (by simp only [H,E,Set.indicator_apply,Set.mem_setOf_eq,if_neg hEq])))
  have hEg : MeasurableSet E := (ProphetSecretary.Probability.observedClockSigma_le (n := n)
    (D := (Fin n × Fin k) → ℝ) (τ j)) _ hE
  have hHmean : (∫ q, H q ∂μ) = μ.real E := integral_indicator_one hEg
  have hfun : (fun q => H q * P.stateFutureError k lo hi (τ j) q^p) =
      fun q => if P.firstCriticalGridEvent τ hi a j q.2 then P.stateFutureError k lo hi (τ j) q^p else 0 := by
    funext q
    simp only [H,E,Set.indicator_apply,Set.mem_setOf_eq]
    split_ifs <;> simp
  rw [hfun,hHmean] at hM
  exact hM

omit [NeZero k] in
lemma Instance.gridEntrance_eventProbability_sum_le (P : Instance n) (τ : ℕ → ℝ) (hτ : Monotone τ)
    (hi a : ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range N, ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)).real
      {q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) | P.firstCriticalGridEvent τ hi a j q.2}) ≤ 1 := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  let E : ℕ → Set (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) := fun j => {q | P.firstCriticalGridEvent τ hi a j q.2}
  let F : ℕ → (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ := fun j q => if q∈E j then 1 else 0
  have hE (j : ℕ) : MeasurableSet (E j) :=
    (ProphetSecretary.Probability.observedClockSigma_le (n := n) (D := (Fin n × Fin k) → ℝ) (τ j)) _
      (P.measurableSet_firstCriticalGridEvent τ hτ hi a j)
  have hI (j : ℕ) : Integrable (F j) μ := by
    apply Integrable.of_bound (Measurable.ite (hE j) measurable_const measurable_const).aestronglyMeasurable 1
    exact Eventually.of_forall fun q => by change ‖if q∈E j then (1:ℝ) else 0‖ ≤ 1; split_ifs <;> norm_num
  have he (j : ℕ) : (∫ q, F j q ∂μ) = μ.real (E j) := integral_indicator_one (hE j)
  have hpoint (q) : (∑ j ∈ Finset.range N, F j q) ≤ 1 := by
    by_cases hex : ∃ j∈Finset.range N, q∈E j
    · obtain ⟨j,hj,hEq⟩ := hex
      rw [Finset.sum_eq_single j]
      · exact le_of_eq (if_pos hEq)
      · intro l _ hlj
        exact if_neg (fun hl => hlj (P.firstCriticalGridEvent_unique τ hi a q.2 hl hEq))
      · intro hn
        exact False.elim (hn hj)
    · have hz : (∑ j ∈ Finset.range N, F j q)=0 := Finset.sum_eq_zero fun j hj => if_neg (fun he => hex ⟨j,hj,he⟩)
      rw [hz]
      exact zero_le_one
  have hmean := integral_mono (integrable_finsetSum _ (fun j _ => hI j)) (integrable_const (1:ℝ)) hpoint
  change (∫ q, ∑ j∈Finset.range N, F j q ∂μ) ≤ (∫ _ : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)), (1:ℝ) ∂μ) at hmean
  rw [integral_finsetSum _ (fun j _ => hI j)] at hmean
  simpa only [he,integral_const,probReal_univ,one_smul] using hmean

/-- The concrete grid error has the full localized moment profile. -/
theorem Instance.gridEntranceError_moment (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi) (ha : 0 ≤ a)
    (τ : ℕ → ℝ) (hτ : Monotone τ) (N : ℕ) (hTimes : ∀ j<N, τ j∈Ico (0:ℝ) 1)
    {p : ℕ} (hp : p=2 ∨ p=6) :
    Integrable (fun q => P.gridEntranceError k τ lo hi a N q^p)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
    (∫ q, P.gridEntranceError k τ lo hi a N q^p ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalRestartMomentBound k lo hi a p := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  have hp0 : 0<p := by rcases hp with rfl|rfl <;> omega
  have hI : Integrable (fun q => P.gridEntranceError k τ lo hi a N q^p) μ := by
    apply Integrable.of_bound ((P.measurable_gridEntranceError τ hτ lo hi a N).pow_const p).aestronglyMeasurable ((2*(n:ℝ))^p)
    filter_upwards [P.gridEntranceError_bounded (k := k) hbound τ lo hi a N hTimes] with q hq
    change ‖P.gridEntranceError k τ lo hi a N q^p‖ ≤ _
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (P.gridEntranceError_nonnegative τ lo hi a N q) p)]
    exact pow_le_pow_left₀ (P.gridEntranceError_nonnegative τ lo hi a N q) hq p
  refine ⟨hI,?_⟩
  have hfun : (fun q => P.gridEntranceError k τ lo hi a N q^p) =
      (fun q => ∑ j∈Finset.range N, if P.firstCriticalGridEvent τ hi a j q.2 then P.stateFutureError k lo hi (τ j) q^p else 0) := by
    funext q
    exact ProphetSecretary.Statistics.pow_sum_one_active (Finset.range N)
      (fun j => P.firstCriticalGridEvent τ hi a j q.2)
      (fun i _ j _ hEi hEj => P.firstCriticalGridEvent_unique τ hi a q.2 hEi hEj)
      (fun j => P.stateFutureError k lo hi (τ j) q) hp0
  have hterms (j : ℕ) (hj : j∈Finset.range N) : Integrable
      (fun q => if P.firstCriticalGridEvent τ hi a j q.2 then P.stateFutureError k lo hi (τ j) q^p else 0) μ :=
    (P.integrable_stateFutureError_pow hbound lo hi (hTimes j (Finset.mem_range.mp hj)).1 (hTimes j (Finset.mem_range.mp hj)).2 p).indicator
      ((ProphetSecretary.Probability.observedClockSigma_le (n := n) (D := (Fin n × Fin k) → ℝ) (τ j)) _
        (P.measurableSet_firstCriticalGridEvent τ hτ hi a j))
  rw [hfun,integral_finsetSum _ hterms]
  have hsum := Finset.sum_le_sum (s:=Finset.range N) fun j hj =>
    P.gridEntrance_eventMoment_le (k:=k) (a:=a) hbound hlo hlohi hhi τ hτ j
      (hTimes j (Finset.mem_range.mp hj)).1 (hTimes j (Finset.mem_range.mp hj)).2 hp
  apply hsum.trans
  rw [← Finset.mul_sum]
  have hK := empiricalRestartMomentBound_nonnegative k (lo:=lo) hhi ha p
  have hb := mul_le_mul_of_nonneg_left (P.gridEntrance_eventProbability_sum_le (k:=k) τ hτ hi a N) hK
  simpa only [mul_one] using hb

end ProphetSecretary.Model
