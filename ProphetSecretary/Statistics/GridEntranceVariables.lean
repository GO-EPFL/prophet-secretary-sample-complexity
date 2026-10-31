import ProphetSecretary.Statistics.GridEntranceMoments

/-!
# Concrete finite-grid entrance error and size variables

The first critical event selects at most one state. The product of its size
and error moment is exactly the sum already bounded by actual conditional
restart moments. A missing entrance contributes zero. No cardinality factor
is introduced by summing candidate grid times.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics

lemma product_sums_one_active {α : Type*} [DecidableEq α] (s : Finset α) (E : α → Prop)
    (hUnique : ∀ i ∈ s, ∀ j ∈ s, E i → E j → i=j) (B G : α → ℝ) (p : ℕ) :
    (∑ i ∈ s, if E i then B i else 0) * (∑ i ∈ s, if E i then G i else 0)^p =
      ∑ i ∈ s, (if E i then B i else 0) * G i^p := by
  have hright : (∑ i ∈ s, (if E i then B i else 0) * G i^p) =
      ∑ i ∈ s, if E i then B i * G i^p else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> simp
  rw [hright]
  by_cases hex : ∃ i ∈ s, E i
  · obtain ⟨i,hi,hE⟩ := hex
    have hsum (f : α → ℝ) : (∑ j ∈ s, if E j then f j else 0) = f i := by
      rw [Finset.sum_eq_single i]
      · exact if_pos hE
      · intro j hj hji
        exact if_neg (fun hjE => hji (hUnique j hj i hi hjE hE))
      · intro hn
        exact False.elim (hn hi)
    rw [hsum B,hsum G,hsum (fun i => B i * G i^p)]
  · have hsum (f : α → ℝ) : (∑ j ∈ s, if E j then f j else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      exact if_neg (fun he => hex ⟨j,hj,he⟩)
    rw [hsum B,hsum G,hsum (fun i => B i * G i^p),zero_mul]

end ProphetSecretary.Statistics

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def Instance.gridEntranceError (P : Instance n) (k : ℕ) [NeZero k]
    (τ : ℕ → ℝ) (lo hi a : ℝ) (N : ℕ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) : ℝ :=
  ∑ j ∈ Finset.range N, if P.firstCriticalGridEvent τ hi a j q.2 then P.stateFutureError k lo hi (τ j) q else 0

noncomputable def Instance.gridEntranceSize (P : Instance n) (k : ℕ)
    (τ : ℕ → ℝ) (hi a : ℝ) (N : ℕ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) : ℝ :=
  ∑ j ∈ Finset.range N, P.gridEntranceSizeMultiplier τ hi a j q

lemma Instance.gridEntrance_size_error_identity (P : Instance n) (τ : ℕ → ℝ) (lo hi a : ℝ)
    (N p : ℕ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) :
    P.gridEntranceSize k τ hi a N q * P.gridEntranceError k τ lo hi a N q ^ p =
      ∑ j ∈ Finset.range N, P.gridEntranceSizeMultiplier τ hi a j q * P.stateFutureError k lo hi (τ j) q ^ p := by
  exact ProphetSecretary.Statistics.product_sums_one_active (Finset.range N)
    (fun j => P.firstCriticalGridEvent τ hi a j q.2)
    (fun i _ j _ hEi hEj => P.firstCriticalGridEvent_unique τ hi a q.2 hEi hEj)
    (fun j => P.remainingSize (τ j) q.2) (fun j => P.stateFutureError k lo hi (τ j) q) p

/-- A genuine random finite-grid entrance has the desired weighted moments. -/
theorem Instance.gridEntrance_weightedError_moment (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi) (ha : 0 ≤ a)
    (τ : ℕ → ℝ) (hτ : Monotone τ) (N : ℕ) (hTimes : ∀ j < N, τ j ∈ Ico (0 : ℝ) 1)
    {p : ℕ} (hp : p=2 ∨ p=6) :
    Integrable (fun q => P.gridEntranceSize k τ hi a N q * P.gridEntranceError k τ lo hi a N q ^ p)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
    (∫ q, P.gridEntranceSize k τ hi a N q * P.gridEntranceError k τ lo hi a N q ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalRestartMomentBound k lo hi a p * (a*(1+P.totalFirstMoment)/hi) := by
  have hI : Integrable (fun q => ∑ j ∈ Finset.range N,
      P.gridEntranceSizeMultiplier τ hi a j q * P.stateFutureError k lo hi (τ j) q ^ p)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) :=
    integrable_finsetSum _ fun j hj => P.integrable_gridEntrance_weightedError (k := k) hbound τ hτ lo hi a j
      (hTimes j (Finset.mem_range.mp hj)).1 (hTimes j (Finset.mem_range.mp hj)).2 p
  have heq : (fun q => P.gridEntranceSize k τ hi a N q * P.gridEntranceError k τ lo hi a N q ^ p) =
      (fun q => ∑ j ∈ Finset.range N, P.gridEntranceSizeMultiplier τ hi a j q * P.stateFutureError k lo hi (τ j) q ^ p) :=
    funext fun q => P.gridEntrance_size_error_identity τ lo hi a N p q
  rw [heq]
  exact ⟨hI,P.integral_gridEntrance_weightedError_sum_le hbound hlo hlohi hhi ha τ hτ N hTimes hp⟩

end ProphetSecretary.Model
