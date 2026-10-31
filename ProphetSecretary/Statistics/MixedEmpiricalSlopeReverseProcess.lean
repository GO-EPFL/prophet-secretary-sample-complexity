import ProphetSecretary.Statistics.MixedEmpiricalSlopeFreshStep
import ProphetSecretary.Statistics.MixedEmpiricalReverseMaximalMoments

/-!
# Actual reverse martingale for mixed scalar increments

The normalized difference of the two fixed-scalar mixed reverse processes is
an actual martingale. Unknown fresh-coordinate moments and exact zero known
jumps give the predictable scalar-increment budgets under the original product
training law.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def mixedSlopeReverseProcess (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z z' : ℝ) (u : Fin n → ℝ) (m : ℕ) (a : (Fin n × Fin k) → ℝ) : ℝ :=
  (mixedReverseProcess P known p z u m a - mixedReverseProcess P known p z' u m a) / (z' - z)

noncomputable def mixedSlopeReverseJump (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z z' : ℝ) (u : Fin n → ℝ) (m : ℕ) (a : (Fin n × Fin k) → ℝ) : ℝ :=
  (mixedReverseJump P known p z u m a - mixedReverseJump P known p z' u m a) / (z' - z)

lemma mixedSlopeReverseProcess_increment (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z z' : ℝ) (u : Fin n → ℝ) (m : ℕ) :
    (fun a => mixedSlopeReverseProcess P known p z z' u (m + 1) a - mixedSlopeReverseProcess P known p z z' u m a) =
      mixedSlopeReverseJump (k := k) P known p z z' u m := by
  funext a
  have h := congrFun (mixedReverseProcess_increment P known p z u m) a
  have h' := congrFun (mixedReverseProcess_increment P known p z' u m) a
  simp only [Pi.sub_apply] at h h'
  dsimp [mixedSlopeReverseProcess, mixedSlopeReverseJump]
  rw [← h, ← h']
  ring

lemma mixedSlopeReverseProcess_zero (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z z' : ℝ) (u : Fin n → ℝ) : mixedSlopeReverseProcess (k := k) P known p z z' u 0 = 0 := by
  funext a
  simp only [mixedSlopeReverseProcess, mixedReverseProcess_zero, Pi.zero_apply, sub_self, zero_div]

lemma mixedSlopeReverseProcess_martingale (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) :
    Martingale (mixedSlopeReverseProcess (k := k) P known p z z' u)
      (reverseTrainingFiltration p) (P.trainingCoordinateLaw k) := by
  have h := ((mixedReverseProcess_martingale (k := k) P known hbound p hz u horder).sub
    (mixedReverseProcess_martingale (k := k) P known hbound p hz' u horder)).smul ((z' - z)⁻¹)
  have heq : mixedSlopeReverseProcess (k := k) P known p z z' u =
      (z' - z)⁻¹ • (mixedReverseProcess P known p z u - mixedReverseProcess P known p z' u) := by
    funext m a
    simp only [mixedSlopeReverseProcess, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq]
  exact h

lemma mixedSlopeReverseProcess_bounded (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (u : Fin n → ℝ) (m : ℕ) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k,
      |mixedSlopeReverseProcess P known p z z' u m a| ≤
        2 * ((n * k : ℕ) * (k : ℝ)⁻¹) / (z' - z) := by
  filter_upwards [mixedReverseProcess_bounded (k := k) P known hbound p hz u m,
    mixedReverseProcess_bounded (k := k) P known hbound p (hz.trans hzz.le) u m] with a ha hb
  simp only [mixedSlopeReverseProcess, abs_div, abs_of_pos (sub_pos.mpr hzz)]
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hzz.le)
  exact (abs_sub _ _).trans (by linarith)

noncomputable def mixedSlopeReversePremium (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z z' : ℝ) (u : Fin n → ℝ) (m : ℕ) (a : (Fin n × Fin k) → ℝ) : ℝ :=
  (mixedReversePremium P known p z u m a - mixedReversePremium P known p z' u m a) / (z' - z)

noncomputable def mixedTrueSlopePremiumSum (P : Instance n) (known : Finset (Fin n)) (z z' : ℝ) (u : Fin n → ℝ)
    (a : (Fin n × Fin k) → ℝ) : ℝ :=
  ((mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u -
    (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z' u) / (z' - z)

lemma mixedSlopeReversePremium_sum_div_pow (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z z' : ℝ) (u : Fin n → ℝ) (a : (Fin n × Fin k) → ℝ) (r : ℕ) :
    (∑ m ∈ Finset.range (n * k), mixedSlopeReversePremium P known p z z' u m a / (k : ℝ) ^ (r + 1)) =
      mixedTrueSlopePremiumSum P known z z' u a / (k : ℝ) ^ r := by
  simp only [mixedSlopeReversePremium, sub_div, div_div]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
    mixedReversePremium_sum P known p z u a, mixedReversePremium_sum P known p z' u a]
  dsimp [mixedTrueSlopePremiumSum]
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne k)
  by_cases hd : z' - z = 0
  · simp only [hd, zero_mul, div_zero, sub_self, zero_div]
  · field_simp [hk, hd, pow_succ]; ring

lemma mixedSlopeReverseJump_conditional_budget (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (u : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ u i) (horder : Instance.HasArrivalOrder u p)
    {m : ℕ} (hm : m < n * k) (r : ℕ) (hr : r = 1 ∨ r = 5) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k,
      ((P.trainingCoordinateLaw k)[(fun a => mixedSlopeReverseJump P known p z z' u m a ^ (r + 1)) |
        reverseTrainingFiltration p m]) a ≤ mixedSlopeReversePremium P known p z z' u m a / (k : ℝ) ^ (r + 1) := by
  let q := reverseSampleOrder (k := k) p ⟨m, hm⟩
  let s := ProphetSecretary.Probability.coordinatesBefore (reverseSampleOrder (k := k) p) m
  have hfresh : q ∉ s := ProphetSecretary.Probability.coordinatesBefore_fresh _ hm
  have hfuture : ∀ b ∈ futureSampleRows u q.1, ∀ j : Fin k, (b, j) ∈ s :=
    futureSampleRows_before_reverseStep p u horder hm
  have h := P.canonicalMixedSlopeFreshJump_conditional_moments
    (P.integrable_maximum_of_bounded hbound) known q.1 q.2 hz hzz u (hu q.1) s hfresh (fun b hb _ l => hfuture b hb l)
  have hp (a : (Fin n × Fin k) → ℝ) :
      (if q.1∈known then 0 else (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).clockPremiumSlopeUnder P z z' u q.1)≤
        (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).clockPremiumSlopeUnder P z z' u q.1 := by
    split_ifs
    · rw [←integral_mixedOfferSlope P (P.integrable_maximum_of_bounded hbound) known z z' u q.1 a]
      exact integral_nonneg fun x => (mixedOfferSlope_bounds P (P.integrable_maximum_of_bounded hbound) known hz hzz u q.1 (hu q.1) a x).1
    · exact le_rfl
  rw [reverseTrainingFiltration_eq]
  rcases hr with rfl | rfl
  · filter_upwards [h.2.1] with a ha
    have hb := ha.trans (div_le_div_of_nonneg_right (hp a) (pow_nonneg (Nat.cast_nonneg k) 2))
    simpa only [mixedSlopeReverseJump,mixedReverseJump,mixedSlopeReversePremium,mixedReversePremium,
      dif_pos hm,Instance.clockPremiumSlopeUnder,q,s,mixedArrivalContinuation,Prod.eta,Nat.reduceAdd] using hb
  · filter_upwards [h.2.2] with a ha
    have hb := ha.trans (div_le_div_of_nonneg_right (hp a) (pow_nonneg (Nat.cast_nonneg k) 6))
    simpa only [mixedSlopeReverseJump,mixedReverseJump,mixedSlopeReversePremium,mixedReversePremium,
      dif_pos hm,Instance.clockPremiumSlopeUnder,q,s,mixedArrivalContinuation,Prod.eta,Nat.reduceAdd] using hb

/-- Actual conditional sample budgets, summed along the reverse reveal order. -/
lemma mixedSlopeReverseProcess_conditional_budget_sum (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (u : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ u i) (horder : Instance.HasArrivalOrder u p)
    (r : ℕ) (hr : r = 1 ∨ r = 5) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k,
      (∑ m ∈ Finset.range (n * k),
        ((P.trainingCoordinateLaw k)[(fun a =>
          (mixedSlopeReverseProcess P known p z z' u (m + 1) a - mixedSlopeReverseProcess P known p z z' u m a) ^ (r + 1)) |
          reverseTrainingFiltration p m]) a) ≤ mixedTrueSlopePremiumSum P known z z' u a / (k : ℝ) ^ r := by
  have hstep (m : ℕ) (hm : m ∈ Finset.range (n * k)) : ∀ᵐ a ∂P.trainingCoordinateLaw k,
      ((P.trainingCoordinateLaw k)[(fun a =>
        (mixedSlopeReverseProcess P known p z z' u (m + 1) a - mixedSlopeReverseProcess P known p z z' u m a) ^ (r + 1)) |
        reverseTrainingFiltration p m]) a ≤ mixedSlopeReversePremium P known p z z' u m a / (k : ℝ) ^ (r + 1) := by
    have heq : (fun a : (Fin n × Fin k) → ℝ =>
        (mixedSlopeReverseProcess P known p z z' u (m + 1) a - mixedSlopeReverseProcess P known p z z' u m a) ^ (r + 1)) =
        (fun a => mixedSlopeReverseJump P known p z z' u m a ^ (r + 1)) := by
      funext a
      exact congrArg (fun x : ℝ => x ^ (r + 1)) (congrFun (mixedSlopeReverseProcess_increment P known p z z' u m) a)
    rw [heq]
    exact mixedSlopeReverseJump_conditional_budget P known hbound p hz hzz u hu horder (Finset.mem_range.mp hm) r hr
  have hall := (Filter.eventually_all_finset (Finset.range (n * k))).mpr hstep
  filter_upwards [hall] with a ha
  exact (Finset.sum_le_sum (fun m hm => ha m hm)).trans_eq (mixedSlopeReversePremium_sum_div_pow P known p z z' u a r)

end ProphetSecretary.Model
