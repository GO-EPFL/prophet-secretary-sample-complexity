import ProphetSecretary.Statistics.EmpiricalSlopeFreshStep
import ProphetSecretary.Statistics.EmpiricalReverseMaximalMoments

/-!
# Reverse martingale for scalar increments

The two scalar coefficients are fixed before training. Their normalized process
difference is an actual martingale for the same reservoir-reveal filtration.
Fresh-coordinate independence supplies its sharper conditional moment budgets.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def empiricalSlopeReverseProcess (P : Instance n) (p : Equiv.Perm (Fin n))
    (z z' : ℝ) (u : Fin n → ℝ) (m : ℕ) (a : (Fin n × Fin k) → ℝ) : ℝ :=
  (empiricalReverseProcess P p z u m a - empiricalReverseProcess P p z' u m a) / (z' - z)

noncomputable def empiricalSlopeReverseJump (P : Instance n) (p : Equiv.Perm (Fin n))
    (z z' : ℝ) (u : Fin n → ℝ) (m : ℕ) (a : (Fin n × Fin k) → ℝ) : ℝ :=
  (empiricalReverseJump P p z u m a - empiricalReverseJump P p z' u m a) / (z' - z)

lemma empiricalSlopeReverseProcess_increment (P : Instance n) (p : Equiv.Perm (Fin n))
    (z z' : ℝ) (u : Fin n → ℝ) (m : ℕ) :
    (fun a => empiricalSlopeReverseProcess P p z z' u (m + 1) a - empiricalSlopeReverseProcess P p z z' u m a) =
      empiricalSlopeReverseJump (k := k) P p z z' u m := by
  funext a
  have h := congrFun (empiricalReverseProcess_increment P p z u m) a
  have h' := congrFun (empiricalReverseProcess_increment P p z' u m) a
  simp only [Pi.sub_apply] at h h'
  dsimp [empiricalSlopeReverseProcess, empiricalSlopeReverseJump]
  rw [← h, ← h']
  ring

lemma empiricalSlopeReverseProcess_zero (P : Instance n) (p : Equiv.Perm (Fin n))
    (z z' : ℝ) (u : Fin n → ℝ) : empiricalSlopeReverseProcess (k := k) P p z z' u 0 = 0 := by
  funext a
  simp only [empiricalSlopeReverseProcess, empiricalReverseProcess_zero, Pi.zero_apply, sub_self, zero_div]

lemma empiricalSlopeReverseProcess_martingale (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) :
    Martingale (empiricalSlopeReverseProcess (k := k) P p z z' u)
      (reverseTrainingFiltration p) (P.trainingCoordinateLaw k) := by
  have h := ((empiricalReverseProcess_martingale (k := k) P hbound p hz u horder).sub
    (empiricalReverseProcess_martingale (k := k) P hbound p hz' u horder)).smul ((z' - z)⁻¹)
  have heq : empiricalSlopeReverseProcess (k := k) P p z z' u =
      (z' - z)⁻¹ • (empiricalReverseProcess P p z u - empiricalReverseProcess P p z' u) := by
    funext m a
    simp only [empiricalSlopeReverseProcess, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq]
  exact h

lemma empiricalSlopeReverseProcess_bounded (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (u : Fin n → ℝ) (m : ℕ) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k,
      |empiricalSlopeReverseProcess P p z z' u m a| ≤
        2 * ((n * k : ℕ) * (k : ℝ)⁻¹) / (z' - z) := by
  filter_upwards [empiricalReverseProcess_bounded (k := k) P hbound p hz u m,
    empiricalReverseProcess_bounded (k := k) P hbound p (hz.trans hzz.le) u m] with a ha hb
  simp only [empiricalSlopeReverseProcess, abs_div, abs_of_pos (sub_pos.mpr hzz)]
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hzz.le)
  exact (abs_sub _ _).trans (by linarith)

noncomputable def empiricalSlopeReversePremium (P : Instance n) (p : Equiv.Perm (Fin n))
    (z z' : ℝ) (u : Fin n → ℝ) (m : ℕ) (a : (Fin n × Fin k) → ℝ) : ℝ :=
  (empiricalReversePremium P p z u m a - empiricalReversePremium P p z' u m a) / (z' - z)

noncomputable def empiricalTrueSlopePremiumSum (P : Instance n) (z z' : ℝ) (u : Fin n → ℝ)
    (a : (Fin n × Fin k) → ℝ) : ℝ :=
  ((totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u -
    (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z' u) / (z' - z)

lemma empiricalSlopeReversePremium_sum_div_pow (P : Instance n) (p : Equiv.Perm (Fin n))
    (z z' : ℝ) (u : Fin n → ℝ) (a : (Fin n × Fin k) → ℝ) (r : ℕ) :
    (∑ m ∈ Finset.range (n * k), empiricalSlopeReversePremium P p z z' u m a / (k : ℝ) ^ (r + 1)) =
      empiricalTrueSlopePremiumSum P z z' u a / (k : ℝ) ^ r := by
  simp only [empiricalSlopeReversePremium, sub_div, div_div]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
    empiricalReversePremium_sum P p z u a, empiricalReversePremium_sum P p z' u a]
  dsimp [empiricalTrueSlopePremiumSum]
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne k)
  by_cases hd : z' - z = 0
  · simp only [hd, zero_mul, div_zero, sub_self, zero_div]
  · field_simp [hk, hd, pow_succ]; ring

lemma empiricalSlopeReverseJump_conditional_budget (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (u : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ u i) (horder : Instance.HasArrivalOrder u p)
    {m : ℕ} (hm : m < n * k) (r : ℕ) (hr : r = 1 ∨ r = 5) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k,
      ((P.trainingCoordinateLaw k)[(fun a => empiricalSlopeReverseJump P p z z' u m a ^ (r + 1)) |
        reverseTrainingFiltration p m]) a ≤ empiricalSlopeReversePremium P p z z' u m a / (k : ℝ) ^ (r + 1) := by
  let q := reverseSampleOrder (k := k) p ⟨m, hm⟩
  let s := ProphetSecretary.Probability.coordinatesBefore (reverseSampleOrder (k := k) p) m
  have hfresh : q ∉ s := ProphetSecretary.Probability.coordinatesBefore_fresh _ hm
  have hfuture : ∀ b ∈ futureSampleRows u q.1, ∀ j : Fin k, (b, j) ∈ s :=
    futureSampleRows_before_reverseStep p u horder hm
  have h := P.canonicalEmpiricalSlopeFreshJump_conditional_moments
    (P.integrable_maximum_of_bounded hbound) q.1 q.2 hz hzz u (hu q.1) s hfresh hfuture
  rw [reverseTrainingFiltration_eq]
  rcases hr with rfl | rfl
  · simpa only [empiricalSlopeReverseJump, empiricalReverseJump, empiricalSlopeReversePremium,
      empiricalReversePremium, dif_pos hm, Instance.clockPremiumSlopeUnder,
      q, s, empiricalArrivalContinuation, Prod.eta, Nat.reduceAdd] using h.2.1
  · simpa only [empiricalSlopeReverseJump, empiricalReverseJump, empiricalSlopeReversePremium,
      empiricalReversePremium, dif_pos hm, Instance.clockPremiumSlopeUnder,
      q, s, empiricalArrivalContinuation, Prod.eta, Nat.reduceAdd] using h.2.2

/-- Actual conditional sample budgets, summed along the reverse reveal order. -/
lemma empiricalSlopeReverseProcess_conditional_budget_sum (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (u : Fin n → ℝ)
    (hu : ∀ i, 0 ≤ u i) (horder : Instance.HasArrivalOrder u p)
    (r : ℕ) (hr : r = 1 ∨ r = 5) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k,
      (∑ m ∈ Finset.range (n * k),
        ((P.trainingCoordinateLaw k)[(fun a =>
          (empiricalSlopeReverseProcess P p z z' u (m + 1) a - empiricalSlopeReverseProcess P p z z' u m a) ^ (r + 1)) |
          reverseTrainingFiltration p m]) a) ≤ empiricalTrueSlopePremiumSum P z z' u a / (k : ℝ) ^ r := by
  have hstep (m : ℕ) (hm : m ∈ Finset.range (n * k)) : ∀ᵐ a ∂P.trainingCoordinateLaw k,
      ((P.trainingCoordinateLaw k)[(fun a =>
        (empiricalSlopeReverseProcess P p z z' u (m + 1) a - empiricalSlopeReverseProcess P p z z' u m a) ^ (r + 1)) |
        reverseTrainingFiltration p m]) a ≤ empiricalSlopeReversePremium P p z z' u m a / (k : ℝ) ^ (r + 1) := by
    have heq : (fun a : (Fin n × Fin k) → ℝ =>
        (empiricalSlopeReverseProcess P p z z' u (m + 1) a - empiricalSlopeReverseProcess P p z z' u m a) ^ (r + 1)) =
        (fun a => empiricalSlopeReverseJump P p z z' u m a ^ (r + 1)) := by
      funext a
      exact congrArg (fun x : ℝ => x ^ (r + 1)) (congrFun (empiricalSlopeReverseProcess_increment P p z z' u m) a)
    rw [heq]
    exact empiricalSlopeReverseJump_conditional_budget P hbound p hz hzz u hu horder (Finset.mem_range.mp hm) r hr
  have hall := (Filter.eventually_all_finset (Finset.range (n * k))).mpr hstep
  filter_upwards [hall] with a ha
  exact (Finset.sum_le_sum (fun m hm => ha m hm)).trans_eq (empiricalSlopeReversePremium_sum_div_pow P p z z' u a r)

end ProphetSecretary.Model
