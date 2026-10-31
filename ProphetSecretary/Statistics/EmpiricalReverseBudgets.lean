import ProphetSecretary.Statistics.EmpiricalReverseProcess
import ProphetSecretary.Statistics.EmpiricalPremiumTotals

/-!
# Predictable budgets of the actual empirical reverse process

The true positive premium of the current marginal controls each fresh sample jump.
Each marginal contributes exactly `k` independent samples, yielding the paper's
quadratic-variation budget `U/k` and sixth-jump budget `U/k^5` at a fixed scalar.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def empiricalReversePremium (P : Instance n) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (m : ℕ) (a : (Fin n × Fin k) → ℝ) : ℝ :=
  if hm : m < n * k then
    let q := reverseSampleOrder (k := k) p ⟨m, hm⟩
    positivePremium (P.law q.1) 1 (empiricalArrivalContinuation 1 z u q.1 a)
  else 0

lemma empiricalReversePremium_sum (P : Instance n) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (a : (Fin n × Fin k) → ℝ) :
    (∑ m ∈ Finset.range (n * k), empiricalReversePremium P p z u m a) =
      (k : ℝ) * (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u := by
  let f : Fin n → ℝ := fun i => positivePremium (P.law i) 1 (empiricalArrivalContinuation 1 z u i a)
  have hfin (m : Fin (n * k)) : empiricalReversePremium P p z u m.val a = f ((reverseSampleOrder p m).1) := by
    simp only [empiricalReversePremium, dif_pos m.is_lt]
    rfl
  calc
    _ = ∑ m : Fin (n * k), empiricalReversePremium P p z u m.val a := (Fin.sum_univ_eq_sum_range (fun m : ℕ => empiricalReversePremium P p z u m a) (n * k)).symm
    _ = ∑ m : Fin (n * k), f ((reverseSampleOrder p m).1) := Finset.sum_congr rfl (fun m _ => hfin m)
    _ = k • (∑ i : Fin n, f i) := sum_reverseSampleOrder_rows p f
    _ = _ := by simp only [nsmul_eq_mul]; rfl

lemma empiricalReversePremium_sum_div_pow (P : Instance n) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (a : (Fin n × Fin k) → ℝ) (r : ℕ) :
    (∑ m ∈ Finset.range (n * k), empiricalReversePremium P p z u m a / (k : ℝ) ^ (r + 1)) =
      (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u / (k : ℝ) ^ r := by
  rw [← Finset.sum_div, empiricalReversePremium_sum, pow_succ]
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne k)
  field_simp

lemma empiricalReverseJump_conditional_budget (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p)
    {m : ℕ} (hm : m < n * k) (r : ℕ) (hr : r = 1 ∨ r = 5) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k,
      ((P.trainingCoordinateLaw k)[(fun a => empiricalReverseJump P p z u m a ^ (r + 1)) |
        reverseTrainingFiltration p m]) a ≤ empiricalReversePremium P p z u m a / (k : ℝ) ^ (r + 1) := by
  let q := reverseSampleOrder (k := k) p ⟨m, hm⟩
  let s := ProphetSecretary.Probability.coordinatesBefore (reverseSampleOrder (k := k) p) m
  have hfresh : q ∉ s := ProphetSecretary.Probability.coordinatesBefore_fresh _ hm
  have hfuture : ∀ b ∈ futureSampleRows u q.1, ∀ j : Fin k, (b, j) ∈ s :=
    futureSampleRows_before_reverseStep p u horder hm
  have h := P.canonicalEmpiricalFreshJump_conditional_moments q.1 q.2 (hbound q.1) hz u s hfresh hfuture
  rw [reverseTrainingFiltration_eq]
  rcases hr with rfl | rfl
  · simpa only [empiricalReverseJump, empiricalReversePremium, dif_pos hm] using h.2.1
  · simpa only [empiricalReverseJump, empiricalReversePremium, dif_pos hm] using h.2.2

/-- Summing the actual conditional sample moments gives the exact `k` normalization. -/
lemma empiricalReverseProcess_conditional_budget_sum (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p)
    (r : ℕ) (hr : r = 1 ∨ r = 5) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k,
      (∑ m ∈ Finset.range (n * k),
        ((P.trainingCoordinateLaw k)[(fun a =>
          (empiricalReverseProcess P p z u (m + 1) a - empiricalReverseProcess P p z u m a) ^ (r + 1)) |
          reverseTrainingFiltration p m]) a) ≤
      (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u / (k : ℝ) ^ r := by
  have hstep (m : ℕ) (hm : m ∈ Finset.range (n * k)) : ∀ᵐ a ∂P.trainingCoordinateLaw k,
      ((P.trainingCoordinateLaw k)[(fun a =>
        (empiricalReverseProcess P p z u (m + 1) a - empiricalReverseProcess P p z u m a) ^ (r + 1)) |
        reverseTrainingFiltration p m]) a ≤ empiricalReversePremium P p z u m a / (k : ℝ) ^ (r + 1) := by
    have heq : (fun a : (Fin n × Fin k) → ℝ => (empiricalReverseProcess P p z u (m + 1) a - empiricalReverseProcess P p z u m a) ^ (r + 1)) =
        (fun a => empiricalReverseJump P p z u m a ^ (r + 1)) := by
      funext a
      exact congrArg (fun t : ℝ => t ^ (r + 1)) (congrFun (empiricalReverseProcess_increment P p z u m) a)
    rw [heq]
    exact empiricalReverseJump_conditional_budget P hbound p hz u horder (Finset.mem_range.mp hm) r hr
  have hall := (Filter.eventually_all_finset (Finset.range (n * k))).mpr hstep
  filter_upwards [hall] with a ha
  exact (Finset.sum_le_sum (fun m hm => ha m hm)).trans_eq (empiricalReversePremium_sum_div_pow P p z u a r)

/-- The predictable quadratic variation is the constructed sum of conditional
second moments. Its budget is proved from the actual independent sample experiment. -/
theorem empiricalReverseProcess_quadraticVariation_le (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k,
      ProphetSecretary.Probability.predictableQuadraticVariation (reverseTrainingFiltration p)
        (P.trainingCoordinateLaw k) (empiricalReverseProcess P p z u) (n * k) a ≤
        (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u / k := by
  simpa only [ProphetSecretary.Probability.predictableQuadraticVariation, pow_one] using
    empiricalReverseProcess_conditional_budget_sum P hbound p hz u horder 1 (Or.inl rfl)

lemma integrable_empiricalTruePremium_pow (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (r : ℕ) :
    Integrable (fun a : (Fin n × Fin k) → ℝ =>
      (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u ^ r)
      (P.trainingCoordinateLaw k) := by
  have hP : Integrable Instance.maximum P.valuesLaw := by
    apply Instance.integrable_maximum
    intro i
    apply Integrable.of_bound aestronglyMeasurable_id 1
    filter_upwards [P.nonnegative i, hbound i] with x hx0 hx1
    simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx0] using hx1
  exact P.integrable_empiricalPremiumUnder_pow (k := k) hP (P.trainingCoordinateLaw k)
    (y := fun a : (Fin n × Fin k) → ℝ => reservoirCoordinates.symm a)
    (c := fun _ => z) (u := fun _ => u)
    (fun i j => measurable_pi_apply (i, j)) measurable_const (fun _ => hz) (fun _ => measurable_const) r

/-- Expected sixth jump sum. The conditional sample bounds are averaged only after
the scalar and complete clock vector have been fixed. -/
theorem empiricalReverseProcess_sixth_jump_budget (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) :
    (∑ m ∈ Finset.range (n * k), ∫ a,
      (empiricalReverseProcess P p z u (m + 1) a - empiricalReverseProcess P p z u m a) ^ 6
        ∂P.trainingCoordinateLaw k) ≤
      (∫ a, (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u
        ∂P.trainingCoordinateLaw k) / (k : ℝ) ^ 5 := by
  have hLI : Integrable (fun a => ∑ m ∈ Finset.range (n * k),
      ((P.trainingCoordinateLaw k)[(fun a =>
        (empiricalReverseProcess P p z u (m + 1) a - empiricalReverseProcess P p z u m a) ^ 6) |
        reverseTrainingFiltration p m]) a) (P.trainingCoordinateLaw k) :=
    integrable_finsetSum _ (fun _ _ => integrable_condExp)
  have hUI : Integrable (fun a : (Fin n × Fin k) → ℝ =>
      (totalEmpiricalInstance (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u) (P.trainingCoordinateLaw k) := by
    simpa only [pow_one] using integrable_empiricalTruePremium_pow (k := k) P hbound hz u 1
  have hineq := integral_mono_ae hLI (hUI.div_const ((k : ℝ) ^ 5))
    (empiricalReverseProcess_conditional_budget_sum P hbound p hz u horder 5 (Or.inr rfl))
  have hMean : (∫ a, ∑ m ∈ Finset.range (n * k),
      ((P.trainingCoordinateLaw k)[(fun a =>
        (empiricalReverseProcess P p z u (m + 1) a - empiricalReverseProcess P p z u m a) ^ 6) |
        reverseTrainingFiltration p m]) a ∂P.trainingCoordinateLaw k) =
      ∑ m ∈ Finset.range (n * k), ∫ a,
        (empiricalReverseProcess P p z u (m + 1) a - empiricalReverseProcess P p z u m a) ^ 6
          ∂P.trainingCoordinateLaw k := by
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl (fun m _ => integral_condExp ((reverseTrainingFiltration (k := k) p).le m))
    · intro m _
      exact integrable_condExp
  rw [hMean, integral_div] at hineq
  exact hineq

end ProphetSecretary.Model
