import ProphetSecretary.Statistics.MixedEmpiricalReverseProcess
import ProphetSecretary.Statistics.MixedEmpiricalPremiumTotals

/-!
# Predictable budgets with exact known marginals

Known rows have zero jumps. Their omission can only reduce the fresh-moment
budgets, so the true unstopped premium sum at the mixed continuation still
bounds quadratic variation by U/k and the sixth-jump sum by U/k^5.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def mixedReversePremium (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (m : ℕ) (a : (Fin n × Fin k) → ℝ) : ℝ :=
  if hm : m < n * k then
    let q := reverseSampleOrder (k := k) p ⟨m, hm⟩
    positivePremium (P.law q.1) 1 (mixedArrivalContinuation P known 1 z u q.1 a)
  else 0

lemma mixedReversePremium_sum (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (a : (Fin n × Fin k) → ℝ) :
    (∑ m ∈ Finset.range (n * k), mixedReversePremium P known p z u m a) =
      (k : ℝ) * (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u := by
  let f : Fin n → ℝ := fun i => positivePremium (P.law i) 1 (mixedArrivalContinuation P known 1 z u i a)
  have hfin (m : Fin (n * k)) : mixedReversePremium P known p z u m.val a = f ((reverseSampleOrder p m).1) := by
    simp only [mixedReversePremium, dif_pos m.is_lt]
    rfl
  calc
    _ = ∑ m : Fin (n * k), mixedReversePremium P known p z u m.val a := (Fin.sum_univ_eq_sum_range (fun m : ℕ => mixedReversePremium P known p z u m a) (n * k)).symm
    _ = ∑ m : Fin (n * k), f ((reverseSampleOrder p m).1) := Finset.sum_congr rfl (fun m _ => hfin m)
    _ = k • (∑ i : Fin n, f i) := sum_reverseSampleOrder_rows p f
    _ = _ := by simp only [nsmul_eq_mul]; rfl

lemma mixedReversePremium_sum_div_pow (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (a : (Fin n × Fin k) → ℝ) (r : ℕ) :
    (∑ m ∈ Finset.range (n * k), mixedReversePremium P known p z u m a / (k : ℝ) ^ (r + 1)) =
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u / (k : ℝ) ^ r := by
  rw [← Finset.sum_div, mixedReversePremium_sum, pow_succ]
  have hk : (k : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne k)
  field_simp

lemma mixedReverseJump_conditional_budget (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p)
    {m : ℕ} (hm : m < n * k) (r : ℕ) (hr : r = 1 ∨ r = 5) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k,
      ((P.trainingCoordinateLaw k)[(fun a => mixedReverseJump P known p z u m a ^ (r + 1)) |
        reverseTrainingFiltration p m]) a ≤ mixedReversePremium P known p z u m a / (k : ℝ) ^ (r + 1) := by
  let q := reverseSampleOrder (k := k) p ⟨m, hm⟩
  let s := ProphetSecretary.Probability.coordinatesBefore (reverseSampleOrder (k := k) p) m
  have hfresh : q ∉ s := ProphetSecretary.Probability.coordinatesBefore_fresh _ hm
  have hfuture : ∀ b ∈ futureSampleRows u q.1, ∀ j : Fin k, (b, j) ∈ s :=
    futureSampleRows_before_reverseStep p u horder hm
  have h := P.canonicalMixedFreshJump_conditional_moments (P.integrable_maximum_of_bounded hbound) known q.1 q.2 (hbound q.1) hz u s hfresh (fun b hb _ l => hfuture b hb l)
  have hp (a : (Fin n × Fin k) → ℝ) :
      (if q.1∈known then 0 else positivePremium (P.law q.1) 1 (mixedArrivalContinuation P known 1 z u q.1 a))≤
        positivePremium (P.law q.1) 1 (mixedArrivalContinuation P known 1 z u q.1 a) := by
    split_ifs
    · exact positivePremium_nonnegative _ _ _
    · exact le_rfl
  rw [reverseTrainingFiltration_eq]
  rcases hr with rfl | rfl
  · filter_upwards [h.2.1] with a ha
    simpa only [mixedReverseJump,mixedReversePremium,dif_pos hm] using
      ha.trans (div_le_div_of_nonneg_right (hp a) (pow_nonneg (Nat.cast_nonneg k) 2))
  · filter_upwards [h.2.2] with a ha
    simpa only [mixedReverseJump,mixedReversePremium,dif_pos hm] using
      ha.trans (div_le_div_of_nonneg_right (hp a) (pow_nonneg (Nat.cast_nonneg k) 6))

/-- Summing the actual conditional sample moments gives the exact `k` normalization. -/
lemma mixedReverseProcess_conditional_budget_sum (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p)
    (r : ℕ) (hr : r = 1 ∨ r = 5) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k,
      (∑ m ∈ Finset.range (n * k),
        ((P.trainingCoordinateLaw k)[(fun a =>
          (mixedReverseProcess P known p z u (m + 1) a - mixedReverseProcess P known p z u m a) ^ (r + 1)) |
          reverseTrainingFiltration p m]) a) ≤
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u / (k : ℝ) ^ r := by
  have hstep (m : ℕ) (hm : m ∈ Finset.range (n * k)) : ∀ᵐ a ∂P.trainingCoordinateLaw k,
      ((P.trainingCoordinateLaw k)[(fun a =>
        (mixedReverseProcess P known p z u (m + 1) a - mixedReverseProcess P known p z u m a) ^ (r + 1)) |
        reverseTrainingFiltration p m]) a ≤ mixedReversePremium P known p z u m a / (k : ℝ) ^ (r + 1) := by
    have heq : (fun a : (Fin n × Fin k) → ℝ => (mixedReverseProcess P known p z u (m + 1) a - mixedReverseProcess P known p z u m a) ^ (r + 1)) =
        (fun a => mixedReverseJump P known p z u m a ^ (r + 1)) := by
      funext a
      exact congrArg (fun t : ℝ => t ^ (r + 1)) (congrFun (mixedReverseProcess_increment P known p z u m) a)
    rw [heq]
    exact mixedReverseJump_conditional_budget P known hbound p hz u horder (Finset.mem_range.mp hm) r hr
  have hall := (Filter.eventually_all_finset (Finset.range (n * k))).mpr hstep
  filter_upwards [hall] with a ha
  exact (Finset.sum_le_sum (fun m hm => ha m hm)).trans_eq (mixedReversePremium_sum_div_pow P known p z u a r)

/-- The predictable quadratic variation is the constructed sum of conditional
second moments. Its budget is proved from the actual independent sample experiment. -/
theorem mixedReverseProcess_quadraticVariation_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k,
      ProphetSecretary.Probability.predictableQuadraticVariation (reverseTrainingFiltration p)
        (P.trainingCoordinateLaw k) (mixedReverseProcess P known p z u) (n * k) a ≤
        (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u / k := by
  simpa only [ProphetSecretary.Probability.predictableQuadraticVariation, pow_one] using
    mixedReverseProcess_conditional_budget_sum P known hbound p hz u horder 1 (Or.inl rfl)

lemma integrable_mixedTruePremium_pow (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (r : ℕ) :
    Integrable (fun a : (Fin n × Fin k) → ℝ =>
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u ^ r)
      (P.trainingCoordinateLaw k) := by
  have hP : Integrable Instance.maximum P.valuesLaw := by
    apply Instance.integrable_maximum
    intro i
    apply Integrable.of_bound aestronglyMeasurable_id 1
    filter_upwards [P.nonnegative i, hbound i] with x hx0 hx1
    simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx0] using hx1
  exact P.integrable_mixedPremiumUnder_pow (k := k) hP known (P.trainingCoordinateLaw k)
    (y := fun a : (Fin n × Fin k) → ℝ => reservoirCoordinates.symm a)
    (c := fun _ => z) (u := fun _ => u)
    (fun i j => measurable_pi_apply (i, j)) measurable_const (fun _ => hz) (fun _ => measurable_const) r

/-- Expected sixth jump sum. The conditional sample bounds are averaged only after
the scalar and complete clock vector have been fixed. -/
theorem mixedReverseProcess_sixth_jump_budget (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) :
    (∑ m ∈ Finset.range (n * k), ∫ a,
      (mixedReverseProcess P known p z u (m + 1) a - mixedReverseProcess P known p z u m a) ^ 6
        ∂P.trainingCoordinateLaw k) ≤
      (∫ a, (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u
        ∂P.trainingCoordinateLaw k) / (k : ℝ) ^ 5 := by
  have hLI : Integrable (fun a => ∑ m ∈ Finset.range (n * k),
      ((P.trainingCoordinateLaw k)[(fun a =>
        (mixedReverseProcess P known p z u (m + 1) a - mixedReverseProcess P known p z u m a) ^ 6) |
        reverseTrainingFiltration p m]) a) (P.trainingCoordinateLaw k) :=
    integrable_finsetSum _ (fun _ _ => integrable_condExp)
  have hUI : Integrable (fun a : (Fin n × Fin k) → ℝ =>
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).unstoppedPremiumUnder P 1 z u) (P.trainingCoordinateLaw k) := by
    simpa only [pow_one] using integrable_mixedTruePremium_pow (k := k) P known hbound hz u 1
  have hineq := integral_mono_ae hLI (hUI.div_const ((k : ℝ) ^ 5))
    (mixedReverseProcess_conditional_budget_sum P known hbound p hz u horder 5 (Or.inr rfl))
  have hMean : (∫ a, ∑ m ∈ Finset.range (n * k),
      ((P.trainingCoordinateLaw k)[(fun a =>
        (mixedReverseProcess P known p z u (m + 1) a - mixedReverseProcess P known p z u m a) ^ 6) |
        reverseTrainingFiltration p m]) a ∂P.trainingCoordinateLaw k) =
      ∑ m ∈ Finset.range (n * k), ∫ a,
        (mixedReverseProcess P known p z u (m + 1) a - mixedReverseProcess P known p z u m a) ^ 6
          ∂P.trainingCoordinateLaw k := by
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl (fun m _ => integral_condExp ((reverseTrainingFiltration (k := k) p).le m))
    · intro m _
      exact integrable_condExp
  rw [hMean, integral_div] at hineq
  exact hineq

end ProphetSecretary.Model
