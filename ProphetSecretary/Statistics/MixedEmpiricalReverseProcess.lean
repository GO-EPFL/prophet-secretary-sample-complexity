import ProphetSecretary.Statistics.MixedEmpiricalFreshStep
import ProphetSecretary.Statistics.EmpiricalReverseProcess
import ProphetSecretary.Statistics.ReverseTrainingOrder
import ProphetSecretary.Probability.MartingaleMoments

/-!
# Reverse empirical martingale with exact known marginals

Known rows have zero increments. Unknown rows use fresh samples at continuation
thresholds derived from the mixed instance. The actual product reservoir law,
future-row masks and conditional moments establish the martingale property.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def mixedReverseJump (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (m : ℕ) : ((Fin n × Fin k) → ℝ) → ℝ :=
  if hm : m < n * k then
    let q := reverseSampleOrder (k := k) p ⟨m, hm⟩
    fun a => P.mixedPremiumJump known k q.1 (mixedArrivalContinuation P known 1 z u q.1 a) (a q)
  else fun _ => 0

noncomputable def mixedReverseProcess (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (m : ℕ) : ((Fin n × Fin k) → ℝ) → ℝ :=
  ∑ j ∈ Finset.range (min m (n * k)), mixedReverseJump P known p z u j

lemma mixedReverseProcess_zero (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n)) (z : ℝ) (u : Fin n → ℝ) :
    mixedReverseProcess (k := k) P known p z u 0 = 0 := by simp [mixedReverseProcess]

lemma mixedReverseProcess_increment (P : Instance n) (known : Finset (Fin n)) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (m : ℕ) :
    mixedReverseProcess (k := k) P known p z u (m + 1) - mixedReverseProcess P known p z u m =
      mixedReverseJump P known p z u m := by
  by_cases hm : m < n * k
  · simp only [mixedReverseProcess, Nat.min_eq_left hm.le,
      Nat.min_eq_left (Nat.succ_le_of_lt hm), Finset.sum_range_succ]
    abel
  · have hNm : n * k ≤ m := le_of_not_gt hm
    simp only [mixedReverseProcess, Nat.min_eq_right hNm,
      Nat.min_eq_right (hNm.trans (Nat.le_succ m)), sub_self, mixedReverseJump, dif_neg hm]
    funext a
    rfl

/-- Adaptedness is derived from actual future-row invariance and the fresh
coordinate's membership in the next revealed set. -/
lemma mixedReverseJump_adapted (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) (m : ℕ) :
    StronglyMeasurable[reverseTrainingFiltration (k := k) p (m + 1)] (mixedReverseJump P known p z u m) := by
  by_cases hm : m < n * k
  · let q := reverseSampleOrder (k := k) p ⟨m, hm⟩
    let s := ProphetSecretary.Probability.coordinatesBefore (reverseSampleOrder (k := k) p) (m + 1)
    let f : ((Fin n × Fin k) → ℝ) → ℝ := fun a =>
      P.mixedPremiumJump known k q.1 (mixedArrivalContinuation P known 1 z u q.1 a) (a q)
    have hfuture : ∀ b ∈ futureSampleRows u q.1, ∀ j : Fin k, (b, j) ∈ s := by
      intro b hb j
      exact (ProphetSecretary.Probability.coordinatesBefore_mono (reverseSampleOrder p) (Nat.le_succ m))
        (futureSampleRows_before_reverseStep p u horder hm b hb j)
    have hq : q ∈ s := by
      change reverseSampleOrder p ⟨m, hm⟩ ∈
        ProphetSecretary.Probability.coordinatesBefore (reverseSampleOrder p) (m + 1)
      rw [ProphetSecretary.Probability.coordinatesBefore_succ _ hm]
      exact Finset.mem_insert_self _ _
    let θ : ((Fin n × Fin k) → ℝ) → ℝ := mixedArrivalContinuation (k:=k) P known 1 z u q.1
    have hθ : Measurable θ := measurable_mixedArrivalContinuation P
      (P.integrable_maximum_of_bounded hbound) known zero_lt_one hz u q.1
    have hG : Measurable (fun r : (((Fin n × Fin k) → ℝ) × ℝ) =>
        P.mixedPremiumJump known k q.1 (θ r.1) r.2) :=
      P.measurable_mixedPremiumJump_product known q.1 (hbound q.1) k (θ:=θ) hθ
    have hpair : Measurable (fun a : (Fin n × Fin k) → ℝ => (a,a q)) :=
      measurable_id.prodMk (measurable_pi_apply q)
    have hfm : Measurable f := by
      convert hG.comp hpair using 1
      funext a
      rfl
    have hmask : ∀ a, f (ProphetSecretary.Probability.maskCoordinates s a) = f a := by
      intro a
      change P.mixedPremiumJump known k q.1
        (mixedArrivalContinuation P known 1 z u q.1 (ProphetSecretary.Probability.maskCoordinates s a))
        (ProphetSecretary.Probability.maskCoordinates s a q) = _
      rw [mixedArrivalContinuation_mask P known 1 z u q.1 s (fun b hb _ l => hfuture b hb l),
        ProphetSecretary.Probability.maskCoordinates, if_pos hq]
    have hms := ProphetSecretary.Probability.measurable_of_mask_invariant hfm hmask
    have hstrong : StronglyMeasurable[ProphetSecretary.Probability.revealedCoordinateSigma s] f := by
      letI : MeasurableSpace (((Fin n × Fin k) → ℝ)) := ProphetSecretary.Probability.revealedCoordinateSigma s
      exact hms.stronglyMeasurable
    rw [reverseTrainingFiltration_eq]
    simpa only [mixedReverseJump, dif_pos hm] using hstrong
  · rw [reverseTrainingFiltration_eq]
    simp only [mixedReverseJump, dif_neg hm]
    exact stronglyMeasurable_const

lemma mixedReverseProcess_stronglyAdapted (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) :
    StronglyAdapted (reverseTrainingFiltration (k := k) p) (mixedReverseProcess P known p z u) := by
  intro m
  letI : MeasurableSpace (((Fin n × Fin k) → ℝ)) := reverseTrainingFiltration (k := k) p m
  apply Finset.stronglyMeasurable_sum
  intro j hj
  have hjm : j + 1 ≤ m := Nat.succ_le_of_lt
    ((Finset.mem_range.mp hj).trans_le (Nat.min_le_left m (n * k)))
  exact (mixedReverseJump_adapted P known hbound p hz u horder j).mono
    ((reverseTrainingFiltration (k := k) p).mono hjm)

/-- A deterministic finite bound is used only for integrability; it will not enter
any maximal-moment constant. The actual sample law supplies the bound almost surely. -/
lemma mixedReverseProcess_bounded (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (m : ℕ) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k,
      |mixedReverseProcess P known p z u m a| ≤ (n * k : ℕ) * (k : ℝ)⁻¹ := by
  have hgood : ∀ᵐ a ∂P.trainingCoordinateLaw k, ∀ q : Fin n × Fin k, 0 ≤ a q ∧ a q ≤ 1 := by
    rw [ae_all_iff]
    intro q
    exact (measurePreserving_eval (fun r : Fin n × Fin k => P.law r.1) q).quasiMeasurePreserving.ae
      ((P.nonnegative q.1).and (hbound q.1))
  filter_upwards [hgood] with a ha
  simp only [mixedReverseProcess, Finset.sum_apply]
  calc
    _ ≤ ∑ j ∈ Finset.range (min m (n * k)), |mixedReverseJump P known p z u j a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (min m (n * k)), (k : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      have hjN : j < n * k := (Finset.mem_range.mp hj).trans_le (Nat.min_le_right m (n * k))
      let q := reverseSampleOrder (k := k) p ⟨j, hjN⟩
      have hθ : 0 ≤ mixedArrivalContinuation (k := k) P known 1 z u q.1 a :=
        (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).continuationAtArrival_nonnegative
          (mixedEmpiricalInstance_integrable P (P.integrable_maximum_of_bounded hbound) known _) zero_le_one hz (fun _ => 0) u q.1
      simpa only [mixedReverseJump, dif_pos hjN] using
        P.mixedPremiumJump_abs_le_unit known q.1 (hbound q.1) k hθ (ha q).1 (ha q).2
    _ = (min m (n * k) : ℕ) * (k : ℝ)⁻¹ := by simp
    _ ≤ (n * k : ℕ) * (k : ℝ)⁻¹ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.min_le_right m (n * k)) (inv_nonneg.mpr (Nat.cast_nonneg k))

lemma mixedReverseJump_condExp_zero (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) (m : ℕ) :
    (P.trainingCoordinateLaw k)[mixedReverseJump P known p z u m | reverseTrainingFiltration p m] =ᵐ[P.trainingCoordinateLaw k] 0 := by
  by_cases hm : m < n * k
  · let q := reverseSampleOrder (k := k) p ⟨m, hm⟩
    let s := ProphetSecretary.Probability.coordinatesBefore (reverseSampleOrder (k := k) p) m
    have hfresh : q ∉ s := ProphetSecretary.Probability.coordinatesBefore_fresh _ hm
    have hfuture : ∀ b ∈ futureSampleRows u q.1, ∀ j : Fin k, (b, j) ∈ s :=
      futureSampleRows_before_reverseStep p u horder hm
    have h := P.canonicalMixedFreshJump_conditional_moments (P.integrable_maximum_of_bounded hbound) known q.1 q.2 (hbound q.1) hz u s hfresh (fun b hb _ l => hfuture b hb l)
    rw [reverseTrainingFiltration_eq]
    simpa only [mixedReverseJump, dif_pos hm] using h.1
  · simp [mixedReverseJump, hm]
    filter_upwards [] with a
    rfl

/-- The sample-by-sample reverse process is an actual martingale under the independent
training reservoir law. Its property is derived, rather than assumed as an interface. -/
theorem mixedReverseProcess_martingale (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) :
    Martingale (mixedReverseProcess (k := k) P known p z u) (reverseTrainingFiltration p) (P.trainingCoordinateLaw k) := by
  have hA := mixedReverseProcess_stronglyAdapted (k := k) P known hbound p hz u horder
  have hI (m : ℕ) : Integrable (mixedReverseProcess (k := k) P known p z u m) (P.trainingCoordinateLaw k) := by
    apply Integrable.of_bound ((hA m).mono ((reverseTrainingFiltration (k := k) p).le m)).aestronglyMeasurable
      ((n * k : ℕ) * (k : ℝ)⁻¹)
    filter_upwards [mixedReverseProcess_bounded (k := k) P known hbound p hz u m] with a ha
    simpa only [Real.norm_eq_abs] using ha
  apply martingale_of_condExp_sub_eq_zero_nat hA hI
  intro m
  rw [mixedReverseProcess_increment]
  exact mixedReverseJump_condExp_zero P known hbound p hz u horder m

end ProphetSecretary.Model
