import ProphetSecretary.Statistics.EmpiricalFreshStep
import ProphetSecretary.Statistics.ReverseTrainingOrder
import ProphetSecretary.Probability.MartingaleMoments

/-!
# The actual reverse empirical sample process

At a fixed scalar and fixed strict arrival order, each next sample is fresh relative
to the derived finite-coordinate reveal filtration. The canonical continuation uses
only rows already revealed. The process is constant after all `n*k` coordinates.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def empiricalReverseJump (P : Instance n) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (m : ℕ) : ((Fin n × Fin k) → ℝ) → ℝ :=
  if hm : m < n * k then
    let q := reverseSampleOrder (k := k) p ⟨m, hm⟩
    fun a => P.empiricalPremiumJump k q.1 (empiricalArrivalContinuation 1 z u q.1 a) (a q)
  else fun _ => 0

noncomputable def empiricalReverseProcess (P : Instance n) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (m : ℕ) : ((Fin n × Fin k) → ℝ) → ℝ :=
  ∑ j ∈ Finset.range (min m (n * k)), empiricalReverseJump P p z u j

def reverseTrainingFiltration (p : Equiv.Perm (Fin n)) :
    Filtration ℕ (MeasurableSpace.pi : MeasurableSpace (((Fin n × Fin k) → ℝ))) :=
  ProphetSecretary.Probability.coordinateRevealFiltration (reverseSampleOrder p)

omit [NeZero k] in
lemma reverseTrainingFiltration_eq (p : Equiv.Perm (Fin n)) (m : ℕ) :
    reverseTrainingFiltration (k := k) p m =
      ProphetSecretary.Probability.revealedCoordinateSigma
        (ProphetSecretary.Probability.coordinatesBefore (reverseSampleOrder p) m) :=
  (ProphetSecretary.Probability.revealedCoordinateSigma_eq_piFinset _).symm

lemma empiricalReverseProcess_zero (P : Instance n) (p : Equiv.Perm (Fin n)) (z : ℝ) (u : Fin n → ℝ) :
    empiricalReverseProcess (k := k) P p z u 0 = 0 := by simp [empiricalReverseProcess]

lemma empiricalReverseProcess_increment (P : Instance n) (p : Equiv.Perm (Fin n))
    (z : ℝ) (u : Fin n → ℝ) (m : ℕ) :
    empiricalReverseProcess (k := k) P p z u (m + 1) - empiricalReverseProcess P p z u m =
      empiricalReverseJump P p z u m := by
  by_cases hm : m < n * k
  · simp only [empiricalReverseProcess, Nat.min_eq_left hm.le,
      Nat.min_eq_left (Nat.succ_le_of_lt hm), Finset.sum_range_succ]
    abel
  · have hNm : n * k ≤ m := le_of_not_gt hm
    simp only [empiricalReverseProcess, Nat.min_eq_right hNm,
      Nat.min_eq_right (hNm.trans (Nat.le_succ m)), sub_self, empiricalReverseJump, dif_neg hm]
    funext a
    rfl

/-- Adaptedness is derived from actual future-row invariance and the fresh
coordinate's membership in the next revealed set. -/
lemma empiricalReverseJump_adapted (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) (m : ℕ) :
    StronglyMeasurable[reverseTrainingFiltration (k := k) p (m + 1)] (empiricalReverseJump P p z u m) := by
  by_cases hm : m < n * k
  · let q := reverseSampleOrder (k := k) p ⟨m, hm⟩
    let s := ProphetSecretary.Probability.coordinatesBefore (reverseSampleOrder (k := k) p) (m + 1)
    let f : ((Fin n × Fin k) → ℝ) → ℝ := fun a =>
      P.empiricalPremiumJump k q.1 (empiricalArrivalContinuation 1 z u q.1 a) (a q)
    have hfuture : ∀ b ∈ futureSampleRows u q.1, ∀ j : Fin k, (b, j) ∈ s := by
      intro b hb j
      exact (ProphetSecretary.Probability.coordinatesBefore_mono (reverseSampleOrder p) (Nat.le_succ m))
        (futureSampleRows_before_reverseStep p u horder hm b hb j)
    have hq : q ∈ s := by
      change reverseSampleOrder p ⟨m, hm⟩ ∈
        ProphetSecretary.Probability.coordinatesBefore (reverseSampleOrder p) (m + 1)
      rw [ProphetSecretary.Probability.coordinatesBefore_succ _ hm]
      exact Finset.mem_insert_self _ _
    have hfm : Measurable f :=
      (P.measurable_empiricalPremiumJump_product q.1 (hbound q.1) k
        (measurable_empiricalArrivalContinuation (by norm_num : (0 : ℝ) < 1) hz u q.1)).comp
        (measurable_id.prodMk (measurable_pi_apply q))
    have hmask : ∀ a, f (ProphetSecretary.Probability.maskCoordinates s a) = f a := by
      intro a
      change P.empiricalPremiumJump k q.1
        (empiricalArrivalContinuation 1 z u q.1 (ProphetSecretary.Probability.maskCoordinates s a))
        (ProphetSecretary.Probability.maskCoordinates s a q) = _
      rw [empiricalArrivalContinuation_mask 1 z u q.1 s hfuture,
        ProphetSecretary.Probability.maskCoordinates, if_pos hq]
    have hms := ProphetSecretary.Probability.measurable_of_mask_invariant hfm hmask
    have hstrong : StronglyMeasurable[ProphetSecretary.Probability.revealedCoordinateSigma s] f := by
      letI : MeasurableSpace (((Fin n × Fin k) → ℝ)) := ProphetSecretary.Probability.revealedCoordinateSigma s
      exact hms.stronglyMeasurable
    rw [reverseTrainingFiltration_eq]
    simpa only [empiricalReverseJump, dif_pos hm] using hstrong
  · rw [reverseTrainingFiltration_eq]
    simp only [empiricalReverseJump, dif_neg hm]
    exact stronglyMeasurable_const

lemma empiricalReverseProcess_stronglyAdapted (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) :
    StronglyAdapted (reverseTrainingFiltration (k := k) p) (empiricalReverseProcess P p z u) := by
  intro m
  letI : MeasurableSpace (((Fin n × Fin k) → ℝ)) := reverseTrainingFiltration (k := k) p m
  apply Finset.stronglyMeasurable_sum
  intro j hj
  have hjm : j + 1 ≤ m := Nat.succ_le_of_lt
    ((Finset.mem_range.mp hj).trans_le (Nat.min_le_left m (n * k)))
  exact (empiricalReverseJump_adapted P hbound p hz u horder j).mono
    ((reverseTrainingFiltration (k := k) p).mono hjm)

/-- A deterministic finite bound is used only for integrability; it will not enter
any maximal-moment constant. The actual sample law supplies the bound almost surely. -/
lemma empiricalReverseProcess_bounded (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (m : ℕ) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k,
      |empiricalReverseProcess P p z u m a| ≤ (n * k : ℕ) * (k : ℝ)⁻¹ := by
  have hgood : ∀ᵐ a ∂P.trainingCoordinateLaw k, ∀ q : Fin n × Fin k, 0 ≤ a q ∧ a q ≤ 1 := by
    rw [ae_all_iff]
    intro q
    exact (measurePreserving_eval (fun r : Fin n × Fin k => P.law r.1) q).quasiMeasurePreserving.ae
      ((P.nonnegative q.1).and (hbound q.1))
  filter_upwards [hgood] with a ha
  simp only [empiricalReverseProcess, Finset.sum_apply]
  calc
    _ ≤ ∑ j ∈ Finset.range (min m (n * k)), |empiricalReverseJump P p z u j a| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (min m (n * k)), (k : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro j hj
      have hjN : j < n * k := (Finset.mem_range.mp hj).trans_le (Nat.min_le_right m (n * k))
      let q := reverseSampleOrder (k := k) p ⟨j, hjN⟩
      have hθ : 0 ≤ empiricalArrivalContinuation (k := k) 1 z u q.1 a :=
        (totalEmpiricalInstance (reservoirCoordinates.symm a)).continuationAtArrival_nonnegative
          (totalEmpiricalInstance_integrable _) zero_le_one hz (fun _ => 0) u q.1
      simpa only [empiricalReverseJump, dif_pos hjN] using
        P.empiricalPremiumJump_abs_le_unit q.1 (hbound q.1) k hθ (ha q).1 (ha q).2
    _ = (min m (n * k) : ℕ) * (k : ℝ)⁻¹ := by simp
    _ ≤ (n * k : ℕ) * (k : ℝ)⁻¹ := mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.min_le_right m (n * k)) (inv_nonneg.mpr (Nat.cast_nonneg k))

lemma empiricalReverseJump_condExp_zero (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) (m : ℕ) :
    (P.trainingCoordinateLaw k)[empiricalReverseJump P p z u m | reverseTrainingFiltration p m] =ᵐ[P.trainingCoordinateLaw k] 0 := by
  by_cases hm : m < n * k
  · let q := reverseSampleOrder (k := k) p ⟨m, hm⟩
    let s := ProphetSecretary.Probability.coordinatesBefore (reverseSampleOrder (k := k) p) m
    have hfresh : q ∉ s := ProphetSecretary.Probability.coordinatesBefore_fresh _ hm
    have hfuture : ∀ b ∈ futureSampleRows u q.1, ∀ j : Fin k, (b, j) ∈ s :=
      futureSampleRows_before_reverseStep p u horder hm
    have h := P.canonicalEmpiricalFreshJump_conditional_moments q.1 q.2 (hbound q.1) hz u s hfresh hfuture
    rw [reverseTrainingFiltration_eq]
    simpa only [empiricalReverseJump, dif_pos hm] using h.1
  · simp [empiricalReverseJump, hm]
    filter_upwards [] with a
    rfl

/-- The sample-by-sample reverse process is an actual martingale under the independent
training reservoir law. Its property is derived, rather than assumed as an interface. -/
theorem empiricalReverseProcess_martingale (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (p : Equiv.Perm (Fin n))
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (horder : Instance.HasArrivalOrder u p) :
    Martingale (empiricalReverseProcess (k := k) P p z u) (reverseTrainingFiltration p) (P.trainingCoordinateLaw k) := by
  have hA := empiricalReverseProcess_stronglyAdapted (k := k) P hbound p hz u horder
  have hI (m : ℕ) : Integrable (empiricalReverseProcess (k := k) P p z u m) (P.trainingCoordinateLaw k) := by
    apply Integrable.of_bound ((hA m).mono ((reverseTrainingFiltration (k := k) p).le m)).aestronglyMeasurable
      ((n * k : ℕ) * (k : ℝ)⁻¹)
    filter_upwards [empiricalReverseProcess_bounded (k := k) P hbound p hz u m] with a ha
    simpa only [Real.norm_eq_abs] using ha
  apply martingale_of_condExp_sub_eq_zero_nat hA hI
  intro m
  rw [empiricalReverseProcess_increment]
  exact empiricalReverseJump_condExp_zero P hbound p hz u horder m

end ProphetSecretary.Model
