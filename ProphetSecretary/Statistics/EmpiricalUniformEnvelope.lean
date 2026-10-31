import ProphetSecretary.Statistics.EmpiricalEnvelopeProcess
import ProphetSecretary.Analysis.DyadicChaining

/-!
# Uniform empirical residual envelopes

Dyadic chaining is applied to the actual empirical residual process. The resulting
measurable envelope controls every scalar in a fixed interval on the same training
outcome, so its domination also holds for training-selected scalars. No centering
claim is made after selecting a scalar from the training data.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.empiricalUniformResidualEnvelope (P : Instance n) (k : ℕ) [NeZero k]
    (lo hi : ℝ) : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ :=
  ProphetSecretary.Analysis.dyadicSupremum (P.empiricalIntervalEnvelope k lo hi)

variable {k : ℕ} [NeZero k]

lemma Instance.measurable_empiricalUniformResidualEnvelope (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (lo hi : ℝ) :
    Measurable (P.empiricalUniformResidualEnvelope k lo hi) :=
  ProphetSecretary.Analysis.measurable_dyadicSupremum (P.measurable_empiricalIntervalEnvelope hP lo hi)

lemma Instance.empiricalUniformResidualEnvelope_nonnegative (P : Instance n) (lo hi : ℝ)
    (v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) :
    0 ≤ P.empiricalUniformResidualEnvelope k lo hi v :=
  ProphetSecretary.Analysis.dyadicSupremum_nonnegative _ _

/-- The actual chaining estimate before any localization of the endpoint values. -/
theorem Instance.empiricalUniformResidualEnvelope_moment (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {p : ℕ} (hp : p = 2 ∨ p = 6) (lo hi : ℝ) :
    Integrable (fun v => P.empiricalUniformResidualEnvelope k lo hi v ^ p)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
    (∫ v, P.empiricalUniformResidualEnvelope k lo hi v ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      ProphetSecretary.Analysis.dyadicChainingConstant p *
        ((∫ v, |P.empiricalIntervalEnvelope k lo hi v 0| ^ p
            ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) +
         (∫ v, |P.empiricalIntervalEnvelope k lo hi v 1| ^ p
            ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) +
         empiricalIncrementMomentConstant k p * |hi - lo| ^ p) := by
  have hP := P.integrable_maximum_of_bounded hbound
  have h := ProphetSecretary.Analysis.continuous_dyadic_chaining
    ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))
    (P.measurable_empiricalIntervalEnvelope hP lo hi) (Nat.cast_nonneg n)
    (mul_nonneg (empiricalIncrementMomentConstant_nonnegative k p) (pow_nonneg (abs_nonneg _) p))
    ((P.empiricalIntervalEnvelope_bounded (k := k) hbound lo hi).mono (fun _ hv t _ => hv t))
    (Filter.Eventually.of_forall (fun v => (P.continuous_empiricalIntervalEnvelope hP lo hi v).continuousOn))
    p (by rcases hp with rfl | rfl <;> omega)
    (fun s _ t _ => by simpa only [abs_sub_comm s t] using P.empiricalIntervalEnvelope_increment_moment (k := k) hbound hp lo hi s t)
  exact ⟨h.2.2.1, h.2.2.2⟩

lemma exists_unitInterval_affine {lo hi z : ℝ} (hlohi : lo ≤ hi) (hz : z ∈ Icc lo hi) :
    ∃ t ∈ Icc (0 : ℝ) 1, lo + (hi - lo) * t = z := by
  by_cases hEq : lo = hi
  · have hzEq : z = lo := by linarith [hz.1, hz.2]
    exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simp [hzEq]⟩
  · have hd : 0 < hi - lo := sub_pos.mpr (lt_of_le_of_ne hlohi hEq)
    refine ⟨(z - lo) / (hi - lo), ⟨div_nonneg (sub_nonneg.mpr hz.1) hd.le,
      (div_le_one hd).mpr (by linarith [hz.2])⟩, ?_⟩
    field_simp [ne_of_gt hd]; ring

/-- Every interval coefficient is controlled on one common probability-one event. -/
theorem Instance.empiricalUniformResidualEnvelope_dominates (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi : ℝ} (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) :
    ∀ᵐ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      ∀ z ∈ Icc lo hi, (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2 ≤
        P.empiricalUniformResidualEnvelope k lo hi v := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hSup := ProphetSecretary.Analysis.continuous_dyadic_chaining
    ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))
    (P.measurable_empiricalIntervalEnvelope hP lo hi) (Nat.cast_nonneg n)
    (mul_nonneg (empiricalIncrementMomentConstant_nonnegative k 2) (sq_nonneg |hi - lo|))
    ((P.empiricalIntervalEnvelope_bounded (k := k) hbound lo hi).mono (fun _ hv t _ => hv t))
    (Filter.Eventually.of_forall (fun v => (P.continuous_empiricalIntervalEnvelope hP lo hi v).continuousOn))
    2 (by decide)
    (fun s _ t _ => by simpa only [abs_sub_comm s t] using P.empiricalIntervalEnvelope_increment_moment (k := k) hbound (Or.inl rfl) lo hi s t)
  filter_upwards [hSup.2.1, P.empiricalIntervalEnvelope_bounded (k := k) hbound lo hi] with v hSup hv
  intro z hz
  obtain ⟨t, ht, he⟩ := exists_unitInterval_affine hlohi hz
  have hz0 : 0 ≤ z := hlo.trans hz.1
  have hB : BddAbove {y : ℝ | ∃ s ∈ Icc (0 : ℝ) 1, y = |P.empiricalIntervalEnvelope k lo hi v s|} := by
    refine ⟨n, ?_⟩
    rintro y ⟨s, _hs, rfl⟩
    exact hv s
  have hMem : |P.empiricalIntervalEnvelope k lo hi v t| ∈
      {y : ℝ | ∃ s ∈ Icc (0 : ℝ) 1, y = |P.empiricalIntervalEnvelope k lo hi v s|} := ⟨t, ht, rfl⟩
  have h := le_csSup hB hMem
  rw [← hSup] at h
  have h0 : 0 ≤ (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2 := ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _
  simpa only [Instance.empiricalUniformResidualEnvelope, Instance.empiricalIntervalEnvelope, he, max_eq_right hz0, abs_of_nonneg h0] using h

/-- In particular, selection using the training array does not invalidate envelope
domination. This statement uses no residual unbiasedness at the selected weight. -/
theorem Instance.empiricalUniformResidualEnvelope_dominates_selected (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi : ℝ} (hlo : 0 ≤ lo) (hlohi : lo ≤ hi)
    (Z : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ) (hZ : ∀ v, Z v ∈ Icc lo hi) :
    ∀ᵐ v ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      (totalEmpiricalInstance (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 (Z v) v.2 ≤
        P.empiricalUniformResidualEnvelope k lo hi v :=
  (P.empiricalUniformResidualEnvelope_dominates hbound hlo hlohi).mono (fun v hv => hv (Z v) (hZ v))

end ProphetSecretary.Model
