import ProphetSecretary.Statistics.MixedEmpiricalEnvelopeProcess
import ProphetSecretary.Statistics.EmpiricalUniformEnvelope
import ProphetSecretary.Analysis.DyadicChaining

/-!
# Uniform residual envelopes with exact known marginals

Dyadic chaining applies to the constructed mixed scalar process. A single
measurable envelope dominates every scalar in the fixed interval on the same
training/clock event. Selecting the scalar from the data therefore introduces
no fixed-weight centering assumption.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.mixedUniformResidualEnvelope (P : Instance n) (known : Finset (Fin n)) (k : ℕ) [NeZero k]
    (lo hi : ℝ) : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ :=
  ProphetSecretary.Analysis.dyadicSupremum (P.mixedIntervalEnvelope known k lo hi)

variable {k : ℕ} [NeZero k]

lemma Instance.measurable_mixedUniformResidualEnvelope (P : Instance n) (known : Finset (Fin n))
    (hP : Integrable Instance.maximum P.valuesLaw) (lo hi : ℝ) :
    Measurable (P.mixedUniformResidualEnvelope known k lo hi) :=
  ProphetSecretary.Analysis.measurable_dyadicSupremum (P.measurable_mixedIntervalEnvelope known hP lo hi)

lemma Instance.mixedUniformResidualEnvelope_nonnegative (P : Instance n) (known : Finset (Fin n)) (lo hi : ℝ)
    (v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) :
    0 ≤ P.mixedUniformResidualEnvelope known k lo hi v :=
  ProphetSecretary.Analysis.dyadicSupremum_nonnegative _ _

/-- The actual chaining estimate before any localization of the endpoint values. -/
theorem Instance.mixedUniformResidualEnvelope_moment (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {p : ℕ} (hp : p = 2 ∨ p = 6) (lo hi : ℝ) :
    Integrable (fun v => P.mixedUniformResidualEnvelope known k lo hi v ^ p)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
    (∫ v, P.mixedUniformResidualEnvelope known k lo hi v ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      ProphetSecretary.Analysis.dyadicChainingConstant p *
        ((∫ v, |P.mixedIntervalEnvelope known k lo hi v 0| ^ p
            ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) +
         (∫ v, |P.mixedIntervalEnvelope known k lo hi v 1| ^ p
            ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) +
         empiricalIncrementMomentConstant k p * |hi - lo| ^ p) := by
  have hP := P.integrable_maximum_of_bounded hbound
  have h := ProphetSecretary.Analysis.continuous_dyadic_chaining
    ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))
    (P.measurable_mixedIntervalEnvelope known hP lo hi) (Nat.cast_nonneg n)
    (mul_nonneg (empiricalIncrementMomentConstant_nonnegative k p) (pow_nonneg (abs_nonneg _) p))
    ((P.mixedIntervalEnvelope_bounded (k := k) known hbound lo hi).mono (fun _ hv t _ => hv t))
    (Filter.Eventually.of_forall (fun v => (P.continuous_mixedIntervalEnvelope known hP lo hi v).continuousOn))
    p (by rcases hp with rfl | rfl <;> omega)
    (fun s _ t _ => by simpa only [abs_sub_comm s t] using P.mixedIntervalEnvelope_increment_moment (k := k) known hbound hp lo hi s t)
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- Every interval coefficient is controlled on one common probability-one event. -/
theorem Instance.mixedUniformResidualEnvelope_dominates (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi : ℝ} (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) :
    ∀ᵐ v : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      ∀ z ∈ Icc lo hi, (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2 ≤
        P.mixedUniformResidualEnvelope known k lo hi v := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hSup := ProphetSecretary.Analysis.continuous_dyadic_chaining
    ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))
    (P.measurable_mixedIntervalEnvelope known hP lo hi) (Nat.cast_nonneg n)
    (mul_nonneg (empiricalIncrementMomentConstant_nonnegative k 2) (sq_nonneg |hi - lo|))
    ((P.mixedIntervalEnvelope_bounded (k := k) known hbound lo hi).mono (fun _ hv t _ => hv t))
    (Filter.Eventually.of_forall (fun v => (P.continuous_mixedIntervalEnvelope known hP lo hi v).continuousOn))
    2 (by decide)
    (fun s _ t _ => by simpa only [abs_sub_comm s t] using P.mixedIntervalEnvelope_increment_moment (k := k) known hbound (Or.inl rfl) lo hi s t)
  filter_upwards [hSup.2.1, P.mixedIntervalEnvelope_bounded (k := k) known hbound lo hi] with v hSup hv
  intro z hz
  obtain ⟨t, ht, he⟩ := exists_unitInterval_affine hlohi hz
  have hz0 : 0 ≤ z := hlo.trans hz.1
  have hB : BddAbove {y : ℝ | ∃ s ∈ Icc (0 : ℝ) 1, y = |P.mixedIntervalEnvelope known k lo hi v s|} := by
    refine ⟨n, ?_⟩
    rintro y ⟨s, _hs, rfl⟩
    exact hv s
  have hMem : |P.mixedIntervalEnvelope known k lo hi v t| ∈
      {y : ℝ | ∃ s ∈ Icc (0 : ℝ) 1, y = |P.mixedIntervalEnvelope known k lo hi v s|} := ⟨t, ht, rfl⟩
  have h := le_csSup hB hMem
  rw [← hSup] at h
  have h0 : 0 ≤ (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 z v.2 := ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _
  simpa only [Instance.mixedUniformResidualEnvelope, Instance.mixedIntervalEnvelope, he, max_eq_right hz0, abs_of_nonneg h0] using h

/-- In particular, selection using the training array does not invalidate envelope
domination. This statement uses no residual unbiasedness at the selected weight. -/
theorem Instance.mixedUniformResidualEnvelope_dominates_selected (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi : ℝ} (hlo : 0 ≤ lo) (hlohi : lo ≤ hi)
    (Z : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ) (hZ : ∀ v, Z v ∈ Icc lo hi) :
    ∀ᵐ v ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).residualSuffixEnvelope P 1 (Z v) v.2 ≤
        P.mixedUniformResidualEnvelope known k lo hi v :=
  (P.mixedUniformResidualEnvelope_dominates known hbound hlo hlohi).mono (fun v hv => hv (Z v) (hZ v))

end ProphetSecretary.Model
