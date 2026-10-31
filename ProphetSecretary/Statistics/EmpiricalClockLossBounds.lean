import ProphetSecretary.Statistics.EmpiricalClockGapLoss

/-!
# Uniform integrability bounds for the actual paired clock losses

When true and empirical laws are bounded by one and the scalar lies in a fixed
nonnegative interval, both potential losses are bounded by 2+2hi at every
nonnegative candidate time. This auxiliary bound is used for Fubini, not for
the sharper statistical rate. It imposes no restriction on candidate values.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma Instance.clockContinuation_le_initialValue (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z t : ℝ} (hz : 0≤z) (ht : 0≤t) (u : Fin n → ℝ) :
    P.clockContinuation z u t ≤ optimalScalarValue P 1 z := by
  let A := ProphetSecretary.Probability.pendingClockSet t u
  have hrem : max 0 (1-t)≤1 := max_le zero_le_one (sub_le_self 1 ht)
  have h := P.continuationValue_horizon_mono hP A (le_max_left 0 (1-t)) hrem zero_le_one hz
  have hRest : P.continuationValue A 1 1 z ≤ optimalScalarValue P 1 z := by
    simpa only [Instance.continuationValue,Instance.restrictTo,mul_one] using
      optimalScalarValue_restrictBy_le P (stateEmbedding A) hP zero_le_one hz
  exact h.trans hRest

lemma Instance.clockContinuation_mem_bound (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {z hi t : ℝ} (hz : 0≤z) (hzhi : z≤hi) (ht : 0≤t) (u : Fin n → ℝ) :
    P.clockContinuation z u t ∈ Icc (0:ℝ) (1+hi) := by
  have hP := P.integrable_maximum_of_bounded hbound
  have h0 := P.continuationValue_nonnegative hP (ProphetSecretary.Probability.pendingClockSet t u)
    (le_max_left 0 (1-t)) zero_le_one hz
  have h1 := P.clockContinuation_le_initialValue hP hz ht u
  have hb := optimalScalarValue_le_benchmark P hP zero_le_one hz
  have hM := P.expectedMaximum_le_of_bounded zero_le_one hbound
  refine ⟨h0,?_⟩
  simp only [one_mul] at hb
  linarith only [h1,hb,hM,hzhi]

/-- Every real array is accepted; its upper bound is an explicit hypothesis,
which is subsequently supplied almost surely by the actual sample law. -/
theorem paired_clockGapLoss_bounded (P : Instance n)
    (hPbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (y : Reservoir n k) (hy : ∀ j l, y j l≤1)
    {z hi t : ℝ} (hz : 0≤z) (hzhi : z≤hi) (ht : 0≤t) (u : Fin n → ℝ) (x : ℝ) :
    empiricalClockGapLoss P y z u x t ≤ 2+2*hi ∧ trueClockGapLossEmpiricalEval P y z u x t ≤ 2+2*hi := by
  have hPt := P.clockContinuation_mem_bound hPbound hz hzhi ht u
  have hQt := (totalEmpiricalInstance y).clockContinuation_mem_bound
    (totalEmpiricalInstance_bounded y zero_le_one hy) hz hzhi ht u
  let E := |P.clockContinuation z u t-(totalEmpiricalInstance y).clockContinuation z u t|
  have hE0 : 0≤E := abs_nonneg _
  have hE : E≤2+2*hi := by
    dsimp [E]
    rw [abs_le]
    constructor <;> linarith only [hPt.1,hPt.2,hQt.1,hQt.2]
  have hb := paired_clockGapLoss_bound P y z u x t E le_rfl
  have hband : (if |x-P.clockContinuation z u t|≤E then E else 0)≤E := by
    split_ifs
    · exact le_rfl
    · exact hE0
  exact ⟨hb.1.trans (hband.trans hE),hb.2.trans (hband.trans hE)⟩

omit [NeZero k] in
lemma Instance.trainingCoordinates_bounded (P : Instance n) {H : ℝ}
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤H) :
    ∀ᵐ a : ((Fin n × Fin k) → ℝ) ∂P.trainingCoordinateLaw k, ∀ j l, a (j,l)≤H :=
  ae_all_iff.mpr fun j => ae_all_iff.mpr fun l =>
    (measurePreserving_eval (fun q : Fin n × Fin k => P.law q.1) (j,l)).quasiMeasurePreserving.ae (hbound j)

/-- The same training event supports every scalar, clock path, candidate value
and nonnegative time. There is no exceptional set in the learner's budget. -/
theorem Instance.paired_clockGapLoss_bounded_ae (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (hi : ℝ) :
    ∀ᵐ a ∂P.trainingCoordinateLaw k, ∀ z∈Icc (0:ℝ) hi, ∀ u : Fin n → ℝ, ∀ x t : ℝ, 0≤t →
      empiricalClockGapLoss P (reservoirCoordinates.symm a) z u x t ≤ 2+2*hi ∧
        trueClockGapLossEmpiricalEval P (reservoirCoordinates.symm a) z u x t ≤ 2+2*hi := by
  filter_upwards [P.trainingCoordinates_bounded (k:=k) hbound] with a ha
  intro z hz u x t ht
  exact paired_clockGapLoss_bounded P hbound (reservoirCoordinates.symm a) ha hz.1 hz.2 ht u x

end ProphetSecretary.Model
