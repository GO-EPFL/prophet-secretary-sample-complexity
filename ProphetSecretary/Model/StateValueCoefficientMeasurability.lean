import ProphetSecretary.Model.ContinuationCoefficientMeasurability
import ProphetSecretary.Model.ClockNearLoss

/-!
# Joint finite-state values and clock continuations

Finite unseen states and all scalar coefficients may be measurable parameters.
The proofs use actual true-law coefficient continuity and the proved empirical
Bellman measurability. This supports joint measurability of the candidate loss
after restriction to its other-variable instance.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

lemma Instance.measurable_continuationValue_coefficients (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {A : Ω → Finset (Fin n)} {u w c : Ω → ℝ}
    (hA : Measurable A) (hu : Measurable u) (hw : Measurable w) (hc : Measurable c)
    (hu0 : ∀ ω, 0≤u ω) (hw0 : ∀ ω, 0≤w ω) (hc0 : ∀ ω, 0≤c ω) :
    Measurable (fun ω => P.continuationValue (A ω) (u ω) (w ω) (c ω)) := by
  have hfixed (B : Finset (Fin n)) : Measurable (fun ω => P.continuationValue B (u ω) (w ω) (c ω)) :=
    (P.restrictTo B).measurable_scalarValue_coefficients (P.restrictTo_integrable_maximum B hP)
      hw (hc.mul hu) hw0 (fun ω => mul_nonneg (hc0 ω) (hu0 ω))
  have hall : Measurable (fun z : Finset (Fin n) × Ω => P.continuationValue z.1 (u z.2) (w z.2) (c z.2)) :=
    measurable_from_prod_countable_right hfixed
  have hpair : Measurable (fun ω => (A ω,ω)) := hA.prodMk measurable_id
  convert hall.comp hpair using 1
  funext ω
  rfl

lemma measurable_totalEmpirical_continuationValue_coefficients {k : ℕ} [NeZero k]
    {y : Ω → Reservoir n k} {A : Ω → Finset (Fin n)} {u w c : Ω → ℝ}
    (hy : ∀ j l, Measurable (fun ω => y ω j l)) (hA : Measurable A)
    (hu : Measurable u) (hw : Measurable w) (hc : Measurable c)
    (hu0 : ∀ ω, 0≤u ω) (hw0 : ∀ ω, 0<w ω) (hc0 : ∀ ω, 0≤c ω) :
    Measurable (fun ω => (totalEmpiricalInstance (y ω)).continuationValue (A ω) (u ω) (w ω) (c ω)) := by
  have hfixed (B : Finset (Fin n)) : Measurable (fun ω =>
      (totalEmpiricalInstance (y ω)).continuationValue B (u ω) (w ω) (c ω)) := by
    have hv := measurable_optimalScalarValue_totalEmpirical
      (y:=fun ω j l => y ω (stateEmbedding B j) l) (w:=w) (c:=fun ω => c ω*u ω)
      (fun j l => hy _ l) hw (hc.mul hu) hw0 (fun ω => mul_nonneg (hc0 ω) (hu0 ω))
    convert hv using 1
    funext ω
    rw [Instance.continuationValue,totalEmpiricalInstance_restrictTo]
  have hall : Measurable (fun z : Finset (Fin n) × Ω =>
      (totalEmpiricalInstance (y z.2)).continuationValue z.1 (u z.2) (w z.2) (c z.2)) :=
    measurable_from_prod_countable_right hfixed
  have hpair : Measurable (fun ω => (A ω,ω)) := hA.prodMk measurable_id
  convert hall.comp hpair using 1
  funext ω
  rfl

lemma measurable_pendingClockSet_parameters {t : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (ht : Measurable t) (hu : ∀ j, Measurable (fun ω => u ω j)) :
    Measurable (fun ω => ProphetSecretary.Probability.pendingClockSet (t ω) (u ω)) := by
  rw [measurable_finset_iff]
  intro j
  apply measurableSet_setOf.mp
  simpa only [Set.preimage_setOf_eq,ProphetSecretary.Probability.mem_pendingClockSet] using measurableSet_le ht (hu j)

lemma Instance.measurable_clockContinuation_parameters (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z t : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hz : Measurable z) (ht : Measurable t) (hu : ∀ j, Measurable (fun ω => u ω j)) (hz0 : ∀ ω, 0≤z ω) :
    Measurable (fun ω => P.clockContinuation (z ω) (u ω) (t ω)) :=
  P.measurable_continuationValue_coefficients hP (measurable_pendingClockSet_parameters ht hu)
    (measurable_const.max (measurable_const.sub ht)) measurable_const hz
    (fun _ => le_max_left _ _) (fun _ => zero_le_one) hz0

lemma measurable_totalEmpirical_clockContinuation_parameters {k : ℕ} [NeZero k]
    {y : Ω → Reservoir n k} {z t : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ j l, Measurable (fun ω => y ω j l)) (hz : Measurable z) (ht : Measurable t)
    (hu : ∀ j, Measurable (fun ω => u ω j)) (hz0 : ∀ ω, 0≤z ω) :
    Measurable (fun ω => (totalEmpiricalInstance (y ω)).clockContinuation (z ω) (u ω) (t ω)) :=
  measurable_totalEmpirical_continuationValue_coefficients hy (measurable_pendingClockSet_parameters ht hu)
    (measurable_const.max (measurable_const.sub ht)) measurable_const hz
    (fun _ => le_max_left _ _) (fun _ => zero_lt_one) hz0

end ProphetSecretary.Model
