import ProphetSecretary.Model.MixedEmpiricalValueMeasurability
import ProphetSecretary.Model.StateValueCoefficientMeasurability

/-!
# Joint actual mixed state values and clock continuations

Finite states, coefficients and clocks may vary jointly as measurable parameters.
Exact known-law restrictions and Bellman-derived mixed value measurability justify
these functions without an assumed measurable optimizer selection.
-/

open MeasureTheory
open scoped Classical
namespace ProphetSecretary.Model
variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_mixed_continuationValue_coefficients {k : ℕ} [NeZero k]
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    {y : Ω → Reservoir n k} {A : Ω → Finset (Fin n)} {u w c : Ω → ℝ}
    (hy : ∀ j l, Measurable (fun ω => y ω j l)) (hA : Measurable A)
    (hu : Measurable u) (hw : Measurable w) (hc : Measurable c)
    (hu0 : ∀ ω, 0≤u ω) (hw0 : ∀ ω, 0<w ω) (hc0 : ∀ ω, 0≤c ω) :
    Measurable (fun ω => (mixedEmpiricalInstance P known (y ω)).continuationValue (A ω) (u ω) (w ω) (c ω)) := by
  have hfixed (B : Finset (Fin n)) : Measurable (fun ω =>
      (mixedEmpiricalInstance P known (y ω)).continuationValue B (u ω) (w ω) (c ω)) := by
    have hv := measurable_optimalScalarValue_mixedEmpirical (P.restrictTo B)
      (P.restrictTo_integrable_maximum B hP) (knownInState known B)
      (y:=fun ω j l => y ω (stateEmbedding B j) l) (w:=w) (c:=fun ω => c ω*u ω)
      (fun j l => hy _ l) hw (hc.mul hu) hw0 (fun ω => mul_nonneg (hc0 ω) (hu0 ω))
    convert hv using 1
    funext ω
    rw [Instance.continuationValue,mixedEmpiricalInstance_restrictTo]
  have hall : Measurable (fun z : Finset (Fin n) × Ω =>
      (mixedEmpiricalInstance P known (y z.2)).continuationValue z.1 (u z.2) (w z.2) (c z.2)) :=
    measurable_from_prod_countable_right hfixed
  have hpair : Measurable (fun ω => (A ω,ω)) := hA.prodMk measurable_id
  convert hall.comp hpair using 1
  funext ω
  rfl

lemma measurable_mixed_clockContinuation_parameters {k : ℕ} [NeZero k]
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    {y : Ω → Reservoir n k} {z t : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ j l, Measurable (fun ω => y ω j l)) (hz : Measurable z) (ht : Measurable t)
    (hu : ∀ j, Measurable (fun ω => u ω j)) (hz0 : ∀ ω, 0≤z ω) :
    Measurable (fun ω => (mixedEmpiricalInstance P known (y ω)).clockContinuation (z ω) (u ω) (t ω)) :=
  measurable_mixed_continuationValue_coefficients P hP known hy (measurable_pendingClockSet_parameters ht hu)
    (measurable_const.max (measurable_const.sub ht)) measurable_const hz
    (fun _ => le_max_left _ _) (fun _ => zero_lt_one) hz0

end ProphetSecretary.Model
