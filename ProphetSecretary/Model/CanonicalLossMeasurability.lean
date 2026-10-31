import ProphetSecretary.Model.ContinuationCoefficientMeasurability
import ProphetSecretary.Model.PairedCanonicalLoss

/-!
# Joint measurability of both canonical comparison losses

Training arrays, independent seeds, arrival clocks and candidate values may
all be parameters. A training-selected nonnegative scalar is treated jointly
for measurability, while it remains fixed during the separate time integrals.
Both directions use the exact canonical gap representation.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Analysis

lemma measurable_threshold_gapLoss {Ω : Type*} [MeasurableSpace Ω]
    {g ĝ : Ω → ℝ} (hg : Measurable g) (hĝ : Measurable ĝ) :
    Measurable (fun ω => gapLoss (decide (0≤ĝ ω)) (g ω)) := by
  have hm : Measurable (fun ω => if 0≤ĝ ω then max (-g ω) 0 else max (g ω) 0) := Measurable.ite (measurableSet_le measurable_const hĝ)
    (hg.neg.max measurable_const) (hg.max measurable_const)
  convert hm using 1
  funext ω
  by_cases h : 0≤ĝ ω <;> simp [gapLoss,h]

end ProphetSecretary.Analysis

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k] {Ω : Type*} [MeasurableSpace Ω]

/-- Both actual local performance losses are jointly measurable on the entire
real array space, including null training outcomes after totalization. -/
theorem measurable_pairedCanonical_arrivalLoss (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    {y : Ω → Reservoir n k} {z : Ω → ℝ} {x u : Ω → Fin n → ℝ}
    (hy : ∀ j l, Measurable (fun ω => y ω j l)) (hz : Measurable z) (hz0 : ∀ ω, 0≤z ω)
    (hx : ∀ j, Measurable (fun ω => x ω j)) (hu : ∀ j, Measurable (fun ω => u ω j)) (i : Fin n) :
    Measurable (fun ω => ((totalEmpiricalInstance (y ω)).valuePolicy
      (totalEmpiricalInstance_integrable (y ω)) zero_le_one (hz0 ω)).rule.arrivalBellmanLoss P 1 (z ω) () (x ω) (u ω) i) ∧
    Measurable (fun ω => (P.valuePolicy hP zero_le_one (hz0 ω)).rule.arrivalBellmanLoss
      (totalEmpiricalInstance (y ω)) 1 (z ω) () (x ω) (u ω) i) := by
  have hV := P.measurable_continuationAtArrival_coefficients hP measurable_const hz
    (fun _ => zero_lt_one) hz0 hx hu i
  have hVhat := measurable_totalEmpirical_continuationAtArrival_coefficients hy measurable_const hz
    (fun _ => zero_lt_one) hz0 hx hu i
  have hg := (hx i).sub hV
  have hĝ := (hx i).sub hVhat
  constructor
  · have hM := ProphetSecretary.Analysis.measurable_threshold_gapLoss hg hĝ
    have heq : (fun ω => ((totalEmpiricalInstance (y ω)).valuePolicy
        (totalEmpiricalInstance_integrable (y ω)) zero_le_one (hz0 ω)).rule.arrivalBellmanLoss P 1 (z ω) () (x ω) (u ω) i) =
        (fun ω => ProphetSecretary.Analysis.gapLoss (decide (0≤x ω i-(totalEmpiricalInstance (y ω)).continuationAtArrival 1 (z ω) (x ω) (u ω) i))
          (x ω i-P.continuationAtArrival 1 (z ω) (x ω) (u ω) i)) :=
      funext fun ω => (totalEmpiricalInstance (y ω)).valuePolicy_arrivalLoss_eq_gapLoss P (totalEmpiricalInstance_integrable _) (hz0 ω) (x ω) (u ω) i
    rw [heq]
    exact hM
  · have hM := ProphetSecretary.Analysis.measurable_threshold_gapLoss hĝ hg
    have heq : (fun ω => (P.valuePolicy hP zero_le_one (hz0 ω)).rule.arrivalBellmanLoss
        (totalEmpiricalInstance (y ω)) 1 (z ω) () (x ω) (u ω) i) =
        (fun ω => ProphetSecretary.Analysis.gapLoss (decide (0≤x ω i-P.continuationAtArrival 1 (z ω) (x ω) (u ω) i))
          (x ω i-(totalEmpiricalInstance (y ω)).continuationAtArrival 1 (z ω) (x ω) (u ω) i)) :=
      funext fun ω => P.valuePolicy_arrivalLoss_eq_gapLoss (totalEmpiricalInstance (y ω)) hP (hz0 ω) (x ω) (u ω) i
    rw [heq]
    exact hM

end ProphetSecretary.Model
