import ProphetSecretary.Model.OuterRetainedMaximum
import ProphetSecretary.Model.OuterRetentionTailCount

/-!
# Measurable retained positive counts

Positive retained values are tested after the actual independent value/tag
map; integrating these tests gives a measurable population tail count.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Model.Instance
variable {n : ℕ}

lemma measurable_retainedAtTag_positiveCount (P : Instance n) :
    Measurable (fun t : ℝ × ℝ => (P.retainedAtTag t).positiveCount) := by
  have hEach (i : Fin n) : Measurable (fun t : ℝ × ℝ => ((P.retainedAtTag t).law i).real (Ioi 0)) := by
    let μ := (P.law i).prod uniformClock
    have hF : Measurable (fun p : (ℝ × ℝ) × (ℝ × ℝ) => if 0<retainAboveTag p.1 p.2 then (1:ℝ) else 0) :=
      measurable_const.ite (measurableSet_lt measurable_const measurable_retainAboveTag) measurable_const
    have hEq : (fun t : ℝ × ℝ => ((P.retainedAtTag t).law i).real (Ioi 0))=
        (fun t => ∫ z, (if 0<retainAboveTag t z then (1:ℝ) else 0) ∂μ) := by
      funext t
      change (μ.map (retainAboveTag t)).real (Ioi 0)=_
      rw [map_measureReal_apply (measurable_retainAboveTag_fixed t) measurableSet_Ioi]
      change μ.real {z : ℝ × ℝ | 0<retainAboveTag t z}=_
      have hA : MeasurableSet {z : ℝ × ℝ | 0<retainAboveTag t z} :=
        measurableSet_lt measurable_const (measurable_retainAboveTag_fixed t)
      have hI := integral_indicator_const (μ:=μ) (1:ℝ) hA
      simpa only [Set.indicator_apply,Set.mem_setOf_eq,smul_eq_mul,mul_one] using hI.symm
    rw [hEq]
    exact (hF.stronglyMeasurable.integral_prod_right' (ν:=μ)).measurable
  exact Finset.measurable_sum Finset.univ fun i _ => hEach i

end ProphetSecretary.Model.Instance
