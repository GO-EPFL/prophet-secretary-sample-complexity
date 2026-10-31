import ProphetSecretary.Probability.FiniteKernelIntegral
import ProphetSecretary.Limiting.ObservationRestrictions

/-!
# Jointly measurable past restrictions of finite observed configurations

Pointwise finiteness is sufficient. There is no bound on the total number of
points in an observed finite configuration.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal

namespace ProphetSecretary.Limiting

noncomputable def finitePast (μ : FiniteMeasure Point) (t : ℝ) : Measure Point :=
  (μ : Measure Point).restrict (Iio t ×ˢ univ)

lemma measurable_finitePast : Measurable (fun q : FiniteMeasure Point × ℝ => finitePast q.1 q.2) := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  let κ : Kernel (FiniteMeasure Point × ℝ) Point :=
    ⟨fun q => (q.1 : Measure Point),measurable_subtype_coe.comp measurable_fst⟩
  have hfinite (q : FiniteMeasure Point × ℝ) : IsFiniteMeasure (κ q) := by
    change IsFiniteMeasure (q.1 : Measure Point)
    infer_instance
  have hT : MeasurableSet {q : (FiniteMeasure Point × ℝ) × Point | q.2 ∈ S ∧ q.2.1 < q.1.2} :=
    (hS.preimage measurable_snd).inter (measurableSet_lt (measurable_fst.comp measurable_snd)
      (measurable_snd.comp measurable_fst))
  have hm := Kernel.measurable_kernel_prodMk_left_of_finite hT hfinite
  have he : (fun q : FiniteMeasure Point × ℝ => finitePast q.1 q.2 S) =
      fun q => κ q (Prod.mk q ⁻¹' {q : (FiniteMeasure Point × ℝ) × Point | q.2 ∈ S ∧ q.2.1 < q.1.2}) := by
    funext q
    rw [finitePast,Measure.restrict_apply hS]
    change (q.1 : Measure Point) (S ∩ Iio q.2 ×ˢ univ) =
      (q.1 : Measure Point) (Prod.mk q ⁻¹' {q : (FiniteMeasure Point × ℝ) × Point | q.2 ∈ S ∧ q.2.1 < q.1.2})
    congr 1
    ext p
    simp
  rw [he]
  exact hm

end ProphetSecretary.Limiting
