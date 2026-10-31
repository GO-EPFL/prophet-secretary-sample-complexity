import Mathlib.Probability.Kernel.MeasurableLIntegral
import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# Parameter integrals for pointwise finite measure families

The library's measurable section lemma requires only pointwise finiteness.
Simple-function approximation extends it to nonnegative parameter integrals,
without an unnecessary uniform bound on the masses of the parameter family.
-/

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal

namespace ProphetSecretary.Probability

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

lemma measurable_lintegral_pointwiseFinite (κ : Kernel α β)
    (hfinite : ∀ a, IsFiniteMeasure (κ a)) {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun a => ∫⁻ b, f (a,b) ∂κ a) := by
  let F : ℕ → SimpleFunc (α × β) ℝ≥0∞ := SimpleFunc.eapprox f
  have he : ∀ a, ⨆ n, F n a = f a := SimpleFunc.iSup_eapprox_apply hf
  simp only [Prod.forall] at he
  simp_rw [← he]
  have hi : ∀ a, (∫⁻ b, ⨆ n, F n (a,b) ∂κ a) = ⨆ n, ∫⁻ b, F n (a,b) ∂κ a := by
    intro a
    rw [lintegral_iSup]
    · exact fun n => (F n).measurable.comp measurable_prodMk_left
    · exact fun i j hij b => SimpleFunc.monotone_eapprox f hij _
  simp_rw [hi]
  refine Measurable.iSup (fun n => ?_)
  refine SimpleFunc.induction
    (motive := fun g => Measurable (fun a : α => ∫⁻ b : β, g (a,b) ∂κ a)) ?_ ?_ (F n)
  · intro c S hS
    simp only [SimpleFunc.const_zero,SimpleFunc.coe_piecewise,SimpleFunc.coe_const,
      SimpleFunc.coe_zero,Set.piecewise_eq_indicator]
    have heq (a : α) : (∫⁻ b, S.indicator (fun _ => c) (a,b) ∂κ a) =
        c * κ a (Prod.mk a ⁻¹' S) := by
      rw [lintegral_indicator_const_comp measurable_prodMk_left hS]
    change Measurable (fun a => ∫⁻ b, S.indicator (fun _ : α × β => c) (a,b) ∂κ a)
    rw [funext heq]
    exact (Kernel.measurable_kernel_prodMk_left_of_finite hS hfinite).const_mul c
  · intro g h _ hg hh
    simp only [SimpleFunc.coe_add,Pi.add_apply]
    have hadd : (fun a => ∫⁻ b, g (a,b) + h (a,b) ∂κ a) =
        (fun a => ∫⁻ b, g (a,b) ∂κ a) + fun a => ∫⁻ b, h (a,b) ∂κ a := by
      funext a
      rw [Pi.add_apply,lintegral_add_left (by fun_prop)]
    rw [hadd]
    exact hg.add hh

lemma measurable_lintegral_finiteFamily {μ : α → FiniteMeasure β} (hμ : Measurable μ)
    {f : α × β → ℝ≥0∞} (hf : Measurable f) :
    Measurable (fun a => ∫⁻ b, f (a,b) ∂(μ a : Measure β)) := by
  let κ : Kernel α β := ⟨fun a => (μ a : Measure β),measurable_subtype_coe.comp hμ⟩
  have hfin (a : α) : IsFiniteMeasure (κ a) := by
    change IsFiniteMeasure (μ a : Measure β)
    infer_instance
  exact measurable_lintegral_pointwiseFinite κ hfin hf

end ProphetSecretary.Probability
