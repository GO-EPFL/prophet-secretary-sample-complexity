import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Conditional projections through an actual product-law representation

This version allows different source and target spaces. The information sigma
algebra is pulled back by the same measure-preserving map as the random variable.
-/

open MeasureTheory Set
namespace ProphetSecretary.Probability
variable {Ω Γ : Type*} [mΩ : MeasurableSpace Ω] [mΓ : MeasurableSpace Γ]
    (μ : Measure Ω) (ν : Measure Γ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]

theorem condExp_pullback_measurePreserving {T : Ω → Γ} (hT : MeasurePreserving T μ ν)
    {m : MeasurableSpace Γ} (hm : m≤mΓ) {f : Γ → ℝ} (hf : Integrable f ν) :
    (fun ω => ν[f|m] (T ω)) =ᵐ[μ] μ[(fun ω => f (T ω))|m.comap T] := by
  letI : MeasurableSpace Γ := mΓ
  have hmT : m.comap T≤mΩ := (MeasurableSpace.comap_mono hm).trans hT.measurable.comap_le
  have hG : StronglyMeasurable[m.comap T] (fun ω => ν[f|m] (T ω)) := by
    have hTm : @Measurable Ω Γ (m.comap T) m T := Measurable.of_comap_le le_rfl
    exact (stronglyMeasurable_condExp (μ:=ν) (m:=m) (f:=f)).comp_measurable hTm
  have hGI : Integrable (fun ω => ν[f|m] (T ω)) μ :=
    hT.integrable_comp_of_integrable integrable_condExp
  have hFI : Integrable (fun ω => f (T ω)) μ := hT.integrable_comp_of_integrable hf
  apply ae_eq_condExp_of_forall_setIntegral_eq hmT hFI (fun _ _ _ => hGI.integrableOn) ?_ hG.aestronglyMeasurable
  intro E hE _
  obtain ⟨s,hs,he⟩ := MeasurableSpace.measurableSet_comap.mp hE
  have hGmapMeas : AEStronglyMeasurable (ν[f|m]) (μ.map T) := by
    rw [hT.map_eq]
    exact (integrable_condExp (μ:=ν) (m:=m) (f:=f)).aestronglyMeasurable
  have hFmapMeas : AEStronglyMeasurable f (μ.map T) := by
    rw [hT.map_eq]
    exact hf.aestronglyMeasurable
  have hGmap := setIntegral_map (μ:=μ) (g:=T) (hm s hs) hGmapMeas hT.measurable.aemeasurable
  have hFmap := setIntegral_map (μ:=μ) (g:=T) (hm s hs) hFmapMeas hT.measurable.aemeasurable
  rw [hT.map_eq,he] at hGmap hFmap
  exact hGmap.symm.trans ((setIntegral_condExp hm hf hs).trans hFmap)

end ProphetSecretary.Probability
