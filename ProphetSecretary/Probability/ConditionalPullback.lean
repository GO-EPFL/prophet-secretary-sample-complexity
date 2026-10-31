import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Conditional expectation under an actual measure-preserving pullback

The observation sigma algebra is pulled back by the same map as the random
variable. The identity follows from actual set-integral transport and conditional
expectation uniqueness. In the posterior experiment the map is the constructed
training/online column swap, not an assumed conditional independence interface.
-/

open MeasureTheory Set
namespace ProphetSecretary.Probability
variable {Ω : Type*} [m0 : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem condExp_comp_measurePreserving {T : Ω → Ω} (hT : MeasurePreserving T μ μ)
    {m : MeasurableSpace Ω} (hm : m≤m0) {f : Ω → ℝ} (hf : Integrable f μ) :
    (fun ω => μ[f|m] (T ω)) =ᵐ[μ] μ[(fun ω => f (T ω))|m.comap T] := by
  letI : MeasurableSpace Ω := m0
  have hmT : m.comap T≤m0 := (MeasurableSpace.comap_mono hm).trans hT.measurable.comap_le
  have hG : StronglyMeasurable[m.comap T] (fun ω => μ[f|m] (T ω)) := by
    have hTm : @Measurable Ω Ω (m.comap T) m T := Measurable.of_comap_le le_rfl
    exact (stronglyMeasurable_condExp (μ:=μ) (m:=m) (f:=f)).comp_measurable hTm
  have hGI : Integrable (fun ω => μ[f|m] (T ω)) μ :=
    hT.integrable_comp_of_integrable integrable_condExp
  have hFI : Integrable (fun ω => f (T ω)) μ := hT.integrable_comp_of_integrable hf
  apply ae_eq_condExp_of_forall_setIntegral_eq hmT hFI (fun _ _ _ => hGI.integrableOn) ?_ hG.aestronglyMeasurable
  intro E hE _
  obtain ⟨s,hs,he⟩ := MeasurableSpace.measurableSet_comap.mp hE
  have hGmapMeas : AEStronglyMeasurable (μ[f|m]) (μ.map T) := by
    rw [hT.map_eq]
    exact (integrable_condExp (μ:=μ) (m:=m) (f:=f)).aestronglyMeasurable
  have hFmapMeas : AEStronglyMeasurable f (μ.map T) := by
    rw [hT.map_eq]
    exact hf.aestronglyMeasurable
  have hGmap := setIntegral_map (μ:=μ) (g:=T) (hm s hs) hGmapMeas hT.measurable.aemeasurable
  have hFmap := setIntegral_map (μ:=μ) (g:=T) (hm s hs) hFmapMeas hT.measurable.aemeasurable
  rw [hT.map_eq,he] at hGmap hFmap
  exact hGmap.symm.trans ((setIntegral_condExp hm hf hs).trans hFmap)

end ProphetSecretary.Probability
