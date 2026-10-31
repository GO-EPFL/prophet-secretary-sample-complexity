import ProphetSecretary.Limiting.CountableInstance
import Mathlib.Topology.Algebra.Indicator

/-!
# Upper bands are continuity bands relative to their certified cap

On the actual support, the indicator of (b,H] agrees with the indicator of
(b,infinity). Only an atom at b is exceptional; an atom at H is allowed.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting

lemma upperBand_indicator_continuousWithinAt_cap_ae (μ : Measure ℝ) (H : ℝ≥0)
    (hCap : ∀ᵐ x ∂μ, x∈Icc (0 : ℝ) H) (b : ℝ) (hAtom : μ {b}=0) :
    ∀ᵐ x ∂μ, ContinuousWithinAt ((Ioc b (H : ℝ)).indicator (fun _ : ℝ => (1 : ℝ))) (Icc (0 : ℝ) H) x := by
  have hFront : μ (frontier (Ioi b))=0 := by rw [frontier_Ioi]; exact hAtom
  have hEq : ∀ y∈Icc (0 : ℝ) H,
      (Ioc b (H : ℝ)).indicator (fun _ : ℝ => (1 : ℝ)) y=(Ioi b).indicator (fun _ : ℝ => (1 : ℝ)) y := by
    intro y hy
    by_cases hb : b<y
    · rw [Set.indicator_of_mem (show y∈Ioc b (H : ℝ) from ⟨hb,hy.2⟩),
        Set.indicator_of_mem (show y∈Ioi b from hb)]
    · rw [Set.indicator_of_notMem (show y∉Ioc b (H : ℝ) from fun h => hb h.1),
        Set.indicator_of_notMem (show y∉Ioi b from hb)]
  filter_upwards [hCap,measure_eq_zero_iff_ae_notMem.mp hFront] with x hx hOutside
  have hContinuous : ContinuousAt ((Ioi b).indicator (fun _ : ℝ => (1 : ℝ))) x :=
    (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousOn.continuousAt_indicator hOutside
  exact hContinuous.continuousWithinAt.congr_of_mem hEq hx

lemma CountableInstance.upperBand_indicator_continuousWithinAt_ae (B : CountableInstance)
    (b : ℝ) (hAtom : B.intensity {b}=0) :
    ∀ᵐ x ∂B.intensity,
      ContinuousWithinAt ((Ioc b (B.cap : ℝ)).indicator (fun _ : ℝ => (1 : ℝ))) (Icc (0 : ℝ) B.cap) x :=
  upperBand_indicator_continuousWithinAt_cap_ae B.intensity B.cap
    (B.intensity_supported.mono (fun _ hx => ⟨B.terminal.property.trans hx.1.le,hx.2⟩)) b hAtom

end ProphetSecretary.Limiting
