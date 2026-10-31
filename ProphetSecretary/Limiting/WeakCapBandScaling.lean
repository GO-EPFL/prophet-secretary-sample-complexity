import ProphetSecretary.Limiting.FiniteBandScaling
import ProphetSecretary.Probability.WeakFiniteAlmostContinuousIntegral
import ProphetSecretary.Probability.CenteredValueScore

/-!
# Weak band scaling with continuity relative to the actual cap

The band indicator need only be continuous from within the common support.
A continuous clamp extends it to the real line for almost-continuous weak
integral transfer. In particular an upper band may contain an atom at the cap.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability

 theorem bandScaledIntensity_tendsto_of_cap_relative_continuity {Γ : Type*} {l : Filter Γ}
    [l.IsCountablyGenerated] {μs : Γ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (H : ℝ≥0) (hCaps : ∀ m, ∀ᵐ x ∂(μs m : Measure ℝ), x∈Icc (0 : ℝ) H)
    (hCap : ∀ᵐ x ∂(μ : Measure ℝ), x∈Icc (0 : ℝ) H)
    (hWeak : Tendsto μs l (𝓝 μ)) {S : Set ℝ} (hS : MeasurableSet S) (r : ℝ≥0)
    (hCont : ∀ᵐ x ∂(μ : Measure ℝ),
      ContinuousWithinAt (S.indicator (fun _ : ℝ => (1 : ℝ))) (Icc (0 : ℝ) H) x) :
    Tendsto (fun m => bandScaledIntensity (μs m) S r) l (𝓝 (bandScaledIntensity μ S r)) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  let I := S.indicator (fun _ : ℝ => (1 : ℝ))
  let G := fun x : ℝ => f x*(1+((r : ℝ)-1)*I (boundedOfferValue H x))
  have hIMeas : Measurable I := measurable_const.indicator hS
  have hGMeas : Measurable G := f.continuous.measurable.mul
    (measurable_const.add ((hIMeas.comp (boundedOfferValue H).continuous.measurable).const_mul ((r : ℝ)-1)))
  have hGFactor (x : ℝ) : G x=f x*bandScaleFactor S r (boundedOfferValue H x) := by
    by_cases hx : boundedOfferValue H x∈S
    · simp only [G,I,Set.indicator_of_mem hx,bandScaleFactor,if_pos hx]
      ring
    · simp only [G,I,Set.indicator_of_notMem hx,bandScaleFactor,if_neg hx,mul_zero,add_zero]
  have hGBound (x : ℝ) : |G x|≤‖f‖*((r : ℝ)+1) := by
    rw [hGFactor x,abs_mul,abs_of_nonneg (bandScaleFactor_nonnegative S r _)]
    have hf : |f x|≤‖f‖ := by simpa only [Real.norm_eq_abs] using f.norm_coe_le_norm x
    have hr : bandScaleFactor S r (boundedOfferValue H x)≤(r : ℝ)+1 := by
      unfold bandScaleFactor
      split_ifs
      · exact le_add_of_nonneg_right zero_le_one
      · exact le_add_of_nonneg_left r.property
    exact mul_le_mul hf hr (bandScaleFactor_nonnegative S r _) (norm_nonneg f)
  have hGCont : ∀ᵐ x ∂(μ : Measure ℝ), ContinuousAt G x := by
    filter_upwards [hCont,hCap] with x hx hRange
    have hI : ContinuousWithinAt (I ∘ boundedOfferValue H) univ x :=
      hx.comp_of_eq (boundedOfferValue H).continuous.continuousAt.continuousWithinAt
        (fun y _ => boundedOfferValue_mem_range H y) (boundedOfferValue_eq H hRange)
    have hIAt : ContinuousAt (I ∘ boundedOfferValue H) x := hI.continuousAt Filter.univ_mem
    exact f.continuous.continuousAt.mul (continuousAt_const.add (hIAt.const_mul ((r : ℝ)-1)))
  have hIntegral (ν : FiniteMeasure ℝ) (hν : ∀ᵐ x ∂(ν : Measure ℝ), x∈Icc (0 : ℝ) H) :
      (∫ x, f x ∂(bandScaledIntensity ν S r : Measure ℝ))=∫ x, G x ∂(ν : Measure ℝ) := by
    rw [bandScaledIntensity_toMeasure ν hS r]
    have hDensity : Measurable (fun x : ℝ => ENNReal.ofReal (bandScaleFactor S r x)) :=
      ENNReal.measurable_ofReal.comp (measurable_bandScaleFactor hS r)
    have hFormula := integral_withDensity_eq_integral_toReal_smul (μ := (ν : Measure ℝ)) hDensity
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)) (fun x => f x)
    apply hFormula.trans
    apply integral_congr_ae
    filter_upwards [hν] with x hx
    rw [ENNReal.toReal_ofReal (bandScaleFactor_nonnegative S r x),smul_eq_mul,hGFactor x,boundedOfferValue_eq H hx,mul_comm]
  have h := finite_integral_tendsto_of_weak_ae_continuous_bounded hWeak hGMeas hGBound hGCont
  have hEq : (fun m => ∫ x, f x ∂(bandScaledIntensity (μs m) S r : Measure ℝ))=
      fun m => ∫ x, G x ∂(μs m : Measure ℝ) := funext (fun m => hIntegral (μs m) (hCaps m))
  rw [hEq,hIntegral μ hCap]
  exact h

end ProphetSecretary.Limiting
