import ProphetSecretary.Limiting.FirstAcceptanceSelectedTags
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integrating the countable selected-tag comparison
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.FirstAcceptance

variable {Ω : Type*} [MeasurableSpace Ω]

lemma integrable_selectedTag (A : Ω → ℕ → Prop) (u a : Ω → ℕ → ℝ)
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (hA : ∀ i, MeasurableSet {ω | A ω i})
    (hu : ∀ i, Measurable (fun ω => u ω i)) (ha : ∀ i, Measurable (fun ω => a ω i))
    {D : ℝ} (hD : 0 ≤ D) (hBound : ∀ᵐ ω ∂μ, ∀ i, |a ω i| ≤ D) :
    Integrable (reward 0 A u a) μ := by
  apply Integrable.of_bound (measurable_reward 0 hA hu ha).aestronglyMeasurable D
  filter_upwards [hBound] with ω hω
  simpa only [Real.norm_eq_abs] using reward_abs_le A u a ω hD hω

lemma integral_selectedTag_difference_le (A B : Ω → ℕ → Prop)
    (u x a : Ω → ℕ → ℝ) (present : Ω → ℕ → Prop)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hA : ∀ i, MeasurableSet {ω | A ω i}) (hB : ∀ i, MeasurableSet {ω | B ω i})
    (hu : ∀ i, Measurable (fun ω => u ω i)) (ha : ∀ i, Measurable (fun ω => a ω i))
    (hAP : ∀ ω i, A ω i → present ω i) (hBP : ∀ ω i, B ω i → present ω i)
    {D b η : ℝ} (hD : 0 ≤ D) (hb : 0 < b) (hη : 0 < η)
    (hBound : ∀ᵐ ω ∂μ, ∀ i, |a ω i| ≤ D)
    (hZero : ∀ᵐ ω ∂μ, ∀ i, x ω i < b → a ω i=0)
    (hPair : MeasurableSet {ω | ClosePositivePair (present ω) (b/2) η (x ω) (u ω)})
    (hError : Integrable (fun ω => |reward 0 A u x ω-reward 0 B u x ω|+
      |stoppingTime A u ω-stoppingTime B u ω|) μ) :
    (∫ ω, |reward 0 A u a ω-reward 0 B u a ω| ∂μ) ≤
      2*D*(2*(∫ ω, |reward 0 A u x ω-reward 0 B u x ω|+
        |stoppingTime A u ω-stoppingTime B u ω| ∂μ)/b+
      (∫ ω, |reward 0 A u x ω-reward 0 B u x ω|+
        |stoppingTime A u ω-stoppingTime B u ω| ∂μ)/η+
      μ.real {ω | ClosePositivePair (present ω) (b/2) η (x ω) (u ω)}) := by
  let Error := fun ω => |reward 0 A u x ω-reward 0 B u x ω|+
    |stoppingTime A u ω-stoppingTime B u ω|
  let Pair : Set Ω := {ω | ClosePositivePair (present ω) (b/2) η (x ω) (u ω)}
  let I : Ω → ℝ := Pair.indicator (fun _ => 1)
  have hI : Integrable I μ := (integrable_const (1 : ℝ)).indicator hPair
  have hIeq : (∫ ω, I ω ∂μ)=μ.real Pair := integral_indicator_one hPair
  have hTag := ((integrable_selectedTag A u a μ hA hu ha hD hBound).sub
    (integrable_selectedTag B u a μ hB hu ha hD hBound)).abs
  have hRHS : Integrable (fun ω => 2*D*(2*Error ω/b+Error ω/η+I ω)) μ :=
    ((((hError.const_mul 2).div_const b).add (hError.div_const η)).add hI).const_mul (2*D)
  have hPoint : ∀ᵐ ω ∂μ, |reward 0 A u a ω-reward 0 B u a ω| ≤
      2*D*(2*Error ω/b+Error ω/η+I ω) := by
    filter_upwards [hBound,hZero] with ω hω hz
    have h := selectedTag_difference_le A B u x a ω (present ω) (hAP ω) (hBP ω) hD hb hη hω hz
    apply h.trans
    apply mul_le_mul_of_nonneg_left _ (show 0 ≤ 2*D by positivity)
    have hR : |reward 0 A u x ω-reward 0 B u x ω| ≤ Error ω := le_add_of_nonneg_right (abs_nonneg _)
    have hT : |stoppingTime A u ω-stoppingTime B u ω| ≤ Error ω := le_add_of_nonneg_left (abs_nonneg _)
    have hRR := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hR (show (0 : ℝ) ≤ 2 by norm_num)) hb.le
    have hTT := div_le_div_of_nonneg_right hT hη.le
    simpa only [I,Pair,Set.indicator_apply,Pi.one_apply,mem_setOf_eq] using
      add_le_add (add_le_add hRR hTT) (le_refl (I ω))
  have h := integral_mono_ae hTag hRHS hPoint
  have hE : Integrable Error μ := hError
  rw [integral_const_mul,
    integral_add (f := fun ω => 2*Error ω/b+Error ω/η) (g := I)
      (((hE.const_mul 2).div_const b).add (hE.div_const η)) hI,
    integral_add (f := fun ω => 2*Error ω/b) (g := fun ω => Error ω/η)
      ((hE.const_mul 2).div_const b) (hE.div_const η),
    integral_div,integral_div,integral_const_mul,hIeq] at h
  exact h

end ProphetSecretary.Limiting.FirstAcceptance
