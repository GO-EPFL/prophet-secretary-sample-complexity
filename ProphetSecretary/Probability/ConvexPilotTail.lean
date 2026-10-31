import ProphetSecretary.Analysis.ConvexPilotBoundary
import Mathlib.MeasureTheory.Measure.Real

/-!
# A random convex minimizer from two fixed-weight tails

The two level locations are chosen from the true function before observing
any data. Hence their probability bounds apply at deterministic weights.
Measurability of a concrete minimizer is a separate obligation when applying
this comparison to expected pilot losses.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Probability
open ProphetSecretary.Analysis

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem convex_pilot_tail {F : ℝ → ℝ} {lo hi a s q : ℝ}
    (hF : ConvexOn ℝ (Icc lo hi) F) (hFc : ContinuousOn F (Icc lo hi))
    (ha : a ∈ Icc lo hi) (hFa : F a ≤ s) (hq : 0 ≤ q)
    (G : Ω → ℝ → ℝ) (b : Ω → ℝ)
    (hG : ∀ᵐ ω ∂μ, ConvexOn ℝ (Icc lo hi) (G ω))
    (hb : ∀ᵐ ω ∂μ, b ω ∈ Icc lo hi)
    (hMin : ∀ᵐ ω ∂μ, G ω (b ω) ≤ G ω a)
    (hTail : ∀ x ∈ Icc lo hi, F x = s → μ.real {ω | G ω x ≤ s/2} ≤ q) :
    μ.real {ω | s < F (b ω)} ≤ μ.real {ω | s/2 < G ω a}+2*q := by
  classical
  obtain ⟨D,hCard,hLevel,hControl⟩ := exists_two_pilot_level_points hF hFc ha hFa
  let E := ⋃ x ∈ D, {ω | G ω x ≤ s/2}
  have hSub : ∀ᵐ ω ∂μ, ω ∈ {ω | s < F (b ω)} → ω ∈ ({ω | s/2 < G ω a} ∪ E) := by
    filter_upwards [hG,hb,hMin] with ω hGω hbω hMinω
    intro hBad
    by_cases hZ : s/2 < G ω a
    · exact Or.inl hZ
    · right
      obtain ⟨x,hx,hxG⟩ := hControl (G ω) hGω (b ω) hbω hBad hMinω
      exact mem_iUnion₂.mpr ⟨x,hx,hxG.trans (le_of_not_gt hZ)⟩
  have hM : μ.real {ω | s < F (b ω)} ≤ μ.real ({ω | s/2 < G ω a} ∪ E) :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hSub)
  have hSum : (∑ x ∈ D, μ.real {ω | G ω x ≤ s/2}) ≤ 2*q := by
    calc
      _ ≤ ∑ x ∈ D, q := Finset.sum_le_sum (fun x hx => hTail x (hLevel x hx).1 (hLevel x hx).2)
      _ = (D.card : ℝ)*q := by simp
      _ ≤ 2*q := mul_le_mul_of_nonneg_right (by exact_mod_cast hCard) hq
  have hE : μ.real E ≤ 2*q :=
    (measureReal_biUnion_finset_le D (fun x => {ω | G ω x ≤ s/2})).trans hSum
  exact hM.trans ((measureReal_union_le _ _).trans (add_le_add le_rfl hE))

end ProphetSecretary.Probability
