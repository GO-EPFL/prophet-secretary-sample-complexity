import ProphetSecretary.Reach.ZeroReach
import ProphetSecretary.Reach.ReachIntegralBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Finite maximum moments and empirical-process chaining

Finite maxima are controlled by sums of fourth moments. These deterministic and
integration lemmas are used for the uniform empirical clock discrepancy estimate.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Reach.EmpiricalChaining

variable {Ω : Type*} {K : ℕ}

/-- Absolute maximum with a zero sentinel, including empty index sets. -/
noncomputable def maxAbs (X : Fin K → Ω → ℝ) (ω : Ω) : ℝ :=
  Finset.univ.sup' ⟨none, Finset.mem_univ _⟩
    (fun i : Option (Fin K) => i.elim 0 (fun j => |X j ω|))

theorem maxAbs_nonnegative (X : Fin K → Ω → ℝ) (ω : Ω) : 0 ≤ maxAbs X ω :=
  Finset.le_sup' (fun i : Option (Fin K) => i.elim 0 (fun j => |X j ω|))
    (Finset.mem_univ none)

theorem le_maxAbs (X : Fin K → Ω → ℝ) (ω : Ω) (j : Fin K) : |X j ω| ≤ maxAbs X ω :=
  Finset.le_sup' (fun i : Option (Fin K) => i.elim 0 (fun j => |X j ω|))
    (Finset.mem_univ (some j))

theorem maxAbs_le {X : Fin K → Ω → ℝ} {ω : Ω} {b : ℝ} (hb : 0 ≤ b)
    (hX : ∀ j, |X j ω| ≤ b) : maxAbs X ω ≤ b := by
  apply Finset.sup'_le
  intro j _
  cases j with
  | none => exact hb
  | some j => exact hX j

theorem maxAbs_fourth_le_sum (X : Fin K → Ω → ℝ) (ω : Ω) :
    maxAbs X ω ^ 4 ≤ ∑ j : Fin K, |X j ω| ^ 4 := by
  let f : Option (Fin K) → ℝ := fun i => i.elim 0 (fun j => |X j ω|)
  obtain ⟨i, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Option (Fin K)))
    f ⟨none, Finset.mem_univ _⟩
  have he : maxAbs X ω = f i := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ fun j hj => hmax j hj
    · exact Finset.le_sup' _ (Finset.mem_univ i)
  rw [he]
  cases i with
  | none => exact by simpa [f] using Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin K))) => pow_nonneg (abs_nonneg (X j ω)) 4)
  | some i =>
    exact Finset.single_le_sum (fun j _ => pow_nonneg (abs_nonneg (X j ω)) 4) (Finset.mem_univ i)

variable [MeasurableSpace Ω]

theorem measurable_maxAbs {X : Fin K → Ω → ℝ} (hX : ∀ j, Measurable (X j)) :
    Measurable (maxAbs X) := by
  have h : Measurable ((Finset.univ : Finset (Option (Fin K))).sup'
      ⟨none, Finset.mem_univ _⟩
      (fun i => fun ω => i.elim 0 (fun j => |X j ω|))) := by
    apply Finset.measurable_sup'
    intro j _
    cases j with
    | none => exact measurable_const
    | some j => exact (continuous_abs.measurable.comp (hX j))
  convert h using 1
  funext ω
  exact (Finset.sup'_apply ⟨none, Finset.mem_univ _⟩
    (fun i : Option (Fin K) => fun ω => i.elim 0 (fun j => |X j ω|)) ω).symm

/-- Twice applying the second-moment Jensen inequality controls the fourth power
of the expected finite maximum by the sum of individual fourth moments. -/
theorem fourth_mean_maxAbs_le_sum (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Fin K → Ω → ℝ} (hX : ∀ j, Measurable (X j))
    (hbound : ∀ j, ∀ᵐ ω ∂μ, |X j ω| ≤ 1) :
    (∫ ω, maxAbs X ω ∂μ) ^ 4 ≤ ∑ j : Fin K, ∫ ω, |X j ω| ^ 4 ∂μ := by
  have hall : ∀ᵐ ω ∂μ, ∀ j, |X j ω| ≤ 1 := (ae_all_iff.mpr hbound)
  have hunit : ∀ᵐ ω ∂μ, 0 ≤ maxAbs X ω ∧ maxAbs X ω ≤ 1 := by
    filter_upwards [hall] with ω hω
    exact ⟨maxAbs_nonnegative X ω, maxAbs_le zero_le_one hω⟩
  have hi : ∀ p : ℕ, Integrable (fun ω => maxAbs X ω ^ p) μ := by
    intro p
    apply Integrable.of_bound ((measurable_maxAbs hX).pow_const p).aestronglyMeasurable 1
    filter_upwards [hunit] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hω.1 p)]
    exact pow_le_one₀ hω.1 hω.2
  have hi1 : Integrable (maxAbs X) μ := by simpa using hi 1
  have hs : ∀ j : Fin K, Integrable (fun ω => |X j ω| ^ 4) μ := by
    intro j
    apply Integrable.of_bound ((continuous_abs.measurable.comp (hX j)).pow_const 4).aestronglyMeasurable 1
    filter_upwards [hbound j] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) 4)]
    exact pow_le_one₀ (abs_nonneg _) hω
  have h1 := ProphetSecretary.Reach.sq_integral_le_integral_sq μ hi1 (hi 2)
  have h2 := ProphetSecretary.Reach.sq_integral_le_integral_sq μ (hi 2)
    (show Integrable (fun ω => (maxAbs X ω ^ 2) ^ 2) μ by simpa [← pow_mul] using hi 4)
  have hmean2 : 0 ≤ ∫ ω, maxAbs X ω ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hsq : ((∫ ω, maxAbs X ω ∂μ) ^ 2) ^ 2 ≤
      (∫ ω, maxAbs X ω ^ 2 ∂μ) ^ 2 :=
    (sq_le_sq₀ (sq_nonneg _) hmean2).mpr h1
  have hm4 : (∫ ω, maxAbs X ω ∂μ) ^ 4 ≤ ∫ ω, maxAbs X ω ^ 4 ∂μ := by
    simpa [← pow_mul] using hsq.trans h2
  have hsum := integral_mono (hi 4) (integrable_finsetSum _ (fun j _ => hs j))
    (maxAbs_fourth_le_sum X)
  rw [integral_finsetSum _ (fun j _ => hs j)] at hsum
  exact hm4.trans hsum

theorem mean_maxAbs_le_of_fourth (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Fin K → Ω → ℝ} (hX : ∀ j, Measurable (X j))
    (hbound : ∀ j, ∀ᵐ ω ∂μ, |X j ω| ≤ 1) {B : ℝ} (hB : 0 ≤ B)
    (hfourth : (∑ j : Fin K, ∫ ω, |X j ω| ^ 4 ∂μ) ≤ B ^ 4) :
    ∫ ω, maxAbs X ω ∂μ ≤ B := by
  have hm := (fourth_mean_maxAbs_le_sum μ hX hbound).trans hfourth
  exact (pow_le_pow_iff_left₀ (integral_nonneg (maxAbs_nonnegative X)) hB (by decide : 4 ≠ 0)).mp hm

end ProphetSecretary.Reach.EmpiricalChaining
