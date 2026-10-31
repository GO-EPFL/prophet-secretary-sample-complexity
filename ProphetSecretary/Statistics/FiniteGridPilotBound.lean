import ProphetSecretary.Statistics.FiniteGridPilotMean
import ProphetSecretary.Statistics.EmpiricalNormalizedGapBias

/-!
# Explicit expected true-gap control for the finite-grid pilot

The comparison holds against every deterministic weight in the pilot interval,
and therefore against its true minimizer. The explicit constant depends only
on the prescribed interior margin δ. The further comparison of the interval
minimum with the unrestricted gap requires the paper's scalar clamp.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

noncomputable def pilotMeanConstant (δ : ℝ) : ℝ :=
  2*empiricalCandidateRegretConstant δ δ⁻¹+128*pilotFirstProjectionConstant δ+16*Real.pi

lemma pilotMeanConstant_positive {δ : ℝ} (hδ : 0 < δ) (hd : δ ≤ 1/2) :
    0 < pilotMeanConstant δ := by
  have hInv : δ ≤ δ⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hδ).mpr
    nlinarith only [hδ,hd]
  have hB := empiricalCandidateRegretConstant_positive hδ hInv
  have hP := pilotFirstProjectionConstant_positive hδ
  unfold pilotMeanConstant
  positivity

variable {n k : ℕ} [NeZero k]

theorem finiteGridPilotWeight_expected_gap_bound (P : Instance n) (G : Finset ℝ)
    (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {lo hi δ : ℝ} (hδ : 0 < δ) (h0 : 0 ≤ lo) (h1 : hi ≤ 1) (hlohi : lo ≤ hi)
    (hInterior : Icc lo hi ⊆ Icc δ (1-δ)) {a : ℝ} (ha : a∈Icc lo hi) :
    (∫ y, normalizedScalarGap P (finiteGridPilotWeight G lo hi h0 h1 hlohi y)
      ∂P.trainingCoordinateLaw k) ≤ 3*normalizedScalarGap P a+
      pilotMeanConstant δ*(1+P.totalFirstMoment)^2/(k : ℝ) := by
  let S := P.totalFirstMoment
  let B := empiricalCandidateRegretConstant δ δ⁻¹
  let K := pilotFirstProjectionConstant δ
  let Z := fun y : (Fin n × Fin k) → ℝ =>
    normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y)) a
  have hS : 0 ≤ S := P.totalFirstMoment_nonnegative
  have hd : δ ≤ 1/2 := by have h := hInterior ha; linarith only [h.1,h.2]
  have hInv : δ ≤ δ⁻¹ := by
    rw [← one_div]
    apply (le_div_iff₀ hδ).mpr
    nlinarith only [hδ,hd]
  have hB : 0 ≤ B := (empiricalCandidateRegretConstant_positive hδ hInv).le
  have hK : 0 ≤ K := (pilotFirstProjectionConstant_positive hδ).le
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hMean := finiteGridPilotWeight_mean_le_reference (k := k) P G hG hcap hδ h0 h1 hlohi hInterior ha
  have hBias := P.empiricalNormalizedGap_bias (k := k) hcap hδ (hInterior ha)
  have hRef : (∫ y, Z y ∂P.trainingCoordinateLaw k) ≤
      normalizedScalarGap P a+B*S*(1+S)/(k : ℝ) := by linarith only [hBias.2]
  have hA : 0 ≤ (1+S)^2-(1+S) := by nlinarith only [sq_nonneg S,hS]
  have hAS : S*(1+S) ≤ (1+S)^2 := by nlinarith only [hS]
  have hA1 : 1 ≤ (1+S)^2 := by nlinarith only [sq_nonneg S,hS]
  have hError : 2*B*S*(1+S)+128*K*(1+S)+16*Real.pi ≤ pilotMeanConstant δ*(1+S)^2 := by
    have hFirst := mul_le_mul_of_nonneg_left hAS (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB)
    have hSecond := mul_le_mul_of_nonneg_left (sub_nonneg.mp hA) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 128) hK)
    have hThird := mul_le_mul_of_nonneg_left hA1 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) Real.pi_pos.le)
    dsimp only [pilotMeanConstant]
    dsimp only [B,K] at hFirst hSecond
    nlinarith only [hFirst,hSecond,hThird]
  calc
    _ ≤ normalizedScalarGap P a+2*(∫ y, Z y ∂P.trainingCoordinateLaw k)+
        2*((64*K*(1+S)+8*Real.pi)/(k : ℝ)) := hMean
    _ ≤ normalizedScalarGap P a+2*(normalizedScalarGap P a+B*S*(1+S)/(k : ℝ))+
        2*((64*K*(1+S)+8*Real.pi)/(k : ℝ)) := by linarith only [hRef]
    _ = 3*normalizedScalarGap P a+(2*B*S*(1+S)+128*K*(1+S)+16*Real.pi)/(k : ℝ) := by ring
    _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_right hError hk)

end ProphetSecretary.Statistics
