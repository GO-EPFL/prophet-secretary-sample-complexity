import ProphetSecretary.Model.CompetitiveBasic
import ProphetSecretary.Reach.Robust
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Countersequences to a uniform quadratic scalar diameter bound

All instance-class parameters are fixed before selecting the sequence.
The gap sums and midpoint gaps tend to zero, including when individual
counterexamples have zero gap. Paper correspondence: `updual:modulus`.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal Topology
namespace ProphetSecretary.Model

theorem exists_scalarDiameter_countersequence (H : ℝ≥0) (S0 mu δ : ℝ) (hδ : 0<δ)
    (hFail : ∀ K : ℝ, 0≤K → ∃ (n : ℕ) (P : Instance n) (a b : ℝ),
      (∀ i, ∀ᵐ x ∂P.law i, x≤(H : ℝ)) ∧ P.totalFirstMoment≤S0 ∧ mu≤P.expectedMaximum ∧
      a∈Icc δ (1-δ) ∧ b∈Icc δ (1-δ) ∧
      K*(normalizedScalarGap P a+normalizedScalarGap P b)<(b-a)^2) :
    ∃ (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) (a b : ℕ → ℝ),
      (∀ m i, ∀ᵐ x ∂(P m).law i, x≤(H : ℝ)) ∧
      (∀ m, (P m).totalFirstMoment≤S0) ∧ (∀ m, mu≤(P m).expectedMaximum) ∧
      (∀ m, a m∈Icc δ (1-δ)) ∧ (∀ m, b m∈Icc δ (1-δ)) ∧
      (∀ m : ℕ, ((m : ℝ)+1)*(normalizedScalarGap (P m) (a m)+normalizedScalarGap (P m) (b m))<(b m-a m)^2) ∧
      Tendsto (fun m => normalizedScalarGap (P m) (a m)+normalizedScalarGap (P m) (b m)) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun m => normalizedScalarGap (P m) ((a m+b m)/2)) atTop (𝓝 (0 : ℝ)) := by
  have hWitness (m : ℕ) := hFail ((m : ℝ)+1) (by positivity)
  choose sizes P a b hCap hS hMean hA hB hStrict using hWitness
  have hP (m : ℕ) := (P m).integrable_maximum_of_bounded (hCap m)
  have hAU (m : ℕ) : a m∈Icc (0 : ℝ) 1 := ⟨hδ.le.trans (hA m).1,by linarith only [(hA m).2,hδ]⟩
  have hBU (m : ℕ) : b m∈Icc (0 : ℝ) 1 := ⟨hδ.le.trans (hB m).1,by linarith only [(hB m).2,hδ]⟩
  let q := fun m => normalizedScalarGap (P m) (a m)+normalizedScalarGap (P m) (b m)
  have hQ0 (m : ℕ) : 0≤q m := add_nonneg
    (normalizedScalarGap_nonnegative (P m) (hP m) (hAU m))
    (normalizedScalarGap_nonnegative (P m) (hP m) (hBU m))
  have hUpper (m : ℕ) : q m≤1/((m : ℝ)+1) := by
    have hSep : (b m-a m)^2≤1 := by
      apply (sq_le_one_iff_abs_le_one _).mpr
      exact abs_le.mpr ⟨by linarith only [(hAU m).2,(hBU m).1],by linarith only [(hAU m).1,(hBU m).2]⟩
    apply (le_div_iff₀ (by positivity : (0 : ℝ)<(m : ℝ)+1)).mpr
    have h := hStrict m
    change ((m : ℝ)+1)*q m<(b m-a m)^2 at h
    nlinarith only [h,hSep]
  have hQLimit : Tendsto q atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero hQ0 hUpper (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ))
  have hMidU (m : ℕ) : (a m+b m)/2∈Icc (0 : ℝ) 1 := by
    constructor <;> linarith only [(hAU m).1,(hAU m).2,(hBU m).1,(hBU m).2]
  have hMidBound (m : ℕ) : normalizedScalarGap (P m) ((a m+b m)/2)≤q m := by
    have h := (normalizedScalarGap_convex (P m) (hP m)).2 (hAU m) (hBU m)
      (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (0 : ℝ)≤1/2) (by norm_num : (1/2 : ℝ)+1/2=1)
    simp only [smul_eq_mul] at h
    have hEq : (1/2 : ℝ)*a m+(1/2 : ℝ)*b m=(a m+b m)/2 := by ring
    rw [hEq] at h
    dsimp only [q] at hQ0 ⊢
    nlinarith only [h,hQ0 m]
  refine ⟨sizes,P,a,b,hCap,hS,hMean,hA,hB,hStrict,hQLimit,?_⟩
  exact squeeze_zero (fun m => normalizedScalarGap_nonnegative (P m) (hP m) (hMidU m)) hMidBound hQLimit

end ProphetSecretary.Model
