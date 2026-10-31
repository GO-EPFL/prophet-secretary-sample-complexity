import ProphetSecretary.Reach.Clipping
import ProphetSecretary.Reach.Robust
import ProphetSecretary.Model.NumericalCompetitiveBound

/-!
# Actual bounded normalized near-minimizers

The definition of the global ratio supplies a positive finite raw instance.
The proved clipping normalization converts it to mean one, uniformly bounded
offers and uniformly interior scalar weights. No bound on its total first
moment is assumed. This is the initial minimizing argument of
`prop:critical-input`.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting
open ProphetSecretary.Model

theorem exists_normalized_nearCritical_instance {eps : ℝ} (hEps : 0<eps) (hEpsSmall : eps≤1/100) :
    ∃ (n : ℕ) (P : Instance n) (a : ℝ), P.HasPositiveFiniteMaximum ∧
      P.expectedMaximum=1 ∧ (∀ i, ∀ᵐ x ∂P.law i, x≤3) ∧
      a∈Icc (1/4 : ℝ) (3/4) ∧ normalizedScalarGap P a<eps := by
  have hApprox : ∃ r∈{r | ∃ (n : ℕ) (P : Instance n), P.HasPositiveFiniteMaximum ∧
      r=optimalScalarValue P 1 0/P.expectedMaximum}, r<optimalCompetitiveRatio+eps := by
    apply exists_lt_of_csInf_lt competitiveRatios_nonempty
    change optimalCompetitiveRatio<optimalCompetitiveRatio+eps
    linarith only [hEps]
  obtain ⟨r,⟨n,P,hP,hr⟩,hRatio⟩ := hApprox
  have hrUpper : r<3/4 := by
    linarith only [hRatio,hEpsSmall,optimalCompetitiveRatio_le_seventyThreeHundredths]
  have hRaw : optimalScalarValue P 1 0/(1*P.expectedMaximum+0)<1 := by
    simp only [one_mul,add_zero]
    rw [←hr]
    linarith only [hrUpper]
  let H := P.clippingHeight 1 0
  let Q := P.cap H
  let d := P.clippedDurationCoefficient H 1 0
  let D := Q.expectedMaximum+d
  let W := Q.scale Q.expectedMaximum⁻¹ (inv_nonneg.mpr Q.expectedMaximum_nonnegative)
  let a := Q.expectedMaximum/D
  let c := d/D
  have hNorm : W.HasPositiveFiniteMaximum ∧ W.expectedMaximum=1 ∧ a+c=1 ∧
      a∈Icc (1-r) r ∧ c∈Icc (1-r) r ∧
      (∀ i, ∀ᵐ x ∂W.law i, x≤r/(1-r)) ∧
      optimalScalarValue W a c/(a*W.expectedMaximum+c)≤r := by
    simpa only [one_mul,add_zero,←hr] using P.clipping_normalization hP zero_lt_one (le_refl (0 : ℝ)) hRaw
  obtain ⟨hW,hM,hSum,ha,_hc,hCap,hValue⟩ := hNorm
  have hCapRatio : r/(1-r)≤3 := (div_le_iff₀ (by linarith only [hrUpper])).mpr (by linarith only [hrUpper])
  have hWeights : a∈Icc (1/4 : ℝ) (3/4) := by constructor <;> linarith only [ha.1,ha.2,hrUpper]
  have hDen : a*W.expectedMaximum+c=1 := by rw [hM,mul_one];exact hSum
  have hValue' : optimalScalarValue W a c≤r := by simpa only [hDen,div_one] using hValue
  have hcEq : c=1-a := by linarith only [hSum]
  refine ⟨n,W,a,hW,hM,(fun i => (hCap i).mono (fun _ hx => hx.trans hCapRatio)),hWeights,?_⟩
  unfold normalizedScalarGap scalarGap
  rw [←hcEq,hM,mul_one,hSum,mul_one]
  linarith only [hValue',hRatio]

end ProphetSecretary.Limiting
