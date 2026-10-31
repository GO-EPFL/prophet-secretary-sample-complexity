import ProphetSecretary.Limiting.WeightedRemainderBand
import ProphetSecretary.Limiting.PositiveIntensityBand
import ProphetSecretary.Limiting.CausalPoissonBand
import ProphetSecretary.Limiting.WeightedOrderedSquareTails

/-!
# Actual ordered finite upper-band Poisson states

The retained dimension is exactly N, including padded zero identities if the
finite source has fewer variables. The intensity is the literal residual band
used in compact measure extraction.
-/

open MeasureTheory Set BoundedContinuousFunction
open scoped BigOperators Classical NNReal

namespace ProphetSecretary.Limiting

variable {n : ℕ}

noncomputable def weightOrderedBandState (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ) (N : ℕ)
    (H b : ℝ≥0) (hbH : b ≤ H) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) :
    FiniteIntensityHybridInstance N :=
  poissonizedBandFamily (weightOrderedPrefix P wgt N) (weightOrderedRemainder P wgt N) H b hbH
    (weightOrderedPrefix_bounded P wgt N H.property hcap)
    (weightOrderedRemainder_bounded P wgt N H.property hcap)

lemma weightOrderedBandState_intensity (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ) (N : ℕ)
    (H b : ℝ≥0) (hbH : b ≤ H) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) :
    (weightOrderedBandState P wgt N H b hbH hcap).intensity = weightOrderedBandResidual P wgt N b := by
  change (positiveOfferIntensity (weightOrderedRemainder P wgt N)).restrict (Ioi (b : ℝ)) = _
  exact (positiveOfferIntensity_restrict_band (weightOrderedRemainder P wgt N) b.property).trans
    (weightOrderedRemainder_band_sum P wgt N b.property)

lemma weightOrderedPrefix_marginalProbabilityLaw (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ)
    (N : ℕ) (i : Fin N) :
    (weightOrderedPrefix P wgt N).marginalProbabilityLaw i = weightOrderedPaddedLaw P wgt i.val := by
  apply Subtype.ext
  rfl

theorem weightOrderedBandState_value_comparison (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ) (N : ℕ)
    (H b : ℝ≥0) (hbH : b ≤ H) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    |Model.optimalTerminalScalarValue P b w c-
      (weightOrderedBandState P wgt N H b hbH hcap).optimalScalarValue w c| ≤
        (Real.pi/2)*w*(H : ℝ)*Real.sqrt
          (∑ i : Fin n, ((weightOrderedRemainder P wgt N).law i).real (Ioi (b : ℝ))^2) := by
  let S := (weightOrderedPrefix P wgt N).appendIndependent (weightOrderedRemainder P wgt N)
  have hV : Model.optimalTerminalScalarValue S b w c = Model.optimalTerminalScalarValue P b w c := by
    exact (congrArg (fun T : Model.Instance (N+n) => Model.optimalTerminalScalarValue T b w c)
      (weightOrderedPrefix_append_remainder P wgt N)).trans
        (weightOrderedPrefix_full_terminal_value P wgt N (P.integrable_maximum_of_bounded hcap) b.property hw hc)
  have h := causalPoisson_band_comparison (weightOrderedPrefix P wgt N) (weightOrderedRemainder P wgt N)
    H b hbH (weightOrderedPrefix_bounded P wgt N H.property hcap)
    (weightOrderedRemainder_bounded P wgt N H.property hcap) hw hc
  have he := congrArg (fun z : ℝ => |z-(weightOrderedBandState P wgt N H b hbH hcap).optimalScalarValue w c|) hV
  exact he.symm.le.trans h

theorem weightOrderedBandState_value_error_le (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ) (N : ℕ)
    (H b : ℝ≥0) (hbH : b ≤ H) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hwgt0 : ∀ x, 0 ≤ wgt x) (hwgtZero : wgt 0 = 0)
    (hWeight : (∑ i, ∫ x, wgt x ∂P.law i) ≤ 1)
    (hbPos : 0 < wgt b) (hbMono : ∀ x, (b : ℝ) < x → wgt b ≤ wgt x)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    |Model.optimalTerminalScalarValue P b w c-
      (weightOrderedBandState P wgt N H b hbH hcap).optimalScalarValue w c| ≤
        (Real.pi/2)*w*(H : ℝ)*Real.sqrt (1/((wgt b)^2*(N+1 : ℕ))) := by
  have h := weightOrderedBandState_value_comparison P wgt N H b hbH hcap hw hc
  have hs := weightOrderedPaddedLaw_residual_tail_square_sum_le P wgt hwgt0 hwgtZero
    hWeight hbPos hbMono N
  have he := weightOrderedRemainder_tail_square_sum P wgt N b.property
  have hs' : (∑ i : Fin n, ((weightOrderedRemainder P wgt N).law i).real (Ioi (b : ℝ))^2) ≤
      1/((wgt b)^2*(N+1 : ℕ)) := he.le.trans hs
  exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs') (by positivity))

end ProphetSecretary.Limiting
