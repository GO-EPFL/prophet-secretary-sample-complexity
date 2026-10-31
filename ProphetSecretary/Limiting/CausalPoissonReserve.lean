import ProphetSecretary.Limiting.HybridReserveShift
import ProphetSecretary.Limiting.CausalPoissonZeroTerminal
import ProphetSecretary.Limiting.ExcessPoissonization
import ProphetSecretary.Model.TerminalZeroWeight

/-!
# Sharp causal Poisson comparison with a fixed terminal reward

Exact finite and hybrid reserve removal reduces the comparison to excess
offers. Positive intensity pushforwards are restricted before forming the
hybrid state, and their marginal positive masses can only decrease. Thus the
same π/2 coefficient and original positive-mass square sum apply.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical NNReal

namespace ProphetSecretary.Limiting

variable {n m : ℕ}

noncomputable def poissonizedFamilyTerminal (P : Model.Instance n) (R : Model.Instance m) (H a : ℝ≥0)
    (haH : a ≤ H) (hP : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hR : ∀ i, ∀ᵐ x ∂R.law i, x ≤ (H : ℝ)) : FiniteIntensityHybridInstance n :=
  { poissonizedFamily P R H hP hR with terminal := a, terminal_le_cap := haH }

lemma poissonizedFamilyTerminal_excessState (P : Model.Instance n) (R : Model.Instance m) (H a : ℝ≥0)
    (haH : a ≤ H) (hP : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hR : ∀ i, ∀ᵐ x ∂R.law i, x ≤ (H : ℝ)) :
    (poissonizedFamilyTerminal P R H a haH hP hR).excessState a =
      poissonizedFamily (P.excessOffers a) (R.excessOffers a) H (excessOffers_bounded P a.property hP)
        (excessOffers_bounded R a.property hR) := by
  change (poissonizedFamily P R H hP hR).excessState a = _
  exact poissonizedFamily_excessState P R H a hP hR

/-- `lem:causal-poisson`, with a fixed terminal reward and the retained/replaced
identity blocks displayed explicitly. General finite competing policies may
use all original zero-valued observations. -/
theorem causalPoisson_fixedTerminal (P : Model.Instance n) (R : Model.Instance m) (H a : ℝ≥0)
    (haH : a ≤ H) (hPcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hRcap : ∀ i, ∀ᵐ x ∂R.law i, x ≤ (H : ℝ)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    |Model.optimalTerminalScalarValue (P.appendIndependent R) a w c -
      (poissonizedFamilyTerminal P R H a haH hPcap hRcap).optimalScalarValue w c| ≤
      (Real.pi / 2) * w * (H : ℝ) * Real.sqrt (∑ i, distributionTail R 0 i ^ 2) := by
  let B := poissonizedFamilyTerminal P R H a haH hPcap hRcap
  by_cases hw0 : w = 0
  · subst w
    rw [Model.optimalTerminalScalarValue_zero_rewardWeight (P.appendIndependent R) a hc,B.value_zero_rewardWeight hc,
      sub_self,abs_zero]
    simp only [mul_zero,zero_mul,le_refl]
  · have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    have hS := (P.appendIndependent R).integrable_maximum_of_bounded (P.appendIndependent_bounded R hPcap hRcap)
    have hF := Model.optimalTerminalScalarValue_eq_excessValue (P.appendIndependent R) hS a.property hwpos hc
    have hB := B.value_reserveShift hwpos hc
    have hBstate : B.excessState B.terminal =
        poissonizedFamily (P.excessOffers a) (R.excessOffers a) H (excessOffers_bounded P a.property hPcap)
          (excessOffers_bounded R a.property hRcap) :=
      poissonizedFamilyTerminal_excessState P R H a haH hPcap hRcap
    have hz := causalPoisson_zeroTerminal (P.excessOffers a) (R.excessOffers a) H
      (excessOffers_bounded P a.property hPcap) (excessOffers_bounded R a.property hRcap) hw hc
    have hsq : (∑ i, distributionTail (R.excessOffers a) 0 i ^ 2) ≤ ∑ i, distributionTail R 0 i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have hp := Model.excessLaw_positiveProbability_le (R.law i) a.property
      exact (sq_le_sq₀ measureReal_nonneg measureReal_nonneg).mpr hp
    have hcoef : 0 ≤ (Real.pi / 2) * w * (H : ℝ) := by positivity
    have hb := hz.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq) hcoef)
    have hF' : Model.optimalTerminalScalarValue (P.appendIndependent R) a w c =
        w * (a : ℝ) + Model.optimalScalarValue ((P.excessOffers a).appendIndependent (R.excessOffers a)) w c :=
      hF.trans (congrArg (fun T : Model.Instance (n + m) => w * (a : ℝ) + Model.optimalScalarValue T w c)
        (excessOffers_appendIndependent P R a))
    have hB' : B.optimalScalarValue w c = w * (a : ℝ) +
        (poissonizedFamily (P.excessOffers a) (R.excessOffers a) H
          (excessOffers_bounded P a.property hPcap) (excessOffers_bounded R a.property hRcap)).optimalScalarValue w c :=
      hB.trans (congrArg (fun T : FiniteIntensityHybridInstance n => w * (a : ℝ) + T.optimalScalarValue w c) hBstate)
    have hdiff : Model.optimalTerminalScalarValue (P.appendIndependent R) a w c - B.optimalScalarValue w c =
        Model.optimalScalarValue ((P.excessOffers a).appendIndependent (R.excessOffers a)) w c -
          (poissonizedFamily (P.excessOffers a) (R.excessOffers a) H
            (excessOffers_bounded P a.property hPcap) (excessOffers_bounded R a.property hRcap)).optimalScalarValue w c := by
      calc
        _ = (w * (a : ℝ) + Model.optimalScalarValue ((P.excessOffers a).appendIndependent (R.excessOffers a)) w c) -
            (w * (a : ℝ) + (poissonizedFamily (P.excessOffers a) (R.excessOffers a) H
              (excessOffers_bounded P a.property hPcap) (excessOffers_bounded R a.property hRcap)).optimalScalarValue w c) :=
          congrArg₂ (fun X Y : ℝ => X - Y) hF' hB'
        _ = _ := by ring
    exact (congrArg abs hdiff).le.trans hb

end ProphetSecretary.Limiting
