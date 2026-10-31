import ProphetSecretary.Limiting.ExcessCutoffIntensity

/-!
# Causal Poisson replacement above a fixed reserve

Only the replaced offers strictly above the reserve enter the intensity and
the error. All lower and zero finite identities remain in the original policy
history in the full-policy comparison inherited from causal Poissonization.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace ProphetSecretary.Limiting

variable {n m : ℕ}

noncomputable def poissonizedBandFamily (P : Model.Instance n) (R : Model.Instance m) (H a : ℝ≥0)
    (haH : a ≤ H) (hP : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hR : ∀ i, ∀ᵐ x ∂R.law i, x ≤ (H : ℝ)) : FiniteIntensityHybridInstance n :=
  (poissonizedFamilyTerminal P R H a haH hP hR).cutoffAtTerminal

theorem causalPoisson_band_comparison (P : Model.Instance n) (R : Model.Instance m) (H a : ℝ≥0)
    (haH : a ≤ H) (hPcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hRcap : ∀ i, ∀ᵐ x ∂R.law i, x ≤ (H : ℝ)) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    |Model.optimalTerminalScalarValue (P.appendIndependent R) a w c-
      (poissonizedBandFamily P R H a haH hPcap hRcap).optimalScalarValue w c| ≤
      (Real.pi/2)*w*(H : ℝ)*Real.sqrt (∑ i, ((R.law i).real (Ioi (a : ℝ)))^2) := by
  let B := poissonizedFamilyTerminal P R H a haH hPcap hRcap
  have hb : (poissonizedBandFamily P R H a haH hPcap hRcap).optimalScalarValue w c =
      B.optimalScalarValue w c := B.value_cutoffAtTerminal hw hc
  rw [hb]
  by_cases hw0 : w = 0
  · subst w
    rw [Model.optimalTerminalScalarValue_zero_rewardWeight _ _ hc,B.value_zero_rewardWeight hc]
    simp only [sub_self,abs_zero,mul_zero,zero_mul,le_refl]
  have hwP : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hS := (P.appendIndependent R).integrable_maximum_of_bounded
    (P.appendIndependent_bounded R hPcap hRcap)
  have hF := Model.optimalTerminalScalarValue_eq_excessValue (P.appendIndependent R) hS a.property hwP hc
  rw [excessOffers_appendIndependent] at hF
  have hB := B.value_reserveShift hwP hc
  have hBe : B.excessState B.terminal = poissonizedFamily (P.excessOffers a) (R.excessOffers a) H
      (excessOffers_bounded P a.property hPcap) (excessOffers_bounded R a.property hRcap) :=
    poissonizedFamilyTerminal_excessState P R H a haH hPcap hRcap
  rw [hBe] at hB
  have hz := causalPoisson_zeroTerminal (P.excessOffers a) (R.excessOffers a) H
    (excessOffers_bounded P a.property hPcap) (excessOffers_bounded R a.property hRcap) hw hc
  have htail (i : Fin m) : distributionTail (R.excessOffers a) 0 i = (R.law i).real (Ioi (a : ℝ)) := by
    change (Model.excessLaw (R.law i) a (Ioi 0)).toReal = _
    have he := Model.excessLaw_positiveTail (R.law i) a.property (show (0 : ℝ) ≤ 0 from le_rfl)
    simp only [add_zero] at he
    exact congrArg ENNReal.toReal he
  simp only [htail] at hz
  have hB' : B.optimalScalarValue w c = w*(a : ℝ)+
      (poissonizedFamily (P.excessOffers a) (R.excessOffers a) H
        (excessOffers_bounded P a.property hPcap) (excessOffers_bounded R a.property hRcap)).optimalScalarValue w c := hB
  have hdiff : Model.optimalTerminalScalarValue (P.appendIndependent R) a w c-B.optimalScalarValue w c =
      Model.optimalScalarValue ((P.excessOffers a).appendIndependent (R.excessOffers a)) w c-
        (poissonizedFamily (P.excessOffers a) (R.excessOffers a) H
          (excessOffers_bounded P a.property hPcap) (excessOffers_bounded R a.property hRcap)).optimalScalarValue w c := by
    calc
      _ = (w*(a : ℝ)+Model.optimalScalarValue ((P.excessOffers a).appendIndependent (R.excessOffers a)) w c)-
          (w*(a : ℝ)+(poissonizedFamily (P.excessOffers a) (R.excessOffers a) H
            (excessOffers_bounded P a.property hPcap) (excessOffers_bounded R a.property hRcap)).optimalScalarValue w c) :=
        congrArg₂ (fun X Y : ℝ => X-Y) hF hB'
      _ = _ := by ring
  exact (congrArg abs hdiff).le.trans hz

end ProphetSecretary.Limiting
