import ProphetSecretary.Limiting.PoissonBenchmarkError
import ProphetSecretary.Limiting.CausalPoissonBand
import ProphetSecretary.Limiting.HybridBenchmarkReserve
import ProphetSecretary.Model.TerminalBenchmark

/-!
# Benchmark Poisson replacement above a fixed reserve

The maximum including the same terminal reserve has error at most H times the
sum of squared replaced upper-tail probabilities. This follows from actual
maximum CDFs after exact finite and hybrid excess transformations.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace ProphetSecretary.Limiting

variable {n m : ℕ}

theorem finite_poisson_band_benchmark_comparison (P : Model.Instance n) (R : Model.Instance m)
    (H a : ℝ≥0) (haH : a ≤ H) (hP : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hR : ∀ i, ∀ᵐ x ∂R.law i, x ≤ (H : ℝ)) :
    let B := poissonizedBandFamily P R H a haH hP hR
    0 ≤ (P.appendIndependent R).expectedTerminalMaximum a-B.expectedMaximum ∧
      (P.appendIndependent R).expectedTerminalMaximum a-B.expectedMaximum ≤
        (H : ℝ)*(∑ i, ((R.law i).real (Ioi (a : ℝ)))^2) := by
  let B := poissonizedBandFamily P R H a haH hP hR
  let D := poissonizedFamilyTerminal P R H a haH hP hR
  let E := poissonizedFamily (P.excessOffers a) (R.excessOffers a) H
    (excessOffers_bounded P a.property hP) (excessOffers_bounded R a.property hR)
  have hBe : B.excessState B.terminal = E :=
    D.cutoffAtTerminal_excess.trans (poissonizedFamilyTerminal_excessState P R H a haH hP hR)
  have hB : B.expectedMaximum = (a : ℝ)+E.expectedMaximum := by
    have h := B.expectedMaximum_reserveShift
    rw [hBe] at h
    exact h
  have hS := (P.appendIndependent R).integrable_maximum_of_bounded (P.appendIndependent_bounded R hP hR)
  have hF : (P.appendIndependent R).expectedTerminalMaximum a =
      (a : ℝ)+((P.excessOffers a).appendIndependent (R.excessOffers a)).expectedMaximum := by
    have h := (P.appendIndependent R).expectedTerminalMaximum_eq_excess hS a.property
    rw [excessOffers_appendIndependent] at h
    exact h
  have h := finite_poisson_benchmark_comparison (P.excessOffers a) (R.excessOffers a) H
    (excessOffers_bounded P a.property hP) (excessOffers_bounded R a.property hR)
  have htail (i : Fin m) : ((R.excessOffers a).law i).real (Ioi 0) = (R.law i).real (Ioi (a : ℝ)) := by
    have he := Model.excessLaw_positiveTail (R.law i) a.property (show (0 : ℝ) ≤ 0 from le_rfl)
    simp only [add_zero] at he
    exact congrArg ENNReal.toReal he
  change 0 ≤ (P.appendIndependent R).expectedTerminalMaximum a-B.expectedMaximum ∧ _
  have hdiff : (P.appendIndependent R).expectedTerminalMaximum a-B.expectedMaximum =
      ((P.excessOffers a).appendIndependent (R.excessOffers a)).expectedMaximum-E.expectedMaximum := by
    calc
      _ = ((a : ℝ)+((P.excessOffers a).appendIndependent (R.excessOffers a)).expectedMaximum)-
          ((a : ℝ)+E.expectedMaximum) := congrArg₂ (fun X Y : ℝ => X-Y) hF hB
      _ = _ := by ring
  rw [hdiff]
  change 0 ≤ ((P.excessOffers a).appendIndependent (R.excessOffers a)).expectedMaximum-E.expectedMaximum ∧
    ((P.excessOffers a).appendIndependent (R.excessOffers a)).expectedMaximum-E.expectedMaximum ≤ _ at h
  simpa only [htail] using h

end ProphetSecretary.Limiting
