import ProphetSecretary.Model.SmallMeanClamp
import ProphetSecretary.Model.ScalarGapMinimum
import ProphetSecretary.Statistics.FiniteGridPilotBound

/-!
# One uniform interval for the clamp and pilot guarantees

The SAME interval [4/5,b] serves the projected empirical policy and the
pilot minimizer. Its outside slack compares the actual restricted and
unrestricted minima. All constants are fixed before the instance, its
size, finite alphabet and sample count. Paper correspondence:
`eq:bayes-restricted-minimum`, `eq:bayes-pilot`, `eq:bayes-clamped-score`.
-/

open MeasureTheory Set
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

theorem bounded_smallMean_clamp_and_pilot (mu : ℝ) (hmu : 0<mu) :
    ∃ b : ℝ, ∃ hb : b∈Ioo (4/5 : ℝ) 1, ∃ Kc Kpilot : ℝ, 0<Kc ∧ 0<Kpilot ∧
      ∀ (n : ℕ) (P : Instance n), (∀ i, ∀ᵐ x ∂P.law i, x≤1) → mu≤P.expectedMaximum →
        P.expectedMaximum≤1/80 →
        (∀ (π : RandomizedPolicy n) (lam r : ℝ), lam∈Icc (0 : ℝ) 1 →
          π.normalizedRegret P (max (4/5) (min b lam))≤r →
          normalizedScalarGap P lam/40-5*r≤π.scalarObjective P lam (1-lam)-
            optimalCompetitiveRatio*(lam*P.expectedMaximum+1-lam)) ∧
        ∀ (m : ℕ) [NeZero m] (G : Finset ℝ) (_hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G),
          (∫ y, normalizedScalarGap P
            (finiteGridPilotWeight G (4/5) b (by norm_num) hb.2.le hb.1.le y)
            ∂P.trainingCoordinateLaw m) ≤
              Kc*minimumNormalizedScalarGap P+Kpilot*(1+P.totalFirstMoment)^2/(m : ℝ) := by
  obtain ⟨b,d,hb,hd,hAll⟩ := bounded_smallMean_clamp_with_slack mu hmu
  have h0 : (0 : ℝ)≤4/5 := by norm_num
  have h1 : b≤1 := hb.2.le
  have hAB : (4/5 : ℝ)≤b := hb.1.le
  have hδ : 0<1-b := sub_pos.mpr hb.2
  have hHalf : 1-b≤1/2 := by linarith only [hb.1]
  have hC : 0<3*(1+1/d) := by positivity
  refine ⟨b,hb,3*(1+1/d),pilotMeanConstant (1-b),hC,pilotMeanConstant_positive hδ hHalf,?_⟩
  intro n P hcap hMean hSmall
  refine ⟨(hAll n P hcap hMean hSmall).2,?_⟩
  intro m hm G hG
  obtain ⟨a,ha,hEq⟩ := intervalNormalizedScalarGapMinimum_attained P
    (P.integrable_maximum_of_bounded hcap) h0 h1 hAB
  have hInterior : Icc (4/5 : ℝ) b⊆Icc (1-b) (1-(1-b)) := by
    intro x hx
    constructor <;> linarith only [hx.1,hx.2,hb.1]
  have hPilot := finiteGridPilotWeight_expected_gap_bound (k:=m) P G hG hcap hδ h0 h1 hAB hInterior ha
  have hCompare := intervalNormalizedScalarGapMinimum_le_global_of_outside_slack P hcap h0 h1 hAB hd
    (hAll n P hcap hMean hSmall).1
  rw [hEq] at hPilot
  linarith only [hPilot,hCompare]

end ProphetSecretary.Statistics
