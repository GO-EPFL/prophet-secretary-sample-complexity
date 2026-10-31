import ProphetSecretary.Model.SelectionWindowIntegration

/-!
# A terminal-window selection lower bound

A uniform survival lower bound and the proved first-moment error imply a
conditional selection lower bound throughout a short terminal window. Actual
uniform-clock integration converts it to the value-conditioned probability.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

/-- Quantitative version before choosing the window length in `upmom:selection`.
The survival premise concerns the actual canonical execution. -/
theorem Instance.canonical_selectionAtValue_window_lower (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c a u ρ : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (ha : 0 < a) (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hwait : c * u ≤ w * a / 2) (herror : 2 * u * P.totalFirstMoment / a ≤ ρ / 2)
    (hsurvive : ∀ t ∈ Icc (0 : ℝ) 1,
      ρ ≤ (P.worldLaw (Measure.dirac ())).real {ω : World n Unit |
        t ≤ (P.valuePolicy hP hw.le hc).rule.stoppingTime () Finset.univ ω.1 ω.2.1})
    (i : Fin n) :
    u * (ρ / 2) ≤ (P.valuePolicy hP hw.le hc).rule.selectionProbabilityAtValue P (Measure.dirac ()) i a := by
  let π : Policy Unit n := (P.valuePolicy hP hw.le hc).rule
  apply π.selectionProbabilityAtValue_ge_window (P.valueThreshold_policy_isMeasurable hP hw.le hc)
    P (Measure.dirac ()) i a hu0 hu1
  intro t ht
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have htu : 1 - t ≤ u := by linarith [ht.1]
  have hct := (mul_le_mul_of_nonneg_left htu hc).trans hwait
  have hlow := P.canonical_selectionAtTimeValue_lower hP hw hc ha ht0 ht.2 hct i
  have hS : 0 ≤ P.totalFirstMoment := by
    unfold Instance.totalFirstMoment
    exact Finset.sum_nonneg fun j _ => integral_nonneg_of_ae (P.nonnegative j)
  have hmul : 2 * (1 - t) * P.totalFirstMoment ≤ 2 * u * P.totalFirstMoment := by
    nlinarith only [htu, hS]
  have herr := (div_le_div_of_nonneg_right hmul ha.le).trans herror
  have hs := hsurvive t ⟨ht0, ht.2⟩
  change (P.worldLaw (Measure.dirac ())).real {ω : World n Unit |
    t ≤ π.stoppingTime () Finset.univ ω.1 ω.2.1} - 2 * (1 - t) * P.totalFirstMoment / a ≤
      π.selectionProbabilityAtTimeValue P (Measure.dirac ()) i t a at hlow
  change ρ ≤ (P.worldLaw (Measure.dirac ())).real {ω : World n Unit |
    t ≤ π.stoppingTime () Finset.univ ω.1 ω.2.1} at hs
  change ρ / 2 ≤ _
  linarith only [hlow, herr, hs]

end ProphetSecretary.Model
