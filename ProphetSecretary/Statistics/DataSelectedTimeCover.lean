import ProphetSecretary.Statistics.DataSelectedLossRegions
import ProphetSecretary.Model.EmpiricalTimeIntegralCover
import ProphetSecretary.Analysis.ExpectedCountableCover

/-!
# Expected loss from the actual countable time-region cover

The time integrals are converted to nonnegative integrals before applying the
cover, so region overlaps and the infinite early-band series cause no exchange
of a conditionally convergent real series.
-/

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ}

theorem Instance.clockRegionLoss_ofReal_cover (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} {hi a x : ℝ}
    (hhi : 0 ≤ hi) (ha : 0 < a)
    {L : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) → ℝ}
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)))
    (hI : Integrable (fun t => L (q,t)) Instance.uniformClock)
    (h0 : ∀ t, 0 ≤ L (q,t)) :
    ENNReal.ofReal (∫ t, L (q,t) ∂Instance.uniformClock) ≤
      ENNReal.ofReal (clockRegionLoss P Z hi a (x/2) true L q) +
      ENNReal.ofReal (clockRegionLoss P Z hi a (x/2) false L q) +
      ∑' j : ℕ, ENNReal.ofReal (clockRegionLoss P (fun _ => hi) hi
        (2*((2 : ℝ)^j*a)) ((2 : ℝ)^j*a) true L q) := by
  have hsub (b z d : ℝ) (above : Bool) : clockLossRegion P (fun _ => z) hi b d above q ⊆ Icc (0 : ℝ) 1 := by
    intro t ht
    exact ⟨(P.trueCriticalEntrance_mem hi b q.2).1.trans ht.1.1.le,ht.1.2⟩
  have hInt (b z d : ℝ) (above : Bool) :
      Integrable (fun t => L (q,t)) (volume.restrict (clockLossRegion P (fun _ => z) hi b d above q)) :=
    hI.mono_measure (Measure.restrict_mono_set volume (hsub b z d above))
  have hwhole := ofReal_integral_eq_lintegral_ofReal hI (Filter.Eventually.of_forall h0)
  have hN := ofReal_integral_eq_lintegral_ofReal (hInt a (Z q.1) (x/2) true) (Filter.Eventually.of_forall h0)
  have hF := ofReal_integral_eq_lintegral_ofReal (hInt a (Z q.1) (x/2) false) (Filter.Eventually.of_forall h0)
  have hE (j : ℕ) := ofReal_integral_eq_lintegral_ofReal
    (hInt (2*((2 : ℝ)^j*a)) hi ((2 : ℝ)^j*a) true) (Filter.Eventually.of_forall h0)
  have hc := P.empirical_time_integral_cover_le (z := Z q.1) (x := x) hP hhi ha q.2
    (fun t => ENNReal.ofReal (L (q,t)))
  simp only [clockRegionLoss,clockLossRegion,Bool.false_eq_true,↓reduceIte] at hN hF hE ⊢
  rw [hwhole,hN,hF]
  simp_rw [hE]
  exact hc

end ProphetSecretary.Model
