import ProphetSecretary.Statistics.EmpiricalPremiumTotals
import ProphetSecretary.Model.MixedEmpiricalThresholdMeasurability

/-!
# True premiums at mixed-law continuation thresholds

Known-law and empirical continuations are jointly measurable. The true-law
unstopped premium sum remains bounded by the true total first moment on every
sample array, giving integrability of every fixed positive integer power.
-/

open MeasureTheory
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k] {Ω : Type*} [MeasurableSpace Ω]

lemma Instance.measurable_mixedPremiumUnder (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    {y : Ω → Reservoir n k} {c : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ i l, Measurable (fun ω => y ω i l)) (hc : Measurable c) (hc0 : ∀ ω, 0≤c ω)
    (hu : ∀ i, Measurable (fun ω => u ω i)) :
    Measurable (fun ω => (mixedEmpiricalInstance P known (y ω)).unstoppedPremiumUnder P 1 (c ω) (u ω)) := by
  apply Finset.measurable_sum
  intro i _
  have hT := measurable_mixedEmpirical_continuationAtArrival P hP known (w:=fun _ => 1)
    (x:=fun _ => fun _ => 0) hy measurable_const hc (fun _ => zero_lt_one) hc0
    (fun _ => measurable_const) hu i
  exact (positivePremium_continuous (P.law i) (P.integrable_maximum_iff.mp hP i) 1).measurable.comp hT

lemma Instance.integrable_mixedPremiumUnder_pow (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    {y : Ω → Reservoir n k} {c : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ i l, Measurable (fun ω => y ω i l)) (hc : Measurable c) (hc0 : ∀ ω, 0≤c ω)
    (hu : ∀ i, Measurable (fun ω => u ω i)) (p : ℕ) :
    Integrable (fun ω => (mixedEmpiricalInstance P known (y ω)).unstoppedPremiumUnder P 1 (c ω) (u ω)^p) ν := by
  have hm := (P.measurable_mixedPremiumUnder hP known hy hc hc0 hu).pow_const p
  apply Integrable.of_bound hm.aestronglyMeasurable (P.totalFirstMoment^p)
  exact Filter.Eventually.of_forall fun ω => by
    have h0 := (mixedEmpiricalInstance P known (y ω)).unstoppedPremiumUnder_nonnegative P 1 (c ω) (u ω)
    have h1 : (mixedEmpiricalInstance P known (y ω)).unstoppedPremiumUnder P 1 (c ω) (u ω)≤P.totalFirstMoment := by
      simpa only [one_mul] using (mixedEmpiricalInstance P known (y ω)).unstoppedPremiumUnder_le_firstMoment P
        (mixedEmpiricalInstance_integrable P hP known _) hP zero_le_one (hc0 ω) (u ω)
    change ‖((mixedEmpiricalInstance P known (y ω)).unstoppedPremiumUnder P 1 (c ω) (u ω))^p‖≤_
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg h0 p)]
    exact pow_le_pow_left₀ h0 h1 p

end ProphetSecretary.Model
