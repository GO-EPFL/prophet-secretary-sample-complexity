import ProphetSecretary.Statistics.MixedEmpiricalSlopeReverseProcess
import ProphetSecretary.Statistics.MixedEmpiricalPremiumTotals

/-!
# True premium budgets for mixed scalar increments

The true-law normalized premium difference lies in [0,1] for each marginal on
nonnegative clocks. Its actual mixed-law joint measurability and all fixed-power
integrability license the predictable and maximal scalar-increment estimates.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma mixedClockPremiumSlopeUnder_bounds (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z')
    (u : Fin n → ℝ) (i : Fin n) (hui : 0 ≤ u i) (a : (Fin n × Fin k) → ℝ) :
    0 ≤ (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).clockPremiumSlopeUnder P z z' u i ∧
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).clockPremiumSlopeUnder P z z' u i ≤ 1 := by
  rw [← integral_mixedOfferSlope P hP known z z' u i a]
  have hf : Integrable (fun x => mixedOfferSlope P known z z' u i (a, x)) (P.law i) := by
    apply Integrable.of_bound ((measurable_mixedOfferSlope P hP known hz (hz.trans hzz.le) u i).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1
    filter_upwards [] with x
    have h := mixedOfferSlope_bounds P hP known hz hzz u i hui a x
    simpa only [Function.comp_def, id_eq, Real.norm_eq_abs, abs_of_nonneg h.1] using h.2
  constructor
  · exact integral_nonneg (fun x => (mixedOfferSlope_bounds P hP known hz hzz u i hui a x).1)
  · have h := integral_mono hf (integrable_const (1 : ℝ)) (fun x => (mixedOfferSlope_bounds P hP known hz hzz u i hui a x).2)
    simpa only [integral_const, probReal_univ, one_smul] using h

lemma mixedTrueSlopePremiumSum_eq_sum (P : Instance n) (known : Finset (Fin n)) (z z' : ℝ) (u : Fin n → ℝ)
    (a : (Fin n × Fin k) → ℝ) :
    mixedTrueSlopePremiumSum P known z z' u a = ∑ i : Fin n,
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).clockPremiumSlopeUnder P z z' u i := by
  simp only [mixedTrueSlopePremiumSum, Instance.clockPremiumSlopeUnder, Instance.unstoppedPremiumUnder,
    ← Finset.sum_sub_distrib, ← Finset.sum_div]

lemma mixedTrueSlopePremiumSum_bounds (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z')
    (u : Fin n → ℝ) (hu : ∀ i, 0 ≤ u i) (a : (Fin n × Fin k) → ℝ) :
    0 ≤ mixedTrueSlopePremiumSum P known z z' u a ∧ mixedTrueSlopePremiumSum P known z z' u a ≤ n := by
  rw [mixedTrueSlopePremiumSum_eq_sum]
  constructor
  · exact Finset.sum_nonneg (fun i _ => (mixedClockPremiumSlopeUnder_bounds P hP known hz hzz u i (hu i) a).1)
  · simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      (mixedClockPremiumSlopeUnder_bounds P hP known hz hzz u i (hu i) a).2)

variable {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_mixedTrueSlopePremiumSum (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z')
    {a : Ω → ((Fin n × Fin k) → ℝ)} {u : Ω → (Fin n → ℝ)}
    (ha : ∀ q, Measurable fun ω => a ω q) (hu : ∀ i, Measurable fun ω => u ω i) :
    Measurable (fun ω => mixedTrueSlopePremiumSum P known z z' (u ω) (a ω)) := by
  have hm (c : ℝ) (hc : 0 ≤ c) : Measurable (fun ω =>
      (mixedEmpiricalInstance P known (reservoirCoordinates.symm (a ω))).unstoppedPremiumUnder P 1 c (u ω)) :=
    P.measurable_mixedPremiumUnder hP known (y := fun ω => reservoirCoordinates.symm (a ω))
      (c := fun _ => c) (u := u) (fun i j => ha (i, j)) measurable_const (fun _ => hc) hu
  exact ((hm z hz).sub (hm z' hz')).div_const _

lemma integrable_mixedTrueSlopePremiumSum_pow (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z')
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    {a : Ω → ((Fin n × Fin k) → ℝ)} {u : Ω → (Fin n → ℝ)}
    (ha : ∀ q, Measurable fun ω => a ω q) (hu : ∀ i, Measurable fun ω => u ω i)
    (hu0 : ∀ᵐ ω ∂ν, ∀ i, 0 ≤ u ω i) (p : ℕ) :
    Integrable (fun ω => mixedTrueSlopePremiumSum P known z z' (u ω) (a ω) ^ p) ν := by
  apply Integrable.of_bound ((measurable_mixedTrueSlopePremiumSum P hP known hz (hz.trans hzz.le) ha hu).pow_const p).aestronglyMeasurable ((n : ℝ) ^ p)
  filter_upwards [hu0] with ω hω
  have h := mixedTrueSlopePremiumSum_bounds P hP known hz hzz (u ω) hω (a ω)
  simpa only [Real.norm_eq_abs, abs_pow, abs_of_nonneg h.1] using pow_le_pow_left₀ h.1 h.2 p

end ProphetSecretary.Model
