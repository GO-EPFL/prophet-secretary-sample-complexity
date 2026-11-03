import ProphetSecretary.Probability.SortedDyadicClocks
import ProphetSecretary.Probability.TaggedOrder
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Rounding the outer tie-breaking marks

Off the collision event, every tagged comparison has the same result. The
event is measurable in the reserved marks alone. A product-law integral
therefore controls loss in units of the expected maximum, even when the
offers are unbounded.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability

lemma gridPoint_strictMono_real (N : ℕ) (hN : 0 < N) : StrictMono (gridPoint (K := ℝ) N) := by
  intro i j hij
  exact div_lt_div_of_pos_right (by exact_mod_cast hij) (Nat.cast_pos.mpr hN)

lemma uniformGridRound_lt_iff_of_distinct {n N : ℕ} (hN : 0 < N) (u : Fin n → ℝ)
    (hu : Function.Injective (fun i => uniformGridIndex N hN (u i))) (i j : Fin n) :
    uniformGridRound N hN (u i) < uniformGridRound N hN (u j) ↔ u i < u j := by
  constructor
  · intro h
    by_contra! h'
    exact h.not_ge (monotone_uniformGridRound N hN h')
  · intro h
    have hle := monotone_uniformGridIndex N hN h.le
    have hne : uniformGridIndex N hN (u i) ≠ uniformGridIndex N hN (u j) :=
      fun he => h.ne (congrArg u (hu he))
    exact gridPoint_strictMono_real N hN (lt_of_le_of_ne hle hne)

theorem outerMark_taggedComparison_rounding {n N : ℕ} (hN : 0 < N) (u : Fin n → ℝ)
    (hu : Function.Injective (fun i => uniformGridIndex N hN (u i)))
    (i j : Fin n) (x y : ℝ) :
    toLex (x,uniformGridRound N hN (u i)) < toLex (y,uniformGridRound N hN (u j)) ↔
      (toLex (x,u i) : TaggedValue) < toLex (y,u j) := by
  rw [Prod.Lex.lt_iff, Prod.Lex.lt_iff]
  simp only [ofLex_toLex, uniformGridRound_lt_iff_of_distinct hN u hu]

def outerMarkCollision (n N : ℕ) (hN : 0 < N) : Set (Fin n → ℝ) :=
  {u | ¬Function.Injective (fun i => uniformGridIndex N hN (u i))}

lemma measurableSet_outerMarkCollision (n N : ℕ) (hN : 0 < N) :
    MeasurableSet (outerMarkCollision n N hN) :=
  (Set.to_countable {u : Fin n → Fin N | ¬Function.Injective u}).measurableSet.preimage
    (measurePreserving_gridIndexVector n N hN).measurable

lemma outerMarkCollision_probability (n N m : ℕ) (hN : 0 < N) (hm : 0 < m)
    (hgrid : m^2*n^2 ≤ N) :
    (Instance.clocksLaw n).real (outerMarkCollision n N hN) ≤ 1/(2*(m:ℝ)^2) := by
  have hQ : (m:ℝ)^2*(n:ℝ)^2 ≤ N := by exact_mod_cast hgrid
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hm' : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hN' : (0:ℝ) < N := Nat.cast_pos.mpr hN
  refine (roundedUniform_collision_probability n N hN).trans ?_
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith [mul_nonneg hn (sq_nonneg (m:ℝ))]

/-- The mark-only exceptional event factors from any integrable numerical
benchmark on the other coordinates of the product world. -/
theorem outerMarkCollision_weighted_expectation {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (n N : ℕ) (hN : 0 < N) :
    (∫ q : Ω × (Fin n → ℝ), Y q.1 * (outerMarkCollision n N hN).indicator 1 q.2
      ∂μ.prod (Instance.clocksLaw n)) =
      (∫ x, Y x ∂μ) * (Instance.clocksLaw n).real (outerMarkCollision n N hN) := by
  rw [integral_prod_mul, integral_indicator_one (measurableSet_outerMarkCollision n N hN)]

/-- A coupling agreeing outside the collision event loses at most
`E[Y]/(2m²)` if both rewards lie between zero and the numerical benchmark
`Y`. The benchmark can be the actual, unbounded offer maximum. -/
theorem outerMarkCollision_reward_loss {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → ℝ) (hY : Integrable Y μ)
    (hYn : ∀ x, 0 ≤ Y x) (n N m : ℕ) (hN : 0 < N) (hm : 0 < m) (hgrid : m^2*n^2 ≤ N)
    (X X' : Ω × (Fin n → ℝ) → ℝ)
    (hX : Measurable X) (hX' : Measurable X')
    (hB : ∀ q, 0 ≤ X q ∧ X q ≤ Y q.1 ∧ 0 ≤ X' q ∧ X' q ≤ Y q.1)
    (hAgree : ∀ q, q.2 ∉ outerMarkCollision n N hN → X q = X' q) :
    (∫ q, |X q-X' q| ∂μ.prod (Instance.clocksLaw n)) ≤
      (∫ x, Y x ∂μ)/(2*(m:ℝ)^2) := by
  let E := outerMarkCollision n N hN
  let G := fun q : Ω × (Fin n → ℝ) => Y q.1 * E.indicator 1 q.2
  have hInd : Integrable (E.indicator (1 : (Fin n → ℝ) → ℝ)) (Instance.clocksLaw n) :=
    (integrable_const 1).indicator (measurableSet_outerMarkCollision n N hN)
  have hG : Integrable G (μ.prod (Instance.clocksLaw n)) := hY.smul_prod hInd
  have hb (q : Ω × (Fin n → ℝ)) : |X q-X' q| ≤ G q := by
    by_cases he : q.2 ∈ E
    · simp only [G, Set.indicator_of_mem he, Pi.one_apply, mul_one]
      exact abs_le.mpr ⟨by linarith [(hB q).1,(hB q).2.2.2],
        by linarith [(hB q).2.1,(hB q).2.2.1]⟩
    · rw [hAgree q he, sub_self, abs_zero]
      simp only [G, Set.indicator_of_notMem he, mul_zero, le_rfl]
  have hL : Integrable (fun q => |X q-X' q|) (μ.prod (Instance.clocksLaw n)) := by
    apply hG.mono' (continuous_abs.measurable.comp (hX.sub hX')).aestronglyMeasurable
    exact ae_of_all _ (fun q => by
      simpa only [Real.norm_eq_abs, Function.comp_apply, Pi.sub_apply, abs_abs] using hb q)
  calc
    _ ≤ ∫ q, G q ∂μ.prod (Instance.clocksLaw n) := integral_mono hL hG hb
    _ = (∫ x, Y x ∂μ) * (Instance.clocksLaw n).real E := outerMarkCollision_weighted_expectation μ Y n N hN
    _ ≤ (∫ x, Y x ∂μ) * (1/(2*(m:ℝ)^2)) := mul_le_mul_of_nonneg_left
      (outerMarkCollision_probability n N m hN hm hgrid) (integral_nonneg hYn)
    _ = _ := by ring

end ProphetSecretary.Statistics
