import ProphetSecretary.Model.ValueResponseIntegrals
import ProphetSecretary.Model.ValueStationarity

/-!
# Simultaneous comparison of selection and maximum probabilities

Equation `upmom:tv` tests the proved response stationarity with measurable signs
of all marginal discrepancies at once. The probabilities are constructed by
actual independent coordinate replacement; they are not unspecified versions
of conditional probabilities. The constant is independent of instance size.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

/-- A bounded measurable sign test, zero outside the designated set. -/
noncomputable def restrictedSign (s : Set ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  if x ∈ s then if f x < 0 then -1 else 1 else 0

lemma measurable_restrictedSign {s : Set ℝ} (hs : MeasurableSet s)
    {f : ℝ → ℝ} (hf : Measurable f) : Measurable (restrictedSign s f) :=
  Measurable.ite hs (Measurable.ite (measurableSet_lt hf measurable_const)
    measurable_const measurable_const) measurable_const

lemma restrictedSign_abs_le_one (s : Set ℝ) (f : ℝ → ℝ) (x : ℝ) :
    |restrictedSign s f x| ≤ 1 := by
  unfold restrictedSign
  split_ifs <;> norm_num

lemma mul_restrictedSign (s : Set ℝ) (f : ℝ → ℝ) (x : ℝ) :
    f x * restrictedSign s f x = s.indicator (fun y => |f y|) x := by
  by_cases hs : x ∈ s
  · by_cases hf : f x < 0
    · simp [restrictedSign, hs, hf, abs_of_neg hf]
    · simp [restrictedSign, hs, hf, abs_of_nonneg (not_lt.mp hf)]
  · simp [restrictedSign, hs]

/-- `upmom:tv`: one sign test simultaneously bounds every marginal discrepancy
on [2h,1]. The base policy is held fixed throughout the two value transports. -/
theorem Instance.selection_prophet_totalVariation (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {δ h w c : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4) :
    let π := P.valuePolicy (P.integrable_maximum_of_bounded hcap)
      (hδ.le.trans hwδ) (hδ.le.trans hcδ)
    (∑ i, ∫ x in Icc (2 * h) 1,
      |π.rule.selectionProbabilityAtValue P π.seedLaw i x -
        optimalCompetitiveRatio * P.prophetProbabilityAtValue π.seedLaw i x| ∂P.law i) ≤
      scalarGap P w c / (w * h) + (32 / δ) * (1 + P.positiveCount) ^ 2 * h / w := by
  let π := P.valuePolicy (P.integrable_maximum_of_bounded hcap)
    (hδ.le.trans hwδ) (hδ.le.trans hcδ)
  let f : Fin n → ℝ → ℝ := fun i x => π.rule.selectionProbabilityAtValue P π.seedLaw i x -
    optimalCompetitiveRatio * P.prophetProbabilityAtValue π.seedLaw i x
  let ψ : Fin n → ℝ → ℝ := fun i => restrictedSign (Icc (2 * h) 1) (f i)
  have hf (i : Fin n) : Measurable (f i) :=
    (π.rule.measurable_selectionProbabilityAtValue π.measurable_rule P π.seedLaw i).sub
      ((P.measurable_prophetProbabilityAtValue π.seedLaw i).const_mul optimalCompetitiveRatio)
  have hψ : ∀ i, Measurable (ψ i) := fun i => measurable_restrictedSign measurableSet_Icc (hf i)
  have hb : ∀ i x, |ψ i x| ≤ 1 := fun i x => restrictedSign_abs_le_one _ _ x
  have hs : ∀ i x, x < 2 * h → ψ i x = 0 := by
    intro i x hx
    have hn : x ∉ Icc (2 * h) 1 := fun hm => (not_le.mpr hx) hm.1
    simp only [ψ, restrictedSign, if_neg hn]
  have hstat := P.valuePerturbation_stationarity hcap hδ hwδ hcδ hsum hh hquarter ψ hψ hb hs
  have heq := π.response_difference_eq_marginal_integrals P ψ hψ hb optimalCompetitiveRatio
  have hsum : π.selectedResponse P ψ - optimalCompetitiveRatio * P.expectedProphetResponse ψ =
      ∑ i, ∫ x in Icc (2 * h) 1, |f i x| ∂P.law i := by
    rw [heq]
    apply Finset.sum_congr rfl
    intro i _
    change (∫ x, f i x * restrictedSign (Icc (2 * h) 1) (f i) x ∂P.law i) = _
    simp_rw [mul_restrictedSign]
    exact integral_indicator measurableSet_Icc
  change (∑ i, ∫ x in Icc (2 * h) 1, |f i x| ∂P.law i) ≤ _
  rw [← hsum]
  exact (le_abs_self _).trans hstat

end ProphetSecretary.Model
