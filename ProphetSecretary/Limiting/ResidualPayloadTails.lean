import ProphetSecretary.Limiting.ResidualPayloadInstance

/-!
# Tail-count changes of randomized residual mark replacements

The changed probability of any event is at most the original upper-band
mass. Summing this bound preserves dense below-reserve supply under the
uniform finite tail bound, independently of the number of finite variables.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal BigOperators
namespace ProphetSecretary.Limiting
variable {T : Type*} [MeasurableSpace T]

lemma cutoffPayloadLaw_event_bounds (q : ProbabilityMeasure ℝ) (κ : Measure T) [IsProbabilityMeasure κ]
    (b : ℝ) (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) {E : Set ℝ} (hE : MeasurableSet E) :
    (q : Measure ℝ) E≤(cutoffPayloadLaw q κ b Φ hΦ : Measure ℝ) E+(q : Measure ℝ) (Ioi b) ∧
    (cutoffPayloadLaw q κ b Φ hΦ : Measure ℝ) E≤(q : Measure ℝ) E+(q : Measure ℝ) (Ioi b) := by
  let μ := (q : Measure ℝ)
  let η := ((μ.restrict (Ioi b)).prod κ).map Φ
  have hOld : (μ.restrict (Ioi b)) E+(μ.restrict (Iic b)) E=μ E := by
    have h := congrArg (fun ν : Measure ℝ => ν E) (Measure.restrict_add_restrict_compl (μ := μ) (s := Ioi b) measurableSet_Ioi)
    simpa only [Measure.add_apply,compl_Ioi] using h
  have hNew : (cutoffPayloadLaw q κ b Φ hΦ : Measure ℝ) E=(μ.restrict (Iic b)) E+η E := by
    change ((μ.prod κ).map (cutoffPayloadDisplay b Φ)) E=_
    rw [map_cutoffPayloadDisplay μ κ b Φ hΦ,Measure.add_apply]
  have hUpper : (μ.restrict (Ioi b)) E≤μ (Ioi b) := by
    rw [Measure.restrict_apply hE]
    exact measure_mono inter_subset_right
  have hLower : (μ.restrict (Iic b)) E≤μ E := Measure.restrict_le_self _
  have hImageMass : η univ=μ (Ioi b) := by
    dsimp only [η]
    rw [Measure.map_apply hΦ MeasurableSet.univ,preimage_univ,← univ_prod_univ,Measure.prod_prod,
      Measure.restrict_apply_univ,measure_univ,mul_one]
  have hImage : η E≤μ (Ioi b) := (measure_mono (subset_univ E)).trans_eq hImageMass
  constructor
  · rw [← hOld,hNew]
    calc
      _ ≤ μ (Ioi b)+(μ.restrict (Iic b)) E := add_le_add hUpper le_rfl
      _ = (μ.restrict (Iic b)) E+μ (Ioi b) := add_comm _ _
      _ ≤ _ := add_le_add (le_add_of_nonneg_right bot_le) le_rfl
  · rw [hNew]
    exact add_le_add hLower hImage

lemma mapResidualOffers_old_tail_le {n : ℕ} (P : Model.Instance n) (N : ℕ) (H : ℝ≥0)
    (hCap : ∀ j, ∀ᵐ x ∂P.law j, x≤(H : ℝ)) (κ : Measure T) [IsProbabilityMeasure κ]
    (b d : ℝ) (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hImage : ∀ j, ∀ᵐ z ∂(P.law j).prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H) :
    extendedTailCount P d≤extendedTailCount (mapResidualOffers P N H hCap κ b Φ hΦ hImage) d+
      extendedTailCount P b := by
  have hPoint (j : Fin n) : P.law j (Ioi d)≤
      (mapResidualOffers P N H hCap κ b Φ hΦ hImage).law j (Ioi d)+P.law j (Ioi b) := by
    change P.law j (Ioi d)≤(if N≤j.val then (cutoffPayloadLaw (P.marginalProbabilityLaw j) κ b Φ hΦ : Measure ℝ) else P.law j) (Ioi d)+P.law j (Ioi b)
    split_ifs
    · exact (cutoffPayloadLaw_event_bounds (P.marginalProbabilityLaw j) κ b Φ hΦ measurableSet_Ioi).1
    · exact le_add_of_nonneg_right bot_le
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hPoint j)
  rw [Finset.sum_add_distrib] at h
  exact h

lemma tendsto_ennreal_top_of_le_add_finite {f g : ℕ → ENNReal} {C : ENNReal} (hC : C<⊤)
    (h : Tendsto f atTop (𝓝 ⊤)) (hBound : ∀ m, f m≤g m+C) :
    Tendsto g atTop (𝓝 ⊤) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    have hPlus : a+C<(⊤ : ENNReal) := ENNReal.add_lt_top.mpr ⟨ha,hC⟩
    filter_upwards [h.eventually (Ioi_mem_nhds hPlus)] with m hm
    by_contra hn
    have hLe : g m≤a := not_lt.mp hn
    exact (not_le_of_gt hm) ((hBound m).trans (add_le_add hLe le_rfl))
  · intro a ha
    exact (not_lt_of_ge le_top ha).elim

end ProphetSecretary.Limiting
