import ProphetSecretary.Limiting.CutoffPayloadLaw
import ProphetSecretary.Limiting.LabeledResidualSums

/-!
# Applying a randomized upper-mark map to actual residual variables

The original finite dimension and every identity are retained. Only laws
whose chosen label is at least N are changed. Their independent-tag image
laws preserve probability, and the displayed cap assumptions are exactly
the bounded-image conditions of paper `lem:closure`.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal
namespace ProphetSecretary.Limiting
variable {n : ℕ} {T : Type*} [MeasurableSpace T]

lemma cutoffPayloadLaw_dirac_zero (κ : Measure T) [IsProbabilityMeasure κ]
    {b : ℝ} (hb : 0≤b) (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) :
    cutoffPayloadLaw (⟨Measure.dirac 0,inferInstance⟩ : ProbabilityMeasure ℝ) κ b Φ hΦ=
      (⟨Measure.dirac 0,inferInstance⟩ : ProbabilityMeasure ℝ) := by
  apply ProbabilityMeasure.toMeasure_injective
  change ((Measure.dirac (0 : ℝ)).prod κ).map (cutoffPayloadDisplay b Φ)=Measure.dirac 0
  rw [map_cutoffPayloadDisplay (Measure.dirac 0) κ b Φ hΦ]
  simp [restrict_dirac',not_lt.mpr hb,hb]

lemma cutoffPayloadLaw_tail_le (q : ProbabilityMeasure ℝ) (κ : Measure T) [IsProbabilityMeasure κ]
    (b d : ℝ) (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) :
    (cutoffPayloadLaw q κ b Φ hΦ : Measure ℝ) (Ioi d)≤(q : Measure ℝ) (Ioi (min b d)) := by
  change (((q : Measure ℝ).prod κ).map (cutoffPayloadDisplay b Φ)) (Ioi d)≤_
  rw [Measure.map_apply (measurable_cutoffPayloadDisplay b hΦ) measurableSet_Ioi]
  have hMP : MeasurePreserving (Prod.fst : ℝ × T → ℝ) ((q : Measure ℝ).prod κ) (q : Measure ℝ) := measurePreserving_fst
  exact (measure_mono (cutoffPayloadDisplay_tail_preimage b d Φ)).trans_eq
    (hMP.measure_preimage measurableSet_Ioi.nullMeasurableSet)

noncomputable def mapResidualOffers (P : Model.Instance n) (N : ℕ) (H : ℝ≥0)
    (hCap : ∀ j, ∀ᵐ x ∂P.law j, x≤(H : ℝ)) (κ : Measure T) [IsProbabilityMeasure κ]
    (b : ℝ) (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hImage : ∀ j, ∀ᵐ z ∂(P.law j).prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H) : Model.Instance n where
  law j := if N≤j.val then (cutoffPayloadLaw (P.marginalProbabilityLaw j) κ b Φ hΦ : Measure ℝ) else P.law j
  probability j := by
    split_ifs
    · exact (cutoffPayloadLaw (P.marginalProbabilityLaw j) κ b Φ hΦ).prop
    · exact P.probability j
  nonnegative j := by
    have hOld : ∀ᵐ x ∂P.law j, x∈Icc (0 : ℝ) H := by
      filter_upwards [P.nonnegative j,hCap j] with x hx hX
      exact ⟨hx,hX⟩
    split_ifs
    · exact (cutoffPayloadLaw_supported (P.marginalProbabilityLaw j) κ b Φ hΦ H hOld (hImage j)).mono (fun _ hx => hx.1)
    · exact P.nonnegative j

lemma mapResidualOffers_bounded (P : Model.Instance n) (N : ℕ) (H : ℝ≥0)
    (hCap : ∀ j, ∀ᵐ x ∂P.law j, x≤(H : ℝ)) (κ : Measure T) [IsProbabilityMeasure κ]
    (b : ℝ) (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hImage : ∀ j, ∀ᵐ z ∂(P.law j).prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H) :
    ∀ j, ∀ᵐ x ∂(mapResidualOffers P N H hCap κ b Φ hΦ hImage).law j, x≤(H : ℝ) := by
  intro j
  change ∀ᵐ x ∂(if N≤j.val then (cutoffPayloadLaw (P.marginalProbabilityLaw j) κ b Φ hΦ : Measure ℝ) else P.law j), x≤(H : ℝ)
  split_ifs
  · have hOld : ∀ᵐ x ∂P.law j, x∈Icc (0 : ℝ) H := by
      filter_upwards [P.nonnegative j,hCap j] with x hx hX
      exact ⟨hx,hX⟩
    exact (cutoffPayloadLaw_supported (P.marginalProbabilityLaw j) κ b Φ hΦ H hOld (hImage j)).mono (fun _ hx => hx.2)
  · exact hCap j

lemma labeledPaddedLaw_mapResidualOffers (P : Model.Instance n) (N : ℕ) (H : ℝ≥0)
    (hCap : ∀ j, ∀ᵐ x ∂P.law j, x≤(H : ℝ)) (κ : Measure T) [IsProbabilityMeasure κ]
    (b : ℝ) (hb : 0≤b) (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hImage : ∀ j, ∀ᵐ z ∂(P.law j).prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H) (j : ℕ) :
    labeledPaddedLaw (mapResidualOffers P N H hCap κ b Φ hΦ hImage) j=
      if N≤j then cutoffPayloadLaw (labeledPaddedLaw P j) κ b Φ hΦ else labeledPaddedLaw P j := by
  by_cases hj : j<n
  · rw [labeledPaddedLaw_of_lt _ hj,labeledPaddedLaw_of_lt P hj]
    apply ProbabilityMeasure.toMeasure_injective
    by_cases hNj : N≤j
    · rw [if_pos hNj]
      change (if N≤j then _ else _)=_
      rw [if_pos hNj]
    · rw [if_neg hNj]
      change (if N≤j then _ else _)=_
      rw [if_neg hNj]
      rfl
  · have hOld : labeledPaddedLaw P j=(⟨Measure.dirac 0,inferInstance⟩ : ProbabilityMeasure ℝ) := by
      apply ProbabilityMeasure.toMeasure_injective
      exact labeledPaddedLaw_of_ge P (not_lt.mp hj)
    have hNew : labeledPaddedLaw (mapResidualOffers P N H hCap κ b Φ hΦ hImage) j=
        (⟨Measure.dirac 0,inferInstance⟩ : ProbabilityMeasure ℝ) := by
      apply ProbabilityMeasure.toMeasure_injective
      exact labeledPaddedLaw_of_ge _ (not_lt.mp hj)
    rw [hOld,hNew,cutoffPayloadLaw_dirac_zero κ hb Φ hΦ]
    split_ifs <;> rfl

lemma mapResidualOffers_tailCount_le (P : Model.Instance n) (N : ℕ) (H : ℝ≥0)
    (hCap : ∀ j, ∀ᵐ x ∂P.law j, x≤(H : ℝ)) (κ : Measure T) [IsProbabilityMeasure κ]
    (b d : ℝ) (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hImage : ∀ j, ∀ᵐ z ∂(P.law j).prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H) :
    (mapResidualOffers P N H hCap κ b Φ hΦ hImage).tailCount d≤P.tailCount (min b d) := by
  apply Finset.sum_le_sum
  intro j _
  have hRaw : (mapResidualOffers P N H hCap κ b Φ hΦ hImage).law j (Ioi d)≤P.law j (Ioi (min b d)) := by
    change (if N≤j.val then (cutoffPayloadLaw (P.marginalProbabilityLaw j) κ b Φ hΦ : Measure ℝ) else P.law j) (Ioi d)≤_
    split_ifs
    · exact cutoffPayloadLaw_tail_le (P.marginalProbabilityLaw j) κ b d Φ hΦ
    · exact measure_mono (Ioi_subset_Ioi (min_le_right _ _))
  exact ENNReal.toReal_mono (measure_ne_top _ _) hRaw

end ProphetSecretary.Limiting
