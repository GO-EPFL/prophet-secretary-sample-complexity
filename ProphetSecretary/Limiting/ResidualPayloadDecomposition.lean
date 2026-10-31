import ProphetSecretary.Limiting.ResidualPayloadInstance
import ProphetSecretary.Limiting.WeakPositiveDifference

/-!
# Positive finite residual decompositions for upper-mark replacement

Before taking any weak limit, the original coarse residual is the sum of
an unchanged positive base measure and the affected old upper-band measure.
The displayed residual above a higher test level replaces exactly the latter
by its actual independent-tag image. No signed residual is postulated.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal BigOperators
namespace ProphetSecretary.Limiting
variable {n : ℕ} {T : Type*} [MeasurableSpace T]

lemma finiteMeasure_restrict_split_upper (μ : FiniteMeasure ℝ) {c b : ℝ} (hcb : c≤b) :
    μ.restrict (Ioi c)=μ.restrict (Ioc c b)+μ.restrict (Ioi b) := by
  have hUnion : Ioc c b∪Ioi b=Ioi c := by
    ext x
    simp only [mem_union,mem_Ioc,mem_Ioi]
    constructor
    · rintro (h | h)
      · exact h.1
      · exact hcb.trans_lt h
    · intro h
      by_cases hx : x≤b
      · exact Or.inl ⟨h,hx⟩
      · exact Or.inr (not_le.mp hx)
  have hDisjoint : Disjoint (Ioc c b) (Ioi b) := disjoint_left.mpr (fun _ hx hy => (not_lt.mpr hx.2) hy)
  rw [← hUnion,FiniteMeasure.restrict_union hDisjoint measurableSet_Ioi]

noncomputable def residualPayloadBase (P : Model.Instance n) (N M : ℕ) (c b : ℝ) : FiniteMeasure ℝ :=
  ∑ i∈Finset.univ.filter (fun i : Fin n => N≤ i.val),
    if i.val<M then (P.marginalProbabilityLaw i).toFiniteMeasure.restrict (Ioi c)
    else (P.marginalProbabilityLaw i).toFiniteMeasure.restrict (Ioc c b)

lemma residualPayloadBase_add_old (P : Model.Instance n) {N M : ℕ} (hNM : N≤M)
    {c b : ℝ} (hcb : c≤b) :
    residualPayloadBase P N M c b+labeledBandResidual P M b=labeledBandResidual P N c := by
  unfold residualPayloadBase labeledBandResidual
  rw [Finset.sum_filter,Finset.sum_filter,Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hNi : N≤ i.val
  · rw [if_pos hNi,if_pos hNi]
    by_cases hMi : M≤ i.val
    · rw [if_pos hMi,if_neg (not_lt.mpr hMi)]
      exact (finiteMeasure_restrict_split_upper _ hcb).symm
    · rw [if_neg hMi,if_pos (not_le.mp hMi),add_zero]
  · have hMi : ¬M≤ i.val := fun hm => hNi (hNM.trans hm)
    rw [if_neg hNi,if_neg hNi,if_neg hMi,zero_add]

lemma residualPayloadBase_eq_difference (P : Model.Instance n) {N M : ℕ} (hNM : N≤M)
    {c b : ℝ} (hcb : c≤b) :
    residualPayloadBase P N M c b=
      positiveFiniteDifference (labeledBandResidual P N c) (labeledBandResidual P M b) := by
  have hOrder : (labeledBandResidual P M b : Measure ℝ)≤(labeledBandResidual P N c : Measure ℝ) := by
    rw [← residualPayloadBase_add_old P hNM hcb,FiniteMeasure.toMeasure_add]
    apply Measure.le_iff.mpr
    intro E _hE
    rw [Measure.add_apply]
    exact le_add_of_nonneg_left bot_le
  have h := congrArg FiniteMeasure.toMeasure ((residualPayloadBase_add_old P hNM hcb).trans
    (positiveFiniteDifference_add _ _ hOrder).symm)
  rw [FiniteMeasure.toMeasure_add,FiniteMeasure.toMeasure_add] at h
  exact FiniteMeasure.toMeasure_injective ((Measure.add_left_inj _ _ _).mp h)

lemma displayedPayloadIntensity_labeledBandResidual (P : Model.Instance n) (M : ℕ) (b : ℝ)
    (κ : Measure T) [IsProbabilityMeasure κ] (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ) :
    displayedPayloadIntensity (labeledBandResidual P M b) κ Φ hΦ=
      ∑ i∈Finset.univ.filter (fun i : Fin n => M≤ i.val),
        displayedPayloadIntensity ((P.marginalProbabilityLaw i).toFiniteMeasure.restrict (Ioi b)) κ Φ hΦ := by
  change payloadImageHom κ Φ hΦ (∑ i∈Finset.univ.filter (fun i : Fin n => M≤ i.val),
    (P.marginalProbabilityLaw i).toFiniteMeasure.restrict (Ioi b))=_
  rw [map_sum]
  rfl

lemma mapResidualOffers_residual_above (P : Model.Instance n) {N M : ℕ} (hNM : N≤M)
    (H : ℝ≥0) (hCap : ∀ j, ∀ᵐ x ∂P.law j, x≤(H : ℝ)) (κ : Measure T) [IsProbabilityMeasure κ]
    (b : ℝ) (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hImage : ∀ j, ∀ᵐ z ∂(P.law j).prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H)
    {c d : ℝ} (hcd : c≤d) :
    labeledBandResidual (mapResidualOffers P M H hCap κ b Φ hΦ hImage) N d=
      (residualPayloadBase P N M c b+displayedPayloadIntensity (labeledBandResidual P M b) κ Φ hΦ).restrict (Ioi d) := by
  rw [displayedPayloadIntensity_labeledBandResidual]
  apply FiniteMeasure.toMeasure_injective
  ext E hE
  rw [FiniteMeasure.restrict_measure_eq,Measure.restrict_apply hE,FiniteMeasure.toMeasure_add,Measure.add_apply]
  unfold labeledBandResidual residualPayloadBase
  rw [FiniteMeasure.toMeasure_sum,Measure.finsetSum_apply,FiniteMeasure.toMeasure_sum,Measure.finsetSum_apply,
    FiniteMeasure.toMeasure_sum,Measure.finsetSum_apply]
  rw [Finset.sum_filter,Finset.sum_filter,Finset.sum_filter,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hNi : N≤ i.val
  · rw [if_pos hNi,if_pos hNi]
    by_cases hMi : M≤ i.val
    · rw [if_pos hMi,if_neg (not_lt.mpr hMi)]
      rw [displayedPayloadIntensity_toMeasure]
      change ((if M≤ i.val then (cutoffPayloadLaw (P.marginalProbabilityLaw i) κ b Φ hΦ : Measure ℝ)
          else P.law i).restrict (Ioi d)) E=
        ((P.law i).restrict (Ioc c b)) (E∩Ioi d)+
          (((P.law i).restrict (Ioi b)).prod κ).map Φ (E∩Ioi d)
      rw [if_pos hMi,Measure.restrict_apply hE]
      change (((P.law i).prod κ).map (cutoffPayloadDisplay b Φ)) (E∩Ioi d)=_
      rw [map_cutoffPayloadDisplay (P.law i) κ b Φ hΦ,Measure.add_apply,
        Measure.restrict_apply (hE.inter measurableSet_Ioi),Measure.restrict_apply (hE.inter measurableSet_Ioi)]
      congr 1
      apply congrArg (P.law i)
      ext x
      simp only [mem_inter_iff,mem_Ioi,mem_Iic,mem_Ioc]
      constructor
      · rintro ⟨⟨hx,hd⟩,hb⟩
        exact ⟨⟨hx,hd⟩,hcd.trans_lt hd,hb⟩
      · rintro ⟨⟨hx,hd⟩,_,hb⟩
        exact ⟨⟨hx,hd⟩,hb⟩
    · rw [if_neg hMi,if_pos (not_le.mp hMi),add_zero]
      change ((if M≤ i.val then (cutoffPayloadLaw (P.marginalProbabilityLaw i) κ b Φ hΦ : Measure ℝ)
          else P.law i).restrict (Ioi d)) E=((P.law i).restrict (Ioi c)) (E∩Ioi d)
      rw [if_neg hMi,Measure.restrict_apply hE,Measure.restrict_apply (hE.inter measurableSet_Ioi)]
      congr 1
      exact (inter_eq_left.mpr (fun _ hx => hcd.trans_lt hx.2)).symm
  · have hMi : ¬M≤ i.val := fun hm => hNi (hNM.trans hm)
    rw [if_neg hNi,if_neg hNi,if_neg hMi,zero_add]

end ProphetSecretary.Limiting
