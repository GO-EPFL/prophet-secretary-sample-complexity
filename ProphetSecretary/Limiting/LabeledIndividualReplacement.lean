import ProphetSecretary.Limiting.LabeledResidualSums

/-!
# Replacing a specified finite label, including a padded zero label

The actual finite family is padded before the selected marginal is replaced.
Every other chosen label retains its law. At nonnegative levels its total
exceedance count changes by at most one, independently of instance size.
-/
open MeasureTheory Set Filter
open scoped Classical Topology ENNReal BigOperators
namespace ProphetSecretary.Limiting
variable {n : ℕ}

noncomputable def replaceLabeledIndividual (P : Model.Instance n) (i : ℕ) (q : ProbabilityMeasure ℝ)
    (hq : ∀ᵐ x ∂(q : Measure ℝ), 0≤x) : Model.Instance (n+(i+1)) where
  law j := if j.val=i then (q : Measure ℝ) else (labeledPaddedLaw P j.val : Measure ℝ)
  probability j := by
    split_ifs
    · exact q.prop
    · exact (labeledPaddedLaw P j.val).prop
  nonnegative j := by
    by_cases hj : j.val=i
    · simpa only [if_pos hj] using hq
    · simpa only [if_neg hj] using labeledPaddedLaw_nonnegative P j.val

lemma labeledPaddedLaw_replaceLabeledIndividual (P : Model.Instance n) (i : ℕ)
    (q : ProbabilityMeasure ℝ) (hq : ∀ᵐ x ∂(q : Measure ℝ), 0≤x) (j : ℕ) :
    labeledPaddedLaw (replaceLabeledIndividual P i q hq) j=Function.update (labeledPaddedLaw P) i q j := by
  by_cases hj : j<n+(i+1)
  · rw [labeledPaddedLaw_of_lt _ hj]
    apply ProbabilityMeasure.toMeasure_injective
    by_cases hji : j=i
    · subst j
      rw [Function.update_self]
      change (if i=i then (q : Measure ℝ) else _)=_
      rw [if_pos rfl]
    · rw [Function.update_of_ne hji]
      change (if j=i then (q : Measure ℝ) else _)=_
      rw [if_neg hji]
  · have hjn : n≤j := by omega
    have hji : j≠i := by omega
    apply ProbabilityMeasure.toMeasure_injective
    rw [labeledPaddedLaw_of_ge _ (not_lt.mp hj),Function.update_of_ne hji,labeledPaddedLaw_of_ge P hjn]

lemma replaceLabeledIndividual_bounded (P : Model.Instance n) (i : ℕ)
    (q : ProbabilityMeasure ℝ) (hq : ∀ᵐ x ∂(q : Measure ℝ), 0≤x)
    {H : ℝ} (hH : 0≤H) (hP : ∀ j, ∀ᵐ x ∂P.law j, x≤H)
    (hQ : ∀ᵐ x ∂(q : Measure ℝ), x≤H) :
    ∀ j, ∀ᵐ x ∂(replaceLabeledIndividual P i q hq).law j, x≤H := by
  intro j
  change ∀ᵐ x ∂(if j.val=i then (q : Measure ℝ) else (labeledPaddedLaw P j.val : Measure ℝ)), x≤H
  by_cases hj : j.val=i
  · rw [if_pos hj]
    exact hQ
  · rw [if_neg hj]
    exact (labeledPaddedLaw_supported P hH hP j.val).mono (fun _ hx => hx.2)

lemma replaceLabeledIndividual_tailCounts (P : Model.Instance n) (i : ℕ)
    (q : ProbabilityMeasure ℝ) (hq : ∀ᵐ x ∂(q : Measure ℝ), 0≤x)
    {b : ℝ} (hb : 0≤b) :
    extendedTailCount P b≤extendedTailCount (replaceLabeledIndividual P i q hq) b+1 ∧
    extendedTailCount (replaceLabeledIndividual P i q hq) b≤extendedTailCount P b+1 := by
  let R := replaceLabeledIndividual P i q hq
  have hOld j : (labeledPaddedLaw P j : Measure ℝ) (Ioi b)≤
      (labeledPaddedLaw R j : Measure ℝ) (Ioi b)+(if j=i then 1 else 0) := by
    by_cases hji : j=i
    · rw [if_pos hji]
      exact (prob_le_one : (labeledPaddedLaw P j : Measure ℝ) (Ioi b)≤1).trans (le_add_of_nonneg_left bot_le)
    · rw [if_neg hji,add_zero,labeledPaddedLaw_replaceLabeledIndividual P i q hq j,Function.update_of_ne hji]
  have hNew j : (labeledPaddedLaw R j : Measure ℝ) (Ioi b)≤
      (labeledPaddedLaw P j : Measure ℝ) (Ioi b)+(if j=i then 1 else 0) := by
    by_cases hji : j=i
    · rw [if_pos hji]
      exact (prob_le_one : (labeledPaddedLaw R j : Measure ℝ) (Ioi b)≤1).trans (le_add_of_nonneg_left bot_le)
    · rw [if_neg hji,add_zero,labeledPaddedLaw_replaceLabeledIndividual P i q hq j,Function.update_of_ne hji]
  have hSingle : (∑' j : ℕ, if j=i then (1 : ENNReal) else 0)=1 := by simp
  rw [extendedTailCount_eq_padded_tsum P hb,extendedTailCount_eq_padded_tsum R hb]
  exact ⟨(ENNReal.tsum_le_tsum hOld).trans_eq (by rw [ENNReal.tsum_add,hSingle]),
    (ENNReal.tsum_le_tsum hNew).trans_eq (by rw [ENNReal.tsum_add,hSingle])⟩

lemma replaceLabeledIndividual_tailCount_le (P : Model.Instance n) (i : ℕ)
    (q : ProbabilityMeasure ℝ) (hq : ∀ᵐ x ∂(q : Measure ℝ), 0≤x)
    {b : ℝ} (hb : 0≤b) :
    (replaceLabeledIndividual P i q hq).tailCount b≤P.tailCount b+1 := by
  have h := (replaceLabeledIndividual_tailCounts P i q hq hb).2
  have hReal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨(extendedTailCount_finite P b).ne,by simp⟩) h
  have hAdd : (extendedTailCount P b+1).toReal=(extendedTailCount P b).toReal+1 := by
    rw [ENNReal.toReal_add (extendedTailCount_finite P b).ne (by simp : (1 : ENNReal)≠⊤),ENNReal.toReal_one]
  rw [hAdd,extendedTailCount_toReal,extendedTailCount_toReal] at hReal
  exact hReal

lemma tendsto_ennreal_top_of_le_add_one {f g : ℕ → ENNReal}
    (h : Tendsto f atTop (𝓝 ⊤)) (hBound : ∀ m, f m≤g m+1) :
    Tendsto g atTop (𝓝 ⊤) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    have hPlus : a+1<(⊤ : ENNReal) := ENNReal.add_lt_top.mpr ⟨ha,by simp⟩
    filter_upwards [h.eventually (Ioi_mem_nhds hPlus)] with m hm
    by_contra hn
    have hLe : g m≤a := not_lt.mp hn
    exact (not_le_of_gt hm) ((hBound m).trans (add_le_add hLe le_rfl))
  · intro a ha
    exact (not_lt_of_ge le_top ha).elim

end ProphetSecretary.Limiting
