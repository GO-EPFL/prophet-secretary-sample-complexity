import ProphetSecretary.Model.LawBranchIntegration

/-!
# Vanishing finite branches at terminal horizon

If a nonempty unseen state contains identity `j`, its actual multiplier can be
nonzero only before `j` arrives, even if its value is zero. Every finite clock
is strictly before one almost surely. A perturbed terminal root therefore moves
only through a region where that multiplier is already zero. The empty state's
zero-value branch is identically zero.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ} {Seed : Type*}

lemma Policy.branchMultiplier_zero_after_member (π : Policy Seed n) (r : Seed) (x u : Fin n → ℝ)
    (i : Fin n) (A : Finset (Fin n)) {j : Fin n} (hj : j ∈ A) {t : ℝ} (hjt : u j < t) :
    π.branchMultiplier r x u i A t = 0 := by
  unfold Policy.branchMultiplier
  apply if_neg
  rintro ⟨_hU, hA, _hR⟩
  have hj' : j ∈ otherUnseen u i t := hA.symm ▸ hj
  exact (not_le_of_gt hjt) (Finset.mem_filter.mp hj').2

lemma Instance.eventually_lawStateBranchLoss_zero_terminal_nonempty (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (i : Fin n) (A : Finset (Fin n))
    (hA : A.Nonempty) (ω : World n Unit) (hxCap : ω.1 i ≤ H) (hClocks : ∀ j, ω.2.1 j < 1)
    (hZero : P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i) = 0) :
    ∀ᶠ δ : ℝ in 𝓝 0, ∀ t : ℝ, P.lawStateBranchLoss hw hc.le hbound h hh hb hm θ (θ + δ) i A ω t = 0 := by
  obtain ⟨j, hj⟩ := hA
  let Q := P.likelihoodWidePath h hh hb hm θ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  let π : Policy Unit n := (Q.valuePolicy hQ hw.le hc.le).rule
  have hRootCont : ContinuousAt (fun q ↦ P.lawStateRoot hbound h hh hb hm w q A (ω.1 i)) θ :=
    continuous_const.continuousAt.mul
      (((P.restrictTo A).lawDurationRoot_continuousOn hH (fun k ↦ hbound (stateEmbedding A k)) hxCap
        (fun k ↦ h (stateEmbedding A k)) (fun k ↦ hh (stateEmbedding A k))
        (fun k ↦ hb (stateEmbedding A k)) (fun k ↦ hm (stateEmbedding A k))).continuousAt (Ioo_mem_nhds hθ.1 hθ.2))
  have hRoot : Tendsto (fun q ↦ P.lawStateRoot hbound h hh hb hm w q A (ω.1 i)) (𝓝 θ) (𝓝 0) := by
    simpa only [hZero] using hRootCont.tendsto
  have hAdd : Tendsto (fun δ : ℝ ↦ θ + δ) (𝓝 0) (𝓝 θ) := by
    have hC : Continuous (fun δ : ℝ ↦ θ + δ) := continuous_const.add continuous_id
    simpa only [add_zero] using hC.tendsto 0
  have hClock : Tendsto (fun δ : ℝ ↦ 1 - P.lawStateRoot hbound h hh hb hm w (θ + δ) A (ω.1 i) / c)
      (𝓝 0) (𝓝 1) := by
    have hR := hRoot.comp hAdd
    change Tendsto (fun δ : ℝ ↦ P.lawStateRoot hbound h hh hb hm w (θ + δ) A (ω.1 i)) (𝓝 0) (𝓝 0) at hR
    simpa only [zero_div, sub_zero] using tendsto_const_nhds.sub (hR.div_const c)
  filter_upwards [hClock (Ioi_mem_nhds (hClocks j))] with δ hδ t
  change π.branchMultiplier () ω.1 ω.2.1 i A t * ProphetSecretary.Analysis.rootActionLoss
    (P.lawStateValue h hh hb hm w (θ + δ) A) (w * ω.1 i) c
    (P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i)) t = 0
  by_cases hMask : t ∈ Icc (0 : ℝ) 1 ∧ otherUnseen ω.2.1 i t = A ∧ t ≤ π.pendingTime () ω.1 ω.2.1 i
  · have hj' : j ∈ otherUnseen ω.2.1 i t := hMask.2.1.symm ▸ hj
    have htj : t ≤ ω.2.1 j := (Finset.mem_filter.mp hj').2
    have ht : t < 1 := htj.trans_lt (hClocks j)
    have htRoot : t < 1 - P.lawStateRoot hbound h hh hb hm w (θ + δ) A (ω.1 i) / c := htj.trans_lt hδ
    let T := P.likelihoodWidePath h hh hb hm (θ + δ)
    have hT := T.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm (θ + δ) hbound)
    have hChild := T.restrictTo_integrable_maximum A hT
    have hAccept := (T.restrictTo A).durationRoot_acceptance_iff hChild hw hc ht (x := ω.1 i)
    rw [← P.lawStateRoot_eq_instanceRoot hbound h hh hb hm w (θ + δ) A (ω.1 i)] at hAccept
    have hNew : w * ω.1 i ≤ optimalScalarValue (T.restrictTo A) w (c * (1 - t)) :=
      (lt_of_not_ge (fun hV ↦ not_le_of_gt htRoot (hAccept.mp hV))).le
    have hValue : P.lawStateValue h hh hb hm w (θ + δ) A (c * (1 - t)) =
        optimalScalarValue (T.restrictTo A) w (c * (1 - t)) := by
      rw [P.lawStateValue_eq_instanceValue h hh hb hm w (θ + δ) A,
        max_eq_right (mul_nonneg hc.le (sub_pos.mpr ht).le)]
    rw [Policy.branchMultiplier, if_pos hMask, one_mul, hZero]
    unfold ProphetSecretary.Analysis.rootActionLoss
    rw [zero_div, sub_zero, if_neg (not_le.mpr ht), hValue, max_eq_right hNew, sub_self]
  · rw [Policy.branchMultiplier, if_neg hMask, zero_mul]

lemma Instance.lawStateBranchLoss_terminal_empty_zero (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ ρ : ℝ) (i : Fin n) (ω : World n Unit) (hx : 0 ≤ ω.1 i)
    (hZero : P.lawStateRoot hbound h hh hb hm w θ ∅ (ω.1 i) = 0) (t : ℝ) :
    P.lawStateBranchLoss hw hc.le hbound h hh hb hm θ ρ i ∅ ω t = 0 := by
  let Q := P.likelihoodWidePath h hh hb hm θ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  let R : Instance 0 := Q.restrictTo (∅ : Finset (Fin n))
  have hR := Q.restrictTo_integrable_maximum (∅ : Finset (Fin n)) hQ
  have hZero' := hZero
  rw [P.lawStateRoot_eq_instanceRoot hbound h hh hb hm w θ ∅ (ω.1 i)] at hZero'
  have hxle : ω.1 i ≤ 0 := by
    by_contra hn
    have hlevel : optimalScalarValue R 1 0 < ω.1 i := by
      rw [optimalScalarValue_empty]
      exact lt_of_not_ge hn
    have hpos := mul_pos hw (R.durationRoot_positive hR hlevel)
    exact hpos.ne' hZero'
  have hx0 : ω.1 i = 0 := le_antisymm hxle hx
  change _ * ProphetSecretary.Analysis.rootActionLoss (P.lawStateValue h hh hb hm w ρ ∅) (w * ω.1 i) c
    (P.lawStateRoot hbound h hh hb hm w θ ∅ (ω.1 i)) t = 0
  rw [hZero, hx0, mul_zero]
  unfold ProphetSecretary.Analysis.rootActionLoss
  have hValue : P.lawStateValue h hh hb hm w ρ ∅ (c * (1 - t)) = max 0 (c * (1 - t)) := by
    rw [P.lawStateValue_eq_instanceValue h hh hb hm w ρ ∅]
    let R' : Instance 0 := (P.likelihoodWidePath h hh hb hm ρ).restrictTo (∅ : Finset (Fin n))
    change optimalScalarValue R' w (max 0 (c * (1 - t))) = _
    exact optimalScalarValue_empty R' w (max 0 (c * (1 - t)))
  rw [hValue, zero_div, sub_zero, max_eq_right (le_max_left 0 (c * (1 - t)))]
  by_cases ht : 1 ≤ t
  · have hCoeff : c * (1 - t) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc.le (sub_nonpos.mpr ht)
    rw [if_pos ht, max_eq_left hCoeff, sub_self, mul_zero]
  · rw [if_neg ht, sub_self, mul_zero]

/-- Every finite terminal-root state branch has zero quadratic contribution.
No derivative or regularity at coefficient zero is assumed. -/
theorem Instance.lawStateBranchLoss_terminal_limit (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (i : Fin n) (A : Finset (Fin n))
    (ω : World n Unit) (hx : 0 ≤ ω.1 i) (hxCap : ω.1 i ≤ H) (hClocks : ∀ j, ω.2.1 j < 1)
    (hZero : P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i) = 0) :
    Tendsto (fun δ : ℝ ↦ (∫ t : ℝ, P.lawStateBranchLoss hw hc.le hbound h hh hb hm θ (θ + δ) i A ω t) / δ ^ 2)
      (𝓝[≠] 0) (𝓝 (0 : ℝ)) := by
  by_cases hA : A = ∅
  · subst A
    apply tendsto_const_nhds.congr'
    exact Filter.Eventually.of_forall (fun δ ↦ by
      have he : (fun t : ℝ ↦ P.lawStateBranchLoss hw hc.le hbound h hh hb hm θ (θ + δ) i ∅ ω t) =
          (fun _ ↦ (0 : ℝ)) := funext (P.lawStateBranchLoss_terminal_empty_zero hw hc hbound h hh hb hm θ (θ + δ) i ω hx hZero)
      change (0 : ℝ) = (∫ t : ℝ, P.lawStateBranchLoss hw hc.le hbound h hh hb hm θ (θ + δ) i ∅ ω t) / δ ^ 2
      rw [he, integral_zero, zero_div])
  · have hAn : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hA
    have hEv := P.eventually_lawStateBranchLoss_zero_terminal_nonempty hw hc hH hbound h hh hb hm hθ i A hAn ω hxCap hClocks hZero
    apply tendsto_const_nhds.congr'
    filter_upwards [hEv.filter_mono nhdsWithin_le_nhds] with δ hδ
    have he : (fun t : ℝ ↦ P.lawStateBranchLoss hw hc.le hbound h hh hb hm θ (θ + δ) i A ω t) =
        (fun _ ↦ (0 : ℝ)) := funext hδ
    change (0 : ℝ) = (∫ t : ℝ, P.lawStateBranchLoss hw hc.le hbound h hh hb hm θ (θ + δ) i A ω t) / δ ^ 2
    rw [he, integral_zero, zero_div]

end ProphetSecretary.Model
