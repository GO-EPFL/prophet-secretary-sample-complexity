import ProphetSecretary.Analysis.MovingThreshold
import ProphetSecretary.Analysis.MovingPrimitive

/-!
# Threshold action loss at an old and a new continuation root

The old action is specified by its elapsed crossing time. A positive change of
coefficient locates that same old crossing in the new continuation function,
allowing the exact oriented integral to reuse the finite threshold calculation.
This coefficient change is analytical and supplies no information to a policy.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace ProphetSecretary.Analysis

noncomputable def rootActionLoss (f : ℝ → ℝ) (x c d t : ℝ) : ℝ :=
  max x (f (c * (1 - t))) - if 1 - d / c ≤ t then x else f (c * (1 - t))

lemma rootActionLoss_nonnegative (f : ℝ → ℝ) (x c d t : ℝ) : 0 ≤ rootActionLoss f x c d t := by
  unfold rootActionLoss
  split_ifs
  · exact sub_nonneg.mpr (le_max_left _ _)
  · exact sub_nonneg.mpr (le_max_right _ _)

lemma measurable_rootActionLoss {f : ℝ → ℝ} (hf : Measurable f) (x c d : ℝ) :
    Measurable (rootActionLoss f x c d) := by
  have hn : Measurable (fun t : ℝ ↦ f (c * (1 - t))) :=
    hf.comp (measurable_const.mul (measurable_const.sub measurable_id))
  exact (measurable_const.max hn).sub (Measurable.ite
    (measurableSet_le measurable_const measurable_id) measurable_const hn)

lemma rootActionLoss_le_abs (f : ℝ → ℝ) (x c d t : ℝ) :
    rootActionLoss f x c d t ≤ |x| + |f (c * (1 - t))| := by
  have h : rootActionLoss f x c d t ≤ |x - f (c * (1 - t))| := by
    unfold rootActionLoss
    split_ifs
    · have hm : max x (f (c * (1 - t))) ≤ x + |x - f (c * (1 - t))| :=
        max_le (by linarith [abs_nonneg (x - f (c * (1 - t)))])
          (by linarith [neg_le_abs (x - f (c * (1 - t)))])
      linarith
    · have hm : max x (f (c * (1 - t))) ≤ f (c * (1 - t)) + |x - f (c * (1 - t))| :=
        max_le (by linarith [le_abs_self (x - f (c * (1 - t)))])
          (by linarith [abs_nonneg (x - f (c * (1 - t)))])
      linarith
  exact h.trans (by simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le x 0 (f (c * (1 - t))))

lemma rootActionLoss_eq_branchThresholdLoss {f : ℝ → ℝ} {c d e : ℝ}
    (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hLevel : ∀ s, f s ≤ f e ↔ s ≤ e) :
    rootActionLoss f (f e) c d = branchThresholdLoss f e (c * e / d) c := by
  have hz : 0 < c * e / d := div_pos (mul_pos hc he) hd
  have hroot : e / (c * e / d) = d / c := by field_simp [hc.ne', hd.ne', he.ne']
  funext t
  unfold rootActionLoss branchThresholdLoss
  simp only [moving_level_iff hLevel hz, hroot]

lemma integral_rootActionLoss {f : ℝ → ℝ} {c d e : ℝ}
    (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hLevel : ∀ s, f s ≤ f e ↔ s ≤ e) :
    (∫ t : ℝ, rootActionLoss f (f e) c d t) =
      (1 / c) * ∫ s in e..d, f s - f e := by
  rw [rootActionLoss_eq_branchThresholdLoss hc hd he hLevel,
    integral_branchThresholdLoss hLevel (div_pos (mul_pos hc he) hd) hc]
  have hEnd : e * c / (c * e / d) = d := by field_simp [hc.ne', hd.ne', he.ne']
  rw [hEnd]

lemma integrable_rootActionLoss {f : ℝ → ℝ} (hf : Continuous f) {c d e : ℝ}
    (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hLevel : ∀ s, f s ≤ f e ↔ s ≤ e) :
    Integrable (rootActionLoss f (f e) c d) volume := by
  rw [rootActionLoss_eq_branchThresholdLoss hc hd he hLevel]
  exact integrable_branchThresholdLoss hf hLevel (div_pos (mul_pos hc he) hd) hc

lemma rootActionLoss_zero_outside {f : ℝ → ℝ} {c d e t : ℝ}
    (hc : 0 < c) (hd : 0 < d) (he : 0 < e)
    (hLevel : ∀ s, f s ≤ f e ↔ s ≤ e)
    (ht : t ∉ uIcc (1 - d / c) (1 - e / c)) : rootActionLoss f (f e) c d t = 0 := by
  rw [rootActionLoss_eq_branchThresholdLoss hc hd he hLevel]
  apply branchThresholdLoss_zero_outside hLevel (div_pos (mul_pos hc he) hd) hc
  have hroot : e / (c * e / d) = d / c := by field_simp [hc.ne', hd.ne', he.ne']
  simpa only [hroot] using ht

/-- A multiplier locally constant at the old crossing is frozen exactly once
the new crossing is sufficiently close, for any supported integrable loss. -/
lemma eventually_freeze_local_multiplier {m r : ℝ → ℝ} {loss : ℝ → ℝ → ℝ} {r0 : ℝ}
    (hm : ∀ᶠ t : ℝ in 𝓝 r0, m t = m r0) (hr : Tendsto r (𝓝 0) (𝓝 r0))
    (hInt : ∀ᶠ h : ℝ in 𝓝 0, Integrable (loss h) volume)
    (hSupp : ∀ᶠ h : ℝ in 𝓝 0, ∀ t : ℝ, t ∉ uIcc r0 (r h) → loss h t = 0) :
    ∀ᶠ h : ℝ in 𝓝 0, Integrable (fun t ↦ m t * loss h t) volume ∧
      (∫ t : ℝ, m t * loss h t) = m r0 * ∫ t : ℝ, loss h t := by
  obtain ⟨ε, hε, hBall⟩ := Metric.mem_nhds_iff.mp hm
  filter_upwards [hr (Metric.ball_mem_nhds r0 hε), hInt, hSupp] with h hh hi hs
  have hfun : (fun t : ℝ ↦ m t * loss h t) = (fun t ↦ m r0 * loss h t) := by
    funext t
    by_cases ht : t ∈ uIcc r0 (r h)
    · have hdist : dist t r0 ≤ dist (r h) r0 := by simpa only [dist_comm] using Real.dist_left_le_of_mem_uIcc ht
      rw [hBall (hdist.trans_lt hh)]
    · rw [hs t ht, mul_zero, mul_zero]
  constructor
  · rw [hfun]
    exact hi.const_mul (m r0)
  · rw [hfun, integral_const_mul]

/-- The full locally weighted triangular limit for a varying continuation
function. The old elapsed crossing remains fixed in the multiplier. -/
theorem tendsto_weighted_rootActionLoss {F T : ℝ → ℝ → ℝ} {r m : ℝ → ℝ}
    {p d c A B a b D : ℝ} {L : ℝ≥0}
    (hp : p ∈ Ioo A B) (hd : d ∈ Ioo a b) (hc : 0 < c) (hdPos : 0 < d)
    (hr0 : r p = d) (hR : HasDerivAt r D p)
    (hLip : ∀ q ∈ Ioo A B, LipschitzWith L (F q))
    (hD : ∀ q ∈ Ioo A B, ∀ z ∈ Ioo a b, HasDerivAt (F q) (T q z) z)
    (hT : ContinuousAt (fun v : ℝ × ℝ ↦ T v.1 v.2) (p, d))
    (hLevel : ∀ q ∈ Ioo A B, ∀ s, F q s ≤ F q (r q) ↔ s ≤ r q)
    (hm : ∀ᶠ t : ℝ in 𝓝 (1 - d / c), m t = m (1 - d / c)) :
    Tendsto (fun h : ℝ ↦ (∫ t : ℝ, m t * rootActionLoss (F (p + h)) (F (p + h) (r (p + h))) c d t) / h ^ 2)
      (𝓝[≠] 0) (𝓝 (m (1 - d / c) * T p d * D ^ 2 / (2 * c))) := by
  have hAdd : Tendsto (fun h : ℝ ↦ p + h) (𝓝 0) (𝓝 p) := by
    have hcont : Continuous (fun h : ℝ ↦ p + h) := continuous_const.add continuous_id
    simpa only [add_zero] using hcont.tendsto 0
  have hr : Tendsto (fun h : ℝ ↦ r (p + h)) (𝓝 0) (𝓝 d) := by
    have hComp := hR.continuousAt.tendsto.comp hAdd
    change Tendsto (fun h : ℝ ↦ r (p + h)) (𝓝 0) (𝓝 (r p)) at hComp
    simpa only [hr0] using hComp
  have hClock : Tendsto (fun h : ℝ ↦ 1 - r (p + h) / c) (𝓝 0) (𝓝 (1 - d / c)) :=
    tendsto_const_nhds.sub (hr.div_const c)
  have hInside : ∀ᶠ h : ℝ in 𝓝 0, p + h ∈ Ioo A B := hAdd (Ioo_mem_nhds hp.1 hp.2)
  have hPos : ∀ᶠ h : ℝ in 𝓝 0, 0 < r (p + h) := hr (Ioi_mem_nhds hdPos)
  let loss := fun h t ↦ rootActionLoss (F (p + h)) (F (p + h) (r (p + h))) c d t
  have hInt : ∀ᶠ h : ℝ in 𝓝 0, Integrable (loss h) volume := by
    filter_upwards [hInside, hPos] with h hh hpos
    exact integrable_rootActionLoss (hLip (p + h) hh).continuous hc hdPos hpos (hLevel (p + h) hh)
  have hSupport : ∀ᶠ h : ℝ in 𝓝 0, ∀ t : ℝ,
      t ∉ uIcc (1 - d / c) (1 - r (p + h) / c) → loss h t = 0 := by
    filter_upwards [hInside, hPos] with h hh hpos t ht
    exact rootActionLoss_zero_outside hc hdPos hpos (hLevel (p + h) hh) ht
  have hFreeze := eventually_freeze_local_multiplier hm hClock hInt hSupport
  have hPrim := (tendsto_moving_primitive_quotient hp hd hr0 hR hLip hD hT).const_mul (m (1 - d / c) / c)
  have hCoeff : (m (1 - d / c) / c) * (T p d * D ^ 2 / 2) = m (1 - d / c) * T p d * D ^ 2 / (2 * c) := by ring
  rw [hCoeff] at hPrim
  apply hPrim.congr'
  filter_upwards [hFreeze.filter_mono nhdsWithin_le_nhds, hInside.filter_mono nhdsWithin_le_nhds,
    hPos.filter_mono nhdsWithin_le_nhds] with h hh hI hpos
  rw [hh.2, integral_rootActionLoss hc hdPos hpos (hLevel (p + h) hI)]
  ring

end ProphetSecretary.Analysis
