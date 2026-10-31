import ProphetSecretary.Analysis.TriangularRegret

/-!
# Exact loss integral between moving threshold roots

For a strict level `f(d)`, the crossing for duration coefficient `z>0` is
`r(z)=1-d/z`. An old threshold action disagrees with the new optimal action
only between the two roots. The full loss integral is an oriented primitive,
so both directions of parameter variation have one formula.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Analysis

noncomputable def branchThresholdLoss (f : ℝ → ℝ) (d z z' t : ℝ) : ℝ :=
  max (f d) (f (z' * (1 - t))) - if f (z * (1 - t)) ≤ f d then f d else f (z' * (1 - t))

lemma moving_level_iff {f : ℝ → ℝ} {d z : ℝ}
    (hlevel : ∀ s, f s ≤ f d ↔ s ≤ d) (hz : 0 < z) (t : ℝ) :
    f (z * (1 - t)) ≤ f d ↔ 1 - d / z ≤ t := by
  rw [hlevel]
  have he : z * (1 - t) ≤ d ↔ 1 - t ≤ d / z := by
    simpa only [mul_comm] using (le_div_iff₀ hz).symm
  rw [he]
  constructor <;> intro h <;> linarith

lemma branchThresholdLoss_eq_indicator_of_root_le {f : ℝ → ℝ} {d z z' : ℝ}
    (hlevel : ∀ s, f s ≤ f d ↔ s ≤ d) (hz : 0 < z) (hz' : 0 < z')
    (hr : 1 - d / z ≤ 1 - d / z') :
    branchThresholdLoss f d z z' = (Ico (1 - d / z) (1 - d / z')).indicator
      (fun t ↦ f (z' * (1 - t)) - f d) := by
  classical
  funext t
  by_cases ho : 1 - d / z ≤ t
  · have hOld := (moving_level_iff hlevel hz t).mpr ho
    by_cases hn : 1 - d / z' ≤ t
    · have hNew := (moving_level_iff hlevel hz' t).mpr hn
      have hnot : t ∉ Ico (1 - d / z) (1 - d / z') := fun ht ↦ not_lt_of_ge hn ht.2
      rw [Set.indicator_of_notMem hnot]
      simp only [branchThresholdLoss, if_pos hOld, max_eq_left hNew, sub_self]
    · have hNew : f d ≤ f (z' * (1 - t)) :=
        (lt_of_not_ge (fun h ↦ hn ((moving_level_iff hlevel hz' t).mp h))).le
      have hmem : t ∈ Ico (1 - d / z) (1 - d / z') := ⟨ho, lt_of_not_ge hn⟩
      rw [Set.indicator_of_mem hmem]
      simp only [branchThresholdLoss, if_pos hOld, max_eq_right hNew]
  · have hOld : ¬f (z * (1 - t)) ≤ f d := fun h ↦ ho ((moving_level_iff hlevel hz t).mp h)
    have hn : ¬1 - d / z' ≤ t := fun h ↦ ho (hr.trans h)
    have hNew : f d ≤ f (z' * (1 - t)) :=
      (lt_of_not_ge (fun h ↦ hn ((moving_level_iff hlevel hz' t).mp h))).le
    have hnot : t ∉ Ico (1 - d / z) (1 - d / z') := fun ht ↦ ho ht.1
    rw [Set.indicator_of_notMem hnot]
    simp only [branchThresholdLoss, if_neg hOld, max_eq_right hNew, sub_self]

lemma branchThresholdLoss_eq_indicator_of_root_ge {f : ℝ → ℝ} {d z z' : ℝ}
    (hlevel : ∀ s, f s ≤ f d ↔ s ≤ d) (hz : 0 < z) (hz' : 0 < z')
    (hr : 1 - d / z' ≤ 1 - d / z) :
    branchThresholdLoss f d z z' = (Ico (1 - d / z') (1 - d / z)).indicator
      (fun t ↦ f d - f (z' * (1 - t))) := by
  classical
  funext t
  by_cases ho : 1 - d / z ≤ t
  · have hOld := (moving_level_iff hlevel hz t).mpr ho
    have hNew := (moving_level_iff hlevel hz' t).mpr (hr.trans ho)
    have hnot : t ∉ Ico (1 - d / z') (1 - d / z) := fun ht ↦ not_lt_of_ge ho ht.2
    rw [Set.indicator_of_notMem hnot]
    simp only [branchThresholdLoss, if_pos hOld, max_eq_left hNew, sub_self]
  · have hOld : ¬f (z * (1 - t)) ≤ f d := fun h ↦ ho ((moving_level_iff hlevel hz t).mp h)
    by_cases hn : 1 - d / z' ≤ t
    · have hNew := (moving_level_iff hlevel hz' t).mpr hn
      have hmem : t ∈ Ico (1 - d / z') (1 - d / z) := ⟨hn, lt_of_not_ge ho⟩
      rw [Set.indicator_of_mem hmem]
      simp only [branchThresholdLoss, if_neg hOld, max_eq_left hNew]
    · have hNew : f d ≤ f (z' * (1 - t)) :=
        (lt_of_not_ge (fun h ↦ hn ((moving_level_iff hlevel hz' t).mp h))).le
      have hnot : t ∉ Ico (1 - d / z') (1 - d / z) := fun ht ↦ hn ht.1
      rw [Set.indicator_of_notMem hnot]
      simp only [branchThresholdLoss, if_neg hOld, max_eq_right hNew, sub_self]

lemma integrable_branchThresholdLoss {f : ℝ → ℝ} (hf : Continuous f) {d z z' : ℝ}
    (hlevel : ∀ s, f s ≤ f d ↔ s ≤ d) (hz : 0 < z) (hz' : 0 < z') :
    Integrable (branchThresholdLoss f d z z') volume := by
  rcases le_total (1 - d / z) (1 - d / z') with hr | hr
  · rw [branchThresholdLoss_eq_indicator_of_root_le hlevel hz hz' hr]
    apply IntegrableOn.integrable_indicator _ measurableSet_Ico
    have hc : Continuous (fun t : ℝ ↦ f (z' * (1 - t)) - f d) :=
      (hf.comp (continuous_const.mul (continuous_const.sub continuous_id))).sub continuous_const
    exact hc.continuousOn.integrableOn_Icc.mono_set Ico_subset_Icc_self
  · rw [branchThresholdLoss_eq_indicator_of_root_ge hlevel hz hz' hr]
    apply IntegrableOn.integrable_indicator _ measurableSet_Ico
    have hc : Continuous (fun t : ℝ ↦ f d - f (z' * (1 - t))) :=
      continuous_const.sub (hf.comp (continuous_const.mul (continuous_const.sub continuous_id)))
    exact hc.continuousOn.integrableOn_Icc.mono_set Ico_subset_Icc_self

lemma integral_branchThresholdLoss_eq_interval {f : ℝ → ℝ} {d z z' : ℝ}
    (hlevel : ∀ s, f s ≤ f d ↔ s ≤ d) (hz : 0 < z) (hz' : 0 < z') :
    (∫ t : ℝ, branchThresholdLoss f d z z' t) =
      ∫ t in (1 - d / z)..(1 - d / z'), f (z' * (1 - t)) - f d := by
  rcases le_total (1 - d / z) (1 - d / z') with hr | hr
  · rw [branchThresholdLoss_eq_indicator_of_root_le hlevel hz hz' hr,
      integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hr]
  · rw [branchThresholdLoss_eq_indicator_of_root_ge hlevel hz hz' hr, integral_indicator measurableSet_Ico]
    have he : (fun t : ℝ ↦ f d - f (z' * (1 - t))) = (fun t ↦ -(f (z' * (1 - t)) - f d)) := by
      funext t
      ring
    rw [he, integral_neg, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hr]
    rw [intervalIntegral.integral_symm (a := 1 - d / z') (b := 1 - d / z)]

/-- Exact triangular-regret primitive, before taking a parameter limit. -/
theorem integral_branchThresholdLoss {f : ℝ → ℝ} {d z z' : ℝ}
    (hlevel : ∀ s, f s ≤ f d ↔ s ≤ d) (hz : 0 < z) (hz' : 0 < z') :
    (∫ t : ℝ, branchThresholdLoss f d z z' t) =
      (1 / z') * ∫ s in d..(d * z' / z), f s - f d := by
  rw [integral_branchThresholdLoss_eq_interval hlevel hz hz']
  have he : (fun t : ℝ ↦ f (z' * (1 - t)) - f d) = (fun t ↦ (fun s ↦ f s - f d) (z' - z' * t)) := by
    funext t
    congr 1
    ring
  rw [he, intervalIntegral.integral_comp_sub_mul (f := fun s ↦ f s - f d) hz'.ne' z']
  have hleft : z' - z' * (1 - d / z') = d := by
    calc
      _ = z' * (d / z') := by ring
      _ = d := by rw [← mul_div_assoc, mul_div_cancel_left₀ _ hz'.ne']
  have hright : z' - z' * (1 - d / z) = d * z' / z := by ring
  rw [hleft, hright, smul_eq_mul, one_div]

lemma branchThresholdLoss_zero_outside {f : ℝ → ℝ} {d z z' t : ℝ}
    (hlevel : ∀ s, f s ≤ f d ↔ s ≤ d) (hz : 0 < z) (hz' : 0 < z')
    (ht : t ∉ uIcc (1 - d / z) (1 - d / z')) : branchThresholdLoss f d z z' t = 0 := by
  rcases le_total (1 - d / z) (1 - d / z') with hr | hr
  · rw [branchThresholdLoss_eq_indicator_of_root_le hlevel hz hz' hr]
    apply Set.indicator_of_notMem
    intro hm
    exact ht (Icc_subset_uIcc (Ico_subset_Icc_self hm))
  · rw [branchThresholdLoss_eq_indicator_of_root_ge hlevel hz hz' hr]
    apply Set.indicator_of_notMem
    intro hm
    exact ht (Icc_subset_uIcc' (Ico_subset_Icc_self hm))

/-- Any multiplier locally constant at the old crossing can be frozen there
once the parameter change is small. Integrability is proved as part of the claim. -/
lemma eventually_weighted_branch_integral {f m : ℝ → ℝ} (hf : Continuous f) {d z : ℝ}
    (hlevel : ∀ s, f s ≤ f d ↔ s ≤ d) (hz : 0 < z)
    (hm : ∀ᶠ t in 𝓝 (1 - d / z), m t = m (1 - d / z)) :
    ∀ᶠ h : ℝ in 𝓝 0,
      Integrable (fun t ↦ m t * branchThresholdLoss f d z (z + h) t) volume ∧
        (∫ t : ℝ, m t * branchThresholdLoss f d z (z + h) t) =
          m (1 - d / z) * ∫ t : ℝ, branchThresholdLoss f d z (z + h) t := by
  let r := 1 - d / z
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hm
  have hDen : Tendsto (fun h : ℝ ↦ z + h) (𝓝 0) (𝓝 z) := by
    have hc : Continuous (fun h : ℝ ↦ z + h) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto 0
  have hDiv : Tendsto (fun h : ℝ ↦ d / (z + h)) (𝓝 0) (𝓝 (d / z)) :=
    tendsto_const_nhds.div hDen hz.ne'
  have hRoot : Tendsto (fun h : ℝ ↦ 1 - d / (z + h)) (𝓝 0) (𝓝 r) :=
    tendsto_const_nhds.sub hDiv
  filter_upwards [hRoot (Metric.ball_mem_nhds r hε), hDen (Ioi_mem_nhds hz)] with h hh hpos
  have hfun : (fun t : ℝ ↦ m t * branchThresholdLoss f d z (z + h) t) =
      (fun t ↦ m r * branchThresholdLoss f d z (z + h) t) := by
    funext t
    by_cases ht : t ∈ uIcc r (1 - d / (z + h))
    · have hdist : dist t r ≤ dist (1 - d / (z + h)) r := by
        calc
          _ = dist r t := dist_comm t r
          _ ≤ dist r (1 - d / (z + h)) := Real.dist_left_le_of_mem_uIcc ht
          _ = _ := dist_comm _ _
      have hmt : m t = m r := hball (lt_of_le_of_lt hdist hh)
      rw [hmt]
    · rw [branchThresholdLoss_zero_outside hlevel hz hpos ht, mul_zero, mul_zero]
  constructor
  · rw [hfun]
    exact (integrable_branchThresholdLoss hf hlevel hz hpos).const_mul (m r)
  · rw [hfun, integral_const_mul]

/-- The locally weighted triangular loss has the exact boundary-Hessian coefficient. -/
theorem tendsto_weighted_branch_regret {f m : ℝ → ℝ} (hf : Continuous f) {d z T : ℝ}
    (hlevel : ∀ s, f s ≤ f d ↔ s ≤ d) (hz : 0 < z) (hD : HasDerivAt f T d)
    (hm : ∀ᶠ t in 𝓝 (1 - d / z), m t = m (1 - d / z)) :
    Tendsto (fun h : ℝ ↦ (∫ t : ℝ, m t * branchThresholdLoss f d z (z + h) t) / h ^ 2)
      (𝓝[≠] 0) (𝓝 (m (1 - d / z) * d ^ 2 * T / (2 * z ^ 3))) := by
  have hbase := tendsto_moving_triangle_quotient hf hD hz
  have hlim : Tendsto (fun h : ℝ ↦ m (1 - d / z) *
      (((∫ t in d..(d + (d / z) * h), f t - f d) / (z + h)) / h ^ 2))
      (𝓝[≠] 0) (𝓝 (m (1 - d / z) * d ^ 2 * T / (2 * z ^ 3))) := by
    convert hbase.const_mul (m (1 - d / z)) using 1
    ring
  have hDen : Tendsto (fun h : ℝ ↦ z + h) (𝓝 0) (𝓝 z) := by
    have hc : Continuous (fun h : ℝ ↦ z + h) := continuous_const.add continuous_id
    simpa only [add_zero] using hc.tendsto 0
  have hPos : ∀ᶠ h : ℝ in 𝓝 0, 0 < z + h := hDen (Ioi_mem_nhds hz)
  apply Filter.Tendsto.congr' _ hlim
  filter_upwards [(eventually_weighted_branch_integral hf hlevel hz hm).filter_mono nhdsWithin_le_nhds,
    hPos.filter_mono nhdsWithin_le_nhds] with h hh hpos
  rw [hh.2, integral_branchThresholdLoss hlevel hz hpos]
  have ha : d * (z + h) / z = d + (d / z) * h := by
    field_simp [hz.ne']
  rw [ha]
  ring

end ProphetSecretary.Analysis
