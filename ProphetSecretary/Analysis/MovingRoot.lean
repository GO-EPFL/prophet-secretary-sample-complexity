import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Differentiating a continuous family of strict scalar roots

A one-parameter envelope derivative at the fixed old root and continuity of the
horizon derivative suffice. The proof uses mean-value secants, so it does not
assume differentiability of the chosen root or a policy reoptimization rule.
-/

open Set Filter
open scoped Topology

namespace ProphetSecretary.Analysis

lemma exists_derivative_eq_secant {f T : ℝ → ℝ} {a b x y : ℝ}
    (hD : ∀ z ∈ Ioo a b, HasDerivAt f (T z) z) (hx : x ∈ Ioo a b) (hy : y ∈ Ioo a b) :
    ∃ z ∈ uIcc x y, T z = if y = x then T x else slope f x y := by
  by_cases he : y = x
  · exact ⟨x, left_mem_uIcc, by rw [if_pos he]⟩
  · rw [if_neg he]
    rcases lt_or_gt_of_ne he with hyx | hxy
    · have hsub : Icc y x ⊆ Ioo a b := fun z hz ↦ ⟨hy.1.trans_le hz.1, hz.2.trans_lt hx.2⟩
      have hcont : ContinuousOn f (Icc y x) := fun z hz ↦ (hD z (hsub hz)).continuousAt.continuousWithinAt
      have hdiff : DifferentiableOn ℝ f (Ioo y x) := fun z hz ↦
        (hD z (hsub ⟨hz.1.le, hz.2.le⟩)).differentiableAt.differentiableWithinAt
      obtain ⟨z, hz, heq⟩ := exists_deriv_eq_slope' f hyx hcont hdiff
      rw [(hD z (hsub ⟨hz.1.le, hz.2.le⟩)).deriv, slope_comm f y x] at heq
      exact ⟨z, Icc_subset_uIcc' ⟨hz.1.le, hz.2.le⟩, heq⟩
    · have hsub : Icc x y ⊆ Ioo a b := fun z hz ↦ ⟨hx.1.trans_le hz.1, hz.2.trans_lt hy.2⟩
      have hcont : ContinuousOn f (Icc x y) := fun z hz ↦ (hD z (hsub hz)).continuousAt.continuousWithinAt
      have hdiff : DifferentiableOn ℝ f (Ioo x y) := fun z hz ↦
        (hD z (hsub ⟨hz.1.le, hz.2.le⟩)).differentiableAt.differentiableWithinAt
      obtain ⟨z, hz, heq⟩ := exists_deriv_eq_slope' f hxy hcont hdiff
      rw [(hD z (hsub ⟨hz.1.le, hz.2.le⟩)).deriv] at heq
      exact ⟨z, Icc_subset_uIcc ⟨hz.1.le, hz.2.le⟩, heq⟩

noncomputable def movingSecant (F T : ℝ → ℝ → ℝ) (r : ℝ → ℝ) (d p : ℝ) : ℝ :=
  if r p = d then T p d else slope (F p) d (r p)

lemma movingSecant_mul_sub (F T : ℝ → ℝ → ℝ) (r : ℝ → ℝ) (d p : ℝ) :
    movingSecant F T r d p * (r p - d) = F p (r p) - F p d := by
  unfold movingSecant
  split_ifs with he
  · simp only [he, sub_self, mul_zero]
  · rw [slope_def_field]
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr he)

lemma tendsto_movingSecant {F T : ℝ → ℝ → ℝ} {r : ℝ → ℝ} {p d A B a b : ℝ}
    (hp : p ∈ Ioo A B) (hd : d ∈ Ioo a b)
    (hr : Tendsto r (𝓝 p) (𝓝 d))
    (hD : ∀ q ∈ Ioo A B, ∀ z ∈ Ioo a b, HasDerivAt (F q) (T q z) z)
    (hT : ContinuousAt (fun v : ℝ × ℝ ↦ T v.1 v.2) (p, d)) :
    Tendsto (movingSecant F T r d) (𝓝 p) (𝓝 (T p d)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδbound⟩ := Metric.continuousAt_iff.mp hT ε hε
  have hq : ∀ᶠ q : ℝ in 𝓝 p, dist q p < δ := Metric.ball_mem_nhds p hδ
  have hroot : ∀ᶠ q : ℝ in 𝓝 p, dist (r q) d < δ := hr (Metric.ball_mem_nhds d hδ)
  have hrootJ : ∀ᶠ q : ℝ in 𝓝 p, r q ∈ Ioo a b := hr (Ioo_mem_nhds hd.1 hd.2)
  filter_upwards [Ioo_mem_nhds hp.1 hp.2, hq, hroot, hrootJ] with q hqI hqp hrd hrJ
  obtain ⟨z, hz, hzEq⟩ := exists_derivative_eq_secant (hD q hqI) hd hrJ
  have hdist : dist z d ≤ dist (r q) d := by
    simpa only [dist_comm] using Real.dist_left_le_of_mem_uIcc hz
  have hpair : dist (q, z) (p, d) < δ := by
    rw [Prod.dist_eq]
    exact max_lt hqp (hdist.trans_lt hrd)
  have h := hδbound hpair
  change dist (T q z) (T p d) < ε at h
  simpa only [hzEq, movingSecant] using h

/-- Root differentiation with a fixed-root parameter derivative. The positive
horizon derivative is the only nondegeneracy condition. -/
theorem hasDerivAt_movingRoot {F T : ℝ → ℝ → ℝ} {r : ℝ → ℝ} {p d A B a b G : ℝ}
    (hp : p ∈ Ioo A B) (hd : d ∈ Ioo a b) (hr0 : r p = d)
    (hr : Tendsto r (𝓝 p) (𝓝 d))
    (hRoot : ∀ᶠ q : ℝ in 𝓝 p, F q (r q) = F p d)
    (hD : ∀ q ∈ Ioo A B, ∀ z ∈ Ioo a b, HasDerivAt (F q) (T q z) z)
    (hT : ContinuousAt (fun v : ℝ × ℝ ↦ T v.1 v.2) (p, d))
    (hPos : 0 < T p d) (hParam : HasDerivAt (fun q ↦ F q d) G p) :
    HasDerivAt r (-G / T p d) p := by
  have hQ := tendsto_movingSecant hp hd hr hD hT
  have hQpos : ∀ᶠ q : ℝ in 𝓝 p, 0 < movingSecant F T r d q := hQ (Ioi_mem_nhds hPos)
  have hRatio := hParam.tendsto_slope.neg.div (hQ.mono_left nhdsWithin_le_nhds) hPos.ne'
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply hRatio.congr'
  filter_upwards [hRoot.filter_mono nhdsWithin_le_nhds, hQpos.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with q hroot hq hne
  have hne' : q ≠ p := by simpa only [mem_compl_iff, mem_singleton_iff] using hne
  have hmul := movingSecant_mul_sub F T r d q
  rw [hroot] at hmul
  change (-slope (fun t ↦ F t d) p q) / movingSecant F T r d q = slope r p q
  rw [slope_def_field, slope_def_field, hr0]
  field_simp [hq.ne', sub_ne_zero.mpr hne']
  nlinarith

/-- A time secant with both endpoints moving. -/
noncomputable def betweenSecant (F T : ℝ → ℝ → ℝ) (r s : ℝ → ℝ) (p : ℝ) : ℝ :=
  if s p = r p then T p (r p) else slope (F p) (r p) (s p)

lemma betweenSecant_mul_sub (F T : ℝ → ℝ → ℝ) (r s : ℝ → ℝ) (p : ℝ) :
    betweenSecant F T r s p * (s p - r p) = F p (s p) - F p (r p) := by
  unfold betweenSecant
  split_ifs with he
  · simp only [he, sub_self, mul_zero]
  · rw [slope_def_field]
    exact div_mul_cancel₀ _ (sub_ne_zero.mpr he)

lemma tendsto_betweenSecant {F T : ℝ → ℝ → ℝ} {r s : ℝ → ℝ} {p d A B a b : ℝ}
    (hp : p ∈ Ioo A B) (hd : d ∈ Ioo a b)
    (hr : Tendsto r (𝓝 p) (𝓝 d)) (hs : Tendsto s (𝓝 p) (𝓝 d))
    (hD : ∀ q ∈ Ioo A B, ∀ z ∈ Ioo a b, HasDerivAt (F q) (T q z) z)
    (hT : ContinuousAt (fun v : ℝ × ℝ ↦ T v.1 v.2) (p, d)) :
    Tendsto (betweenSecant F T r s) (𝓝 p) (𝓝 (T p d)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδbound⟩ := Metric.continuousAt_iff.mp hT ε hε
  have hq : ∀ᶠ q : ℝ in 𝓝 p, dist q p < δ := Metric.ball_mem_nhds p hδ
  have hroot : ∀ᶠ q : ℝ in 𝓝 p, dist (r q) d < δ / 4 := hr (Metric.ball_mem_nhds d (by positivity))
  have hsroot : ∀ᶠ q : ℝ in 𝓝 p, dist (s q) d < δ / 4 := hs (Metric.ball_mem_nhds d (by positivity))
  filter_upwards [Ioo_mem_nhds hp.1 hp.2, hq, hroot, hsroot,
    hr (Ioo_mem_nhds hd.1 hd.2), hs (Ioo_mem_nhds hd.1 hd.2)] with q hqI hqp hrd hsd hrJ hsJ
  obtain ⟨z, hz, hzEq⟩ := exists_derivative_eq_secant (hD q hqI) hrJ hsJ
  have hzDist : dist z (r q) ≤ dist (s q) (r q) := by
    simpa only [dist_comm] using Real.dist_left_le_of_mem_uIcc hz
  have hdist : dist z d < δ := by
    have h1 := dist_triangle z (r q) d
    have h2 := dist_triangle (s q) d (r q)
    rw [dist_comm d (r q)] at h2
    linarith
  have hpair : dist (q, z) (p, d) < δ := by
    rw [Prod.dist_eq]
    exact max_lt hqp hdist
  have h := hδbound hpair
  change dist (T q z) (T p d) < ε at h
  simpa only [hzEq, betweenSecant] using h

end ProphetSecretary.Analysis
