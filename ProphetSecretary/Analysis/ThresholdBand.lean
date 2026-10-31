import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Time spent near a threshold crossing

A gap growing at rate at least `a > 0` can spend at most `2δ/a` time within `δ`
of zero. Upward jumps are permitted: the hypothesis is a pairwise lower increment
bound, not continuity. A local loss bounded by `δ` on this band has integral at most
`2δ²/a`. Applications must separately prove the increment or derivative hypotheses.
-/

open MeasureTheory Set
open scoped ENNReal

namespace ProphetSecretary.Analysis

/-- The gap's increase between any two ordered points dominates the indicated linear
increase. The definition permits upward jumps. -/
def SlopeLowerBoundOn (g : ℝ → ℝ) (a : ℝ) (S : Set ℝ) : Prop :=
  ∀ t ∈ S, ∀ s ∈ S, t ≤ s → a * (s - t) ≤ g s - g t

def thresholdBand (g : ℝ → ℝ) (δ : ℝ) : Set ℝ :=
  Icc (0 : ℝ) 1 ∩ {t | |g t| ≤ δ}

lemma measurableSet_thresholdBand {g : ℝ → ℝ} (hg : Measurable g) (δ : ℝ) :
    MeasurableSet (thresholdBand g δ) :=
  measurableSet_Icc.inter (measurableSet_le (continuous_abs.measurable.comp hg) measurable_const)

lemma dist_le_of_band {g : ℝ → ℝ} {a δ : ℝ} (ha : 0 < a)
    (hslope : SlopeLowerBoundOn g a (Icc (0 : ℝ) 1)) {t s : ℝ}
    (ht : t ∈ thresholdBand g δ) (hs : s ∈ thresholdBand g δ) :
    dist t s ≤ 2 * δ / a := by
  obtain ⟨ht0, ht1⟩ := ht
  obtain ⟨hs0, hs1⟩ := hs
  change |g t| ≤ δ at ht1
  change |g s| ≤ δ at hs1
  obtain ⟨hgt0, hgt1⟩ := abs_le.mp ht1
  obtain ⟨hgs0, hgs1⟩ := abs_le.mp hs1
  rcases le_total t s with hts | hst
  · have h := hslope t ht0 s hs0 hts
    have hd : s - t ≤ 2 * δ / a := (le_div_iff₀ ha).mpr (by nlinarith)
    simpa only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hts), neg_sub] using hd
  · have h := hslope s hs0 t ht0 hst
    have hd : t - s ≤ 2 * δ / a := (le_div_iff₀ ha).mpr (by nlinarith)
    simpa only [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hst)] using hd

/-- Outer Lebesgue measure already obeys the estimate, so this geometric statement
requires no measurability assumption beyond the pairwise increment condition. -/
theorem volume_thresholdBand_le {g : ℝ → ℝ} {a δ : ℝ} (ha : 0 < a)
    (hslope : SlopeLowerBoundOn g a (Icc (0 : ℝ) 1)) :
    volume (thresholdBand g δ) ≤ ENNReal.ofReal (2 * δ / a) :=
  (Real.volume_le_diam _).trans
    (Metric.ediam_le_of_forall_dist_le fun _ ht _ hs => dist_le_of_band ha hslope ht hs)

theorem volumeReal_thresholdBand_le {g : ℝ → ℝ} {a δ : ℝ} (ha : 0 < a) (hδ : 0 ≤ δ)
    (hslope : SlopeLowerBoundOn g a (Icc (0 : ℝ) 1)) :
    volume.real (thresholdBand g δ) ≤ 2 * δ / a :=
  ENNReal.toReal_le_of_le_ofReal (by positivity) (volume_thresholdBand_le ha hslope)

/-- The positive-rate hypothesis makes exact threshold equalities a null event in time. -/
theorem volume_zero_threshold_eq_zero {g : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hslope : SlopeLowerBoundOn g a (Icc (0 : ℝ) 1)) :
    volume (Icc (0 : ℝ) 1 ∩ {t | g t = 0}) = 0 := by
  have h := volume_thresholdBand_le (δ := 0) ha hslope
  simpa only [thresholdBand, abs_nonpos_iff, mul_zero, zero_div, ENNReal.ofReal_zero, nonpos_iff_eq_zero] using h

/-- A measurable nonnegative local loss supported on the threshold band is quadratic
in the threshold error. The expectation here is integration over elapsed unit time. -/
theorem integral_local_loss_le {g loss : ℝ → ℝ} {a δ : ℝ}
    (ha : 0 < a) (hδ : 0 ≤ δ) (hg : Measurable g)
    (hslope : SlopeLowerBoundOn g a (Icc (0 : ℝ) 1))
    (hloss : AEStronglyMeasurable loss (volume.restrict (Icc (0 : ℝ) 1)))
    (h0 : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), 0 ≤ loss t)
    (hband : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      loss t ≤ (thresholdBand g δ).indicator (fun _ => δ) t) :
    (∫ t in Icc (0 : ℝ) 1, loss t) ≤ 2 * δ ^ 2 / a := by
  have hm := measurableSet_thresholdBand hg δ
  have hi : Integrable loss (volume.restrict (Icc (0 : ℝ) 1)) := by
    apply Integrable.of_bound hloss δ
    filter_upwards [h0, hband] with t ht hb
    rw [Real.norm_eq_abs, abs_of_nonneg ht]
    exact hb.trans (by by_cases h : t ∈ thresholdBand g δ <;> simp [h, hδ])
  have hiBand := (integrable_const δ : Integrable (fun _ : ℝ => δ)
    (volume.restrict (Icc (0 : ℝ) 1))).indicator hm
  have hInt := integral_mono_ae hi hiBand hband
  have hsubset : thresholdBand g δ ∩ Icc (0 : ℝ) 1 = thresholdBand g δ :=
    inter_eq_left.mpr (fun _ ht => ht.1)
  rw [integral_indicator_const δ hm, measureReal_restrict_apply hm, hsubset, smul_eq_mul] at hInt
  calc
    (∫ t in Icc (0 : ℝ) 1, loss t) ≤ volume.real (thresholdBand g δ) * δ := hInt
    _ ≤ (2 * δ / a) * δ := mul_le_mul_of_nonneg_right (volumeReal_thresholdBand_le ha hδ hslope) hδ
    _ = 2 * δ ^ 2 / a := by ring

/-- Version whose gap is defined only on the paper's unit-time domain. -/
def unitThresholdBand (g : Icc (0 : ℝ) 1 → ℝ) (δ : ℝ) : Set ℝ :=
  Subtype.val '' {t | |g t| ≤ δ}

private lemma extend_unit_gap {g : Icc (0 : ℝ) 1 → ℝ} (hg : Measurable g) :
    ∃ G : ℝ → ℝ, Measurable G ∧ ∀ t : Icc (0 : ℝ) 1, G t = g t := by
  obtain ⟨G, hG, he⟩ := (MeasurableEmbedding.subtype_coe measurableSet_Icc).exists_measurable_extend hg
    (fun _ => inferInstance : ℝ → Nonempty ℝ)
  exact ⟨G, hG, fun t => congrFun he t⟩

private lemma unitThresholdBand_eq {g : Icc (0 : ℝ) 1 → ℝ} {G : ℝ → ℝ}
    (hG : ∀ t : Icc (0 : ℝ) 1, G t = g t) (δ : ℝ) :
    unitThresholdBand g δ = thresholdBand G δ := by
  ext t
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u.property, ?_⟩
    change |G u| ≤ δ
    rw [hG u]
    exact hu
  · rintro ⟨ht, hband⟩
    refine ⟨⟨t, ht⟩, ?_, rfl⟩
    change |g ⟨t, ht⟩| ≤ δ
    rw [← hG ⟨t, ht⟩]
    exact hband

theorem volume_unitThresholdBand_le {g : Icc (0 : ℝ) 1 → ℝ} {a δ : ℝ}
    (hg : Measurable g) (ha : 0 < a)
    (hslope : ∀ t s : Icc (0 : ℝ) 1, (t : ℝ) ≤ s → a * ((s : ℝ) - t) ≤ g s - g t) :
    volume (unitThresholdBand g δ) ≤ ENNReal.ofReal (2 * δ / a) := by
  obtain ⟨G, hG, he⟩ := extend_unit_gap hg
  rw [unitThresholdBand_eq he δ]
  apply volume_thresholdBand_le ha
  intro t ht s hs hts
  simpa only [he ⟨s, hs⟩, he ⟨t, ht⟩] using hslope ⟨t, ht⟩ ⟨s, hs⟩ hts

theorem integral_local_loss_unit_le {g : Icc (0 : ℝ) 1 → ℝ} {loss : ℝ → ℝ} {a δ : ℝ}
    (ha : 0 < a) (hδ : 0 ≤ δ) (hg : Measurable g)
    (hslope : ∀ t s : Icc (0 : ℝ) 1, (t : ℝ) ≤ s → a * ((s : ℝ) - t) ≤ g s - g t)
    (hloss : AEStronglyMeasurable loss (volume.restrict (Icc (0 : ℝ) 1)))
    (h0 : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), 0 ≤ loss t)
    (hband : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      loss t ≤ (unitThresholdBand g δ).indicator (fun _ => δ) t) :
    (∫ t in Icc (0 : ℝ) 1, loss t) ≤ 2 * δ ^ 2 / a := by
  obtain ⟨G, hG, he⟩ := extend_unit_gap hg
  rw [unitThresholdBand_eq he δ] at hband
  apply integral_local_loss_le ha hδ hG _ hloss h0 hband
  intro t ht s hs hts
  simpa only [he ⟨s, hs⟩, he ⟨t, ht⟩] using hslope ⟨t, ht⟩ ⟨s, hs⟩ hts

/-- A derivative lower bound on a continuous branch implies the required finite
increment bound; the signs refer to increasing elapsed time. -/
lemma slopeLowerBoundOn_of_deriv {g : ℝ → ℝ} {a l u : ℝ}
    (hcont : ContinuousOn g (Icc l u)) (hdiff : DifferentiableOn ℝ g (Ioo l u))
    (hderiv : ∀ t ∈ Ioo l u, a ≤ deriv g t) :
    SlopeLowerBoundOn g a (Icc l u) := by
  apply (convex_Icc l u).mul_sub_le_image_sub_of_le_deriv hcont
  · simpa only [interior_Icc] using hdiff
  · simpa only [interior_Icc] using hderiv

lemma slopeLowerBoundOn_of_hasDerivAt {g d : ℝ → ℝ} {a l u : ℝ}
    (hcont : ContinuousOn g (Icc l u)) (hdiff : ∀ t ∈ Ioo l u, HasDerivAt g (d t) t)
    (hderiv : ∀ t ∈ Ioo l u, a ≤ d t) :
    SlopeLowerBoundOn g a (Icc l u) := by
  apply slopeLowerBoundOn_of_deriv hcont
  · exact fun t ht => (hdiff t ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [(hdiff t ht).deriv]
    exact hderiv t ht

noncomputable def glueAt (b : ℝ) (f g : ℝ → ℝ) (t : ℝ) : ℝ := if t < b then f t else g t

/-- Increasing-rate branches can be glued across an upward jump. Repeated application
handles any finite sequence of such jumps without assuming continuity across them. -/
lemma slopeLowerBoundOn_glueAt {f g : ℝ → ℝ} {a l b u : ℝ}
    (hlb : l ≤ b) (hbu : b ≤ u)
    (hf : SlopeLowerBoundOn f a (Icc l b)) (hg : SlopeLowerBoundOn g a (Icc b u))
    (hjump : f b ≤ g b) : SlopeLowerBoundOn (glueAt b f g) a (Icc l u) := by
  intro t ht s hs hts
  by_cases htb : t < b
  · by_cases hsb : s < b
    · simpa only [glueAt, if_pos htb, if_pos hsb] using
        hf t ⟨ht.1, htb.le⟩ s ⟨hs.1, hsb.le⟩ hts
    · have hbs : b ≤ s := le_of_not_gt hsb
      have hleft := hf t ⟨ht.1, htb.le⟩ b ⟨hlb, le_rfl⟩ htb.le
      have hright := hg b ⟨le_rfl, hbu⟩ s ⟨hbs, hs.2⟩ hbs
      simp only [glueAt, if_pos htb, if_neg hsb]
      linarith
  · have hbt : b ≤ t := le_of_not_gt htb
    have hsb : ¬s < b := not_lt_of_ge (hbt.trans hts)
    simpa only [glueAt, if_neg htb, if_neg hsb] using
      hg t ⟨hbt, ht.2⟩ s ⟨hbt.trans hts, hs.2⟩ hts

lemma slopeLowerBoundOn_glueAt_of_deriv {f g : ℝ → ℝ} {a l b u : ℝ}
    (hlb : l ≤ b) (hbu : b ≤ u)
    (hfcont : ContinuousOn f (Icc l b)) (hfdiff : DifferentiableOn ℝ f (Ioo l b))
    (hfderiv : ∀ t ∈ Ioo l b, a ≤ deriv f t)
    (hgcont : ContinuousOn g (Icc b u)) (hgdiff : DifferentiableOn ℝ g (Ioo b u))
    (hgderiv : ∀ t ∈ Ioo b u, a ≤ deriv g t) (hjump : f b ≤ g b) :
    SlopeLowerBoundOn (glueAt b f g) a (Icc l u) :=
  slopeLowerBoundOn_glueAt hlb hbu (slopeLowerBoundOn_of_deriv hfcont hfdiff hfderiv)
    (slopeLowerBoundOn_of_deriv hgcont hgdiff hgderiv) hjump

end ProphetSecretary.Analysis

