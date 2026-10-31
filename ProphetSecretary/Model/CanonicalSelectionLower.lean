import ProphetSecretary.Model.LateSelectionWindow
import ProphetSecretary.Model.TwoOfferCompetitiveBound

/-!
# Per-value selection from uniform canonical survival

Choosing a window γx/(1+S) in the proved terminal-window bound yields the
quantitative per-value estimate used in `upmom:selection`. All inequalities
and parameter dependencies are explicit, including at zero expected maximum.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

/-- The selection estimate with its survival and window constants explicit.
The uniform survival premise is discharged separately by `SurvivalBound`. -/
theorem Instance.canonical_selectionAtValue_lower_of_survival (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c γ ρ : ℝ}
    (hw : 0 < w) (hc : 0 ≤ c) (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hγρ : γ ≤ ρ / 4) (hγc : c * γ ≤ w / 2)
    (hsurvive : ∀ t ∈ Icc (0 : ℝ) 1,
      ρ ≤ (P.worldLaw (Measure.dirac ())).real {ω : World n Unit |
        t ≤ (P.valuePolicy hP hw.le hc).rule.stoppingTime () Finset.univ ω.1 ω.2.1})
    (i : Fin n) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    (γ * ρ / 2) * a / (1 + P.totalFirstMoment) ≤
      (P.valuePolicy hP hw.le hc).rule.selectionProbabilityAtValue P (Measure.dirac ()) i a := by
  let S := P.totalFirstMoment
  let u := γ * a / (1 + S)
  have hS : 0 ≤ S := P.totalFirstMoment_nonnegative
  have hd : 0 < 1 + S := by linarith
  have hga : 0 ≤ γ * a := mul_nonneg hγ0 ha.le
  have hu0 : 0 ≤ u := div_nonneg hga hd.le
  have hga1 : γ * a ≤ 1 := by nlinarith only [hγ0, hγ1, ha1, ha]
  have hu1 : u ≤ 1 := (div_le_one hd).mpr (by linarith only [hga1, hS])
  have hwait : c * u ≤ w * a / 2 := by
    change c * (γ * a / (1 + S)) ≤ _
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    have hbase := mul_le_mul_of_nonneg_right hγc ha.le
    have hextra : 0 ≤ (w * a / 2) * S := by positivity
    nlinarith only [hbase, hextra]
  have heq : 2 * u * S / a = 2 * γ * S / (1 + S) := by
    dsimp [u]
    field_simp
  have herr : 2 * u * P.totalFirstMoment / a ≤ ρ / 2 := by
    change 2 * u * S / a ≤ _
    rw [heq]
    have hbound : 2 * γ * S / (1 + S) ≤ 2 * γ := by
      apply (div_le_iff₀ hd).mpr
      nlinarith only [hγ0]
    linarith only [hbound, hγρ]
  have h := P.canonical_selectionAtValue_window_lower hP hw hc ha hu0 hu1 hwait herr hsurvive i
  have heq' : u * (ρ / 2) = (γ * ρ / 2) * a / (1 + P.totalFirstMoment) := by
    dsimp [u, S]
    ring
  rw [heq'] at h
  exact h

/-- `upmom:selection` with the explicit acceptance error bound that implies
uniform survival. Here ρ=(1−C)/2 and κ=ρ min(ρ/4,δ/2)/2. -/
theorem Instance.canonical_selectionAtValue_lower (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {δ h w c : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4)
    (herror : scalarGap P w c / (w * h) + (32 / δ) * (1 + P.positiveCount) ^ 2 * h / w +
      (2 * w / c) * P.positiveCount * h ≤ (1 - optimalCompetitiveRatio) / 2)
    (i : Fin n) {a : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) :
    let ρ := (1 - optimalCompetitiveRatio) / 2
    let γ := min (ρ / 4) (δ / 2)
    ((γ * ρ / 2) * a / (1 + P.totalFirstMoment)) ≤
      (P.valuePolicy (P.integrable_maximum_of_bounded hcap)
        (hδ.le.trans hwδ) (hδ.le.trans hcδ)).rule.selectionProbabilityAtValue P (Measure.dirac ()) i a := by
  let ρ := (1 - optimalCompetitiveRatio) / 2
  let γ := min (ρ / 4) (δ / 2)
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; linarith [optimalCompetitiveRatio_le_threeQuarters]
  have hρ1 : ρ ≤ 1 / 2 := by dsimp [ρ]; linarith [optimalCompetitiveRatio_nonnegative]
  have hγ0 : 0 ≤ γ := le_min (by positivity) (by positivity)
  have hγρ : γ ≤ ρ / 4 := min_le_left _ _
  have hγδ : γ ≤ δ / 2 := min_le_right _ _
  have hγ1 : γ ≤ 1 := by linarith
  have hw : 0 < w := hδ.trans_le hwδ
  have hc : 0 < c := hδ.trans_le hcδ
  have hc1 : c ≤ 1 := by linarith
  have hγc : c * γ ≤ w / 2 := by
    have hcg := mul_le_mul_of_nonneg_right hc1 hγ0
    simp only [one_mul] at hcg
    linarith only [hcg, hγδ, hwδ]
  have hs : ∀ t ∈ Icc (0 : ℝ) 1,
      ρ ≤ (P.worldLaw (Measure.dirac ())).real {ω : World n Unit |
        t ≤ (P.valuePolicy (P.integrable_maximum_of_bounded hcap) hw.le hc.le).rule.stoppingTime
          () Finset.univ ω.1 ω.2.1} := by
    intro t ht
    have hb := P.canonical_survivalProbability_lower hcap hδ hwδ hcδ hsum hh hquarter ht.2
    change 1 - optimalCompetitiveRatio -
      (scalarGap P w c / (w * h) + 32 / δ * (1 + P.positiveCount) ^ 2 * h / w) -
      (2 * w / c) * P.positiveCount * h ≤
      (P.worldLaw (Measure.dirac ())).real {ω : World n Unit |
        t ≤ (P.valuePolicy (P.integrable_maximum_of_bounded hcap) hw.le hc.le).rule.stoppingTime
          () Finset.univ ω.1 ω.2.1} at hb
    dsimp [ρ]
    linarith only [hb, herror]
  exact P.canonical_selectionAtValue_lower_of_survival (P.integrable_maximum_of_bounded hcap)
    hw hc.le hγ0 hγ1 hγρ hγc hs i ha ha1

end ProphetSecretary.Model
