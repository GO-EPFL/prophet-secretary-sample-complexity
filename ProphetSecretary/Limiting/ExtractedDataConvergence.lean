import ProphetSecretary.Limiting.ExtractedBandApproximation
import ProphetSecretary.Limiting.ReserveContinuityCutoffs
import ProphetSecretary.Limiting.WeightedTailCount
import ProphetSecretary.Limiting.ZeroReserveBandLimit
import ProphetSecretary.Limiting.PositiveReserveBandLimit
import ProphetSecretary.Limiting.CapReserveLimit
import ProphetSecretary.Limiting.ZeroCapLimit

/-!
# Actual scalar and maximum convergence for extracted cap-bounded data

Common continuity cutoffs are constructed from the finite weighted measure.
The zero, interior and cap reserve cases use the separately proved terminal
comparisons. All conclusions concern the actual full randomized policy values.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal Classical BigOperators

namespace ProphetSecretary.Limiting

section Extracted

variable (H : ℝ≥0) (a : ℝ) (ha : a ∈ Icc (0 : ℝ) H)
    (wgt : ℝ →ᵇ ℝ) (hwgt0 : ∀ x, 0 ≤ wgt x) (hwgtZero : wgt 0 = 0)
    (hwgt : Monotone wgt) (hpos : ∀ b, a < b → 0 < wgt b)
    (Q : ℕ → ProbabilityMeasure ℝ) (ρ : ℕ → FiniteMeasure ℝ)
    (hρ : ∀ N, ρ N = continuousWeightedLaw (Q N) wgt+ρ (N+1))
    (hQ : ∀ i, (Q i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0)
    (hρcap : ∀ N, (ρ N : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) (hρmass : (ρ 0).mass ≤ 1)
    (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ (H : ℝ))
    (hWeight : ∀ m, (∑ i, ∫ x, wgt x ∂(P m).law i) ≤ 1)
    (hQweak : ∀ i, Tendsto (fun m => weightOrderedPaddedLaw (P m) wgt i) atTop (𝓝 (Q i)))
    (hρweak : ∀ N, Tendsto (fun m => weightOrderedResidual (P m) wgt N) atTop (𝓝 (ρ N)))
    (hBelow : ∀ ℓ, 0 ≤ ℓ → ℓ < a → Tendsto (fun m => extendedTailCount (P m) ℓ) atTop (𝓝 ⊤))

local notation "B" => extractedCountableInstance H a ha wgt hwgt0 hwgt hpos Q ρ hρ hQ (hρcap 0)

include hwgtZero hρmass hcap hWeight hQweak hρweak hBelow

theorem extracted_data_convergence (W C : ℝ≥0) :
    ∀ ε > (0 : ℝ), ∀ᶠ m in atTop,
      (∀ w c : ℝ, 0 ≤ w → w ≤ (W : ℝ) → 0 ≤ c → c ≤ (C : ℝ) →
        |Model.optimalScalarValue (P m) w c-(B).optimalScalarValue w c| < ε) ∧
      |(P m).expectedMaximum-(B).expectedMaximum| < ε := by
  by_cases hH0 : H = 0
  · have h := zero_cap_convergence sizes P B hH0 hcap
    intro ε hε
    filter_upwards [h ε hε] with m hm
    exact ⟨fun w c hw _ hc _ => hm.1 w c hw hc,hm.2⟩
  by_cases hAtCap : a = (H : ℝ)
  · have hReserve : (B).terminal = (B).cap := by apply Subtype.ext; exact hAtCap
    have hH : 0 < (B).cap := lt_of_le_of_ne zero_le (Ne.symm hH0)
    have hDense : ∀ ℓ, 0 ≤ ℓ → ℓ < ((B).cap : ℝ) →
        Tendsto (fun m => extendedTailCount (P m) ℓ) atTop (𝓝 ⊤) := by
      intro ℓ hℓ0 hℓH
      exact hBelow ℓ hℓ0 (hℓH.trans_eq hAtCap.symm)
    exact cap_reserve_convergence_of_dense_tails sizes P B hReserve hH W C hcap hDense
  have haH : a < (H : ℝ) := lt_of_le_of_ne ha.2 hAtCap
  let good : ℝ≥0 → Prop := fun b => (∀ i, (Q i : Measure ℝ) {(b : ℝ)} = 0) ∧ (B).intensity {(b : ℝ)} = 0
  obtain ⟨bs,_hAnti,hbs,hbsLim,hAtoms⟩ := exists_reserve_common_continuity_cutoffs a wgt hpos Q ρ hρ
  have hGood : ∀ δ > (0 : ℝ), ∃ b : ℝ≥0, ((B).terminal : ℝ) < b ∧ b ≤ (B).cap ∧
      (b : ℝ) < ((B).terminal : ℝ)+δ ∧ good b := by
    intro δ hδ
    have hRadius : a < min (H : ℝ) (a+δ) := lt_min haH (lt_add_of_pos_right a hδ)
    obtain ⟨k,hk⟩ := (hbsLim.eventually (gt_mem_nhds hRadius)).exists
    let b : ℝ≥0 := ⟨bs k,ha.1.trans (hbs k).1.le⟩
    refine ⟨b,(hbs k).1,?_,?_,?_⟩
    · exact_mod_cast (hk.trans_le (min_le_left _ _)).le
    · exact hk.trans_le (min_le_right _ _)
    · exact (hAtoms k).2
  have hBands (b : ℝ≥0) (hb : ((B).terminal : ℝ) < b) (hbH : b ≤ (B).cap) (hg : good b) :=
    extracted_fixed_band_approximation H a ha wgt hwgt0 hwgtZero hwgt hpos Q ρ hρ hQ hρcap hρmass
      sizes P hcap hWeight hQweak hρweak b W hb hbH hg.1 hg.2
  by_cases hZero : a = 0
  · have hBZero : (B).terminal = 0 := by apply Subtype.ext; exact hZero
    have hGoodZero : ∀ δ > (0 : ℝ), ∃ b : ℝ≥0, 0 < b ∧ b ≤ (B).cap ∧ (b : ℝ) < δ ∧ good b := by
      intro δ hδ
      obtain ⟨b,hb,hbH,hSmall,hGoodB⟩ := hGood δ hδ
      have hb0 : 0 < b := by
        change a < (b : ℝ) at hb
        rw [hZero] at hb
        exact_mod_cast hb
      have hSmall' : (b : ℝ) < δ := by
        change (b : ℝ) < a+δ at hSmall
        simpa only [hZero,zero_add] using hSmall
      exact ⟨b,hb0,hbH,hSmall',hGoodB⟩
    have h := zero_reserve_convergence_of_band_limits sizes P B hBZero W hcap good hGoodZero hBands
    intro ε hε
    filter_upwards [h ε hε] with m hm
    exact ⟨fun w c hw hwW hc _ => hm.1 w c hw hwW hc,hm.2⟩
  have hA : 0 < (B).terminal := by
    have ha0 : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm hZero)
    exact_mod_cast ha0
  let L : ℝ≥0 → ℝ≥0 := fun b => ⟨1/wgt b,one_div_nonneg.mpr (hwgt0 b)⟩
  have hAbove (b : ℝ≥0) (hb : ((B).terminal : ℝ) < b) (_hbH : b ≤ (B).cap) (_hg : good b)
      (m : ℕ) : (P m).tailCount b ≤ (L b : ℝ) :=
    tailCount_le_inverse_weight (P m) wgt hwgt0 hwgt (hWeight m) (hpos b hb)
  exact positive_reserve_convergence_of_band_limits sizes P B hA W C hcap good hGood L hAbove hBelow hBands

end Extracted

end ProphetSecretary.Limiting
