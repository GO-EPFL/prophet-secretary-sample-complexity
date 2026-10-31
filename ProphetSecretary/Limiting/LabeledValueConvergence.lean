import ProphetSecretary.Limiting.LabeledFixedBandTwoLimits
import ProphetSecretary.Limiting.CountableCommonContinuityCutoffs
import ProphetSecretary.Limiting.ZeroReserveBandLimit
import ProphetSecretary.Limiting.PositiveReserveBandLimit
import ProphetSecretary.Limiting.CapReserveLimit
import ProphetSecretary.Limiting.ZeroCapLimit

/-!
# Actual value and benchmark convergence from arbitrary labeled body data

The structural conditions of paper `def:body-convergence` imply convergence
of actual maxima and unrestricted scalar values. The cutoff comparisons
cover zero, interior and cap reserves, and are uniform on bounded weight
rectangles. No optimizer, score or derivative convergence is inferred here.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting

theorem LabeledBandConvergence.values_and_maxima {sizes : ℕ → ℕ}
    {P : ∀ m, Model.Instance (sizes m)} {B : CountableInstance}
    (h : LabeledBandConvergence sizes P B)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap : ℝ)) (W C : ℝ≥0) :
    ∀ ε>(0 : ℝ), ∀ᶠ m in atTop,
      (∀ w c : ℝ, 0≤w → w≤W → 0≤c → c≤C →
        |Model.optimalScalarValue (P m) w c-B.optimalScalarValue w c|<ε) ∧
      |(P m).expectedMaximum-B.expectedMaximum|<ε := by
  by_cases hCapZero : B.cap=0
  · intro ε hε
    filter_upwards [zero_cap_convergence sizes P B hCapZero hCap ε hε] with m hm
    exact ⟨fun w c hw _ hc _ => hm.1 w c hw hc,hm.2⟩
  by_cases hAtCap : B.terminal=B.cap
  · exact cap_reserve_convergence_of_dense_tails sizes P B hAtCap
      (lt_of_le_of_ne zero_le (Ne.symm hCapZero)) W C hCap
      (fun ℓ hℓ hℓH => h.below_reserve ℓ hℓ (by simpa only [hAtCap] using hℓH))
  have haH : (B.terminal : ℝ)<B.cap := by
    exact_mod_cast lt_of_le_of_ne B.terminal_le_cap hAtCap
  let good := fun b : ℝ≥0 => (∀ i, (B.individuals i : Measure ℝ) {(b : ℝ)}=0) ∧ B.intensity {(b : ℝ)}=0
  obtain ⟨bs,_hAnti,hbs,hbsLim,hAtoms⟩ := B.exists_common_continuity_cutoffs
  have hGood : ∀ δ>(0 : ℝ), ∃ b : ℝ≥0, (B.terminal : ℝ)<b ∧ b≤B.cap ∧
      (b : ℝ)<(B.terminal : ℝ)+δ ∧ good b := by
    intro δ hδ
    have hRadius : (B.terminal : ℝ)<min (B.cap : ℝ) ((B.terminal : ℝ)+δ) :=
      lt_min haH (lt_add_of_pos_right _ hδ)
    obtain ⟨k,hk⟩ := (hbsLim.eventually (gt_mem_nhds hRadius)).exists
    let b : ℝ≥0 := ⟨bs k,B.terminal.property.trans (hbs k).1.le⟩
    refine ⟨b,(hbs k).1,?_,?_,(hAtoms k).2,(hAtoms k).1⟩
    · exact_mod_cast (hk.trans_le (min_le_left _ _)).le
    · exact hk.trans_le (min_le_right _ _)
  have hBands (b : ℝ≥0) (hb : (B.terminal : ℝ)<b) (hbH : b≤B.cap) (hg : good b) :=
    h.fixed_band_two_limits hCap b W hb hbH hg.1 hg.2
  by_cases hZero : B.terminal=0
  · have hGoodZero : ∀ δ>(0 : ℝ), ∃ b : ℝ≥0, 0<b ∧ b≤B.cap ∧ (b : ℝ)<δ ∧ good b := by
      intro δ hδ
      obtain ⟨b,hb,hbH,hSmall,hGoodB⟩ := hGood δ hδ
      refine ⟨b,?_,hbH,?_,hGoodB⟩
      · exact_mod_cast (by simpa only [hZero,NNReal.coe_zero] using hb : (0 : ℝ)<b)
      · simpa only [hZero,NNReal.coe_zero,zero_add] using hSmall
    have hResult := zero_reserve_convergence_of_band_limits sizes P B hZero W hCap good hGoodZero hBands
    intro ε hε
    filter_upwards [hResult ε hε] with m hm
    exact ⟨fun w c hw hwW hc _ => hm.1 w c hw hwW hc,hm.2⟩
  · have hA : 0<B.terminal := lt_of_le_of_ne zero_le (Ne.symm hZero)
    let L : ℝ≥0 → ℝ≥0 := fun b => if hb : (B.terminal : ℝ)<b then
      ⟨Classical.choose (h.above_reserve b hb),(Classical.choose_spec (h.above_reserve b hb)).1⟩ else 0
    have hAbove (b : ℝ≥0) (hb : (B.terminal : ℝ)<b) (_hbH : b≤B.cap) (_hg : good b) (m : ℕ) :
        (P m).tailCount b≤(L b : ℝ) := by
      dsimp only [L]
      rw [dif_pos hb]
      exact (Classical.choose_spec (h.above_reserve b hb)).2 m
    exact positive_reserve_convergence_of_band_limits sizes P B hA W C hCap good hGood L hAbove h.below_reserve hBands

theorem LabeledBandConvergence.expectedMaximum_tendsto {sizes : ℕ → ℕ}
    {P : ∀ m, Model.Instance (sizes m)} {B : CountableInstance}
    (h : LabeledBandConvergence sizes P B)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap : ℝ)) :
    Tendsto (fun m => (P m).expectedMaximum) atTop (𝓝 B.expectedMaximum) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [h.values_and_maxima hCap 0 0 ε hε] with m hm
  simpa only [Real.dist_eq] using hm.2

theorem LabeledBandConvergence.optimalScalarValue_tendsto {sizes : ℕ → ℕ}
    {P : ∀ m, Model.Instance (sizes m)} {B : CountableInstance}
    (h : LabeledBandConvergence sizes P B)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap : ℝ))
    {w c : ℝ} (hw : 0≤w) (hc : 0≤c) :
    Tendsto (fun m => Model.optimalScalarValue (P m) w c) atTop (𝓝 (B.optimalScalarValue w c)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [h.values_and_maxima hCap ⟨w,hw⟩ ⟨c,hc⟩ ε hε] with m hm
  simpa only [Real.dist_eq] using hm.1 w c hw le_rfl hc le_rfl

end ProphetSecretary.Limiting
