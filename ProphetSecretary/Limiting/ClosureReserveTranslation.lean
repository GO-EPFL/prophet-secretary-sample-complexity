import ProphetSecretary.Limiting.LabeledExcessLaws

/-!
# Closure under translation of a positive reserve

This proves operation (c) of paper `lem:closure` for the actual original
finite sequence. Each finite variable is pushed through the same continuous
excess map, and the limiting reserve is lowered by the same amount. The
structural convergence proof uses exact positive-tail identities.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal
namespace ProphetSecretary.Limiting
open Model

private lemma reserveTranslation_old_level (B : CountableInstance) (a : ℝ≥0)
    (ha : a<B.terminal) {b : ℝ} (hb : ((B.reserveTranslation a ha).terminal : ℝ)<b) :
    (B.terminal : ℝ)<(a : ℝ)+b := by
  change ((B.terminal-a : ℝ≥0) : ℝ)<b at hb
  rw [NNReal.coe_sub ha.le] at hb
  linarith only [hb]

theorem LabeledBandConvergence.reserveTranslation {sizes : ℕ → ℕ}
    {P : ∀ m, Model.Instance (sizes m)} {B : CountableInstance}
    (h : LabeledBandConvergence sizes P B) (a : ℝ≥0) (ha : a<B.terminal) :
    LabeledBandConvergence sizes (fun m => (P m).excessOffers a) (B.reserveTranslation a ha) := by
  constructor
  · intro i
    have hWeak := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ (h.individual_weak i)
      (continuous_excessValueMap a)
    change Tendsto (fun m => labeledPaddedLaw ((P m).excessOffers a) i) atTop
      (𝓝 ((B.individuals i).map (measurable_excessValueMap a).aemeasurable))
    simp_rw [labeledPaddedLaw_excessOffers]
    exact hWeak
  · intro b hb hQatom hμatom
    have hbPos : 0<b := (B.terminal-a).property.trans_lt hb
    have hOld := reserveTranslation_old_level B a ha hb
    have hAtomMap (μ : Measure ℝ) : (μ.map (excessValueMap a)) {b}=μ {(a : ℝ)+b} := by
      rw [Measure.map_apply (measurable_excessValueMap a) (measurableSet_singleton b),
        excessValueMap_preimage_singleton (a := (a : ℝ)) (b := b) a.property hbPos]
    have hQOld (i : ℕ) : (B.individuals i : Measure ℝ) {(a : ℝ)+b}=0 :=
      (hAtomMap (B.individuals i : Measure ℝ)).symm.trans (hQatom i)
    have hμOld : B.intensity {(a : ℝ)+b}=0 := (hAtomMap B.intensity).symm.trans hμatom
    obtain ⟨ρ,hFirst,hSecond⟩ := h.residual_bands ((a : ℝ)+b) hOld hQOld hμOld
    refine ⟨fun N => (ρ N).map (excessValueMap a),?_,?_⟩
    · intro N
      have hWeak := FiniteMeasure.tendsto_map_of_tendsto_of_continuous _ _ (hFirst N) (continuous_excessValueMap a)
      simpa only [labeledBandResidual_excessOffers _ _ _ _ hbPos.le] using hWeak
    · rw [B.reserveTranslation_intensityAbove a ha b hb]
      exact FiniteMeasure.tendsto_map_of_tendsto_of_continuous _ _ hSecond (continuous_excessValueMap a)
  · intro b hb ε hε
    have hb0 : 0≤b := (B.terminal-a).property.trans hb.le
    have hOld := reserveTranslation_old_level B a ha hb
    obtain ⟨N,hRare⟩ := h.rare ((a : ℝ)+b) hOld ε hε
    refine ⟨N,?_⟩
    filter_upwards [hRare] with m hm i hi
    change ((labeledPaddedLaw ((P m).excessOffers a) i : Measure ℝ) (Ioi b)).toReal<ε
    rw [labeledPaddedLaw_excess_positiveTail (P m) a i b hb0]
    exact hm i hi
  · intro b hb0 hb
    have hOld : (a : ℝ)+b<(B.terminal : ℝ) := by
      change b<((B.terminal-a : ℝ≥0) : ℝ) at hb
      rw [NNReal.coe_sub ha.le] at hb
      linarith only [hb]
    have hWeak := h.below_reserve ((a : ℝ)+b) (add_nonneg a.property hb0) hOld
    simpa only [extendedTailCount_excessOffers _ a b hb0] using hWeak
  · intro b hb
    have hb0 : 0≤b := (B.terminal-a).property.trans hb.le
    obtain ⟨K,hK,hBound⟩ := h.above_reserve ((a : ℝ)+b) (reserveTranslation_old_level B a ha hb)
    refine ⟨K,hK,?_⟩
    intro m
    rw [tailCount_excessOffers (P m) a b hb0]
    exact hBound m

/-- The translated original finite sequence has convergent actual maxima and
all scalar values, uniformly on bounded nonnegative weight rectangles. -/
theorem LabeledBandConvergence.reserveTranslation_values_and_maxima {sizes : ℕ → ℕ}
    {P : ∀ m, Model.Instance (sizes m)} {B : CountableInstance}
    (h : LabeledBandConvergence sizes P B)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap : ℝ))
    (a : ℝ≥0) (ha : a<B.terminal) (W C : ℝ≥0) :
    ∀ ε>(0 : ℝ), ∀ᶠ m in atTop,
      (∀ w c : ℝ, 0≤w → w≤W → 0≤c → c≤C →
        |Model.optimalScalarValue ((P m).excessOffers a) w c-(B.reserveTranslation a ha).optimalScalarValue w c|<ε) ∧
      |((P m).excessOffers a).expectedMaximum-(B.reserveTranslation a ha).expectedMaximum|<ε := by
  apply (h.reserveTranslation a ha).values_and_maxima _ W C
  intro m i
  change ∀ᵐ x ∂((P m).law i).map (excessValueMap a), x≤(B.cap : ℝ)
  apply (ae_map_iff (measurable_excessValueMap a).aemeasurable measurableSet_Iic).mpr
  exact (hCap m i).mono (fun x hx => (excessValueMap_le_self a.property x).trans hx)

end ProphetSecretary.Limiting
