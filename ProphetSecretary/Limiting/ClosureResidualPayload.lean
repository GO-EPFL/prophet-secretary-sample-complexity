import ProphetSecretary.Limiting.CountablePayloadCoarse
import ProphetSecretary.Limiting.ResidualPayloadTails
import ProphetSecretary.Limiting.LabeledResidualDiagonal
import ProphetSecretary.Limiting.LabeledValueConvergence

/-!
# Closure under an actual randomized residual mark replacement

The old residual upper-band measure converges along one cofinal schedule.
At each fixed retained prefix, positive coarse premeasures identify the new
weak residual limit. Restriction is taken only after its null boundary is
proved from the cloud limit and remaining marginal atoms. This proves the
randomized-map part of operation (b) in paper `lem:closure`.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal
namespace ProphetSecretary.Limiting
variable {T : Type*} [MeasurableSpace T]

lemma LabeledBandConvergence.mapResidualOffers_of_diagonal {sizes : ℕ → ℕ}
    {P : ∀ m, Model.Instance (sizes m)} {B : CountableInstance}
    (h : LabeledBandConvergence sizes P B)
    (hCap : ∀ m j, ∀ᵐ x ∂(P m).law j, x≤(B.cap : ℝ))
    (b : ℝ) (hb : (B.terminal : ℝ)<b) (H : ℝ≥0) (hH : B.cap≤H)
    (κ : Measure T) [IsProbabilityMeasure κ] (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hImage : ∀ᵐ z ∂B.intensity.prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H)
    (hImages : ∀ m j, ∀ᵐ z ∂((P m).law j).prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H)
    (hKernel : ∀ᵐ x ∂(B.intensityAbove b hb : Measure ℝ), ContinuousAt (randomizedMarkKernel κ Φ hΦ) x)
    (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
    (hDiagonal : Tendsto (fun m => labeledBandResidual (P m) (Ns m) b) atTop (𝓝 (B.intensityAbove b hb))) :
    LabeledBandConvergence sizes
      (fun m => mapResidualOffers (P m) (Ns m) H (fun j => (hCap m j).mono (fun _ hx => hx.trans hH)) κ b Φ hΦ (hImages m))
      (B.mapPoissonAbove b hb H hH κ Φ hΦ hImage) := by
  let capH := fun m j => (hCap m j).mono (fun _ hx => hx.trans hH)
  let Ps := fun m => mapResidualOffers (P m) (Ns m) H (capH m) κ b Φ hΦ (hImages m)
  let Q := B.mapPoissonAbove b hb H hH κ Φ hΦ hImage
  have hb0 : 0≤b := B.terminal.property.trans hb.le
  constructor
  · intro i
    have hEq : (fun m => labeledPaddedLaw (Ps m) i)=ᶠ[atTop](fun m => labeledPaddedLaw (P m) i) := by
      filter_upwards [hNs (eventually_gt_atTop i)] with m hm
      change labeledPaddedLaw (mapResidualOffers (P m) (Ns m) H (capH m) κ b Φ hΦ (hImages m)) i=_
      rw [labeledPaddedLaw_mapResidualOffers (P m) (Ns m) H (capH m) κ b hb0 Φ hΦ (hImages m) i,
        if_neg (not_le.mpr hm)]
    exact (h.individual_weak i).congr' hEq.symm
  · intro d hd hQatom hμatom
    have hMin : (B.terminal : ℝ)<min b d := lt_min hb hd
    obtain ⟨cs,_hAnti,hCs,hCsLim,hAtoms⟩ := B.exists_common_continuity_cutoffs
    obtain ⟨j,hj⟩ := (hCsLim.eventually (Iio_mem_nhds hMin)).exists
    let c := cs j
    have hc : (B.terminal : ℝ)<c := (hCs j).1
    have hcb : c≤b := (hj.trans_le (min_le_left _ _)).le
    have hcd : c<d := hj.trans_le (min_le_right _ _)
    obtain ⟨ρ,hFirst,hSecond,_hSupport,hDominates⟩ := h.residual_data hCap c hc (hAtoms j).2 (hAtoms j).1
    let μ := B.intensityAbove b hb
    have hOrderBase : (μ : Measure ℝ)≤(B.intensityAbove c hc : Measure ℝ) :=
      Measure.restrict_mono (Ioi_subset_Ioi hcb) le_rfl
    have hOrder (N : ℕ) : (μ : Measure ℝ)≤(ρ N : Measure ℝ) := hOrderBase.trans (hDominates N)
    have hSucc := residual_successor_of_weak_limits (B.terminal.property.trans hc.le)
      h.individual_weak hFirst (hAtoms j).2
    let ν := residualPayloadLimit ρ μ κ Φ hΦ
    have hνWeak : Tendsto ν atTop (𝓝 (B.payloadCoarseIntensity c hc b hb κ Φ hΦ)) :=
      residualPayloadLimit_tendsto hSecond hOrder hOrderBase κ Φ hΦ
    have hνSucc : ∀ N, ν N=(B.individuals N).toFiniteMeasure.restrict (Ioi c)+ν (N+1) :=
      residualPayloadLimit_successor ρ μ B.individuals c hSucc hOrder κ Φ hΦ
    have hAtomLimit : (B.payloadCoarseIntensity c hc b hb κ Φ hΦ : Measure ℝ) {d}=0 :=
      (B.payloadCoarseIntensity_atom b hb H hH κ Φ hΦ hImage c hc hcb d hcd).trans hμatom
    have hAtom (N : ℕ) : (ν N : Measure ℝ) {d}=0 :=
      residual_atom_zero_of_remaining_atoms_zero hνSucc hνWeak hAtomLimit N (fun i _ => hQatom i)
    have hImageWeak := displayedPayloadIntensity_tendsto_of_weak_kernel hDiagonal κ Φ hΦ hKernel
    refine ⟨fun N => (ν N).restrict (Ioi d),?_,?_⟩
    · intro N
      have hBaseWeak := residualPayloadBase_tendsto P N Ns hNs hcb (hFirst N) hDiagonal (hOrder N)
      have hPreWeak := hBaseWeak.add hImageWeak
      change Tendsto (fun m => residualPayloadBase (P m) N (Ns m) c b+
        displayedPayloadIntensity (labeledBandResidual (P m) (Ns m) b) κ Φ hΦ) atTop (𝓝 (ν N)) at hPreWeak
      have hRestrict := ProphetSecretary.Probability.finite_upperRestriction_tendsto hPreWeak d (hAtom N)
      apply hRestrict.congr'
      filter_upwards [hNs (eventually_ge_atTop N)] with m hm
      exact (mapResidualOffers_residual_above (P m) hm H (capH m) κ b Φ hΦ (hImages m) hcd.le).symm
    · have hRestrict := ProphetSecretary.Probability.finite_upperRestriction_tendsto hνWeak d hAtomLimit
      rwa [B.payloadCoarseIntensity_restrict b hb H hH κ Φ hΦ hImage c hc hcb d hcd.le] at hRestrict
  · intro d hd ε hε
    have hMin : (B.terminal : ℝ)<min b d := lt_min hb hd
    obtain ⟨N,hRare⟩ := h.rare (min b d) hMin ε hε
    refine ⟨N,?_⟩
    filter_upwards [hRare] with m hm i hi
    have hRaw : (labeledPaddedLaw (Ps m) i : Measure ℝ) (Ioi d)≤
        (labeledPaddedLaw (P m) i : Measure ℝ) (Ioi (min b d)) := by
      change (labeledPaddedLaw (mapResidualOffers (P m) (Ns m) H (capH m) κ b Φ hΦ (hImages m)) i : Measure ℝ) (Ioi d)≤_
      rw [labeledPaddedLaw_mapResidualOffers (P m) (Ns m) H (capH m) κ b hb0 Φ hΦ (hImages m) i]
      split_ifs
      · exact cutoffPayloadLaw_tail_le (labeledPaddedLaw (P m) i) κ b d Φ hΦ
      · exact measure_mono (Ioi_subset_Ioi (min_le_right _ _))
    exact (ENNReal.toReal_mono (measure_ne_top _ _) hRaw).trans_lt (hm i hi)
  · intro d hd0 hd
    obtain ⟨K,hK,hBound⟩ := h.above_reserve b hb
    have hRawBound (m : ℕ) : extendedTailCount (P m) b≤ENNReal.ofReal K := by
      have h := ENNReal.ofReal_le_ofReal (hBound m)
      rw [← extendedTailCount_toReal,ENNReal.ofReal_toReal (extendedTailCount_finite (P m) b).ne] at h
      exact h
    exact tendsto_ennreal_top_of_le_add_finite (ENNReal.ofReal_lt_top) (h.below_reserve d hd0 hd)
      (fun m => (mapResidualOffers_old_tail_le (P m) (Ns m) H (capH m) κ b d Φ hΦ (hImages m)).trans
        (add_le_add le_rfl (hRawBound m)))
  · intro d hd
    obtain ⟨K,hK,hBound⟩ := h.above_reserve (min b d) (lt_min hb hd)
    refine ⟨K,hK,?_⟩
    intro m
    exact (mapResidualOffers_tailCount_le (P m) (Ns m) H (capH m) κ b d Φ hΦ (hImages m)).trans (hBound m)

/-- A single actual residual schedule supplies the randomized-map finite
approximations of operation (b), retaining all finite identities. -/
theorem LabeledBandConvergence.mapPoissonAbove {sizes : ℕ → ℕ}
    {P : ∀ m, Model.Instance (sizes m)} {B : CountableInstance}
    (h : LabeledBandConvergence sizes P B)
    (hCap : ∀ m j, ∀ᵐ x ∂(P m).law j, x≤(B.cap : ℝ))
    (b : ℝ) (hb : (B.terminal : ℝ)<b) (hAtom : B.intensity {b}=0)
    (H : ℝ≥0) (hH : B.cap≤H) (κ : Measure T) [IsProbabilityMeasure κ]
    (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
    (hImage : ∀ᵐ z ∂B.intensity.prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H)
    (hImages : ∀ m j, ∀ᵐ z ∂((P m).law j).prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H)
    (hKernel : ∀ᵐ x ∂(B.intensityAbove b hb : Measure ℝ), ContinuousAt (randomizedMarkKernel κ Φ hΦ) x) :
    ∃ Ns : ℕ → ℕ, Monotone Ns ∧ (∀ m, Ns m≤m) ∧ Tendsto Ns atTop atTop ∧
      LabeledBandConvergence sizes
        (fun m => mapResidualOffers (P m) (Ns m) H (fun j => (hCap m j).mono (fun _ hx => hx.trans hH)) κ b Φ hΦ (hImages m))
        (B.mapPoissonAbove b hb H hH κ Φ hΦ hImage) := by
  obtain ⟨Ns,hMono,hLe,hTop,hDiag,_hRare⟩ := h.exists_all_continuity_residual_diagonal
  exact ⟨Ns,hMono,hLe,hTop,h.mapResidualOffers_of_diagonal hCap b hb H hH κ Φ hΦ hImage hImages hKernel Ns hTop (hDiag b hb hAtom)⟩

end ProphetSecretary.Limiting
