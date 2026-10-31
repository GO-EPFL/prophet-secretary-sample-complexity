import ProphetSecretary.Limiting.ClosureCompensatedIntensityDiagonal
import ProphetSecretary.Limiting.ClosureCompensatedIntensityDecomposition
import ProphetSecretary.Limiting.ResidualPayloadWeak
import ProphetSecretary.Limiting.LabeledResidualDiagonal
import ProphetSecretary.Limiting.LabeledResidualConsistency
import ProphetSecretary.Limiting.CountableBandCutoff

/-!
# The two ordered residual limits under compensated band scaling

The original sequence limit at a fixed prefix is a positive unchanged
segment plus the scaled Poisson diagonal. Only after taking that limit does
the retained prefix tend to infinity. Restriction at a higher level follows
from its actual null atom, not from a null endpoint at the common cap.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting

lemma LabeledBandConvergence.compensatedResidualOffers_residual_limits {sizes : ℕ → ℕ}
    {P : ∀ m, Model.Instance (sizes m)} {B : CountableInstance}
    (h : LabeledBandConvergence sizes P B)
    (hCap : ∀ m j, ∀ᵐ x ∂(P m).law j, x≤(B.cap : ℝ))
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal : ℝ)<b)
    (hCont : ∀ᵐ x ∂B.intensity,
      ContinuousWithinAt (S.indicator (fun _ : ℝ => (1 : ℝ))) (Icc (0 : ℝ) B.cap) x)
    (θ : ℝ) (hθ : |θ|≤1/4) (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
    (hDiagonal : ∀ (d : ℝ) (hd : (B.terminal : ℝ)<d), B.intensity {d}=0 →
      Tendsto (fun m => labeledBandResidual (P m) (Ns m) d) atTop (𝓝 (B.intensityAbove d hd)))
    (hRarity : ∀ ε>(0 : ℝ), ∀ᶠ m in atTop, ∀ j : Fin (sizes m), Ns m≤j.val → ((P m).law j).real S<ε) :
    ∀ (d : ℝ) (hd : (B.terminal : ℝ)<d),
      (∀ i, (B.individuals i : Measure ℝ) {d}=0) →
      (B.scaleBand S ⟨1+θ,by have := (abs_le.mp hθ).1; linarith⟩).intensity {d}=0 →
      ∃ νs : ℕ → FiniteMeasure ℝ,
        (∀ N, Tendsto (fun m => labeledBandResidual
          (compensatedResidualOffers (P m) (Ns m) S hS θ hθ) N d) atTop (𝓝 (νs N))) ∧
        Tendsto νs atTop (𝓝 ((B.scaleBand S ⟨1+θ,by have := (abs_le.mp hθ).1; linarith⟩).intensityAbove d hd)) := by
  let r : ℝ≥0 := ⟨1+θ,by have := (abs_le.mp hθ).1; linarith⟩
  let Q := B.scaleBand S r
  intro d hd hQatom hμatom
  have hMin : (B.terminal : ℝ)<min b d := lt_min hb hd
  obtain ⟨cs,_hAnti,hCs,hCsLim,hAtoms⟩ := B.exists_common_continuity_cutoffs
  obtain ⟨j,hj⟩ := (hCsLim.eventually (Iio_mem_nhds hMin)).exists
  let c := cs j
  have hc : (B.terminal : ℝ)<c := (hCs j).1
  have hc0 : 0≤c := B.terminal.property.trans hc.le
  have hcd : c<d := hj.trans_le (min_le_right _ _)
  obtain ⟨ρ,hFirst,hSecond,_hSupport,hDominates⟩ := h.residual_data hCap c hc (hAtoms j).2 (hAtoms j).1
  let μ := B.intensityAbove c hc
  let μ' := Q.intensityAbove c hc
  have hμ' : μ'=bandScaledIntensity μ S r := B.scaleBand_intensityAbove hS r c hc
  have hCapμ : ∀ᵐ x ∂(μ : Measure ℝ), x∈Icc (0 : ℝ) B.cap :=
    (ae_restrict_of_ae B.intensity_supported).mono (fun _ hx => ⟨B.terminal.property.trans hx.1.le,hx.2⟩)
  obtain ⟨K,_hK,hTail⟩ := h.above_reserve c hc
  have hDiagNew : Tendsto (fun m => labeledBandResidual
      (compensatedResidualOffers (P m) (Ns m) S hS θ hθ) (Ns m) c) atTop (𝓝 μ') := by
    rw [hμ']
    exact compensatedResidualOffers_diagonal_tendsto P Ns B.cap hCap hS θ hθ hRarity hc0 hTail
      (hDiagonal c hc (hAtoms j).1) hCapμ (ae_restrict_of_ae hCont)
  let ν := fun N => positiveFiniteDifference (ρ N) μ+μ'
  have hSucc := residual_successor_of_weak_limits hc0 h.individual_weak hFirst (hAtoms j).2
  have hνSucc : ∀ N, ν N=(B.individuals N).toFiniteMeasure.restrict (Ioi c)+ν (N+1) := by
    intro N
    dsimp only [ν]
    rw [hSucc N,positiveFiniteDifference_add_left _ _ _ (hDominates (N+1)),add_assoc]
  have hνWeak : Tendsto ν atTop (𝓝 μ') := by
    have hZero : positiveFiniteDifference μ μ=0 := by
      apply FiniteMeasure.toMeasure_injective
      exact Measure.sub_self
    have hWeak := (positiveFiniteDifference_tendsto hDominates le_rfl hSecond tendsto_const_nhds).add_const μ'
    change Tendsto ν atTop (𝓝 (positiveFiniteDifference μ μ+μ')) at hWeak
    simpa only [hZero,zero_add] using hWeak
  have hAtomLimit : (μ' : Measure ℝ) {d}=0 :=
    le_antisymm ((Measure.restrict_le_self _).trans_eq hμatom) bot_le
  have hAtom (N : ℕ) : (ν N : Measure ℝ) {d}=0 :=
    residual_atom_zero_of_remaining_atoms_zero hνSucc hνWeak hAtomLimit N (fun i _ => hQatom i)
  refine ⟨fun N => (ν N).restrict (Ioi d),?_,?_⟩
  · intro N
    have hBase := residualPayloadBase_tendsto P N Ns hNs le_rfl (hFirst N)
      (hDiagonal c hc (hAtoms j).1) (hDominates N)
    have hPre := hBase.add hDiagNew
    have hFixed : Tendsto (fun m => labeledBandResidual
        (compensatedResidualOffers (P m) (Ns m) S hS θ hθ) N c) atTop (𝓝 (ν N)) := by
      apply hPre.congr'
      filter_upwards [hNs (eventually_ge_atTop N)] with m hm
      exact (compensatedResidualOffers_residual_decomposition (P m) hm c hS θ hθ).symm
    have hRestr := ProphetSecretary.Probability.finite_upperRestriction_tendsto hFixed d (hAtom N)
    simpa only [labeledBandResidual_restrict _ _ hcd.le] using hRestr
  · have hRestr := ProphetSecretary.Probability.finite_upperRestriction_tendsto hνWeak d hAtomLimit
    rwa [Q.intensityAbove_restrict hc hd hcd.le] at hRestr

end ProphetSecretary.Limiting
