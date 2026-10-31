import ProphetSecretary.Limiting.ClosureCompensatedIntensityResiduals
import ProphetSecretary.Limiting.ClosureCompensatedIntensityTails

/-!
# Closure under complement-compensated Poisson intensity perturbations

This is the intensity part of paper `lem:closure(b)`. One slowly growing
retained prefix is chosen from the original finite sequence. Beyond it,
the chosen band receives multiplier 1+θ and its full complement receives
the probability-preserving compensation. The finite dimensions and all
original identity labels are preserved.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting

 theorem LabeledBandConvergence.compensatedIntensity {sizes : ℕ → ℕ}
    {P : ∀ m, Model.Instance (sizes m)} {B : CountableInstance}
    (h : LabeledBandConvergence sizes P B)
    (hCap : ∀ m j, ∀ᵐ x ∂(P m).law j, x≤(B.cap : ℝ))
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b)
    (hCont : ∀ᵐ x ∂B.intensity,
      ContinuousWithinAt (S.indicator (fun _ : ℝ => (1 : ℝ))) (Icc (0 : ℝ) B.cap) x)
    (θ : ℝ) (hθ : |θ|≤1/4) :
    ∃ Ns : ℕ → ℕ, Monotone Ns ∧ (∀ m, Ns m≤m) ∧ Tendsto Ns atTop atTop ∧
      (∀ m j, ∀ᵐ x ∂(compensatedResidualOffers (P m) (Ns m) S hS θ hθ).law j, x≤(B.cap : ℝ)) ∧
      LabeledBandConvergence sizes
        (fun m => compensatedResidualOffers (P m) (Ns m) S hS θ hθ)
        (B.scaleBand S ⟨1+θ,by have := (abs_le.mp hθ).1; linarith⟩) := by
  obtain ⟨Ns,hMono,hLe,hTop,hDiag,hRare⟩ := h.exists_all_continuity_residual_diagonal
  have hBandRare : ∀ ε>(0 : ℝ), ∀ᶠ m in atTop, ∀ j : Fin (sizes m), Ns m≤j.val → ((P m).law j).real S<ε := by
    intro ε hε
    filter_upwards [hRare b hb ε hε] with m hm j hj
    have hOld := hm j.val hj
    rw [labeledPaddedLaw_of_lt (P m) j.isLt] at hOld
    exact (measureReal_mono hSub).trans_lt hOld
  obtain ⟨hIndividual,hR,hBelow,hAbove⟩ := h.compensated_structural_clauses Ns hTop hS θ hθ
  refine ⟨Ns,hMono,hLe,hTop,fun m => compensatedResidualOffers_bounded (P m) (Ns m) hS θ hθ (hCap m),?_⟩
  exact ⟨hIndividual,h.compensatedResidualOffers_residual_limits hCap hS hb hCont θ hθ Ns hTop hDiag hBandRare,
    hR,hBelow,hAbove⟩

end ProphetSecretary.Limiting
