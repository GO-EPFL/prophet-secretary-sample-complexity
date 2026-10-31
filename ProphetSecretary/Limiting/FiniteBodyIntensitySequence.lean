import ProphetSecretary.Limiting.FiniteBodySequence
import ProphetSecretary.Limiting.ClosureCompensatedIntensity

/-!
# Consecutive finite sequences for compensated intensity operations

The same original finite labels and dimensions remain. The quarter-interval
scaling and its complementary probability compensation are those of the
actual guarded residual family. Convergence follows from its independently
proved structural and residual limits along the supplied original diagonal.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting

noncomputable def quarterIntensityRate (θ : ℝ) (hθ : |θ|≤1/4) : ℝ≥0 :=
  ⟨1+θ,by linarith only [(abs_le.mp hθ).1]⟩

namespace FiniteBodySequence

noncomputable def compensateIntensity (A : FiniteBodySequence) (Ns : ℕ → ℕ)
    (S : Set ℝ) (hS : MeasurableSet S) (θ : ℝ) (hθ : |θ|≤1/4) : FiniteBodySequence where
  size := A.size
  offers m := compensatedResidualOffers (A.offers m) (Ns m) S hS θ hθ
  target := A.target.scaleBand S (quarterIntensityRate θ hθ)
  bounded m := compensatedResidualOffers_bounded (A.offers m) (Ns m) hS θ hθ (A.bounded m)

lemma converges_compensateIntensity (A : FiniteBodySequence) (hA : A.Converges)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (A.target.terminal : ℝ)<b) (hSub : S⊆Ioi b)
    (hCont : ∀ᵐ x ∂A.target.intensity,
      ContinuousWithinAt (S.indicator (fun _ : ℝ => (1 : ℝ))) (Icc (0 : ℝ) A.target.cap) x)
    (θ : ℝ) (hθ : |θ|≤1/4) (Ns : ℕ → ℕ) (hNs : Tendsto Ns atTop atTop)
    (hDiagonal : ∀ (d : ℝ) (hd : (A.target.terminal : ℝ)<d), A.target.intensity {d}=0 →
      Tendsto (fun m => labeledBandResidual (A.offers m) (Ns m) d) atTop (𝓝 (A.target.intensityAbove d hd))) :
    (A.compensateIntensity Ns S hS θ hθ).Converges := by
  have hConv : LabeledBandConvergence A.size A.offers A.target := hA
  have hBandRare : ∀ ε>(0 : ℝ), ∀ᶠ m in atTop, ∀ j : Fin (A.size m),
      Ns m≤j.val → ((A.offers m).law j).real S<ε := by
    intro ε hε
    obtain ⟨N,hRare⟩ := hConv.rare b hb ε hε
    filter_upwards [hNs (eventually_ge_atTop N),hRare] with m hm hR j hj
    have hOld := hR j.val (hm.trans hj)
    rw [labeledPaddedLaw_of_lt (A.offers m) j.isLt] at hOld
    exact (measureReal_mono hSub).trans_lt hOld
  obtain ⟨hIndividual,hRare,hBelow,hAbove⟩ := hConv.compensated_structural_clauses Ns hNs hS θ hθ
  refine ⟨hIndividual,?_,hRare,hBelow,hAbove⟩
  exact hConv.compensatedResidualOffers_residual_limits A.bounded hS hb hCont θ hθ Ns hNs hDiagonal hBandRare

end FiniteBodySequence
end ProphetSecretary.Limiting
