import ProphetSecretary.Limiting.DirectFiniteApproximation
import ProphetSecretary.Limiting.RareDesignTail
import ProphetSecretary.Probability.TailLikelihoodBounds

/-!
# Uniform tail profiles for the perturbed direct finite instances

The same factor 5/4 works for every finite index and every quarter parameter.
The profile is finite at each positive level even when total first moments
diverge near zero. This supplies the tail assertion used after perturbation
in the proof of `lem:direct-approx`.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model ProphetSecretary.Probability

lemma finiteDirectApproximationAt_tailCount_eq (B : CountableInstance) (N : ℕ) (cut : ℝ)
    (hcut : (B.terminal : ℝ)<cut) (k : ℕ) (hk : 0<k)
    (hm : (B.intensityAbove cut hcut).mass≤(k : ℝ≥0)) {b : ℝ} (hb : 0≤b) :
    (B.finiteDirectApproximationAt N cut hcut k hk hm).tailCount b=
      (B.individualPrefix N).tailCount b+(B.intensityAbove cut hcut : Measure ℝ).real (Ioi b) :=
  rareDesign_tailCount_eq (B.truncation N cut hcut).individuals
    (B.intensityAbove cut hcut) B.cap
    ((B.truncation N cut hcut).intensity_supported.mono (fun _ hx => ⟨hx.1.le,hx.2⟩)) k hk hm hb

theorem directBandApproximation_tailCount_le (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {θ : ℝ} (hθ : |θ|≤1/4) (m : ℕ) {b : ℝ} (hb : 0<b) :
    (B.directBandApproximation hZero hS hθ m).tailCount b≤(5/4)*(B.totalTailMass b).toReal := by
  let D := B.bandLikelihoodPath S θ
  let r : ℝ≥0 := ⟨1+θ,by have h := (abs_le.mp hθ).1; linarith⟩
  have hPrefix : D.individualPrefix m=B.individualPrefix m := by
    apply Model.Instance.eq_of_law_eq
    funext i
    change (D.individuals i.val : Measure ℝ)=(B.individuals i.val : Measure ℝ)
    dsimp only [D]
    rw [B.bandLikelihoodPath_of_mem S hθ]
    rfl
  have hInt := congrArg (fun μ : FiniteMeasure ℝ => (μ : Measure ℝ).real (Ioi b))
    (B.directBandPath_intensityAbove hS hθ r rfl m)
  change (D.finiteDirectApproximationAt m (B.markCutoff m) (B.directBandPath_cut S hθ m)
    (B.directVirtualCount hZero m) (B.directVirtualCount_positive hZero m)
    (B.directBandPath_mass_le hZero hS hθ m)).tailCount b≤_
  rw [D.finiteDirectApproximationAt_tailCount_eq _ _ _ _ _ _ hb.le,hPrefix,hInt]
  have hCloud := bandScaledIntensity_real_le_quarter (B.directTruncation m).intensity (A:=Ioi b) hS
    measurableSet_Ioi hθ r rfl
  have hAbove : (B.terminal : ℝ)<b := by simpa only [hZero,NNReal.coe_zero] using hb
  have hBase : (B.individualPrefix m).tailCount b+
      ((B.directTruncation m).intensity : Measure ℝ).real (Ioi b)≤(B.totalTailMass b).toReal :=
    B.truncation_tailCount_le m (B.terminal_lt_markCutoff m) b hAbove
  have hNonneg : 0≤(B.individualPrefix m).tailCount b := by
    unfold Model.Instance.tailCount
    exact Finset.sum_nonneg (fun _ _ => measureReal_nonneg)
  nlinarith only [hCloud,hBase,hNonneg]

theorem directIndividualPerturbation_tailCount_le (B : CountableInstance) (hZero : B.terminal=0)
    (i : ℕ) (f : ℝ →ᵇ ℝ) {θ : ℝ} (hθ : |θ|≤1/4) (m : ℕ) {b : ℝ} (hb : 0<b) :
    (B.directIndividualPerturbation hZero i f θ m).tailCount b≤(5/4)*(B.totalTailMass b).toReal := by
  let Q := (B.individualPrefix m).appendIndependent (B.directVirtualOfferInstance hZero m)
  have hProps := directIndividualScore_properties (B.individualPrefix m)
    (B.directVirtualOfferInstance hZero m) i f
  have hTilt := Q.tailCount_likelihoodWidePath_quarter_le
    (directIndividualScore (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f)
    hProps.1 (fun j => Eventually.of_forall (hProps.2.1 j)) hProps.2.2.1 hθ b
  have hBase : Q.tailCount b≤(B.totalTailMass b).toReal := by
    rw [show Q=B.directFiniteApproximation hZero m from
      (B.directFiniteApproximation_eq_appendVirtual hZero m).symm]
    exact B.directFiniteApproximation_tailCount_le hZero m hb
  exact hTilt.trans (mul_le_mul_of_nonneg_left hBase (by norm_num : (0:ℝ)≤5/4))

end ProphetSecretary.Limiting.CountableInstance
