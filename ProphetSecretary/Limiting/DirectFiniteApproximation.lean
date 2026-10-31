import ProphetSecretary.Limiting.DirectIndividualPerturbedApproximation
import ProphetSecretary.Limiting.DirectCloudPerturbedValue
import ProphetSecretary.Limiting.CountableFirstBandWindow

/-!
# Direct finite approximation and its perturbed limits

This is `con:direct-approx` and `lem:direct-approx`. The retained prefix is m,
the cutoff decreases to zero, and the virtual count is chosen from the base
instance alone. The same counts and cutoffs approximate each fixed perturbed
law. Maxima, scalar values and positive-level tail counts are separate claims.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model ProphetSecretary.Probability

lemma directFiniteApproximation_eq_prescribed (B : CountableInstance) (hZero : B.terminal=0) (m : ℕ) :
    B.directFiniteApproximation hZero m=
      B.finiteDirectApproximationAt m (B.markCutoff m) (B.terminal_lt_markCutoff m)
        (B.directVirtualCount hZero m) (B.directVirtualCount_positive hZero m)
        (B.directVirtualCount_rate_le hZero m) := by
  rw [B.directFiniteApproximation_eq_appendVirtual hZero m]
  apply Model.Instance.eq_of_law_eq
  rfl

/-- Base convergence and the explicit uniform tail profile in `lem:direct-approx`.
The positive virtual count satisfies the stronger zero-mass bound 1/2. -/
theorem direct_finite_approximation (B : CountableInstance) (hZero : B.terminal=0) :
    Antitone B.markCutoff ∧ Tendsto B.markCutoff atTop (𝓝 (0 : ℝ)) ∧
    Tendsto (B.directVirtualCount hZero) atTop atTop ∧
    (∀ m, ((B.directTruncation m).intensity.mass : ℝ)/(B.directVirtualCount hZero m : ℝ)≤1/2) ∧
    (∀ m i, ∀ᵐ x ∂(B.directFiniteApproximation hZero m).law i, x≤(B.cap : ℝ)) ∧
    Tendsto (fun m => (B.directFiniteApproximation hZero m).expectedMaximum) atTop (𝓝 B.expectedMaximum) ∧
    (∀ w c : ℝ, 0≤w → 0≤c →
      Tendsto (fun m => Model.optimalScalarValue (B.directFiniteApproximation hZero m) w c)
        atTop (𝓝 (B.optimalScalarValue w c))) ∧
    ∀ b : ℝ, 0<b → ∃ K : ℝ, 0≤K ∧ ∀ m, (B.directFiniteApproximation hZero m).tailCount b≤K := by
  refine ⟨B.markCutoff_antitone,?_,B.directVirtualCount_tendsto hZero,
    B.directVirtualCount_probability_le_half hZero,B.directFiniteApproximation_bounded hZero,
    B.directFiniteApproximation_expectedMaximum_tendsto hZero,
    (fun _ _ hw hc => B.directFiniteApproximation_value_tendsto hZero hw hc),?_⟩
  · simpa only [hZero,NNReal.coe_zero] using B.markCutoff_tendsto
  · intro b hb
    exact ⟨(B.totalTailMass b).toReal,ENNReal.toReal_nonneg,
      fun m => B.directFiniteApproximation_tailCount_le hZero m hb⟩

lemma directBandPath_cut (B : CountableInstance) (S : Set ℝ) {θ : ℝ}
    (hθ : |θ|≤1/4) (m : ℕ) :
    ((B.bandLikelihoodPath S θ).terminal : ℝ)<B.markCutoff m := by
  rw [B.bandLikelihoodPath_of_mem S hθ]
  exact B.terminal_lt_markCutoff m

lemma directBandPath_intensityAbove (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    {θ : ℝ} (hθ : |θ|≤1/4) (r : ℝ≥0) (hr : (r : ℝ)=1+θ) (m : ℕ) :
    (B.bandLikelihoodPath S θ).intensityAbove (B.markCutoff m) (B.directBandPath_cut S hθ m)=
      bandScaledIntensity (B.directTruncation m).intensity S r := by
  apply FiniteMeasure.toMeasure_injective
  change (B.bandLikelihoodPath S θ).intensity.restrict (Ioi (B.markCutoff m))=
    (bandScaledIntensity (B.directTruncation m).intensity S r : Measure ℝ)
  have hPath : B.bandLikelihoodPath S θ=B.scaleBand S r := by
    rw [B.bandLikelihoodPath_of_mem S hθ]
    congr 1
    exact Subtype.ext hr.symm
  rw [hPath]
  exact congrArg (fun μ : FiniteMeasure ℝ => (μ : Measure ℝ))
    (B.scaleBand_intensityAbove hS r (B.markCutoff m) (B.terminal_lt_markCutoff m))

lemma directBandPath_mass_le (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {θ : ℝ} (hθ : |θ|≤1/4) (m : ℕ) :
    ((B.bandLikelihoodPath S θ).intensityAbove (B.markCutoff m)
      (B.directBandPath_cut S hθ m)).mass≤(B.directVirtualCount hZero m : ℝ≥0) := by
  let r : ℝ≥0 := ⟨1+θ,by have h := (abs_le.mp hθ).1; linarith⟩
  rw [B.directBandPath_intensityAbove hS hθ r rfl]
  exact bandScaledIntensity_mass_le_fixedCount (B.directTruncation m).intensity hS
    (B.directVirtualCount hZero m) (B.directVirtualCount_positive hZero m)
    (B.directVirtualCount_probability_le_half hZero m) hθ r rfl

/-- Multiply the chosen cloud intensity by 1+θ on S, while keeping the base
retained prefix, cutoff and number of finite variables unchanged. -/
noncomputable def directBandApproximation (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {θ : ℝ} (hθ : |θ|≤1/4) (m : ℕ) :
    Model.Instance (m+B.directVirtualCount hZero m) :=
  (B.bandLikelihoodPath S θ).finiteDirectApproximationAt m (B.markCutoff m)
    (B.directBandPath_cut S hθ m) (B.directVirtualCount hZero m)
    (B.directVirtualCount_positive hZero m) (B.directBandPath_mass_le hZero hS hθ m)

/-- The intensity-perturbation clause of `lem:direct-approx`. The same schedule
works for every fixed measurable affected set and every quarter parameter. -/
theorem directBandApproximation_limits (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {θ : ℝ} (hθ : |θ|≤1/4) :
    Tendsto (fun m => (B.directBandApproximation hZero hS hθ m).expectedMaximum)
      atTop (𝓝 (B.bandLikelihoodPath S θ).expectedMaximum) ∧
    ∀ w c : ℝ, 0≤w → 0≤c →
      Tendsto (fun m => Model.optimalScalarValue (B.directBandApproximation hZero hS hθ m) w c)
        atTop (𝓝 ((B.bandLikelihoodPath S θ).optimalScalarValue w c)) := by
  let D := B.bandLikelihoodPath S θ
  have hDZero : D.terminal=0 := by
    dsimp only [D]
    rw [B.bandLikelihoodPath_of_mem S hθ]
    exact hZero
  have hCut : Tendsto B.markCutoff atTop (𝓝 (D.terminal : ℝ)) := by
    rw [hDZero]
    simpa only [hZero,NNReal.coe_zero] using B.markCutoff_tendsto
  have hM := D.finiteDirectApproximationAt_expectedMaximum_tendsto hDZero id
    (B.directVirtualCount hZero) B.markCutoff (B.directBandPath_cut S hθ)
    (B.directVirtualCount_positive hZero) (B.directBandPath_mass_le hZero hS hθ)
    tendsto_id hCut (B.directVirtualCount_tendsto hZero)
  refine ⟨hM,?_⟩
  intro w c hw hc
  let r : ℝ≥0 := ⟨1+θ,by have h := (abs_le.mp hθ).1; linarith⟩
  have hSquare : Tendsto (fun m => ((D.intensityAbove (B.markCutoff m)
      (B.directBandPath_cut S hθ m)).mass : ℝ)^2/(B.directVirtualCount hZero m : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
    dsimp only [D]
    simp_rw [B.directBandPath_intensityAbove hS hθ r rfl]
    exact bandScaledIntensity_square_error_tendsto (fun m => (B.directTruncation m).intensity)
      (B.directVirtualCount hZero) hS hθ r rfl (B.directVirtualCount_square_error_tendsto hZero)
  exact D.finiteDirectApproximationAt_value_tendsto hDZero id
    (B.directVirtualCount hZero) B.markCutoff (B.directBandPath_cut S hθ)
    (B.directVirtualCount_positive hZero) (B.directBandPath_mass_le hZero hS hθ)
    tendsto_id hCut hSquare hw hc

/-- The bounded continuous individual-likelihood clause of `lem:direct-approx`.
The same base count and cutoff apply to every fixed individual and parameter. -/
theorem directIndividualPerturbation_limits (B : CountableInstance) (hZero : B.terminal=0)
    (i : ℕ) (f : ℝ →ᵇ ℝ) {θ : ℝ} (hθ : |θ|≤1/4) :
    Tendsto (fun m => (B.directIndividualPerturbation hZero i f θ m).expectedMaximum)
      atTop (𝓝 (B.individualBoundedScorePath i f θ).expectedMaximum) ∧
    ∀ w c : ℝ, 0≤w → 0≤c →
      Tendsto (fun m => Model.optimalScalarValue (B.directIndividualPerturbation hZero i f θ m) w c)
        atTop (𝓝 ((B.individualBoundedScorePath i f θ).optimalScalarValue w c)) :=
  ⟨B.directIndividualPerturbation_expectedMaximum_tendsto hZero i f hθ,
    fun _ _ hw hc => B.directIndividualPerturbation_value_tendsto hZero i f hθ hw hc⟩

end ProphetSecretary.Limiting.CountableInstance
