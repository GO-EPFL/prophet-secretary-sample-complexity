import ProphetSecretary.Limiting.DirectVirtualOfferInstance
import ProphetSecretary.Limiting.DirectApproximationBenchmark

/-!
# Individual perturbations with the same direct count and cutoff

The full individual tilt leaves the cap, terminal reward and Poisson intensity
unchanged. Hence the prescribed base virtual count and cutoff satisfy the
same mass and rarity bounds for every parameter. The actual direct finite
likelihood family is identified before its benchmark and value limits are used.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model ProphetSecretary.Probability

noncomputable def individualBoundedScorePath (B : CountableInstance) (i : ℕ) (f : ℝ →ᵇ ℝ) (θ : ℝ) :
    CountableInstance := B.individualLikelihoodPath i (centeredBoundedScore (B.individuals i : Measure ℝ) f)
      (continuous_centeredBoundedScore (B.individuals i : Measure ℝ) f).measurable
      (Filter.Eventually.of_forall (centeredBoundedScore_abs_le_one (B.individuals i : Measure ℝ) f))
      (centeredBoundedScore_mean (B.individuals i : Measure ℝ) f) θ

lemma individualBoundedScorePath_geometry (B : CountableInstance) (i : ℕ) (f : ℝ →ᵇ ℝ) (θ : ℝ) :
    (B.individualBoundedScorePath i f θ).terminal=B.terminal ∧
      (B.individualBoundedScorePath i f θ).intensity=B.intensity ∧
      (B.individualBoundedScorePath i f θ).cap=B.cap := by
  unfold individualBoundedScorePath individualLikelihoodPath
  split_ifs <;> exact ⟨rfl,rfl,rfl⟩

lemma individualBoundedScorePath_cut (B : CountableInstance) (i : ℕ) (f : ℝ →ᵇ ℝ) (θ : ℝ) (m : ℕ) :
    ((B.individualBoundedScorePath i f θ).terminal : ℝ)<B.markCutoff m := by
  rw [(B.individualBoundedScorePath_geometry i f θ).1]
  exact B.terminal_lt_markCutoff m

lemma individualBoundedScorePath_intensityAbove (B : CountableInstance) (i : ℕ) (f : ℝ →ᵇ ℝ) (θ : ℝ) (m : ℕ) :
    (B.individualBoundedScorePath i f θ).intensityAbove (B.markCutoff m) (B.individualBoundedScorePath_cut i f θ m)=
      (B.directTruncation m).intensity := by
  apply FiniteMeasure.toMeasure_injective
  change (B.individualBoundedScorePath i f θ).intensity.restrict (Ioi (B.markCutoff m))=
    B.intensity.restrict (Ioi (B.markCutoff m))
  rw [(B.individualBoundedScorePath_geometry i f θ).2.1]

lemma individualBoundedScorePath_mass_le (B : CountableInstance) (hZero : B.terminal=0)
    (i : ℕ) (f : ℝ →ᵇ ℝ) (θ : ℝ) (m : ℕ) :
    ((B.individualBoundedScorePath i f θ).intensityAbove (B.markCutoff m)
      (B.individualBoundedScorePath_cut i f θ m)).mass≤(B.directVirtualCount hZero m : ℝ≥0) := by
  rw [B.individualBoundedScorePath_intensityAbove]
  exact B.directVirtualCount_rate_le hZero m

noncomputable def individualDirectApproximationAt (B : CountableInstance) (hZero : B.terminal=0)
    (i : ℕ) (f : ℝ →ᵇ ℝ) (θ : ℝ) (m : ℕ) : Instance (m+B.directVirtualCount hZero m) :=
  (B.individualBoundedScorePath i f θ).finiteDirectApproximationAt m (B.markCutoff m)
    (B.individualBoundedScorePath_cut i f θ m) (B.directVirtualCount hZero m)
    (B.directVirtualCount_positive hZero m) (B.individualBoundedScorePath_mass_le hZero i f θ m)

lemma individualDirectApproximationAt_eq_appendVirtual (B : CountableInstance) (hZero : B.terminal=0)
    (i : ℕ) (f : ℝ →ᵇ ℝ) (θ : ℝ) (m : ℕ) :
    B.individualDirectApproximationAt hZero i f θ m=
      ((B.individualBoundedScorePath i f θ).individualPrefix m).appendIndependent (B.directVirtualOfferInstance hZero m) := by
  have hMu := B.individualBoundedScorePath_intensityAbove i f θ m
  apply Model.Instance.eq_of_law_eq
  funext j
  induction j using Fin.addCases with
  | left j =>
    simp only [individualDirectApproximationAt,finiteDirectApproximationAt,rareDesign,appendIID,
      Model.Instance.appendIndependent,Fin.addCases_left]
    rfl
  | right j =>
    simp only [individualDirectApproximationAt,finiteDirectApproximationAt,rareDesign,appendIID,
      Model.Instance.appendIndependent,directVirtualOfferInstance,Model.iidOfferInstance,Fin.addCases_right]
    change (rareFiniteLaw ((B.individualBoundedScorePath i f θ).intensityAbove (B.markCutoff m)
      (B.individualBoundedScorePath_cut i f θ m)) (B.directVirtualCount hZero m) : Measure ℝ)=
      (rareFiniteLaw (B.directTruncation m).intensity (B.directVirtualCount hZero m) : Measure ℝ)
    rw [hMu]

noncomputable def directIndividualPerturbation (B : CountableInstance) (hZero : B.terminal=0)
    (i : ℕ) (f : ℝ →ᵇ ℝ) (θ : ℝ) (m : ℕ) : Instance (m+B.directVirtualCount hZero m) :=
  ((B.individualPrefix m).appendIndependent (B.directVirtualOfferInstance hZero m)).likelihoodWidePath
    (directIndividualScore (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f)
    (directIndividualScore_properties (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f).1
    (fun j => Filter.Eventually.of_forall
      ((directIndividualScore_properties (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f).2.1 j))
    (directIndividualScore_properties (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f).2.2.1 θ

lemma directIndividualPerturbation_eq_prescribed (B : CountableInstance) (hZero : B.terminal=0)
    (i : ℕ) (f : ℝ →ᵇ ℝ) {θ : ℝ} (hθ : |θ|≤1/4) (m : ℕ) :
    B.directIndividualPerturbation hZero i f θ m=B.individualDirectApproximationAt hZero i f θ m := by
  unfold directIndividualPerturbation
  rw [directIndividualScore_likelihoodWidePath B m (B.directVirtualCount hZero m)
    (B.directVirtualOfferInstance hZero m) i f hθ]
  exact (B.individualDirectApproximationAt_eq_appendVirtual hZero i f θ m).symm

/-- Pointwise perturbed benchmark convergence uses the base virtual count,
not the count selected afresh for the perturbed instance. -/
theorem directIndividualPerturbation_expectedMaximum_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (i : ℕ) (f : ℝ →ᵇ ℝ) {θ : ℝ} (hθ : |θ|≤1/4) :
    Tendsto (fun m => (B.directIndividualPerturbation hZero i f θ m).expectedMaximum)
      atTop (𝓝 (B.individualBoundedScorePath i f θ).expectedMaximum) := by
  let C := B.individualBoundedScorePath i f θ
  have hCZero : C.terminal=0 := (B.individualBoundedScorePath_geometry i f θ).1.trans hZero
  have hCut : Tendsto B.markCutoff atTop (𝓝 (C.terminal : ℝ)) := by
    rw [show C.terminal=B.terminal from (B.individualBoundedScorePath_geometry i f θ).1]
    exact B.markCutoff_tendsto
  have h := C.finiteDirectApproximationAt_expectedMaximum_tendsto hCZero id (B.directVirtualCount hZero) B.markCutoff
    (B.individualBoundedScorePath_cut i f θ) (B.directVirtualCount_positive hZero)
    (B.individualBoundedScorePath_mass_le hZero i f θ) tendsto_id hCut (B.directVirtualCount_tendsto hZero)
  simp_rw [B.directIndividualPerturbation_eq_prescribed hZero i f hθ]
  exact h

theorem directIndividualPerturbation_value_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (i : ℕ) (f : ℝ →ᵇ ℝ) {θ w c : ℝ} (hθ : |θ|≤1/4) (hw : 0≤w) (hc : 0≤c) :
    Tendsto (fun m => Model.optimalScalarValue (B.directIndividualPerturbation hZero i f θ m) w c)
      atTop (𝓝 ((B.individualBoundedScorePath i f θ).optimalScalarValue w c)) := by
  let C := B.individualBoundedScorePath i f θ
  have hCZero : C.terminal=0 := (B.individualBoundedScorePath_geometry i f θ).1.trans hZero
  have hCut : Tendsto B.markCutoff atTop (𝓝 (C.terminal : ℝ)) := by
    rw [show C.terminal=B.terminal from (B.individualBoundedScorePath_geometry i f θ).1]
    exact B.markCutoff_tendsto
  have hSquare : Tendsto (fun m => ((C.intensityAbove (B.markCutoff m)
      (B.individualBoundedScorePath_cut i f θ m)).mass : ℝ)^2/(B.directVirtualCount hZero m : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
    dsimp only [C]
    simp_rw [B.individualBoundedScorePath_intensityAbove i f θ]
    exact B.directVirtualCount_square_error_tendsto hZero
  have h := C.finiteDirectApproximationAt_value_tendsto hCZero id (B.directVirtualCount hZero) B.markCutoff
    (B.individualBoundedScorePath_cut i f θ) (B.directVirtualCount_positive hZero)
    (B.individualBoundedScorePath_mass_le hZero i f θ) tendsto_id hCut hSquare hw hc
  simp_rw [B.directIndividualPerturbation_eq_prescribed hZero i f hθ]
  exact h

end ProphetSecretary.Limiting.CountableInstance
