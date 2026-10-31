import ProphetSecretary.Limiting.FiniteBodyIntensitySequence
import Mathlib.Logic.Relation
import ProphetSecretary.Limiting.CapBandContinuity

/-!
# Law operations and their consecutive finite-sequence realizations

The sequence relation records the actual finite families, rather than only
existence of some approximation to their target laws. A residual schedule is
certified by its original-sequence band limit; existence of that schedule is
proved from structural convergence when lifting a law operation.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
universe u
namespace ProphetSecretary.Limiting

inductive BodyModification : CountableInstance → CountableInstance → Prop where
  | enlargeCap (B : CountableInstance) (H : ℝ≥0) (hH : B.cap≤H) :
      BodyModification B (B.withCap H hH)
  | individual (B : CountableInstance) (i : ℕ) (q : ProbabilityMeasure ℝ)
      (hq : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) B.cap)
      (qs : ℕ → ProbabilityMeasure ℝ) (hqs : ∀ m, ∀ᵐ x ∂(qs m : Measure ℝ), x∈Icc (0 : ℝ) B.cap)
      (hWeak : Tendsto qs atTop (𝓝 q)) : BodyModification B (B.updateIndividual i q hq)
  | reserve (B : CountableInstance) (a : ℝ≥0) (ha0 : 0<a) (ha : a<B.terminal) :
      BodyModification B (B.reserveTranslation a ha)
  | marks (B : CountableInstance) {T : Type u} [MeasurableSpace T]
      (b : ℝ) (hb : (B.terminal : ℝ)<b) (hAtom : B.intensity {b}=0)
      (H : ℝ≥0) (hH : B.cap≤H) (κ : Measure T) [IsProbabilityMeasure κ]
      (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
      (hImage : ∀ᵐ z ∂B.intensity.prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H)
      (hKernel : ∀ᵐ x ∂(B.intensityAbove b hb : Measure ℝ), ContinuousWithinAt (randomizedMarkKernel κ Φ hΦ) (Icc (0 : ℝ) B.cap) x) :
      BodyModification B (B.mapPoissonAbove b hb H hH κ Φ hΦ hImage)

  | intensity (B : CountableInstance) (S : Set ℝ) (hS : MeasurableSet S)
      (b : ℝ) (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b)
      (hCont : ∀ᵐ x ∂B.intensity,
        ContinuousWithinAt (S.indicator (fun _ : ℝ => (1 : ℝ))) (Icc (0 : ℝ) B.cap) x)
      (θ : ℝ) (hθ : |θ|≤1/4) : BodyModification B (B.scaleBand S (quarterIntensityRate θ hθ))

inductive FiniteSequenceModification : FiniteBodySequence → FiniteBodySequence → Prop where
  | enlargeCap (A : FiniteBodySequence) (H : ℝ≥0) (hH : A.target.cap≤H) :
      FiniteSequenceModification A (A.enlargeCap H hH)
  | individual (A : FiniteBodySequence) (i : ℕ) (q : ProbabilityMeasure ℝ)
      (hq : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) A.target.cap)
      (qs : ℕ → ProbabilityMeasure ℝ) (hqs : ∀ m, ∀ᵐ x ∂(qs m : Measure ℝ), x∈Icc (0 : ℝ) A.target.cap)
      (hWeak : Tendsto qs atTop (𝓝 q)) :
      FiniteSequenceModification A (A.replaceIndividual i q hq qs hqs)
  | reserve (A : FiniteBodySequence) (a : ℝ≥0) (ha0 : 0<a) (ha : a<A.target.terminal) :
      FiniteSequenceModification A (A.translateReserve a ha)
  | marks (A : FiniteBodySequence) {T : Type u} [MeasurableSpace T]
      (b : ℝ) (hb : (A.target.terminal : ℝ)<b) (hAtom : A.target.intensity {b}=0)
      (H : ℝ≥0) (hH : A.target.cap≤H) (κ : Measure T) [IsProbabilityMeasure κ]
      (Φ : ℝ × T → ℝ) (hΦ : Measurable Φ)
      (hImage : ∀ᵐ z ∂A.target.intensity.prod κ, b<z.1 → Φ z∈Icc (0 : ℝ) H)
      (hKernel : ∀ᵐ x ∂(A.target.intensityAbove b hb : Measure ℝ), ContinuousWithinAt (randomizedMarkKernel κ Φ hΦ) (Icc (0 : ℝ) A.target.cap) x)
      (Ns : ℕ → ℕ) (hMono : Monotone Ns) (hLe : ∀ m, Ns m≤m) (hNs : Tendsto Ns atTop atTop)
      (hDiagonal : Tendsto (fun m => labeledBandResidual (A.offers m) (Ns m) b) atTop
        (𝓝 (A.target.intensityAbove b hb))) :
      FiniteSequenceModification A (A.replaceResidualMarks b hb H hH κ Φ hΦ hImage Ns)

  | intensity (A : FiniteBodySequence) (S : Set ℝ) (hS : MeasurableSet S)
      (b : ℝ) (hb : (A.target.terminal : ℝ)<b) (hSub : S⊆Ioi b)
      (hCont : ∀ᵐ x ∂A.target.intensity,
        ContinuousWithinAt (S.indicator (fun _ : ℝ => (1 : ℝ))) (Icc (0 : ℝ) A.target.cap) x)
      (θ : ℝ) (hθ : |θ|≤1/4) (Ns : ℕ → ℕ) (hMono : Monotone Ns) (hLe : ∀ m, Ns m≤m)
      (hNs : Tendsto Ns atTop atTop)
      (hDiagonal : ∀ (d : ℝ) (hd : (A.target.terminal : ℝ)<d), A.target.intensity {d}=0 →
        Tendsto (fun m => labeledBandResidual (A.offers m) (Ns m) d) atTop (𝓝 (A.target.intensityAbove d hd))) :
      FiniteSequenceModification A (A.compensateIntensity Ns S hS θ hθ)

lemma FiniteSequenceModification.preserves_convergence {A D : FiniteBodySequence}
    (h : FiniteSequenceModification.{u} A D) (hA : A.Converges) : D.Converges := by
  cases h with
  | enlargeCap H hH => exact A.converges_enlargeCap hA H hH
  | individual i q hq qs hqs hWeak => exact A.converges_replaceIndividual hA i q hq qs hqs hWeak
  | reserve a _ha0 ha => exact A.converges_translateReserve hA a ha
  | marks b hb _hAtom H hH κ Φ hΦ hImage hKernel Ns _hMono _hLe hNs hDiagonal =>
    exact A.converges_replaceResidualMarks hA b hb H hH κ Φ hΦ hImage hKernel Ns hNs hDiagonal

  | intensity S hS _b hb hSub hCont θ hθ Ns _hMono _hLe hNs hDiagonal =>
    exact A.converges_compensateIntensity hA hS hb hSub hCont θ hθ Ns hNs hDiagonal

lemma FiniteSequenceModification.target_modification {A D : FiniteBodySequence}
    (h : FiniteSequenceModification.{u} A D) : BodyModification.{u} A.target D.target := by
  cases h with
  | enlargeCap H hH => exact BodyModification.enlargeCap A.target H hH
  | individual i q hq qs hqs hWeak => exact BodyModification.individual A.target i q hq qs hqs hWeak
  | reserve a ha0 ha => exact BodyModification.reserve A.target a ha0 ha
  | marks b hb hAtom H hH κ Φ hΦ hImage hKernel _Ns _hMono _hLe _hNs _hDiagonal =>
    exact BodyModification.marks A.target b hb hAtom H hH κ Φ hΦ hImage hKernel

  | intensity S hS b hb hSub hCont θ hθ _Ns _hMono _hLe _hNs _hDiagonal =>
    exact BodyModification.intensity A.target S hS b hb hSub hCont θ hθ

lemma BodyModification.lift_given_sequence {A : FiniteBodySequence} {B : CountableInstance}
    (h : BodyModification.{u} A.target B) (hA : A.Converges) :
    ∃ D : FiniteBodySequence, D.target=B ∧ FiniteSequenceModification.{u} A D ∧ D.Converges := by
  cases h with
  | enlargeCap H hH =>
    exact ⟨A.enlargeCap H hH,rfl,FiniteSequenceModification.enlargeCap A H hH,A.converges_enlargeCap hA H hH⟩
  | individual i q hq qs hqs hWeak =>
    exact ⟨A.replaceIndividual i q hq qs hqs,rfl,FiniteSequenceModification.individual A i q hq qs hqs hWeak,
      A.converges_replaceIndividual hA i q hq qs hqs hWeak⟩
  | reserve a ha0 ha =>
    exact ⟨A.translateReserve a ha,rfl,FiniteSequenceModification.reserve A a ha0 ha,A.converges_translateReserve hA a ha⟩
  | marks b hb hAtom H hH κ Φ hΦ hImage hKernel =>
    have hConv : LabeledBandConvergence A.size A.offers A.target := hA
    obtain ⟨Ns,hMono,hLe,hTop,hDiag,_hRare⟩ := hConv.exists_all_continuity_residual_diagonal
    have hStep := FiniteSequenceModification.marks A b hb hAtom H hH κ Φ hΦ hImage hKernel Ns hMono hLe hTop (hDiag b hb hAtom)
    exact ⟨A.replaceResidualMarks b hb H hH κ Φ hΦ hImage Ns,rfl,hStep,hStep.preserves_convergence hA⟩

  | intensity S hS b hb hSub hCont θ hθ =>
    have hConv : LabeledBandConvergence A.size A.offers A.target := hA
    obtain ⟨Ns,hMono,hLe,hTop,hDiag,_hRare⟩ := hConv.exists_all_continuity_residual_diagonal
    have hStep := FiniteSequenceModification.intensity A S hS b hb hSub hCont θ hθ Ns hMono hLe hTop hDiag
    exact ⟨A.compensateIntensity Ns S hS θ hθ,rfl,hStep,hStep.preserves_convergence hA⟩

lemma BodyModification.upperIntensity (B : CountableInstance) (b : ℝ) (hb : (B.terminal : ℝ)<b)
    (hAtom : B.intensity {b}=0) (θ : ℝ) (hθ : |θ|≤1/4) :
    BodyModification.{u} B (B.scaleBand (Ioc b (B.cap : ℝ)) (quarterIntensityRate θ hθ)) :=
  BodyModification.intensity B _ measurableSet_Ioc b hb (fun _ hx => hx.1)
    (B.upperBand_indicator_continuousWithinAt_ae b hAtom) θ hθ

lemma BodyModification.intensity_of_null_frontier (B : CountableInstance) (S : Set ℝ)
    (hS : MeasurableSet S) (b : ℝ) (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b)
    (hFront : B.intensity (frontier S)=0) (θ : ℝ) (hθ : |θ|≤1/4) :
    BodyModification.{u} B (B.scaleBand S (quarterIntensityRate θ hθ)) := by
  apply BodyModification.intensity B S hS b hb hSub _ θ hθ
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hFront] with x hx
  exact ((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).continuousOn.continuousAt_indicator hx).continuousWithinAt

end ProphetSecretary.Limiting
