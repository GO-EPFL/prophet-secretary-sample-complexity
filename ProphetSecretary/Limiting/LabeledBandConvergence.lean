import ProphetSecretary.Limiting.LabeledPaddedInstance
import ProphetSecretary.Limiting.OrderedBandConvergence

/-!
# Body convergence with arbitrary chosen finite identity labels

This is paper `def:body-convergence` before imposing a particular sorting
scheme. The original-sequence limit is taken at each fixed retained prefix,
then the prefix tends to infinity. Rarity has the source's eventual-in-sequence
quantifier order. No value or policy convergence is a field of this definition.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology
namespace ProphetSecretary.Limiting

noncomputable def labeledBandResidual {n : ℕ} (P : Model.Instance n) (N : ℕ) (b : ℝ) : FiniteMeasure ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => N≤ i.val),
    (P.marginalProbabilityLaw i).toFiniteMeasure.restrict (Ioi b)

structure LabeledBandConvergence (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (B : CountableInstance) : Prop where
  individual_weak : ∀ i, Tendsto (fun m => labeledPaddedLaw (P m) i) atTop (𝓝 (B.individuals i))
  residual_bands : ∀ (b : ℝ) (hb : (B.terminal : ℝ)<b),
    (∀ i, (B.individuals i : Measure ℝ) {b}=0) → B.intensity {b}=0 →
    ∃ μs : ℕ → FiniteMeasure ℝ,
      (∀ N, Tendsto (fun m => labeledBandResidual (P m) N b) atTop (𝓝 (μs N))) ∧
      Tendsto μs atTop (𝓝 (B.intensityAbove b hb))
  rare : ∀ b : ℝ, (B.terminal : ℝ)<b → ∀ ε>(0 : ℝ),
    ∃ N : ℕ, ∀ᶠ m in atTop, ∀ j, N≤j → (labeledPaddedLaw (P m) j : Measure ℝ).real (Ioi b)<ε
  below_reserve : ∀ x : ℝ, 0≤x → x<(B.terminal : ℝ) →
    Tendsto (fun m => extendedTailCount (P m) x) atTop (𝓝 ⊤)
  above_reserve : ∀ b : ℝ, (B.terminal : ℝ)<b →
    ∃ K : ℝ, 0≤K ∧ ∀ m, (P m).tailCount b≤K

lemma labeledBandResidual_weightOrdered {n : ℕ} (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ) (N : ℕ) (b : ℝ) :
    labeledBandResidual (P.restrictBy (weightedMeanPermutation P wgt).toEmbedding) N b=
      weightOrderedBandResidual P wgt N b := by
  unfold labeledBandResidual weightOrderedBandResidual
  apply Finset.sum_congr rfl
  intro i _
  rfl

lemma extendedTailCount_restrictBy_equiv {n : ℕ} (P : Model.Instance n) (e : Equiv.Perm (Fin n)) (x : ℝ) :
    extendedTailCount (P.restrictBy e.toEmbedding) x=extendedTailCount P x :=
  Equiv.sum_comp e (fun i => P.law i (Ioi x))

lemma tailCount_restrictBy_equiv {n : ℕ} (P : Model.Instance n) (e : Equiv.Perm (Fin n)) (x : ℝ) :
    (P.restrictBy e.toEmbedding).tailCount x=P.tailCount x :=
  Equiv.sum_comp e (fun i => (P.law i).real (Ioi x))

/-- Ordered extraction gives the general labeled convergence after the actual
finite relabelings supplied by its sorting permutations. -/
theorem OrderedBandConvergence.to_labeled {sizes : ℕ → ℕ} {P : ∀ m, Model.Instance (sizes m)}
    {wgt : ℝ →ᵇ ℝ} {B : CountableInstance} (h : OrderedBandConvergence sizes P wgt B) :
    LabeledBandConvergence sizes
      (fun m => (P m).restrictBy (weightedMeanPermutation (P m) wgt).toEmbedding) B := by
  constructor
  · intro i
    simp_rw [labeledPaddedLaw_weightOrdered]
    exact h.individual_weak i
  · intro b hb hQ hμ
    obtain ⟨μs,hFirst,hSecond⟩ := h.residual_bands b hb hQ hμ
    refine ⟨μs,?_,hSecond⟩
    intro N
    simp_rw [labeledBandResidual_weightOrdered]
    exact hFirst N
  · intro b hb ε hε
    obtain ⟨N,hN⟩ := h.uniformly_rare b hb ε hε
    refine ⟨N,Eventually.of_forall (fun m j hj => ?_)⟩
    rw [labeledPaddedLaw_weightOrdered]
    exact hN m j hj
  · intro x hx hxa
    simp_rw [extendedTailCount_restrictBy_equiv]
    exact h.below_reserve x hx hxa
  · intro b hb
    obtain ⟨K,hK,hBound⟩ := h.above_reserve b hb
    refine ⟨K,hK,?_⟩
    intro m
    rw [tailCount_restrictBy_equiv]
    exact hBound m

end ProphetSecretary.Limiting
