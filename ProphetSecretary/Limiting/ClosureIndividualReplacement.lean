import ProphetSecretary.Limiting.LabeledIndividualReplacement
import ProphetSecretary.Limiting.LabeledResidualPrefixCompletion
import ProphetSecretary.Limiting.LabeledResidualTailContinuity
import ProphetSecretary.Limiting.LabeledValueConvergence
import ProphetSecretary.Limiting.CountableIndividualChange

/-!
# Closure under a specified weakly approximated individual replacement

This is operation (a) of paper `lem:closure`, for one arbitrary label. The
actual original finite family is padded before replacing the selected law,
so even a previously absent zero label has an explicit approximation.
Cutoff atoms of replaced old marginals do not enter the new residual limits.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal
namespace ProphetSecretary.Limiting

noncomputable def replaceLabeledSequence {sizes : ℕ → ℕ} (P : ∀ m, Model.Instance (sizes m))
    (i : ℕ) (qs : ℕ → ProbabilityMeasure ℝ) (hqs : ∀ m, ∀ᵐ x ∂(qs m : Measure ℝ), 0≤x) :
    ∀ m, Model.Instance (sizes m+(i+1)) :=
  fun m => replaceLabeledIndividual (P m) i (qs m) (hqs m)

theorem LabeledBandConvergence.updateIndividual {sizes : ℕ → ℕ}
    {P : ∀ m, Model.Instance (sizes m)} {B : CountableInstance}
    (h : LabeledBandConvergence sizes P B) (i : ℕ) (q : ProbabilityMeasure ℝ)
    (hq : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) B.cap)
    (qs : ℕ → ProbabilityMeasure ℝ) (hqs : ∀ m, ∀ᵐ x ∂(qs m : Measure ℝ), 0≤x)
    (hWeak : Tendsto qs atTop (𝓝 q)) :
    LabeledBandConvergence (fun m => sizes m+(i+1)) (replaceLabeledSequence P i qs hqs)
      (B.updateIndividual i q hq) := by
  let Ps := replaceLabeledSequence P i qs hqs
  let Q := B.updateIndividual i q hq
  have hIndividuals (j : ℕ) : Tendsto (fun m => labeledPaddedLaw (Ps m) j) atTop (𝓝 (Q.individuals j)) := by
    by_cases hji : j=i
    · subst j
      have hFun : (fun m => labeledPaddedLaw (Ps m) i)=qs := by
        funext m
        exact (labeledPaddedLaw_replaceLabeledIndividual (P m) i (qs m) (hqs m) i).trans (Function.update_self _ _ _)
      rw [hFun]
      change Tendsto qs atTop (𝓝 (Function.update B.individuals i q i))
      rw [Function.update_self]
      exact hWeak
    · have hFun : (fun m => labeledPaddedLaw (Ps m) j)=fun m => labeledPaddedLaw (P m) j := by
        funext m
        exact (labeledPaddedLaw_replaceLabeledIndividual (P m) i (qs m) (hqs m) j).trans (Function.update_of_ne hji _ _)
      rw [hFun]
      change Tendsto (fun m => labeledPaddedLaw (P m) j) atTop (𝓝 (Function.update B.individuals i q j))
      rw [Function.update_of_ne hji]
      exact h.individual_weak j
  refine ⟨hIndividuals,?_,?_,?_,?_⟩
  · intro b hb hQatom hμatom
    have hb0 : 0≤b := B.terminal.property.trans hb.le
    let K := i+1
    have hRemaining (j : ℕ) (hj : K≤j) : (B.individuals j : Measure ℝ) {b}=0 := by
      have hji : j≠i := by dsimp only [K] at hj; omega
      have h := hQatom j
      change ((Function.update B.individuals i q j : ProbabilityMeasure ℝ) : Measure ℝ) {b}=0 at h
      rwa [Function.update_of_ne hji] at h
    obtain ⟨ρ,hFirst,hSecond⟩ := h.tail_continuity_residual_limits K b hb hRemaining hμatom
    have hNewFirst (N : ℕ) (hKN : K≤N) :
        Tendsto (fun m => labeledBandResidual (Ps m) N b) atTop (𝓝 (ρ N)) := by
      have hEq (m : ℕ) : labeledBandResidual (Ps m) N b=labeledBandResidual (P m) N b := by
        apply labeledBandResidual_eq_of_padded_tail_eq (Ps m) (P m) N hb0
        intro j hj
        have hji : j≠i := by dsimp only [K] at hKN; omega
        exact (labeledPaddedLaw_replaceLabeledIndividual (P m) i (qs m) (hqs m) j).trans (Function.update_of_ne hji _ _)
      simp_rw [hEq]
      exact hFirst N hKN
    exact complete_residual_band_limits_from_prefix hb0 hIndividuals hQatom K ρ (B.intensityAbove b hb) hNewFirst hSecond
  · intro b hb ε hε
    obtain ⟨N,hRare⟩ := h.rare b hb ε hε
    refine ⟨max N (i+1),?_⟩
    filter_upwards [hRare] with m hm j hj
    have hji : j≠i := by have h := (le_max_right N (i+1)).trans hj; omega
    change (labeledPaddedLaw (replaceLabeledIndividual (P m) i (qs m) (hqs m)) j : Measure ℝ).real (Ioi b)<ε
    rw [labeledPaddedLaw_replaceLabeledIndividual (P m) i (qs m) (hqs m) j,Function.update_of_ne hji]
    exact hm j ((le_max_left _ _).trans hj)
  · intro b hb0 hb
    exact tendsto_ennreal_top_of_le_add_one (h.below_reserve b hb0 hb)
      (fun m => (replaceLabeledIndividual_tailCounts (P m) i (qs m) (hqs m) hb0).1)
  · intro b hb
    have hb0 : 0≤b := B.terminal.property.trans hb.le
    obtain ⟨K,hK,hBound⟩ := h.above_reserve b hb
    refine ⟨K+1,by positivity,?_⟩
    intro m
    exact (replaceLabeledIndividual_tailCount_le (P m) i (qs m) (hqs m) hb0).trans
      (add_le_add (hBound m) le_rfl)

theorem LabeledBandConvergence.updateIndividual_values_and_maxima {sizes : ℕ → ℕ}
    {P : ∀ m, Model.Instance (sizes m)} {B : CountableInstance}
    (h : LabeledBandConvergence sizes P B)
    (hCap : ∀ m j, ∀ᵐ x ∂(P m).law j, x≤(B.cap : ℝ))
    (i : ℕ) (q : ProbabilityMeasure ℝ) (hq : ∀ᵐ x ∂(q : Measure ℝ), x∈Icc (0 : ℝ) B.cap)
    (qs : ℕ → ProbabilityMeasure ℝ) (hqs : ∀ m, ∀ᵐ x ∂(qs m : Measure ℝ), x∈Icc (0 : ℝ) B.cap)
    (hWeak : Tendsto qs atTop (𝓝 q)) (W C : ℝ≥0) :
    ∀ ε>(0 : ℝ), ∀ᶠ m in atTop,
      (∀ w c : ℝ, 0≤w → w≤W → 0≤c → c≤C →
        |Model.optimalScalarValue (replaceLabeledIndividual (P m) i (qs m) ((hqs m).mono (fun _ hx => hx.1))) w c-
          (B.updateIndividual i q hq).optimalScalarValue w c|<ε) ∧
      |(replaceLabeledIndividual (P m) i (qs m) ((hqs m).mono (fun _ hx => hx.1))).expectedMaximum-
        (B.updateIndividual i q hq).expectedMaximum|<ε := by
  exact (h.updateIndividual i q hq qs (fun m => (hqs m).mono (fun _ hx => hx.1)) hWeak).values_and_maxima
    (fun m => replaceLabeledIndividual_bounded (P m) i (qs m) _ B.cap.property (hCap m)
      ((hqs m).mono (fun _ hx => hx.2))) W C

end ProphetSecretary.Limiting
