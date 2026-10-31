import ProphetSecretary.Limiting.WeightedResidualScore
import ProphetSecretary.Limiting.WeightedCoarseScore
import ProphetSecretary.Limiting.FiniteShiftedSum
import ProphetSecretary.Limiting.OrderedResidualTailSup

/-!
# Original residual likelihood scores equal the coarse score pullback

The identity is of complete analytical value vectors. Zero padding contributes
zero score on its actual zero value, and a finite shifted-sum identity keeps
exactly the original coordinates outside the retained prefix.
-/
open MeasureTheory Set BoundedContinuousFunction
open scoped Classical BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n K : ℕ}

noncomputable def weightedPaddedValue (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ)
    (x : Fin n → ℝ) (j : ℕ) : ℝ :=
  if hj : j<n then x (weightedMeanPermutation P wgt ⟨j,hj⟩) else 0

lemma appendOrderedValues_eq_weightedPaddedValue (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ)
    (N : ℕ) (x : Fin n → ℝ) (k : Fin (n+N)) :
    Model.ZeroSimulation.appendValues (x ∘ weightedMeanPermutation P wgt) k=weightedPaddedValue P wgt x k.val := by
  induction k using Fin.addCases with
  | left i => simp [Model.ZeroSimulation.appendValues,weightedPaddedValue,Fin.addCases_left,i.isLt,Function.comp_def]
  | right j =>
    have hj : ¬n+j.val<n := by omega
    simp [Model.ZeroSimulation.appendValues,weightedPaddedValue,Fin.addCases_right,hj]

lemma weightedResidualScore_completeScore_eq_filter (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ)
    (N : ℕ) (B : Set ℝ) (x : Fin n → ℝ) :
    completeScore (weightedResidualScore P wgt N B) x=
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => N ≤ i.val),
        compensatedBandScore (P.law (weightedMeanPermutation P wgt i)) B (x (weightedMeanPermutation P wgt i)) := by
  let f := fun i : Fin n => weightedResidualScore P wgt N B i (x i)
  change (∑ i, f i)=_
  rw [← Equiv.sum_comp (weightedMeanPermutation P wgt) f]
  simp only [f,weightedResidualScore,Equiv.symm_apply_apply,Finset.sum_filter]

lemma compensatedBandScore_dirac_zero_value {B : Set ℝ} (hB : MeasurableSet B) (hB0 : (0:ℝ)∉B) :
    compensatedBandScore (Measure.dirac 0) B 0=0 := by
  rw [compensatedBandScore_of_notMem _ hB0]
  simp [Measure.real,Measure.dirac_apply' _ hB,Set.indicator,hB0]

lemma weightedCoarseScore_residual_eq_completeScore (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ)
    (N : ℕ) (hKN : K ≤ N) {B : Set ℝ} (hB : MeasurableSet B) (hB0 : (0:ℝ)∉B) (x : Fin n → ℝ) :
    weightedCoarseScore P wgt N hKN
      (fun y : Fin (K+n) → ℝ => completeScore
        (fun j : Fin n => compensatedBandScore ((weightOrderedRemainder P wgt N).law j) B)
        (fun j => y (j.natAdd K))) x = completeScore (weightedResidualScore P wgt N B) x := by
  let f := fun j : ℕ => compensatedBandScore (weightOrderedPaddedLaw P wgt j:Measure ℝ) B
    (weightedPaddedValue P wgt x j)
  have hf (j : ℕ) (hj : n ≤ j) : f j=0 := by
    dsimp [f]
    rw [weightOrderedPaddedLaw_of_ge P wgt hj]
    have hval : weightedPaddedValue P wgt x j=0 := by simp [weightedPaddedValue,not_lt.mpr hj]
    rw [hval]
    exact compensatedBandScore_dirac_zero_value hB hB0
  have hF (i : Fin n) : f i.val=
      compensatedBandScore (P.law (weightedMeanPermutation P wgt i)) B (x (weightedMeanPermutation P wgt i)) := by
    dsimp [f]
    rw [weightOrderedPaddedLaw_of_lt P wgt i.isLt]
    simp only [weightedPaddedValue,dif_pos i.isLt]
    rfl
  calc
    _ = ∑ j : Fin n, f (N+j.val) := by
      unfold weightedCoarseScore completeScore
      apply Finset.sum_congr rfl
      intro j _
      change compensatedBandScore ((weightOrderedRemainder P wgt N).law j) B
        (Model.ZeroSimulation.appendValues (x ∘ weightedMeanPermutation P wgt)
          (weightedCoarseEmbedding n K N hKN (j.natAdd K)))=f (N+j.val)
      rw [appendOrderedValues_eq_weightedPaddedValue,weightedCoarseEmbedding_right]
      rfl
    _ = ∑ i ∈ Finset.univ.filter (fun i : Fin n => N ≤ i.val), f i.val := shifted_fin_sum_eq_filtered f n N hf
    _ = _ := by
      rw [weightedResidualScore_completeScore_eq_filter]
      apply Finset.sum_congr rfl
      intro i _
      exact hF i

lemma weightedResidualScore_half_of_sup (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ) (N : ℕ)
    {B : Set ℝ} {b : ℝ} (hAbove : B⊆Ioi b)
    (hSup : residualTailSup (fun j => weightOrderedPaddedLaw P wgt j) N b≤1/2) :
    ∀ i, N ≤ ((weightedMeanPermutation P wgt).symm i).val → (P.law i).real B≤1/2 := by
  intro i hi
  let j := (weightedMeanPermutation P wgt).symm i
  have hLaw : (weightOrderedPaddedLaw P wgt j.val:Measure ℝ)=P.law i := by
    rw [weightOrderedPaddedLaw_of_lt P wgt j.isLt]
    change P.law (weightedMeanPermutation P wgt j)=P.law i
    rw [Equiv.apply_symm_apply]
  have hTail := tail_le_residualTailSup (fun j => weightOrderedPaddedLaw P wgt j) N b j.val hi
  rw [hLaw] at hTail
  exact (measureReal_mono (μ := P.law i) hAbove).trans (hTail.trans hSup)
end ProphetSecretary.Limiting
