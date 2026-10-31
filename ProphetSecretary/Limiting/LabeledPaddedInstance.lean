import ProphetSecretary.Limiting.WeightedPaddedInstance
import ProphetSecretary.Model.TerminalBenchmarkReindex
import ProphetSecretary.Model.WeakValueContinuity

/-!
# Finite padded prefixes with arbitrary fixed identity labels

The finite labels are retained in their given order. Coordinates beyond the
actual size have deterministic zero law. Prefix/remainder decompositions
therefore preserve all original identities, and appended zero observations
are handled by the proved causal simulation rather than erased by definition.
-/
open MeasureTheory Set BoundedContinuousFunction
open scoped Classical NNReal
namespace ProphetSecretary.Limiting
variable {n : ℕ}

noncomputable def labeledPaddedLaw (P : Model.Instance n) (j : ℕ) : ProbabilityMeasure ℝ :=
  if hj : j<n then P.marginalProbabilityLaw ⟨j,hj⟩ else ⟨Measure.dirac 0,inferInstance⟩

lemma labeledPaddedLaw_of_lt (P : Model.Instance n) {j : ℕ} (hj : j<n) :
    labeledPaddedLaw P j=P.marginalProbabilityLaw ⟨j,hj⟩ := dif_pos hj

lemma labeledPaddedLaw_of_ge (P : Model.Instance n) {j : ℕ} (hj : n≤j) :
    (labeledPaddedLaw P j : Measure ℝ)=Measure.dirac 0 := by
  simp only [labeledPaddedLaw,dif_neg (not_lt.mpr hj)]
  rfl

lemma labeledPaddedLaw_nonnegative (P : Model.Instance n) (j : ℕ) :
    ∀ᵐ x ∂(labeledPaddedLaw P j : Measure ℝ), 0≤x := by
  by_cases hj : j<n
  · rw [labeledPaddedLaw_of_lt P hj]
    exact P.nonnegative _
  · rw [labeledPaddedLaw_of_ge P (not_lt.mp hj)]
    simp

lemma labeledPaddedLaw_supported (P : Model.Instance n) {H : ℝ} (hH : 0≤H)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤H) (j : ℕ) :
    ∀ᵐ x ∂(labeledPaddedLaw P j : Measure ℝ), x∈Icc (0 : ℝ) H := by
  by_cases hj : j<n
  · rw [labeledPaddedLaw_of_lt P hj]
    filter_upwards [P.nonnegative ⟨j,hj⟩,hcap ⟨j,hj⟩] with x hx hX
    exact ⟨hx,hX⟩
  · rw [labeledPaddedLaw_of_ge P (not_lt.mp hj)]
    simp [hH]

noncomputable def labeledPrefix (P : Model.Instance n) (N : ℕ) : Model.Instance N where
  law i := (labeledPaddedLaw P i.val : Measure ℝ)
  probability i := (labeledPaddedLaw P i.val).prop
  nonnegative i := labeledPaddedLaw_nonnegative P i.val

noncomputable def labeledRemainder (P : Model.Instance n) (N : ℕ) : Model.Instance n where
  law i := (labeledPaddedLaw P (N+i.val) : Measure ℝ)
  probability i := (labeledPaddedLaw P (N+i.val)).prop
  nonnegative i := labeledPaddedLaw_nonnegative P (N+i.val)

lemma labeledPrefix_bounded (P : Model.Instance n) (N : ℕ) {H : ℝ} (hH : 0≤H)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤H) :
    ∀ i, ∀ᵐ x ∂(labeledPrefix P N).law i, x≤H :=
  fun i => (labeledPaddedLaw_supported P hH hcap i.val).mono (fun _ hx => hx.2)

lemma labeledRemainder_bounded (P : Model.Instance n) (N : ℕ) {H : ℝ} (hH : 0≤H)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤H) :
    ∀ i, ∀ᵐ x ∂(labeledRemainder P N).law i, x≤H :=
  fun i => (labeledPaddedLaw_supported P hH hcap (N+i.val)).mono (fun _ hx => hx.2)

lemma labeledPrefix_append_remainder (P : Model.Instance n) (N : ℕ) :
    (labeledPrefix P N).appendIndependent (labeledRemainder P N)=labeledPrefix P (N+n) := by
  apply Model.Instance.eq_of_law_eq
  funext i
  induction i using Fin.addCases <;>
    simp only [Model.Instance.appendIndependent,Fin.addCases_left,Fin.addCases_right,
      labeledPrefix,labeledRemainder,Fin.val_castAdd,Fin.val_natAdd]

lemma labeledPrefix_full_law (P : Model.Instance n) (N : ℕ) (i : Fin (n+N)) :
    (P.appendZeros N).law i=(labeledPrefix P (N+n)).law ((finCongr (Nat.add_comm n N)) i) := by
  induction i using Fin.addCases with
  | left i =>
    simp only [Model.Instance.appendZeros,Fin.addCases_left,labeledPrefix]
    change P.law i=(labeledPaddedLaw P i.val : Measure ℝ)
    rw [labeledPaddedLaw_of_lt P i.isLt]
    rfl
  | right j =>
    simp only [Model.Instance.appendZeros,Fin.addCases_right,labeledPrefix]
    change Measure.dirac (0 : ℝ)=(labeledPaddedLaw P (n+j.val) : Measure ℝ)
    exact (labeledPaddedLaw_of_ge P (by omega)).symm

lemma labeledPrefix_full_terminal_value (P : Model.Instance n) (N : ℕ)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) {a w c : ℝ}
    (ha : 0≤a) (hw : 0≤w) (hc : 0≤c) :
    Model.optimalTerminalScalarValue (labeledPrefix P (N+n)) a w c=
      Model.optimalTerminalScalarValue P a w c := by
  have hS := P.appendZeros_integrable_maximum N hP
  have he := (P.appendZeros N).optimalTerminalScalarValue_eq_of_law_equiv
    (labeledPrefix P (N+n)) (finCongr (Nat.add_comm N n))
    (fun i => by
      have h := labeledPrefix_full_law P N ((finCongr (Nat.add_comm N n)) i)
      have hcast : (finCongr (Nat.add_comm n N)) ((finCongr (Nat.add_comm N n)) i)=i := by apply Fin.ext; rfl
      rw [hcast] at h
      exact h.symm) hS ha hw hc
  exact he.trans (P.optimalTerminalScalarValue_appendZeros N hP ha hw hc)

lemma labeledPrefix_full_terminal_benchmark (P : Model.Instance n) (N : ℕ)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) {a : ℝ} (ha : 0≤a) :
    (labeledPrefix P (N+n)).expectedTerminalMaximum a=P.expectedTerminalMaximum a := by
  have hS := P.appendZeros_integrable_maximum N hP
  have he := (P.appendZeros N).expectedTerminalMaximum_eq_of_law_equiv
    (labeledPrefix P (N+n)) (finCongr (Nat.add_comm N n))
    (fun i => by
      have h := labeledPrefix_full_law P N ((finCongr (Nat.add_comm N n)) i)
      have hcast : (finCongr (Nat.add_comm n N)) ((finCongr (Nat.add_comm N n)) i)=i := by apply Fin.ext; rfl
      rw [hcast] at h
      exact h.symm) hS ha
  exact he.trans (P.expectedTerminalMaximum_appendZeros N hP ha)

lemma labeledPaddedLaw_weightOrdered (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ) (j : ℕ) :
    labeledPaddedLaw (P.restrictBy (weightedMeanPermutation P wgt).toEmbedding) j=
      weightOrderedPaddedLaw P wgt j := by
  by_cases hj : j<n
  · rw [labeledPaddedLaw_of_lt _ hj,weightOrderedPaddedLaw_of_lt P wgt hj]
    rfl
  · apply ProbabilityMeasure.toMeasure_injective
    rw [labeledPaddedLaw_of_ge _ (not_lt.mp hj),weightOrderedPaddedLaw_of_ge P wgt (not_lt.mp hj)]

end ProphetSecretary.Limiting
