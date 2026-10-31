import ProphetSecretary.Limiting.WeightedOrdering

/-!
# Continuous-weight residuals after actual finite marginal ordering

Positive finite residuals remove exactly one weighted padded marginal at each
step. Their mass is bounded by the actual aggregate expected weight.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal BigOperators Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

private lemma mass_finsetSum {ι : Type*} (s : Finset ι) (f : ι → FiniteMeasure ℝ) :
    (∑ i ∈ s, f i).mass = ∑ i ∈ s, (f i).mass := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    have hadd := congrFun (FiniteMeasure.coeFn_add (f i) (∑ j ∈ s, f j)) Set.univ
    change (f i + ∑ j ∈ s, f j).mass = (f i).mass + ∑ j ∈ s, (f j).mass
    exact hadd.trans (congrArg (fun a => (f i).mass + a) ih)

noncomputable def weightOrderedResidual (P : Model.Instance n) (w : ℝ →ᵇ ℝ) (N : ℕ) : FiniteMeasure ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => N ≤ i.val), continuousWeightedLaw (weightOrderedMarginalLaw P w i) w

lemma weightOrderedResidual_mass_le_total (P : Model.Instance n) (w : ℝ →ᵇ ℝ)
    (hw : ∀ x, 0 ≤ w x) (N : ℕ) :
    ((weightOrderedResidual P w N).mass : ℝ) ≤ ∑ i, ∫ x, w x ∂P.law i := by
  unfold weightOrderedResidual
  rw [mass_finsetSum,NNReal.coe_sum]
  simp_rw [continuousWeightedLaw_mass _ w hw]
  exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _ => integral_nonneg hw)).trans_eq (sum_weightOrdered_scores P w)

lemma weightOrderedResidual_supported_interval (P : Model.Instance n) (w : ℝ →ᵇ ℝ)
    {H : ℝ} (hH : 0 ≤ H) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) (N : ℕ) :
    (weightOrderedResidual P w N : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0 := by
  unfold weightOrderedResidual
  rw [FiniteMeasure.toMeasure_sum,Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  have h := weightOrderedPaddedLaw_supported_interval P w hH hcap i.val
  rw [weightOrderedPaddedLaw_of_lt P w i.isLt] at h
  exact continuousWeightedLaw_supported_interval _ w h

/-- Exact finite-prefix subtraction, including residuals beyond the actual
instance size. It is an identity of constructed positive finite measures. -/
theorem weightOrderedResidual_succ (P : Model.Instance n) (w : ℝ →ᵇ ℝ) (hw : ∀ x, 0 ≤ w x) (hw0 : w 0 = 0) (N : ℕ) :
    weightOrderedResidual P w N = continuousWeightedLaw (weightOrderedPaddedLaw P w N) w + weightOrderedResidual P w (N+1) := by
  by_cases hN : N < n
  · let k : Fin n := ⟨N,hN⟩
    have hset : Finset.univ.filter (fun i : Fin n => N ≤ i.val) =
        insert k (Finset.univ.filter (fun i : Fin n => N+1 ≤ i.val)) := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
      constructor
      · intro hi
        by_cases hie : i.val = N
        · exact Or.inl (Fin.ext hie)
        · exact Or.inr (by omega)
      · rintro (rfl | hi)
        · exact le_rfl
        · omega
    have hnot : k ∉ Finset.univ.filter (fun i : Fin n => N+1 ≤ i.val) := by simp [k]
    unfold weightOrderedResidual
    rw [hset,Finset.sum_insert hnot,weightOrderedPaddedLaw_of_lt P w hN]
  · have hzero (M : ℕ) (hNM : N ≤ M) : Finset.univ.filter (fun i : Fin n => M ≤ i.val) = ∅ := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      have hnot : ¬M ≤ i.val := by
        have hi := i.isLt
        omega
      simp [hnot]
    have hpad : weightOrderedPaddedLaw P w N = (⟨Measure.dirac 0,inferInstance⟩ : ProbabilityMeasure ℝ) := dif_neg hN
    rw [hpad,continuousWeightedLaw_dirac_zero w hw hw0]
    simp only [weightOrderedResidual,hzero N le_rfl,hzero (N+1) (by omega),Finset.sum_empty,zero_add]

end ProphetSecretary.Limiting
