import ProphetSecretary.Limiting.ValueWeightedMeasure
import ProphetSecretary.Limiting.OrderedPaddedLaws

/-!
# Actual value-weighted residual measures of an ordered finite instance

After an actual decreasing-mean permutation, the residual after N retained
identities is a positive finite sum of value-weighted marginal laws. Its mass
is at most S and its support remains in the original cap interval. Increasing
N removes exactly the next padded individual law, including the padded-zero
case. These are constructed input measures for weak compact extraction.
-/
open MeasureTheory Set Filter
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Limiting
variable {n : ℕ}

private lemma finiteMeasure_mass_finsetSum {ι : Type*} (s : Finset ι) (f : ι → FiniteMeasure ℝ) :
    (∑ i ∈ s, f i).mass = ∑ i ∈ s, (f i).mass := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    have hadd := congrFun (FiniteMeasure.coeFn_add (f i) (∑ j ∈ s, f j)) Set.univ
    change (f i + ∑ j ∈ s, f j).mass = (f i).mass + ∑ j ∈ s, (f j).mass
    exact hadd.trans (congrArg (fun a => (f i).mass + a) ih)

lemma orderedMarginalLaw_supported_interval (P : Model.Instance n) {H : ℝ} (hH : 0 ≤ H)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) (i : Fin n) :
    (orderedMarginalLaw P i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0 := by
  have h := orderedPaddedLaw_supported_interval P hH hcap i.val
  rw [orderedPaddedLaw_of_lt P i.isLt] at h
  exact h

noncomputable def orderedWeightedResidual (P : Model.Instance n) (H : ℝ≥0) (N : ℕ) : FiniteMeasure ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => N ≤ i.val), valueWeightedLaw (orderedMarginalLaw P i) H

lemma orderedWeightedResidual_mass_le_total (P : Model.Instance n) (H : ℝ≥0)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) (N : ℕ) :
    ((orderedWeightedResidual P H N).mass : ℝ) ≤ P.totalFirstMoment := by
  unfold orderedWeightedResidual
  rw [finiteMeasure_mass_finsetSum,NNReal.coe_sum]
  have hmean (i : Fin n) : ((valueWeightedLaw (orderedMarginalLaw P i) H).mass : ℝ) =
      ∫ x, x ∂(orderedMarginalLaw P i : Measure ℝ) :=
    valueWeightedLaw_mass_eq_mean _ H (ae_iff.mpr (orderedMarginalLaw_supported_interval P H.coe_nonneg hcap i))
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i : Fin n => N ≤ i.val), ∫ x, x ∂(orderedMarginalLaw P i : Measure ℝ) :=
      Finset.sum_congr rfl (fun i _ => hmean i)
    _ ≤ ∑ i : Fin n, ∫ x, x ∂(orderedMarginalLaw P i : Measure ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun i _ _ => integral_nonneg_of_ae (P.nonnegative _))
    _ = _ := sum_ordered_marginal_means P

lemma orderedWeightedResidual_mass_le (P : Model.Instance n) (H S₀ : ℝ≥0)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) (hS : P.totalFirstMoment ≤ (S₀ : ℝ)) (N : ℕ) :
    (orderedWeightedResidual P H N).mass ≤ S₀ := by
  change ((orderedWeightedResidual P H N).mass : ℝ) ≤ (S₀ : ℝ)
  exact (orderedWeightedResidual_mass_le_total P H hcap N).trans hS

lemma orderedWeightedResidual_supported_interval (P : Model.Instance n) (H : ℝ≥0)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ)) (N : ℕ) :
    (orderedWeightedResidual P H N : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0 := by
  unfold orderedWeightedResidual
  rw [FiniteMeasure.toMeasure_sum,Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  exact valueWeightedLaw_supported_interval _ H (orderedMarginalLaw_supported_interval P H.coe_nonneg hcap i)

lemma valueWeightedLaw_dirac_zero (H : ℝ≥0) :
    valueWeightedLaw (⟨Measure.dirac 0,inferInstance⟩ : ProbabilityMeasure ℝ) H = 0 := by
  apply (FiniteMeasure.mass_zero_iff _).mp
  have h := valueWeightedLaw_mass (⟨Measure.dirac 0,inferInstance⟩ : ProbabilityMeasure ℝ) H
  change _ = (∫ x, ProphetSecretary.Probability.boundedOfferValue H x ∂Measure.dirac (0 : ℝ)) at h
  rw [integral_dirac] at h
  have hv : ProphetSecretary.Probability.boundedOfferValue H 0 = 0 :=
    ProphetSecretary.Probability.boundedOfferValue_eq H ⟨le_rfl,H.coe_nonneg⟩
  rw [hv] at h
  exact_mod_cast h

/-- Exact finite-prefix subtraction, including residuals beyond the actual
instance size. It is an identity of constructed positive finite measures. -/
theorem orderedWeightedResidual_succ (P : Model.Instance n) (H : ℝ≥0) (N : ℕ) :
    orderedWeightedResidual P H N = valueWeightedLaw (orderedPaddedLaw P N) H + orderedWeightedResidual P H (N+1) := by
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
    unfold orderedWeightedResidual
    rw [hset,Finset.sum_insert hnot,orderedPaddedLaw_of_lt P hN]
  · have hzero (M : ℕ) (hNM : N ≤ M) : Finset.univ.filter (fun i : Fin n => M ≤ i.val) = ∅ := by
      ext i
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      have hnot : ¬M ≤ i.val := by
        have hi := i.isLt
        omega
      simp [hnot]
    have hpad : orderedPaddedLaw P N = (⟨Measure.dirac 0,inferInstance⟩ : ProbabilityMeasure ℝ) := dif_neg hN
    rw [hpad,valueWeightedLaw_dirac_zero]
    simp only [orderedWeightedResidual,hzero N le_rfl,hzero (N+1) (by omega),Finset.sum_empty,zero_add]

end ProphetSecretary.Limiting
