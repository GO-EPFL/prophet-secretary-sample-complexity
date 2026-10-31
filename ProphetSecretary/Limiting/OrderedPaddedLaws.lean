import ProphetSecretary.Limiting.FiniteMeasureSubsequence
import ProphetSecretary.Model.Reindex
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Decreasing-mean ordering and zero padding of actual finite marginals

Each finite array is relabeled by an actual permutation, then padded by the
point mass at zero. Its ordered marginal means are nonincreasing, and the
j-th mean is at most S/(j+1). This is the ordering needed in the bounded-first-
moment extraction subcase; it does not replace the paper's general H-only
ordering above a possible positive terminal reserve.
-/
open MeasureTheory Set Filter
open scoped Classical BigOperators Topology
namespace ProphetSecretary.Limiting
variable {n : ℕ}

noncomputable def orderedMeanPermutation (P : Model.Instance n) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => OrderDual.toDual (∫ x, x ∂P.law i))

lemma orderedMeanPermutation_antitone (P : Model.Instance n) :
    Antitone (fun i => ∫ x, x ∂P.law (orderedMeanPermutation P i)) :=
  Tuple.monotone_sort (fun i => OrderDual.toDual (∫ x, x ∂P.law i))

noncomputable def orderedMarginalLaw (P : Model.Instance n) (i : Fin n) : ProbabilityMeasure ℝ :=
  ⟨P.law (orderedMeanPermutation P i),P.probability _⟩

noncomputable def orderedPaddedLaw (P : Model.Instance n) (j : ℕ) : ProbabilityMeasure ℝ :=
  if hj : j < n then orderedMarginalLaw P ⟨j,hj⟩ else ⟨Measure.dirac 0,inferInstance⟩

lemma orderedPaddedLaw_of_lt (P : Model.Instance n) {j : ℕ} (hj : j < n) :
    orderedPaddedLaw P j = orderedMarginalLaw P ⟨j,hj⟩ := dif_pos hj
lemma orderedPaddedLaw_of_ge (P : Model.Instance n) {j : ℕ} (hj : n ≤ j) :
    (orderedPaddedLaw P j : Measure ℝ) = Measure.dirac 0 := by
  simp only [orderedPaddedLaw,dif_neg (not_lt.mpr hj)]
  rfl

lemma orderedPaddedLaw_nonnegative (P : Model.Instance n) (j : ℕ) :
    ∀ᵐ x ∂(orderedPaddedLaw P j : Measure ℝ), 0 ≤ x := by
  by_cases hj : j < n
  · rw [orderedPaddedLaw_of_lt P hj]
    exact P.nonnegative _
  · rw [orderedPaddedLaw_of_ge P (not_lt.mp hj)]
    simp

lemma orderedPaddedLaw_supported_interval (P : Model.Instance n) {H : ℝ} (hH : 0 ≤ H)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) (j : ℕ) :
    (orderedPaddedLaw P j : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0 := by
  apply ae_iff.mp
  by_cases hj : j < n
  · rw [orderedPaddedLaw_of_lt P hj]
    filter_upwards [P.nonnegative (orderedMeanPermutation P ⟨j,hj⟩),hcap (orderedMeanPermutation P ⟨j,hj⟩)] with x hx0 hxH
    exact ⟨hx0,hxH⟩
  · rw [orderedPaddedLaw_of_ge P (not_lt.mp hj)]
    simp [hH]

lemma orderedPaddedLaw_integrable_id (P : Model.Instance n)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (j : ℕ) :
    Integrable (fun x : ℝ => x) (orderedPaddedLaw P j : Measure ℝ) := by
  by_cases hj : j < n
  · rw [orderedPaddedLaw_of_lt P hj]
    exact P.integrable_maximum_iff.mp hP _
  · rw [orderedPaddedLaw_of_ge P (not_lt.mp hj)]
    exact integrable_dirac (a := (0 : ℝ)) (f := fun x : ℝ => x) (by simp)

lemma orderedPaddedMean_nonnegative (P : Model.Instance n) (j : ℕ) :
    0 ≤ ∫ x, x ∂(orderedPaddedLaw P j : Measure ℝ) :=
  integral_nonneg_of_ae (orderedPaddedLaw_nonnegative P j)

lemma orderedPaddedMean_antitone (P : Model.Instance n) :
    Antitone (fun j => ∫ x, x ∂(orderedPaddedLaw P j : Measure ℝ)) := by
  intro i j hij
  change (∫ x, x ∂(orderedPaddedLaw P j : Measure ℝ)) ≤ (∫ x, x ∂(orderedPaddedLaw P i : Measure ℝ))
  by_cases hj : j < n
  · have hi : i < n := lt_of_le_of_lt hij hj
    rw [orderedPaddedLaw_of_lt P hi,orderedPaddedLaw_of_lt P hj]
    exact orderedMeanPermutation_antitone P hij
  · rw [orderedPaddedLaw_of_ge P (not_lt.mp hj)]
    simpa only [integral_dirac] using orderedPaddedMean_nonnegative P i

lemma sum_ordered_marginal_means (P : Model.Instance n) :
    (∑ i : Fin n, ∫ x, x ∂(orderedMarginalLaw P i : Measure ℝ)) = P.totalFirstMoment :=
  Equiv.sum_comp (orderedMeanPermutation P) (fun i => ∫ x, x ∂P.law i)

/-- Exact finite prefix bound before dividing by j+1. -/
lemma ordered_marginal_mean_mul_rank_le (P : Model.Instance n) (i : Fin n) :
    ((i.val+1 : ℕ) : ℝ) * (∫ x, x ∂(orderedMarginalLaw P i : Measure ℝ)) ≤ P.totalFirstMoment := by
  let f : Fin n → ℝ := fun j => ∫ x, x ∂(orderedMarginalLaw P j : Measure ℝ)
  have hanti : Antitone f := orderedMeanPermutation_antitone P
  have hpos (j : Fin n) : 0 ≤ f j := integral_nonneg_of_ae (P.nonnegative _)
  calc
    _ = ∑ _j ∈ Finset.Iic i, f i := by
      change ((i.val+1 : ℕ) : ℝ) * f i = _
      simp [nsmul_eq_mul]
    _ ≤ ∑ j ∈ Finset.Iic i, f j := Finset.sum_le_sum fun j hj => hanti (Finset.mem_Iic.mp hj)
    _ ≤ ∑ j : Fin n, f j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hpos j)
    _ = _ := sum_ordered_marginal_means P

/-- Uniform mean ordering is preserved by the zero padding. -/
theorem orderedPaddedMean_le_total_div_rank (P : Model.Instance n) (j : ℕ) :
    (∫ x, x ∂(orderedPaddedLaw P j : Measure ℝ)) ≤ P.totalFirstMoment / (j+1 : ℕ) := by
  by_cases hj : j < n
  · rw [orderedPaddedLaw_of_lt P hj]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (j+1 : ℕ))).mpr
    have h := ordered_marginal_mean_mul_rank_le P ⟨j,hj⟩
    simpa only [Fin.val_mk,mul_comm] using h
  · rw [orderedPaddedLaw_of_ge P (not_lt.mp hj)]
    rw [integral_dirac]
    exact div_nonneg (Finset.sum_nonneg fun i _ => integral_nonneg_of_ae (P.nonnegative i)) (Nat.cast_nonneg _)

/-- Markov's inequality plus actual variable ordering controls each residual
exceedance probability, without a factor depending on the instance size. -/
theorem orderedPaddedLaw_tail_le (P : Model.Instance n)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) {b : ℝ} (hb : 0 < b) (j : ℕ) :
    (orderedPaddedLaw P j : Measure ℝ).real (Ioi b) ≤ P.totalFirstMoment / (b * (j+1 : ℕ)) := by
  let ν : Measure ℝ := orderedPaddedLaw P j
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := ν) (f := fun x : ℝ => x)
    (orderedPaddedLaw_nonnegative P j) (orderedPaddedLaw_integrable_id P hP j) b
  have hsub : ν.real (Ioi b) ≤ ν.real (Ici b) := measureReal_mono Ioi_subset_Ici_self
  have hmul := (mul_le_mul_of_nonneg_left hsub hb.le).trans hm
  have hprob : ν.real (Ioi b) ≤ (∫ x, x ∂ν) / b := by
    apply (le_div_iff₀ hb).mpr
    simpa only [mul_comm] using hmul
  have hmean := div_le_div_of_nonneg_right (orderedPaddedMean_le_total_div_rank P j) hb.le
  exact hprob.trans (hmean.trans_eq (by ring))

end ProphetSecretary.Limiting
