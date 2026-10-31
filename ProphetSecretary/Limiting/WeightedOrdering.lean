import ProphetSecretary.Limiting.ContinuousWeightedMeasure
import ProphetSecretary.Model.Reindex
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Actual ordering by an arbitrary nonnegative continuous weight

The input variables are permuted by their expected continuous weight and
padded by zero laws. A weight vanishing at zero preserves the decreasing
ordering under padding. This generalizes decreasing-mean ordering to the
H-only compact-extraction case with a possible positive terminal reserve.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical BigOperators Topology
namespace ProphetSecretary.Limiting
variable {n : ℕ}

noncomputable def weightedMeanPermutation (P : Model.Instance n) (w : ℝ →ᵇ ℝ) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => OrderDual.toDual (∫ x, w x ∂P.law i))

lemma weightedMeanPermutation_antitone (P : Model.Instance n) (w : ℝ →ᵇ ℝ) :
    Antitone (fun i => ∫ x, w x ∂P.law (weightedMeanPermutation P w i)) :=
  Tuple.monotone_sort (fun i => OrderDual.toDual (∫ x, w x ∂P.law i))

noncomputable def weightOrderedMarginalLaw (P : Model.Instance n) (w : ℝ →ᵇ ℝ) (i : Fin n) : ProbabilityMeasure ℝ :=
  ⟨P.law (weightedMeanPermutation P w i),P.probability _⟩

noncomputable def weightOrderedPaddedLaw (P : Model.Instance n) (w : ℝ →ᵇ ℝ) (j : ℕ) : ProbabilityMeasure ℝ :=
  if hj : j < n then weightOrderedMarginalLaw P w ⟨j,hj⟩ else ⟨Measure.dirac 0,inferInstance⟩

lemma weightOrderedPaddedLaw_of_lt (P : Model.Instance n) (w : ℝ →ᵇ ℝ) {j : ℕ} (hj : j < n) :
    weightOrderedPaddedLaw P w j = weightOrderedMarginalLaw P w ⟨j,hj⟩ := dif_pos hj
lemma weightOrderedPaddedLaw_of_ge (P : Model.Instance n) (w : ℝ →ᵇ ℝ) {j : ℕ} (hj : n ≤ j) :
    (weightOrderedPaddedLaw P w j : Measure ℝ) = Measure.dirac 0 := by
  simp only [weightOrderedPaddedLaw,dif_neg (not_lt.mpr hj)]
  rfl

lemma weightOrderedPaddedLaw_nonnegative (P : Model.Instance n) (w : ℝ →ᵇ ℝ) (j : ℕ) :
    ∀ᵐ x ∂(weightOrderedPaddedLaw P w j : Measure ℝ), 0 ≤ x := by
  by_cases hj : j < n
  · rw [weightOrderedPaddedLaw_of_lt P w hj]
    exact P.nonnegative _
  · rw [weightOrderedPaddedLaw_of_ge P w (not_lt.mp hj)]
    simp

lemma weightOrderedPaddedLaw_supported_interval (P : Model.Instance n) (w : ℝ →ᵇ ℝ) {H : ℝ} (hH : 0 ≤ H)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) (j : ℕ) :
    (weightOrderedPaddedLaw P w j : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0 := by
  apply ae_iff.mp
  by_cases hj : j < n
  · rw [weightOrderedPaddedLaw_of_lt P w hj]
    filter_upwards [P.nonnegative (weightedMeanPermutation P w ⟨j,hj⟩),hcap (weightedMeanPermutation P w ⟨j,hj⟩)] with x hx0 hxH
    exact ⟨hx0,hxH⟩
  · rw [weightOrderedPaddedLaw_of_ge P w (not_lt.mp hj)]
    simp [hH]

lemma weightOrderedScore_nonnegative (P : Model.Instance n) (w : ℝ →ᵇ ℝ) (hw : ∀ x, 0 ≤ w x) (j : ℕ) :
    0 ≤ ∫ x, w x ∂(weightOrderedPaddedLaw P w j : Measure ℝ) :=
  integral_nonneg hw

lemma weightOrderedScore_antitone (P : Model.Instance n) (w : ℝ →ᵇ ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw0 : w 0 = 0) :
    Antitone (fun j => ∫ x, w x ∂(weightOrderedPaddedLaw P w j : Measure ℝ)) := by
  intro i j hij
  change (∫ x, w x ∂(weightOrderedPaddedLaw P w j : Measure ℝ)) ≤ (∫ x, w x ∂(weightOrderedPaddedLaw P w i : Measure ℝ))
  by_cases hj : j < n
  · have hi : i < n := lt_of_le_of_lt hij hj
    rw [weightOrderedPaddedLaw_of_lt P w hi,weightOrderedPaddedLaw_of_lt P w hj]
    exact weightedMeanPermutation_antitone P w hij
  · rw [weightOrderedPaddedLaw_of_ge P w (not_lt.mp hj)]
    simpa only [integral_dirac,hw0] using weightOrderedScore_nonnegative P w hw i

lemma sum_weightOrdered_scores (P : Model.Instance n) (w : ℝ →ᵇ ℝ) :
    (∑ i : Fin n, ∫ x, w x ∂(weightOrderedMarginalLaw P w i : Measure ℝ)) = (∑ i, ∫ x, w x ∂P.law i) :=
  Equiv.sum_comp (weightedMeanPermutation P w) (fun i => ∫ x, w x ∂P.law i)

/-- Exact finite prefix bound before dividing by j+1. -/
lemma weightOrdered_score_mul_rank_le (P : Model.Instance n) (w : ℝ →ᵇ ℝ)
    (hw : ∀ x, 0 ≤ w x) (i : Fin n) :
    ((i.val+1 : ℕ) : ℝ) * (∫ x, w x ∂(weightOrderedMarginalLaw P w i : Measure ℝ)) ≤ (∑ i, ∫ x, w x ∂P.law i) := by
  let f : Fin n → ℝ := fun j => ∫ x, w x ∂(weightOrderedMarginalLaw P w j : Measure ℝ)
  have hanti : Antitone f := weightedMeanPermutation_antitone P w
  have hpos (j : Fin n) : 0 ≤ f j := integral_nonneg hw
  calc
    _ = ∑ _j ∈ Finset.Iic i, f i := by
      change ((i.val+1 : ℕ) : ℝ) * f i = _
      simp [nsmul_eq_mul]
    _ ≤ ∑ j ∈ Finset.Iic i, f j := Finset.sum_le_sum fun j hj => hanti (Finset.mem_Iic.mp hj)
    _ ≤ ∑ j : Fin n, f j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hpos j)
    _ = _ := sum_weightOrdered_scores P w

/-- Uniform mean ordering is preserved by the zero padding. -/
theorem weightOrderedScore_le_total_div_rank (P : Model.Instance n) (w : ℝ →ᵇ ℝ)
    (hw : ∀ x, 0 ≤ w x) (hw0 : w 0 = 0) (j : ℕ) :
    (∫ x, w x ∂(weightOrderedPaddedLaw P w j : Measure ℝ)) ≤ (∑ i, ∫ x, w x ∂P.law i) / (j+1 : ℕ) := by
  by_cases hj : j < n
  · rw [weightOrderedPaddedLaw_of_lt P w hj]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (j+1 : ℕ))).mpr
    have h := weightOrdered_score_mul_rank_le P w hw ⟨j,hj⟩
    simpa only [Fin.val_mk,mul_comm] using h
  · rw [weightOrderedPaddedLaw_of_ge P w (not_lt.mp hj)]
    rw [integral_dirac,hw0]
    exact div_nonneg (Finset.sum_nonneg fun i _ => integral_nonneg hw) (Nat.cast_nonneg _)


end ProphetSecretary.Limiting
