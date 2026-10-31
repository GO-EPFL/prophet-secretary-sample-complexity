import ProphetSecretary.Statistics.ResidualComparison
import ProphetSecretary.Model.BellmanResidualPath

/-!
# Residual suffixes after an observed prefix

Every future suffix, including the full future sum, is a suffix of the original
complete path. The actual Bellman transition residual transports along the
continuation construction, so the comparison applies to unrestricted policies'
residual identities without a Markov-policy restriction.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Statistics

variable {n : ℕ}

lemma abs_futureSum_le_suffixEnvelope (u ξ : Fin n → ℝ) (t : ℝ) :
    |∑ i, if t < u i then ξ i else 0| ≤ suffixEnvelope u ξ := by
  let F := Finset.univ.filter fun i => t < u i
  by_cases hF : F.Nonempty
  · obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image F u hF
    have hjt : t < u j := (Finset.mem_filter.mp hj).2
    have hiff (i : Fin n) : t < u i ↔ u j ≤ u i := by
      constructor
      · intro hi
        exact hmin i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
      · exact fun hi => hjt.trans_le hi
    simpa only [hiff, suffixSum] using le_suffixEnvelope u ξ (some j)
  · have he : (∑ i, if t < u i then ξ i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      have hi : ¬ t < u i := fun hi => hF ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
      simp only [hi, ite_false]
    rw [he, abs_zero]
    exact suffixEnvelope_nonnegative _ _

end ProphetSecretary.Statistics

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma sum_stateEmbedding_futureSuffix (A : Finset (Fin n)) (f : Fin n → ℝ) :
    (∑ j : Fin A.card, f (stateEmbedding A j)) = ∑ i ∈ A, f i := by
  have hmap : Finset.univ.map (stateEmbedding A) = A := A.map_orderEmbOfFin_univ rfl
  have he : (∑ i ∈ Finset.univ.map (stateEmbedding A), f i) = ∑ j : Fin A.card, f (stateEmbedding A j) := by
    rw [Finset.sum_map]
  rw [hmap] at he
  exact he.symm

lemma extendClocks_past_le (A : Finset (Fin n)) {s : ℝ} (H : History n)
    (hH : ValidPrefix A s H) (v : Fin A.card → ℝ) (i : Fin n) (hi : i ∉ A) :
    extendClocks A s H v i ≤ s := by
  obtain ⟨t, x, he, ht⟩ := hH.2 i hi
  simpa [extendClocks, hi, he, observationTime] using ht

lemma extendClocks_future_gt (A : Finset (Fin n)) {s : ℝ} (hs : s < 1) (H : History n)
    (v : Fin A.card → ℝ) (j : Fin A.card) (hj : 0 < v j) :
    s < extendClocks A s H v (stateEmbedding A j) := by
  rw [extendClocks_stateEmbedding]
  nlinarith [mul_pos (sub_pos.mpr hs) hj]

/-- Pure finite suffix comparison for a continuation path. Past observations may
have zero values or timestamps equal to the prefix time. -/
lemma suffixEnvelope_extended_path_le (A : Finset (Fin n)) {s : ℝ} (hs : s < 1)
    (H : History n) (hH : ValidPrefix A s H) (v : Fin A.card → ℝ) (hv : ∀ j, 0 < v j)
    (ξ : Fin n → ℝ) (η : Fin A.card → ℝ) (hξη : ∀ j, ξ (stateEmbedding A j) = η j) :
    ProphetSecretary.Statistics.suffixEnvelope v η ≤
      ProphetSecretary.Statistics.suffixEnvelope (extendClocks A s H v) ξ := by
  let u := extendClocks A s H v
  have htail (j : Fin A.card) : ProphetSecretary.Statistics.suffixSum v η (some j) =
      ProphetSecretary.Statistics.suffixSum u ξ (some (stateEmbedding A j)) := by
    have hdrop : (∑ i ∈ A, if u (stateEmbedding A j) ≤ u i then ξ i else 0) =
        ∑ i : Fin n, if u (stateEmbedding A j) ≤ u i then ξ i else 0 := by
      apply Finset.sum_subset (Finset.subset_univ A)
      intro i _ hi
      have hp : u i ≤ s := extendClocks_past_le A H hH v i hi
      have hf : s < u (stateEmbedding A j) := extendClocks_future_gt A hs H v j (hv j)
      simp only [show ¬ u (stateEmbedding A j) ≤ u i by linarith, ite_false]
    simp only [ProphetSecretary.Statistics.suffixSum]
    rw [← hdrop, ← sum_stateEmbedding_futureSuffix A (fun i => if u (stateEmbedding A j) ≤ u i then ξ i else 0)]
    apply Finset.sum_congr rfl
    intro k _
    have hiff : u (stateEmbedding A j) ≤ u (stateEmbedding A k) ↔ v j ≤ v k := by
      dsimp [u]
      rw [extendClocks_stateEmbedding, extendClocks_stateEmbedding]
      constructor <;> intro h
      · nlinarith [sub_pos.mpr hs]
      · nlinarith [sub_pos.mpr hs]
    simp only [hiff, hξη]
  have hfull : (∑ j : Fin A.card, η j) = ∑ i : Fin n, if s < u i then ξ i else 0 := by
    have hdrop : (∑ i ∈ A, if s < u i then ξ i else 0) = ∑ i : Fin n, if s < u i then ξ i else 0 := by
      apply Finset.sum_subset (Finset.subset_univ A)
      intro i _ hi
      exact if_neg (not_lt_of_ge (show u i ≤ s from extendClocks_past_le A H hH v i hi))
    rw [← hdrop, ← sum_stateEmbedding_futureSuffix A (fun i => if s < u i then ξ i else 0)]
    apply Finset.sum_congr rfl
    intro j _
    rw [if_pos (show s < u (stateEmbedding A j) from extendClocks_future_gt A hs H v j (hv j)), hξη]
  apply Finset.sup'_le
  intro j _
  cases j with
  | none =>
    change |∑ j : Fin A.card, η j| ≤ _
    rw [hfull]
    exact ProphetSecretary.Statistics.abs_futureSum_le_suffixEnvelope u ξ s
  | some j =>
    rw [htail]
    exact ProphetSecretary.Statistics.le_suffixEnvelope _ _ _

/-- The actual Bellman residual's future envelope is dominated by its original
complete-path envelope, with no loss in the constant. -/
theorem Instance.residualSuffixEnvelope_continuation_le (Q P : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (A : Finset (Fin n))
    {s : ℝ} (hs : s < 1) (H : History n) (hH : ValidPrefix A s H)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (v : Fin A.card → ℝ) (hv : ∀ j, 0 < v j) :
    (Q.restrictTo A).residualSuffixEnvelope (P.restrictTo A) w (c * (1 - s)) v ≤
      Q.residualSuffixEnvelope P w c (extendClocks A s H v) := by
  apply suffixEnvelope_extended_path_le A hs H hH v hv
  intro j
  exact Q.transitionResidual_extend P hQ A hs H hH hw hc (fun _ => 0) v j (hv j)

end ProphetSecretary.Model
