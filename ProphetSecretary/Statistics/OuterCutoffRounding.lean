import ProphetSecretary.Statistics.OuterMarkRounding
import ProphetSecretary.Statistics.OuterCutoffProgram

/-!
# The actual outer cutoff under mark rounding

Rounding the second coordinate is monotone for the tagged order. It commutes
with the training maximum and cutoff minimum. The cutoff is one of the
reserved training observations, so every retention comparison is unchanged
off the single collision event.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability

noncomputable def roundTaggedValue (N : ℕ) (hN : 0 < N) (z : TaggedValue) : TaggedValue :=
  toLex ((ofLex z).1, uniformGridRound N hN (ofLex z).2)

lemma monotone_roundTaggedValue (N : ℕ) (hN : 0 < N) : Monotone (roundTaggedValue N hN) := by
  intro x y h
  rw [Prod.Lex.le_iff] at h ⊢
  rcases h with h | ⟨h₁,h₂⟩
  · exact Or.inl h
  · exact Or.inr ⟨h₁,monotone_uniformGridRound N hN h₂⟩

lemma outerTaggedMaximum_rounding {n : ℕ} (hn : 0 < n) (N : ℕ) (hN : 0 < N)
    (z : Fin n → ℝ × ℝ) :
    outerTaggedMaximum hn (fun i => ((z i).1, uniformGridRound N hN (z i).2)) =
      roundTaggedValue N hN (outerTaggedMaximum hn z) := by
  exact (Finset.apply_sup'_eq_sup'_comp (outerOfferIndices_nonempty hn) (roundTaggedValue N hN)
    (fun x y => (monotone_roundTaggedValue N hN).map_sup x y)).symm

lemma outerCutoffTaggedRows_rounding {n : ℕ} (hn : 0 < n) (m : ℕ) (hm : 1 ≤ m)
    (N : ℕ) (hN : 0 < N) (z : Fin m → Fin n → ℝ × ℝ) :
    outerCutoffTaggedRows m hm (fun r i => ((z r i).1, uniformGridRound N hN (z r i).2)) =
      roundTaggedValue N hN (outerCutoffTaggedRows m hm z) := by
  simp only [outerCutoffTaggedRows, dif_pos hn, outerTaggedMaximum_rounding]
  exact (Finset.apply_inf'_eq_inf'_comp (outerOfferIndices_nonempty (show 0 < m by omega))
    (roundTaggedValue N hN) (fun x y => (monotone_roundTaggedValue N hN).map_inf x y)).symm

lemma outerCutoffTaggedRows_is_observation {n : ℕ} (hn : 0 < n) (m : ℕ) (hm : 1 ≤ m)
    (z : Fin m → Fin n → ℝ × ℝ) :
    ∃ r i, outerCutoffTaggedRows m hm z = toLex (z r i) := by
  rw [outerCutoffTaggedRows, dif_pos hn]
  obtain ⟨r,_,hr⟩ := Finset.exists_mem_eq_inf'
    (outerOfferIndices_nonempty (show 0 < m by omega)) (fun r => outerTaggedMaximum hn (z r))
  rw [hr]
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' (outerOfferIndices_nonempty hn) (fun i => toLex (z r i))
  exact ⟨r,i,hi⟩

theorem retainAboveOuterCutoff_rounding {n M N : ℕ} (hn : 0 < n) (m : ℕ) (hm : 1 ≤ m)
    (hN : 0 < N) (v : Fin m → Fin n → ℝ) (u : Fin M → ℝ)
    (hu : Function.Injective (fun j => uniformGridIndex N hN (u j)))
    (idx : Fin m → Fin n → Fin M) (j : Fin M) (x : ℝ) :
    retainAboveTag
      (ofLex (outerCutoffTaggedRows m hm (fun r i => (v r i, uniformGridRound N hN (u (idx r i))))))
      (x, uniformGridRound N hN (u j)) =
    retainAboveTag (ofLex (outerCutoffTaggedRows m hm (fun r i => (v r i,u (idx r i))))) (x,u j) := by
  let z := fun r i => (v r i,u (idx r i))
  change retainAboveTag (ofLex (outerCutoffTaggedRows m hm
    (fun r i => ((z r i).1,uniformGridRound N hN (z r i).2)))) _ = _
  rw [outerCutoffTaggedRows_rounding hn, show (fun r i => (v r i,u (idx r i))) = z by rfl]
  obtain ⟨r,i,hi⟩ := outerCutoffTaggedRows_is_observation hn m hm z
  rw [hi]
  have h : taggedAbove (v r i,uniformGridRound N hN (u (idx r i))) (x,uniformGridRound N hN (u j)) ↔
      taggedAbove (v r i,u (idx r i)) (x,u j) := by
    rw [taggedAbove_iff_lex_lt, taggedAbove_iff_lex_lt]
    exact outerMark_taggedComparison_rounding hN u hu (idx r i) j (v r i) x
  by_cases ht : taggedAbove (v r i,u (idx r i)) (x,u j)
  · simp only [retainAboveTag, roundTaggedValue, z, ofLex_toLex, h.mpr ht, ht, if_true]
  · have htr := mt h.mp ht
    simp only [retainAboveTag, roundTaggedValue, z, ofLex_toLex, htr, ht, if_false]

end ProphetSecretary.Statistics
