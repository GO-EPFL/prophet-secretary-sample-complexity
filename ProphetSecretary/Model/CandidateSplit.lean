import ProphetSecretary.Model.ContinuationTransport

/-!
# Splitting one candidate from a finite product law

The remaining coordinates use exactly the sorted labels of `P_A`, avoiding
identification of different identity sets. Independence is proved from coordinate
erasure and the original product law.
-/

open MeasureTheory Set ProbabilityTheory

namespace ProphetSecretary.Model

variable {n : ℕ}

def remainingSet (i : Fin n) : Finset (Fin n) := Finset.univ.erase i

lemma stateEmbedding_remaining_ne (i : Fin n) (j : Fin (remainingSet i).card) :
    stateEmbedding (remainingSet i) j ≠ i :=
  (Finset.mem_erase.mp (stateEmbedding_mem (remainingSet i) j)).1

/-- Insert a candidate and its sorted remaining coordinates into the full vector. -/
noncomputable def insertCandidate (i : Fin n)
    (z : ℝ × (Fin (remainingSet i).card → ℝ)) : Fin n → ℝ :=
  fun j ↦ if hji : j = i then z.1 else z.2 (stateIndex (remainingSet i) j (by simp [remainingSet, hji]))

@[simp] lemma insertCandidate_same (i : Fin n) (z : ℝ × (Fin (remainingSet i).card → ℝ)) :
    insertCandidate i z i = z.1 := by simp [insertCandidate]

@[simp] lemma insertCandidate_remaining (i : Fin n)
    (z : ℝ × (Fin (remainingSet i).card → ℝ)) (j : Fin (remainingSet i).card) :
    insertCandidate i z (stateEmbedding (remainingSet i) j) = z.2 j := by
  simp only [insertCandidate, dif_neg (stateEmbedding_remaining_ne i j), stateIndex_stateEmbedding]

lemma measurable_insertCandidate (i : Fin n) : Measurable (insertCandidate i) := by
  classical
  apply measurable_pi_lambda
  intro j
  by_cases hji : j = i
  · simp only [insertCandidate, dif_pos hji]
    exact measurable_fst
  · simp only [insertCandidate, dif_neg hji]
    exact (measurable_pi_apply _).comp measurable_snd

/-- Measurable equivalence between the full vector and candidate-plus-state data. -/
noncomputable def splitCandidate (i : Fin n) :
    (Fin n → ℝ) ≃ᵐ ℝ × (Fin (remainingSet i).card → ℝ) where
  toFun x := (x i, x ∘ stateEmbedding (remainingSet i))
  invFun := insertCandidate i
  left_inv x := by
    funext j
    by_cases hji : j = i
    · simp [insertCandidate, hji]
    · simp only [insertCandidate, dif_neg hji, Function.comp_apply, stateEmbedding_stateIndex]
  right_inv z := by
    apply Prod.ext
    · exact insertCandidate_same i z
    · funext j
      exact insertCandidate_remaining i z j
  measurable_toFun := (measurable_pi_apply i).prodMk
    (measurable_pi_lambda _ (fun j ↦ measurable_pi_apply (stateEmbedding (remainingSet i) j)))
  measurable_invFun := measurable_insertCandidate i

/-- The candidate and the original-label remaining coordinates have independent
marginal laws. No independence of a policy execution is assumed. -/
lemma splitCandidate_measurePreserving (μ : Fin n → Measure ℝ)
    [∀ j, IsProbabilityMeasure (μ j)] (i : Fin n) :
    MeasurePreserving (splitCandidate i) (Measure.pi μ)
      ((μ i).prod (Measure.pi (fun j ↦ μ (stateEmbedding (remainingSet i) j)))) := by
  have hrest : Measurable (fun x : Fin n → ℝ ↦ x ∘ stateEmbedding (remainingSet i)) :=
    measurable_pi_lambda _ (fun j ↦ measurable_pi_apply (stateEmbedding (remainingSet i) j))
  have hind := erasedFunctional_independent μ i 0
    (fun x : Fin n → ℝ ↦ x ∘ stateEmbedding (remainingSet i)) hrest
  have he : (fun x : Fin n → ℝ ↦ eraseCoordinate i 0 x ∘ stateEmbedding (remainingSet i)) =
      (fun x : Fin n → ℝ ↦ x ∘ stateEmbedding (remainingSet i)) := by
    funext x j
    exact Function.update_of_ne (stateEmbedding_remaining_ne i j) _ _
  rw [he] at hind
  have hm := hind.symm.map_prod_eq_prod_map_map (measurable_pi_apply i).aemeasurable hrest.aemeasurable
  rw [(measurePreserving_eval μ i).map_eq,
    (measurePreserving_restrictCoordinates μ (stateEmbedding (remainingSet i))).map_eq] at hm
  exact ⟨(splitCandidate i).measurable, hm⟩

lemma Instance.splitCandidate_values_measurePreserving (P : Instance n) (i : Fin n) :
    MeasurePreserving (splitCandidate i) P.valuesLaw
      ((P.law i).prod (P.restrictTo (remainingSet i)).valuesLaw) :=
  splitCandidate_measurePreserving P.law i

lemma splitCandidate_clocks_measurePreserving (i : Fin n) :
    MeasurePreserving (splitCandidate i) (Instance.clocksLaw n)
      (Instance.uniformClock.prod (Instance.clocksLaw (remainingSet i).card)) :=
  splitCandidate_measurePreserving (fun _ ↦ Instance.uniformClock) i

end ProphetSecretary.Model
