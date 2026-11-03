import ProphetSecretary.Model.AllSamplesLearner

/-!
# A computable full-sample request protocol

The request rule scans the finite identity list for the first marginal with
an unused slot. It depends only on observed request counts. The existing
transcript decoder reconstructs every requested observation, and the rule
fills the complete reservoir on every raw outcome.
-/

open MeasureTheory
open scoped BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ}

def firstAvailableFromCounts (k : ℕ) (counts : Fin n → ℕ) : Option (Fin n) :=
  (List.finRange n).find? (fun i => decide (counts i < k))

def firstAvailableRequest (k : ℕ) {Seed : Type*} : RequestRule n Seed :=
  fun _ h => firstAvailableFromCounts k (fun i => requests h i)

lemma firstAvailableRequest_some_available {Seed : Type*} (seed : Seed) (h : Transcript n)
    (i : Fin n) (hi : firstAvailableRequest (k := k) seed h = some i) : requests h i < k := by
  have hFind : (List.finRange n).find? (fun j => decide (requests h j < k)) = some i := hi
  have hTrue : decide (requests h i < k) = true :=
    List.find?_some (p := fun j => decide (requests h j < k)) (a := i) hFind
  exact of_decide_eq_true hTrue

lemma firstAvailableRequest_none_full {Seed : Type*} (seed : Seed) (h : Transcript n)
    (hn : firstAvailableRequest (k := k) seed h = none) (hh : WithinBudget k h) :
    ∀ i, requests h i = k := by
  intro i
  have hNone := List.find?_eq_none.mp hn i (by simp)
  have hnot : ¬requests h i < k := by simpa only [decide_eq_true_eq] using hNone
  exact le_antisymm (hh i) (le_of_not_gt hnot)

lemma train_firstAvailable_full {Seed : Type*} (seed : Seed) (y : Reservoir n k)
    (fuel : ℕ) (h : Transcript n) (hh : WithinBudget k h) (hlen : n*k ≤ h.length+fuel) :
    ∀ i, requests (train (firstAvailableRequest k) seed y fuel h) i = k := by
  induction fuel generalizing h with
  | zero =>
    intro i
    change requests h i = k
    apply le_antisymm (hh i)
    by_contra hi
    have hlt : requests h i < k := lt_of_not_ge hi
    have hsum : (∑ j : Fin n, requests h j) < ∑ _j : Fin n, k :=
      Finset.sum_lt_sum (fun j _ => hh j) ⟨i, Finset.mem_univ _, hlt⟩
    rw [sum_requests_eq_length] at hsum
    simp only [Finset.sum_const, Finset.card_fin, smul_eq_mul] at hsum
    omega
  | succ fuel ih =>
    rw [train]
    split
    · rename_i hn
      exact firstAvailableRequest_none_full seed h hn hh
    · rename_i q hq
      have havail := firstAvailableRequest_some_available seed h q hq
      rw [dif_pos havail]
      apply ih
      · intro j
        rw [requests_cons]
        by_cases he : q = j
        · subst j
          simp only [eq_self, ite_true]
          omega
        · simp only [he, if_false, Nat.add_zero]
          exact hh j
      · simp only [List.length_cons]
        omega

lemma decodedReservoir_firstAvailable_transcript {Seed : Type*} (seed : Seed) (y : Reservoir n k) :
    decodedReservoir (trainingTranscript (firstAvailableRequest k) seed y) = y := by
  have hfull := train_firstAvailable_full seed y (n*k) [] (by simp [WithinBudget]) (by simp)
  have hcons := (reservoirConsistent_nil y).train (firstAvailableRequest k) seed (n*k)
  funext i j
  apply hcons i j
  rw [hfull i]
  exact j.is_lt

lemma measurable_firstAvailableRequest {Seed : Type*} [MeasurableSpace Seed] :
    MeasurableRequestRule (firstAvailableRequest (n := n) (k := k) (Seed := Seed)) := by
  have hcounts : Measurable (fun z : Seed × Transcript n => fun i => requests z.2 i) :=
    measurable_pi_lambda _ (fun i => (measurable_requests i).comp measurable_snd)
  exact (measurable_of_countable (firstAvailableFromCounts (n := n) k)).comp hcounts

/-- A full-sample policy implemented through the computable causal request scan. -/
noncomputable def Learner.ofComputedSamplePolicy (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (Reservoir n k × Seed) n) (hπ : π.IsMeasurable) : Learner n k where
  Seed := Seed
  seedLaw := ν
  request := firstAvailableRequest k
  measurable_request := measurable_firstAvailableRequest
  decide r h t i x H := π.decide (decodedReservoir h, r) t i x H
  measurable_decide := (Learner.ofSamplePolicy Seed ν π hπ).measurable_decide

lemma Learner.ofComputedSamplePolicy_decide (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (Reservoir n k × Seed) n) (hπ : π.IsMeasurable)
    (y : Reservoir n k) (r : Seed) (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (Learner.ofComputedSamplePolicy Seed ν π hπ).policy.decide (y,r) t i x H =
      π.decide (y,r) t i x H := by
  change π.decide (decodedReservoir (trainingTranscript (firstAvailableRequest k) r y),r) t i x H = _
  rw [decodedReservoir_firstAvailable_transcript]

lemma Learner.ofComputedSamplePolicy_requests_eq (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (Reservoir n k × Seed) n) (hπ : π.IsMeasurable)
    (y : Reservoir n k) (r : Seed) (i : Fin n) :
    requests (trainingTranscript (Learner.ofComputedSamplePolicy Seed ν π hπ).request r y) i = k := by
  exact train_firstAvailable_full r y (n*k) [] (by simp [WithinBudget]) (by simp) i

/-- Availability tests along the same finite scan used by `firstAvailableFromCounts`. -/
def firstAvailableComparisons (k : ℕ) (counts : Fin n → ℕ) : List (Fin n) → ℕ
  | [] => 0
  | i :: rest => 1+if counts i < k then 0 else firstAvailableComparisons k counts rest

lemma firstAvailableComparisons_le (k : ℕ) (counts : Fin n → ℕ) (ids : List (Fin n)) :
    firstAvailableComparisons k counts ids ≤ ids.length := by
  induction ids with
  | nil => simp [firstAvailableComparisons]
  | cons i ids ih =>
    simp only [firstAvailableComparisons, List.length_cons]
    split_ifs <;> omega

/-- Each request inspects at most `n` marginal budget counts, on every transcript. -/
lemma firstAvailableRequest_comparisons_le (h : Transcript n) :
    firstAvailableComparisons k (fun i => requests h i) (List.finRange n) ≤ n := by
  simpa only [List.length_finRange] using
    firstAvailableComparisons_le k (fun i => requests h i) (List.finRange n)

end ProphetSecretary.Model
