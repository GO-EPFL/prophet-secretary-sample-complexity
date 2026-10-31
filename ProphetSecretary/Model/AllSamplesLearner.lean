import ProphetSecretary.Model.Learner

/-!
# A causal full-budget sampling protocol

The request rule asks any marginal whose visible request count is below `k`.
The transcript alone reconstructs the whole reservoir after `n*k` requests, on
all sample outcomes. This permits concrete sample-based learners without exposing
the executor's hidden reservoir to their decision functions.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ}

/-- The value of the `j`th sample of marginal `i`, or zero if that request has not
occurred. Transcripts are stored with the most recent observation first. -/
def decodedReservoir : Transcript n → Reservoir n k
  | [] => fun _ _ => 0
  | (q, x) :: h => fun i j =>
      if q = i ∧ requests h i = j.val then x else decodedReservoir h i j

lemma decodedReservoir_cons {h : Transcript n} (q : Fin n) (x : ℝ) (i : Fin n) (j : Fin k) :
    decodedReservoir ((q, x) :: h) i j =
      if q = i ∧ requests h i = j.val then x else decodedReservoir h i j := rfl

/-- Every sample that has been requested can be recovered from its visible transcript. -/
def ReservoirConsistent (y : Reservoir n k) (h : Transcript n) : Prop :=
  ∀ i j, j.val < requests h i → decodedReservoir h i j = y i j

lemma reservoirConsistent_nil (y : Reservoir n k) : ReservoirConsistent y [] := by
  intro i j hj
  simp only [requests_nil] at hj
  omega

lemma ReservoirConsistent.cons {y : Reservoir n k} {h : Transcript n}
    (hh : ReservoirConsistent y h) (q : Fin n) (hq : requests h q < k) :
    ReservoirConsistent y ((q, y q ⟨requests h q, hq⟩) :: h) := by
  intro i j hj
  rw [requests_cons] at hj
  rw [decodedReservoir_cons]
  by_cases hi : q = i
  · subst i
    simp only [eq_self, ite_true, true_and] at hj ⊢
    by_cases he : requests h q = j.val
    · rw [if_pos he]
      congr 1
      exact Fin.ext he
    · rw [if_neg he]
      exact hh q j (by omega)
  · simp only [hi, false_and, if_false] at hj ⊢
    exact hh i j (by omega)

lemma ReservoirConsistent.train {Seed : Type*} {y : Reservoir n k} {h : Transcript n}
    (hh : ReservoirConsistent y h) (rule : RequestRule n Seed) (seed : Seed) (fuel : ℕ) :
    ReservoirConsistent y (train rule seed y fuel h) := by
  induction fuel generalizing h with
  | zero => exact hh
  | succ fuel ih =>
    rw [ProphetSecretary.Model.train]
    split
    · exact hh
    · rename_i q hq
      split
      · rename_i havail
        exact ih (hh.cons q havail)
      · exact hh

/-- Request a marginal with an unused slot; only visible counts are consulted. -/
noncomputable def requestAllFromCounts (q : Fin n → ℕ) : Option (Fin n) :=
  if h : ∃ i, q i < k then some (Classical.choose h) else none

noncomputable def requestAll (k : ℕ) {Seed : Type*} : RequestRule n Seed :=
  fun _ h => requestAllFromCounts (k := k) (fun i => requests h i)

lemma requestAll_some_available {Seed : Type*} (seed : Seed) (h : Transcript n) (i : Fin n)
    (hi : requestAll (k := k) seed h = some i) : requests h i < k := by
  unfold requestAll requestAllFromCounts at hi
  split at hi
  · rename_i hex
    have he := Option.some.inj hi
    exact he ▸ Classical.choose_spec hex
  · simp at hi

lemma requestAll_none_full {Seed : Type*} (seed : Seed) (h : Transcript n)
    (hn : requestAll (k := k) seed h = none) (hh : WithinBudget k h) :
    ∀ i, requests h i = k := by
  unfold requestAll requestAllFromCounts at hn
  split at hn
  · simp at hn
  · rename_i hnone
    intro i
    apply le_antisymm (hh i)
    exact le_of_not_gt (fun hi => hnone ⟨i, hi⟩)

lemma train_requestAll_full {Seed : Type*} (seed : Seed) (y : Reservoir n k)
    (fuel : ℕ) (h : Transcript n) (hh : WithinBudget k h)
    (hlen : n * k ≤ h.length + fuel) :
    ∀ i, requests (train (requestAll k) seed y fuel h) i = k := by
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
      exact requestAll_none_full seed h hn hh
    · rename_i q hq
      have havail := requestAll_some_available seed h q hq
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

/-- On every seed and every real reservoir, the transcript exposes exactly the
array used by a full-sample empirical learner. -/
theorem decodedReservoir_trainingTranscript {Seed : Type*} (seed : Seed) (y : Reservoir n k) :
    decodedReservoir (trainingTranscript (requestAll k) seed y) = y := by
  have hfull := train_requestAll_full seed y (n * k) [] (by simp [WithinBudget]) (by simp)
  have hcons := (reservoirConsistent_nil y).train (requestAll k) seed (n * k)
  funext i j
  apply hcons i j
  rw [hfull i]
  exact j.is_lt

variable {Ω Seed : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed]

lemma measurable_requestAll : MeasurableRequestRule (requestAll (n := n) (k := k) (Seed := Seed)) := by
  have hcounts : Measurable (fun z : Seed × Transcript n => fun i => requests z.2 i) :=
    measurable_pi_lambda _ (fun i => (measurable_requests i).comp measurable_snd)
  exact (measurable_of_countable (requestAllFromCounts (n := n) (k := k))).comp hcounts

lemma measurable_decodedReservoir : Measurable (@decodedReservoir n k) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  rw [measurable_from_transcript_iff]
  intro m
  induction m with
  | zero =>
    simpa only [List.ofFn_zero, decodedReservoir] using
      (measurable_const : Measurable fun _ : Fin 0 → Fin n × ℝ => (0 : ℝ))
  | succ m ih =>
    have htail : Measurable (fun h : Fin (m + 1) → Fin n × ℝ => fun a : Fin m => h a.succ) :=
      measurable_pi_lambda _ (fun a => measurable_pi_apply a.succ)
    have htailList := (measurable_transcript_ofFn m).comp htail
    have hc := (measurable_requests i).comp htailList
    have hid : Measurable (fun h : Fin (m + 1) → Fin n × ℝ => (h 0).1) :=
      measurable_fst.comp (measurable_pi_apply 0)
    have hv : Measurable (fun h : Fin (m + 1) → Fin n × ℝ => (h 0).2) :=
      measurable_snd.comp (measurable_pi_apply 0)
    have hs : MeasurableSet {h : Fin (m + 1) → Fin n × ℝ |
        (h 0).1 = i ∧ requests (List.ofFn fun a : Fin m => h a.succ) i = j.val} :=
      (measurableSet_eq_fun hid measurable_const).inter (measurableSet_eq_fun hc measurable_const)
    convert Measurable.ite hs hv (ih.comp htail) using 1
    funext h
    rw [List.ofFn_succ]
    rfl

/-- Convert a jointly measurable sample-based rule into a causal learner. Its request
rule and decision rule are fixed independently of the unknown distribution. -/
noncomputable def Learner.ofSamplePolicy (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (Reservoir n k × Seed) n) (hπ : π.IsMeasurable) : Learner n k where
  Seed := Seed
  seedLaw := ν
  request := requestAll k
  measurable_request := measurable_requestAll
  decide r h t i x H := π.decide (decodedReservoir h, r) t i x H
  measurable_decide := by
    let T := (Seed × Transcript n) × (ℝ × (Fin n × (ℝ × History n)))
    have hd : Measurable (fun z : T => decodedReservoir (k := k) z.1.2) :=
      (measurable_decodedReservoir (n := n) (k := k)).comp (measurable_snd.comp measurable_fst)
    have hr : Measurable (fun z : T => z.1.1) := measurable_fst.comp measurable_fst
    exact hπ.comp ((hd.prodMk hr).prodMk measurable_snd)

/-- Every actual decision agrees with the supplied sample-based rule on every
training outcome; the hard budget is inherited from the actual request executor. -/
lemma Learner.ofSamplePolicy_decide (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (Reservoir n k × Seed) n) (hπ : π.IsMeasurable)
    (y : Reservoir n k) (r : Seed) (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (Learner.ofSamplePolicy Seed ν π hπ).policy.decide (y, r) t i x H =
      π.decide (y, r) t i x H := by
  change π.decide (decodedReservoir (trainingTranscript (requestAll k) r y), r) t i x H = _
  rw [decodedReservoir_trainingTranscript]

end ProphetSecretary.Model
