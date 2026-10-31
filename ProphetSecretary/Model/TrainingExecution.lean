import ProphetSecretary.Model.TrainingMeasurability

/-!
# Measurability of adaptive sampling

The next request is a measurable function of the observed transcript and seed. A finite
reservoir supplies each requested sample exactly once, and the executor halts on any
exhausted request. Its pathwise hard-budget property is in `Training.lean`.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

/-- Evaluation at a measurable countable-valued index. -/
theorem measurable_countable_choice {Ω I A : Type*} [MeasurableSpace Ω]
    [MeasurableSpace I] [MeasurableSingletonClass I] [Countable I] [MeasurableSpace A]
    {f : I → Ω → A} {i : Ω → I} (hi : Measurable i) (hf : ∀ j, Measurable (f j)) :
    Measurable (fun ω => f (i ω) ω) := by
  intro s hs
  have heq : (fun ω => f (i ω) ω) ⁻¹' s =
      ⋃ j : I, {ω | i ω = j} ∩ (f j ⁻¹' s) := by
    ext ω
    simp only [mem_preimage, mem_iUnion, mem_inter_iff, mem_setOf_eq]
    constructor
    · intro h
      exact ⟨i ω, rfl, h⟩
    · rintro ⟨j, hj, h⟩
      simpa only [hj] using h
  rw [heq]
  exact MeasurableSet.iUnion fun j => (hi (measurableSet_singleton j)).inter (hf j hs)

instance sampleRequestSpace (n k : ℕ) : MeasurableSpace (Option (Fin n × Fin k)) := ⊤
instance sampleRequestSingletonClass (n k : ℕ) :
    MeasurableSingletonClass (Option (Fin n × Fin k)) := ⟨fun _ => trivial⟩

/-- The identity and next unused reservoir index; no value is inspected to choose them. -/
def activeRequest {n k : ℕ} (req : Option (Fin n)) (counts : Fin n → ℕ) :
    Option (Fin n × Fin k) :=
  match req with
  | none => none
  | some i => if h : counts i < k then some (i, ⟨counts i, h⟩) else none

variable {Ω Seed : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed] {n k : ℕ}

/-- The adaptive executor is measurable when its request rule is measurable.
The initial observed transcript may itself be random and is encoded by a fixed finite tuple. -/
theorem measurable_train_ofFn (rule : RequestRule n Seed) (hRule : MeasurableRequestRule rule)
    {r : Ω → Seed} {samples : Ω → Reservoir n k} (hr : Measurable r)
    (hs : Measurable samples) (fuel m : ℕ) (h : Ω → Fin m → (Fin n × ℝ))
    (hh : ∀ j, Measurable fun ω => h ω j) :
    Measurable fun ω => train rule (r ω) (samples ω) fuel (List.ofFn (h ω)) := by
  induction fuel generalizing m with
  | zero =>
    exact (measurable_transcript_ofFn m).comp (measurable_pi_lambda h hh)
  | succ fuel ih =>
    have hhist : Measurable fun ω => (List.ofFn (h ω) : Transcript n) :=
      (measurable_transcript_ofFn m).comp (measurable_pi_lambda h hh)
    have hreq : Measurable fun ω => rule (r ω) (List.ofFn (h ω)) :=
      hRule.comp (hr.prodMk hhist)
    have hcounts : Measurable fun ω => fun i => requests (List.ofFn (h ω)) i :=
      measurable_pi_lambda _ fun i => (measurable_requests i).comp hhist
    have hactive : Measurable fun ω =>
        activeRequest (k := k) (rule (r ω) (List.ofFn (h ω)))
          (fun i => requests (List.ofFn (h ω)) i) :=
      (measurable_of_countable (fun z : Option (Fin n) × (Fin n → ℕ) =>
        activeRequest (k := k) z.1 z.2)).comp (hreq.prodMk hcounts)
    let branch : Option (Fin n × Fin k) → Ω → Transcript n := fun req ω =>
      match req with
      | none => List.ofFn (h ω)
      | some (i, j) => train rule (r ω) (samples ω) fuel
          ((i, samples ω i j) :: List.ofFn (h ω))
    have hbranch : ∀ req, Measurable (branch req) := by
      intro req
      cases req with
      | none => exact hhist
      | some ij =>
        rcases ij with ⟨i, j⟩
        have hnew : ∀ a : Fin (m + 1), Measurable fun ω =>
            (Fin.cons (i, samples ω i j) (h ω) : Fin (m + 1) → (Fin n × ℝ)) a := by
          intro a
          refine Fin.cases ?_ (fun b => ?_) a
          · exact measurable_const.prodMk ((hs.eval (a := i)).eval (a := j))
          · exact hh b
        have hi := ih (m + 1) (fun ω => Fin.cons (i, samples ω i j) (h ω)) hnew
        simpa only [List.ofFn_succ, Fin.cons_zero, Fin.cons_succ] using hi
    have hm := measurable_countable_choice hactive hbranch
    convert hm using 1
    funext ω
    simp only [train]
    cases hq : rule (r ω) (List.ofFn (h ω)) with
    | none => simp [activeRequest, branch]
    | some i =>
      simp only [activeRequest]
      split <;> rfl

/-- In particular, the transcript generated from an empty history is measurable. -/
theorem measurable_trainingTranscript (rule : RequestRule n Seed)
    (hRule : MeasurableRequestRule rule) {r : Ω → Seed} {samples : Ω → Reservoir n k}
    (hr : Measurable r) (hs : Measurable samples) :
    Measurable fun ω => trainingTranscript rule (r ω) (samples ω) := by
  have h := measurable_train_ofFn rule hRule hr hs (n * k) 0
    (fun _ => Fin.elim0) (fun i => Fin.elim0 i)
  simpa only [List.ofFn_zero, trainingTranscript] using h

end ProphetSecretary.Model
