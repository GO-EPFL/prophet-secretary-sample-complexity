import Mathlib.Data.List.Count
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-!
# Adaptive training with a hard budget

A reservoir contains `k` fresh samples of each distribution. The request rule sees its
seed and the transcript only; the executor supplies the next unused sample of the requested
distribution. It cannot inspect future samples. Transcripts are stored in reverse order.
The budget is pathwise, including on transcripts of probability zero.
-/

namespace ProphetSecretary.Model

abbrev Transcript (n : ℕ) := List (Fin n × ℝ)

/-- Number of requests to distribution `i`. -/
def requests {n : ℕ} (h : Transcript n) (i : Fin n) : ℕ :=
  (h.map Prod.fst).count i

@[simp] theorem requests_nil {n : ℕ} (i : Fin n) : requests [] i = 0 := rfl

@[simp] theorem requests_cons {n : ℕ} (h : Transcript n) (i j : Fin n) (x : ℝ) :
    requests ((j, x) :: h) i = requests h i + if j = i then 1 else 0 := by
  simp only [requests, List.map_cons, List.count_cons]
  split <;> split <;> simp_all

theorem sum_requests_eq_length {n : ℕ} (h : Transcript n) :
    ∑ i : Fin n, requests h i = h.length := by
  induction h with
  | nil => simp
  | cons e h ih =>
    rcases e with ⟨j, x⟩
    simp only [requests_cons, Finset.sum_add_distrib, ih, List.length_cons]
    simp

/-- A hard per-distribution budget. -/
def WithinBudget {n : ℕ} (k : ℕ) (h : Transcript n) : Prop :=
  ∀ i, requests h i ≤ k

/-- Requests use only earlier observations and independent auxiliary randomness. -/
abbrev RequestRule (n : ℕ) (Seed : Type*) := Seed → Transcript n → Option (Fin n)

abbrev Reservoir (n k : ℕ) := Fin n → Fin k → ℝ

/-- A halt or an exhausted request ends training. -/
def train {n k : ℕ} {Seed : Type*} (rule : RequestRule n Seed)
    (seed : Seed) (samples : Reservoir n k) : ℕ → Transcript n → Transcript n
  | 0, h => h
  | fuel + 1, h =>
    match rule seed h with
    | none => h
    | some i =>
      if hi : requests h i < k then
        train rule seed samples fuel ((i, samples i ⟨requests h i, hi⟩) :: h)
      else h

theorem train_withinBudget {n k : ℕ} {Seed : Type*} (rule : RequestRule n Seed)
    (seed : Seed) (samples : Reservoir n k) (fuel : ℕ) (h : Transcript n)
    (hh : WithinBudget k h) :
    WithinBudget k (train rule seed samples fuel h) := by
  induction fuel generalizing h with
  | zero => exact hh
  | succ fuel ih =>
    simp only [train]
    split
    · exact hh
    · rename_i i hr
      split
      · rename_i hi
        apply ih
        intro j
        simp only [requests_cons]
        split
        · rename_i hij
          subst j
          omega
        · simpa using hh j
      · exact hh

/-- The bound holds for every execution, independently of sample values. -/
theorem train_empty_withinBudget {n k : ℕ} {Seed : Type*} (rule : RequestRule n Seed)
    (seed : Seed) (samples : Reservoir n k) (fuel : ℕ) :
    WithinBudget k (train rule seed samples fuel []) :=
  train_withinBudget rule seed samples fuel [] (by simp [WithinBudget])

def trainingTranscript {n k : ℕ} {Seed : Type*} (rule : RequestRule n Seed)
    (seed : Seed) (samples : Reservoir n k) : Transcript n :=
  train rule seed samples (n * k) []

theorem trainingTranscript_budget {n k : ℕ} {Seed : Type*}
    (rule : RequestRule n Seed) (seed : Seed) (samples : Reservoir n k) (i : Fin n) :
    requests (trainingTranscript rule seed samples) i ≤ k :=
  train_empty_withinBudget rule seed samples (n * k) i

theorem WithinBudget.length_le {n k : ℕ} {h : Transcript n} (hh : WithinBudget k h) :
    h.length ≤ n * k := by
  rw [← sum_requests_eq_length]
  calc
    (∑ i : Fin n, requests h i) ≤ ∑ _i : Fin n, k := Finset.sum_le_sum fun i _ => hh i
    _ = n * k := by simp

end ProphetSecretary.Model
