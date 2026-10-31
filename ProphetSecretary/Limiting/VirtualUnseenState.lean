import ProphetSecretary.Limiting.AppendIIDState
import ProphetSecretary.Limiting.VirtualClockFraction
import ProphetSecretary.Limiting.FinitePotentialPolicy

/-!
# Actual unseen original and virtual identities

The virtual count is read from the full strict-past history. An observed zero
is `some (time,0)`, so its identity is removed from the unseen set exactly like
every other arrival. Its clock equals the current time only on a null event,
which is treated separately by the clock-fraction lemmas.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n q : ℕ}

lemma virtualSet_unseen_history (x u : Fin (n+q) → ℝ) (t : ℝ) :
    virtualSet n (Model.unseen (Model.history Finset.univ x u t)) =
      Finset.univ.filter (fun j : Fin q => t ≤ u (j.natAdd n)) := by
  ext j
  simp [virtualSet,Model.unseen,Model.history,not_lt]

lemma virtualSet_erase_individual (S : Finset (Fin (n+q))) (i : Fin n) :
    virtualSet n (S.erase (i.castAdd q)) = virtualSet n S := by
  ext j
  have hne : j.natAdd n ≠ i.castAdd q := by
    intro he
    have hh := congrArg Fin.val he
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hh
    omega
  simp only [virtualSet,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase]
  exact and_iff_right hne

lemma retainedSet_unseen_history (x u : Fin (n+q) → ℝ) (t : ℝ) :
    Model.retainedSet q (Model.unseen (Model.history Finset.univ x u t)) =
      Model.unseen (Model.history Finset.univ (fun i : Fin n => x (i.castAdd q))
        (fun i : Fin n => u (i.castAdd q)) t) := by
  ext i
  simp [Model.retainedSet,Model.unseen,Model.history]

noncomputable def virtualContinuationState (x u : Fin (n+q) → ℝ) (t : ℝ) (candidate : Option (Fin n)) :
    Finset (Fin (n+q)) :=
  candidate.elim (Model.unseen (Model.history Finset.univ x u t))
    (fun i => (Model.unseen (Model.history Finset.univ x u t)).erase (i.castAdd q))

lemma virtualContinuationState_virtual_count (x u : Fin (n+q) → ℝ) (t : ℝ) (candidate : Option (Fin n)) :
    (virtualSet n (virtualContinuationState x u t candidate)).card =
      virtualUnseenCount t (fun j : Fin q => u (j.natAdd n)) := by
  cases candidate with
  | none => rw [virtualContinuationState,Option.elim_none,virtualSet_unseen_history]; rfl
  | some i => rw [virtualContinuationState,Option.elim_some,virtualSet_erase_individual,virtualSet_unseen_history]; rfl

lemma virtualContinuationState_retained (x u : Fin (n+q) → ℝ) (t : ℝ) (candidate : Option (Fin n)) :
    Model.retainedSet q (virtualContinuationState x u t candidate) =
      candidate.elim (Model.unseen (Model.history Finset.univ (fun i : Fin n => x (i.castAdd q))
        (fun i : Fin n => u (i.castAdd q)) t))
      (fun i => (Model.unseen (Model.history Finset.univ (fun i : Fin n => x (i.castAdd q))
        (fun i : Fin n => u (i.castAdd q)) t)).erase i) := by
  cases candidate with
  | none => rw [virtualContinuationState,Option.elim_none,retainedSet_unseen_history]; rfl
  | some i => rw [virtualContinuationState,Option.elim_some,retainedSet_erase_individual,retainedSet_unseen_history]; rfl

end ProphetSecretary.Limiting
