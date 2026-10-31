import ProphetSecretary.Model.Outcome
import Mathlib.Order.Fin.Basic

/-!
# Deleting zero-payoff candidates from an execution

The retained candidates have exactly the same actions after a causal history
simulation. Deleting the other zero-valued candidates cannot stop earlier and
cannot reduce reward. Increasing identity embeddings preserve literal tie-breaking.
-/

open scoped Classical

namespace ProphetSecretary.Model

variable {m n : ℕ} {SmallSeed BigSeed : Type*}

lemma Policy.stoppingTime_le_of_subexecution (π : Policy BigSeed n) (σ : Policy SmallSeed m)
    (e : Fin m ↪ Fin n) (r : BigSeed) (s : SmallSeed) (x u : Fin n → ℝ) (y v : Fin m → ℝ)
    (hu : ∀ i, u (e i) = v i)
    (ha : ∀ i, σ.action s Finset.univ y v i = π.action r Finset.univ x u (e i)) :
    π.stoppingTime r Finset.univ x u ≤ σ.stoppingTime s Finset.univ y v := by
  apply (σ.le_stoppingTime_iff s Finset.univ y v _).mpr
  refine ⟨π.stoppingTime_le_one _ _ _ _, ?_⟩
  intro i hi
  have hacc := (σ.mem_accepted s Finset.univ y v i).mp hi
  have hbig : e i ∈ π.accepted r Finset.univ x u :=
    (π.mem_accepted r Finset.univ x u (e i)).mpr ⟨Finset.mem_univ _, by rw [← ha i]; exact hacc.2⟩
  exact (π.stoppingTime_le_of_accepted r Finset.univ x u (e i) hbig).trans_eq (hu i)

lemma Policy.actualSelects_of_subexecution (π : Policy BigSeed n) (σ : Policy SmallSeed m)
    (e : Fin m ↪o Fin n) (r : BigSeed) (s : SmallSeed) (x u : Fin n → ℝ) (y v : Fin m → ℝ)
    (hu : ∀ i, u (e i) = v i)
    (ha : ∀ i, σ.action s Finset.univ y v i = π.action r Finset.univ x u (e i))
    (i : Fin m) (hi : π.ActualSelects r Finset.univ x u (e i)) : σ.ActualSelects s Finset.univ y v i := by
  have hacc : i ∈ σ.accepted s Finset.univ y v :=
    (σ.mem_accepted s Finset.univ y v i).mpr ⟨Finset.mem_univ _, by
      rw [ha i]
      exact ((π.mem_accepted r Finset.univ x u (e i)).mp hi.1.1).2⟩
  have hd := π.stoppingTime_le_of_subexecution σ e.toEmbedding r s x u y v hu ha
  have hv : v i = π.stoppingTime r Finset.univ x u := (hu i).symm.trans hi.1.2
  have htime : σ.stoppingTime s Finset.univ y v = π.stoppingTime r Finset.univ x u :=
    le_antisymm ((σ.stoppingTime_le_of_accepted s Finset.univ y v i hacc).trans_eq hv) hd
  refine ⟨⟨hacc, hv.trans htime.symm⟩, ?_⟩
  intro j hj
  have hbig : π.Selects r Finset.univ x u (e j) := by
    refine ⟨(π.mem_accepted r Finset.univ x u (e j)).mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · rw [← ha j]
      exact ((σ.mem_accepted s Finset.univ y v j).mp hj.1).2
    · rw [hu j, hj.2, htime]
  exact e.le_iff_le.mp (hi.2 (e j) hbig)

lemma Policy.reward_le_of_zero_subexecution (π : Policy BigSeed n) (σ : Policy SmallSeed m)
    (e : Fin m ↪o Fin n) (r : BigSeed) (s : SmallSeed) (x u : Fin n → ℝ) (y v : Fin m → ℝ)
    (hx : ∀ i, x (e i) = y i) (hu : ∀ i, u (e i) = v i)
    (ha : ∀ i, σ.action s Finset.univ y v i = π.action r Finset.univ x u (e i))
    (hz : ∀ j ∉ Set.range e, x j = 0) (hy : ∀ i, 0 ≤ y i) :
    π.reward r Finset.univ x u ≤ σ.reward s Finset.univ y v := by
  have hn := σ.reward_nonnegative s Finset.univ y v hy
  by_cases hs : ∃ j, π.ActualSelects r Finset.univ x u j
  · obtain ⟨j, hj⟩ := hs
    by_cases he : j ∈ Set.range e
    · obtain ⟨i, rfl⟩ := he
      have hi := π.actualSelects_of_subexecution σ e r s x u y v hu ha i hj
      rw [π.reward_eq_of_actualSelects r Finset.univ x u hj,
        σ.reward_eq_of_actualSelects s Finset.univ y v hi, hx i]
    · rw [π.reward_eq_of_actualSelects r Finset.univ x u hj, hz j he]
      exact hn
  · rw [π.reward_eq_zero_of_no_actualSelection r Finset.univ x u (fun i hi => hs ⟨i, hi⟩)]
    exact hn

end ProphetSecretary.Model
