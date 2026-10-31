import ProphetSecretary.Model.Outcome

/-!
# Equality of actual executions from their candidate actions

Equality is proved on a fixed complete value/clock vector. Potential actions
at candidates after stopping are only analytical evaluations; the executed
policies retain their original observation rules.
-/
open scoped Classical
namespace ProphetSecretary.Model
variable {n : ℕ} {Seed T : Type*}

lemma Policy.outcomes_eq_of_actions_eq (π : Policy Seed n) (σ : Policy T n) (r : Seed) (s : T)
    (D : Finset (Fin n)) (x u : Fin n → ℝ)
    (ha : ∀ i, π.action r D x u i = σ.action s D x u i) :
    π.reward r D x u = σ.reward s D x u ∧ π.stoppingTime r D x u = σ.stoppingTime s D x u := by
  have hacc : π.accepted r D x u = σ.accepted s D x u := by
    ext i
    simp only [Policy.mem_accepted,ha i]
  have htimes : π.stopTimes r D x u = σ.stopTimes s D x u := by
    simp only [Policy.stopTimes,hacc]
  have hstop : π.stoppingTime r D x u = σ.stoppingTime s D x u := by
    unfold Policy.stoppingTime
    simp only [htimes]
  refine ⟨?_,hstop⟩
  have hselect (i : Fin n) : π.ActualSelects r D x u i ↔ σ.ActualSelects s D x u i := by
    simp only [Policy.ActualSelects,Policy.Selects,hacc,hstop]
  unfold Policy.reward
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : σ.ActualSelects s D x u i
  · rw [if_pos hi,if_pos ((hselect i).mpr hi)]
  · rw [if_neg hi,if_neg (fun h => hi ((hselect i).mp h))]

end ProphetSecretary.Model
