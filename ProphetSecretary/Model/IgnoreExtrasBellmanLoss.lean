import ProphetSecretary.Model.BellmanPerformance
import ProphetSecretary.Model.Simulation
import ProphetSecretary.Analysis.StoppingDecisionLoss

/-!
# Reached Bellman loss after adding ignored zero identities

Actions and reach at original labels are preserved by the actual causal
ignore-extra construction. Extra deterministic-zero observations have zero
Bellman loss against any nonnegative design continuation. For an arbitrary
analytical comparison continuation, the remaining loss error is bounded by
the sum of its continuation errors, with coefficient one.
-/
open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Model
variable {m n : ℕ} {Seed : Type*}

lemma Policy.ignoreExtras_action_iff (π : Policy Seed m) (e : Fin m ↪ Fin n)
    (r : Seed) (x u : Fin n → ℝ) (i : Fin m) :
    (π.ignoreExtras e).action r Finset.univ x u (e i) = true ↔
      π.action r Finset.univ (x ∘ e) (u ∘ e) i = true := by
  have h := π.ignoreExtras_mem_accepted e r x u (e i)
  simpa only [Policy.mem_accepted,Finset.mem_univ,true_and,e.injective.eq_iff,exists_eq_left] using h

lemma Policy.ignoreExtras_action_eq (π : Policy Seed m) (e : Fin m ↪ Fin n)
    (r : Seed) (x u : Fin n → ℝ) (i : Fin m) :
    (π.ignoreExtras e).action r Finset.univ x u (e i) = π.action r Finset.univ (x ∘ e) (u ∘ e) i := by
  have h := π.ignoreExtras_action_iff e r x u i
  cases ha : (π.ignoreExtras e).action r Finset.univ x u (e i) <;>
    cases hb : π.action r Finset.univ (x ∘ e) (u ∘ e) i <;> simp_all

lemma Policy.ignoreExtras_action_not_true (π : Policy Seed m) (e : Fin m ↪ Fin n)
    (r : Seed) (x u : Fin n → ℝ) (j : Fin n) (hj : ∀ i, e i ≠ j) :
    (π.ignoreExtras e).action r Finset.univ x u j ≠ true := by
  intro hA
  have hMem : j ∈ (π.ignoreExtras e).accepted r Finset.univ x u :=
    ((π.ignoreExtras e).mem_accepted r Finset.univ x u j).mpr ⟨Finset.mem_univ _,hA⟩
  obtain ⟨i,hi,_⟩ := (π.ignoreExtras_mem_accepted e r x u j).mp hMem
  exact hj i hi

lemma Policy.ignoreExtras_reaches_iff (π : Policy Seed m) (e : Fin m ↪ Fin n)
    (r : Seed) (x u : Fin n → ℝ) (i : Fin m) :
    (π.ignoreExtras e).Reaches r x u (e i) ↔ π.Reaches r (x ∘ e) (u ∘ e) i := by
  unfold Policy.Reaches
  rw [π.ignoreExtras_stoppingTime]
  rfl

/-- No class restriction is imposed on the original causal policy. The
comparison continuation vector v is analytical and is not an input to it. -/
theorem Policy.ignoreExtras_reachedBellmanLoss_error (π : Policy Seed m) (e : Fin m ↪ Fin n)
    (Q : Instance n) (hQ : Integrable Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (r : Seed) (x u : Fin n → ℝ) (hz : ∀ j, (∀ i, e i ≠ j) → x j = 0) (v : Fin m → ℝ) :
    |(π.ignoreExtras e).reachedBellmanLoss Q w c r x u-
      (∑ i : Fin m, if π.Reaches r (x ∘ e) (u ∘ e) i then
        ProphetSecretary.Analysis.gapLoss (π.action r Finset.univ (x ∘ e) (u ∘ e) i) (w*x (e i)-v i) else 0)| ≤
      ∑ i : Fin m, |Q.continuationAtArrival w c x u (e i)-v i| := by
  let f : Fin n → ℝ := fun j => if (π.ignoreExtras e).Reaches r x u j then
    (π.ignoreExtras e).arrivalBellmanLoss Q w c r x u j else 0
  let D := Finset.univ.map e
  have hOutside (j : Fin n) (hj : j ∉ D) : f j = 0 := by
    have hNo : ∀ i, e i ≠ j := fun i hi => hj (Finset.mem_map.mpr ⟨i,Finset.mem_univ _,hi⟩)
    have hx := hz j hNo
    have hAct := π.ignoreExtras_action_not_true e r x u j hNo
    have hV := Q.continuationAtArrival_nonnegative hQ hw hc x u j
    dsimp only [f]
    split_ifs
    · unfold Policy.arrivalBellmanLoss
      rw [if_neg hAct,hx,mul_zero,max_eq_right hV,sub_self]
    · rfl
  have hSum : (π.ignoreExtras e).reachedBellmanLoss Q w c r x u = ∑ i : Fin m, f (e i) := by
    change (∑ j : Fin n, f j) = _
    calc
      _ = ∑ j ∈ D, f j := (Finset.sum_subset (Finset.subset_univ D) (fun j _ hj => hOutside j hj)).symm
      _ = _ := by simp only [D,Finset.sum_map]
  have hTerm (i : Fin m) : f (e i) = if π.Reaches r (x ∘ e) (u ∘ e) i then
      ProphetSecretary.Analysis.gapLoss (π.action r Finset.univ (x ∘ e) (u ∘ e) i)
        (w*x (e i)-Q.continuationAtArrival w c x u (e i)) else 0 := by
    dsimp only [f]
    rw [π.ignoreExtras_reaches_iff]
    split_ifs
    · unfold Policy.arrivalBellmanLoss
      rw [π.ignoreExtras_action_eq]
      exact (ProphetSecretary.Analysis.gapLoss_eq_decisionLoss _ _ _).symm
    · rfl
  rw [hSum]
  simp_rw [hTerm]
  rw [← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  by_cases hR : π.Reaches r (x ∘ e) (u ∘ e) i
  · rw [if_pos hR,if_pos hR]
    have h := ProphetSecretary.Analysis.gapLoss_lipschitz
      (π.action r Finset.univ (x ∘ e) (u ∘ e) i) (w*x (e i)-v i)
      (w*x (e i)-Q.continuationAtArrival w c x u (e i))
    have he : (w*x (e i)-Q.continuationAtArrival w c x u (e i))-(w*x (e i)-v i) =
        -(Q.continuationAtArrival w c x u (e i)-v i) := by ring
    rw [he,abs_neg] at h
    exact h
  · rw [if_neg hR,if_neg hR,sub_self,abs_zero]
    exact abs_nonneg _

end ProphetSecretary.Model
