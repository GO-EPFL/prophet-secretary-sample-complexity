import ProphetSecretary.Limiting.HybridOutcomes
import ProphetSecretary.Model.ZeroSimulation
import ProphetSecretary.Model.SubexecutionComparison

/-!
# Causal simulation of individual zero identities in a hybrid process

Independent virtual clocks reconstruct the entire observed zero-identity past.
Only that past is supplied to the original callbacks. The simulator deletes
zero candidates from the acceptance set, increasing duration and preserving
or increasing reward; it never observes future individual offers.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.HybridZeroSimulation

variable {n k N : ℕ} {Seed : Type*}

noncomputable def simulate (π : HybridRule (n + k) Seed) : HybridRule n (Seed × (Fin k → ℝ)) where
  individual rz t i x H Ξ := π.individual rz.1 t (i.castAdd k) x
    (Model.ZeroSimulation.augmentedHistory H rz.2 t) Ξ
  poisson rz t x H Ξ := π.poisson rz.1 t x (Model.ZeroSimulation.augmentedHistory H rz.2 t) Ξ

/-- Insert the zero block between retained base identities and anonymous indices.
This embedding is used only to compare analytical finite-array executions. -/
def keepEmbedding (n k N : ℕ) : Fin (n + N) ↪o Fin (n + k + N) :=
  OrderEmbedding.ofStrictMono (Fin.addCases (fun i => (i.castAdd k).castAdd N) (fun j => j.natAdd (n + k))) (by
    intro a b hab
    induction a using Fin.addCases with
    | left a =>
      induction b using Fin.addCases with
      | left b =>
        simp only [Fin.addCases_left]
        change a.val < b.val at hab ⊢
        exact hab
      | right b =>
        simp only [Fin.addCases_left, Fin.addCases_right]
        change a.val < n + k + b.val
        omega
    | right a =>
      induction b using Fin.addCases with
      | left b =>
        have hbad : n + a.val < b.val := hab
        omega
      | right b => simpa only [Fin.addCases_right, Fin.natAdd_lt_natAdd_iff] using hab)

lemma keepEmbedding_left (i : Fin n) : keepEmbedding n k N (i.castAdd N) = (i.castAdd k).castAdd N := by
  change (Fin.addCases (fun j : Fin n => (j.castAdd k).castAdd N) (fun j : Fin N => j.natAdd (n + k)) :
    Fin (n + N) → Fin (n + k + N)) (i.castAdd N) = _
  exact Fin.addCases_left i

lemma keepEmbedding_right (j : Fin N) : keepEmbedding n k N (j.natAdd n) = j.natAdd (n + k) := by
  change (Fin.addCases (fun i : Fin n => (i.castAdd k).castAdd N) (fun j : Fin N => j.natAdd (n + k)) :
    Fin (n + N) → Fin (n + k + N)) (j.natAdd n) = _
  exact Fin.addCases_right j

lemma combinedValues_keep (x : Fin n → ℝ) (v : Fin N → Point) (i : Fin (n + N)) :
    combinedValues (Model.ZeroSimulation.appendValues (m := k) x) v (keepEmbedding n k N i) = combinedValues x v i := by
  induction i using Fin.addCases with
  | left i => simp only [keepEmbedding_left, combinedValues, Fin.addCases_left, Model.ZeroSimulation.appendValues]
  | right j => simp only [keepEmbedding_right, combinedValues, Fin.addCases_right]

lemma combinedClocks_keep (u : Fin n → ℝ) (z : Fin k → ℝ) (v : Fin N → Point) (i : Fin (n + N)) :
    combinedClocks (Model.ZeroSimulation.appendClocks u z) v (keepEmbedding n k N i) = combinedClocks u v i := by
  induction i using Fin.addCases with
  | left i => simp only [keepEmbedding_left, combinedClocks, Fin.addCases_left, Model.ZeroSimulation.appendClocks]
  | right j => simp only [keepEmbedding_right, combinedClocks, Fin.addCases_right]

lemma action_eq (π : HybridRule (n + k) Seed) (r : Seed) (x u : Fin n → ℝ) (z : Fin k → ℝ)
    (v : Fin N → Point) (i : Fin (n + N)) :
    ((simulate π).asFinitePolicy N).action (r, z) Finset.univ (combinedValues x v) (combinedClocks u v) i =
      (π.asFinitePolicy N).action r Finset.univ (combinedValues (Model.ZeroSimulation.appendValues x) v)
        (combinedClocks (Model.ZeroSimulation.appendClocks u z) v) (keepEmbedding n k N i) := by
  induction i using Fin.addCases with
  | left i =>
    rw [keepEmbedding_left, HybridRule.individual_action, HybridRule.individual_action]
    simp only [simulate, Model.ZeroSimulation.appendClocks, Model.ZeroSimulation.appendValues, Fin.addCases_left]
    rw [Model.ZeroSimulation.augmentedHistory_history x u z le_rfl]
  | right j =>
    rw [keepEmbedding_right, HybridRule.poisson_action, HybridRule.poisson_action]
    simp only [simulate]
    rw [Model.ZeroSimulation.augmentedHistory_history x u z le_rfl]

lemma removed_values_zero (x : Fin n → ℝ) (v : Fin N → Point) (j : Fin (n + k + N))
    (hj : j ∉ Set.range (keepEmbedding n k N)) :
    combinedValues (Model.ZeroSimulation.appendValues (m := k) x) v j = 0 := by
  induction j using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i => exact False.elim (hj ⟨i.castAdd N, keepEmbedding_left i⟩)
    | right i => simp only [combinedValues, Fin.addCases_left, Model.ZeroSimulation.appendValues, Fin.addCases_right]
  | right j => exact False.elim (hj ⟨j.natAdd n, keepEmbedding_right j⟩)

lemma stoppingTime_le_simulated (π : HybridRule (n + k) Seed) (r : Seed)
    (x u : Fin n → ℝ) (z : Fin k → ℝ) (ω : Configuration) :
    π.stoppingTime r (Model.ZeroSimulation.appendValues x) (Model.ZeroSimulation.appendClocks u z) ω ≤
      (simulate π).stoppingTime (r, z) x u ω :=
  (π.asFinitePolicy ω.1).stoppingTime_le_of_subexecution ((simulate π).asFinitePolicy ω.1)
    (keepEmbedding n k ω.1).toEmbedding r (r, z) _ _ _ _
      (combinedClocks_keep u z ω.2) (action_eq π r x u z ω.2)

lemma finiteReward_le_simulated (π : HybridRule (n + k) Seed) (r : Seed)
    (x u : Fin n → ℝ) (z : Fin k → ℝ) (ω : Configuration)
    (hx : ∀ i, 0 ≤ combinedValues x ω.2 i) :
    (π.asFinitePolicy ω.1).reward r Finset.univ (combinedValues (Model.ZeroSimulation.appendValues x) ω.2)
      (combinedClocks (Model.ZeroSimulation.appendClocks u z) ω.2) ≤
    ((simulate π).asFinitePolicy ω.1).reward (r, z) Finset.univ (combinedValues x ω.2) (combinedClocks u ω.2) :=
  (π.asFinitePolicy ω.1).reward_le_of_zero_subexecution ((simulate π).asFinitePolicy ω.1)
    (keepEmbedding n k ω.1) r (r, z) _ _ _ _ (combinedValues_keep x ω.2)
      (combinedClocks_keep u z ω.2) (action_eq π r x u z ω.2) (removed_values_zero x ω.2) hx

lemma reward_zero_eq_finite (π : HybridRule n Seed) (r : Seed) (x u : Fin n → ℝ) (ω : Configuration) :
    π.reward 0 r x u ω = (π.asFinitePolicy ω.1).reward r Finset.univ (combinedValues x ω.2) (combinedClocks u ω.2) := by
  unfold HybridRule.reward
  split_ifs with hs
  · rfl
  · symm
    exact (π.asFinitePolicy ω.1).reward_eq_zero_of_no_actualSelection _ _ _ _ (fun i hi => hs ⟨i, hi⟩)

lemma reward_le_simulated (π : HybridRule (n + k) Seed) (r : Seed)
    (x u : Fin n → ℝ) (z : Fin k → ℝ) (ω : Configuration)
    (hx : ∀ i, 0 ≤ combinedValues x ω.2 i) :
    π.reward 0 r (Model.ZeroSimulation.appendValues x) (Model.ZeroSimulation.appendClocks u z) ω ≤
      (simulate π).reward 0 (r, z) x u ω := by
  rw [reward_zero_eq_finite, reward_zero_eq_finite]
  exact finiteReward_le_simulated π r x u z ω hx

variable [MeasurableSpace Seed]

lemma simulate_isMeasurable (π : HybridRule (n + k) Seed) (hπ : π.IsMeasurable) :
    (simulate π).IsMeasurable := by
  constructor
  · let Ω := (Seed × (Fin k → ℝ)) × (ℝ × (Fin n × (ℝ × (Model.History n × Measure Point))))
    have hr : Measurable (fun q : Ω => q.1.1) := by fun_prop
    have ht : Measurable (fun q : Ω => q.2.1) := by fun_prop
    have hi : Measurable (fun q : Ω => (q.2.2.1).castAdd k) := by fun_prop
    have hx : Measurable (fun q : Ω => q.2.2.2.1) := by fun_prop
    have hΞ : Measurable (fun q : Ω => q.2.2.2.2.2) := by fun_prop
    have hH : Measurable (fun q : Ω => Model.ZeroSimulation.augmentedHistory q.2.2.2.2.1 q.1.2 q.2.1) :=
      Model.ZeroSimulation.measurable_augmentedHistory
        (fun i => (measurable_pi_apply i).comp (by fun_prop))
        (fun j => (measurable_pi_apply j).comp (by fun_prop)) ht
    exact hπ.1.comp (hr.prodMk (ht.prodMk (hi.prodMk (hx.prodMk (hH.prodMk hΞ)))))
  · let Ω := (Seed × (Fin k → ℝ)) × (Point × (Model.History n × Measure Point))
    have hr : Measurable (fun q : Ω => q.1.1) := by fun_prop
    have ht : Measurable (fun q : Ω => q.2.1.1) := by fun_prop
    have hx : Measurable (fun q : Ω => q.2.1.2) := by fun_prop
    have hΞ : Measurable (fun q : Ω => q.2.2.2) := by fun_prop
    have hH : Measurable (fun q : Ω => Model.ZeroSimulation.augmentedHistory q.2.2.1 q.1.2 q.2.1.1) :=
      Model.ZeroSimulation.measurable_augmentedHistory
        (fun i => (measurable_pi_apply i).comp (by fun_prop))
        (fun j => (measurable_pi_apply j).comp (by fun_prop)) ht
    have hp : Measurable (fun q : Ω => (q.2.1.1, q.2.1.2)) := ht.prodMk hx
    exact hπ.2.comp (hr.prodMk (hp.prodMk (hH.prodMk hΞ)))

end ProphetSecretary.Limiting.HybridZeroSimulation
