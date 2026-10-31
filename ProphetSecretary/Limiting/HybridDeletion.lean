import ProphetSecretary.Limiting.HybridPolicy
import Lean.Elab.Tactic.Omega

/-!
# Deleting a Poisson candidate in the hybrid execution

Only the candidate anonymous point is suppressed. Every retained identity, including
its zero-valued arrival, remains in the observed history. The same hybrid rule is
executed on the deleted configuration, so the auxiliary execution cannot learn the
realized Poisson count from the deletion.
-/

open MeasureTheory Set
open scoped BigOperators Classical ENNReal NNReal

namespace ProphetSecretary.Limiting

variable {n m N : ℕ} {Seed : Type*}

lemma retainedIndex_ne_poissonIndex (i : Fin n) (j : Fin N) :
    (i.castAdd N : Fin (n + N)) ≠ j.natAdd n := by
  intro he
  have hv := congrArg Fin.val he
  change i.val = n + j.val at hv
  have hi := i.isLt
  omega

lemma poissonIndex_eq_iff (n : ℕ) (j k : Fin N) :
    (j.natAdd n : Fin (n + N)) = k.natAdd n ↔ j = k := by
  constructor
  · intro he
    apply Fin.ext
    have hv := congrArg Fin.val he
    change n + j.val = n + k.val at hv
    omega
  · rintro rfl
    rfl

lemma retainedHistory_history_erase_poisson (x u : Fin n → ℝ) (v : Fin (m + 1) → Point)
    (j : Fin (m + 1)) (t : ℝ) :
    retainedHistory (ProphetSecretary.Model.history (Finset.univ.erase (j.natAdd n))
      (combinedValues x v) (combinedClocks u v) t) = ProphetSecretary.Model.history Finset.univ x u t := by
  funext i
  have hi := retainedIndex_ne_poissonIndex i j
  simp [retainedHistory, ProphetSecretary.Model.history, combinedValues, combinedClocks, hi]

lemma poissonHistory_history_erase_poisson (x u : Fin n → ℝ) (v : Fin (m + 1) → Point)
    (j : Fin (m + 1)) (t : ℝ) :
    poissonHistory (ProphetSecretary.Model.history (Finset.univ.erase (j.natAdd n))
      (combinedValues x v) (combinedClocks u v) t) =
        observedHistory (configurationMk m (fun k => v (j.succAbove k))) t := by
  calc
    _ = historyMeasure (ProphetSecretary.Model.history (Finset.univ.erase j)
        (fun k => (v k).2) (fun k => (v k).1) t) := by
      unfold poissonHistory historyMeasure
      apply Finset.sum_congr rfl
      intro k _
      simp only [ProphetSecretary.Model.history, Finset.mem_erase, Finset.mem_univ, and_true,
        combinedValues, combinedClocks, Fin.addCases_right, ne_eq, poissonIndex_eq_iff n k j]
    _ = _ := historyMeasure_history_erase v j t

lemma HybridRule.pending_poisson_individual_action (π : HybridRule n Seed) (r : Seed)
    (x u : Fin n → ℝ) (v : Fin (m + 1) → Point) (j : Fin (m + 1)) (i : Fin n) :
    (π.asFinitePolicy (m + 1)).action r (Finset.univ.erase (j.natAdd n))
      (combinedValues x v) (combinedClocks u v) (i.castAdd (m + 1)) =
        (π.asFinitePolicy m).action r Finset.univ (combinedValues x (fun k => v (j.succAbove k)))
          (combinedClocks u (fun k => v (j.succAbove k))) (i.castAdd m) := by
  rw [π.individual_action]
  unfold ProphetSecretary.Model.Policy.action HybridRule.asFinitePolicy
  dsimp only
  simp only [Fin.addCases_left, combinedValues, combinedClocks]
  rw [retainedHistory_history_erase_poisson, poissonHistory_history_erase_poisson]

lemma HybridRule.pending_poisson_poisson_action (π : HybridRule n Seed) (r : Seed)
    (x u : Fin n → ℝ) (v : Fin (m + 1) → Point) (j : Fin (m + 1)) (k : Fin m) :
    (π.asFinitePolicy (m + 1)).action r (Finset.univ.erase (j.natAdd n))
      (combinedValues x v) (combinedClocks u v) ((j.succAbove k).natAdd n) =
        (π.asFinitePolicy m).action r Finset.univ (combinedValues x (fun l => v (j.succAbove l)))
          (combinedClocks u (fun l => v (j.succAbove l))) (k.natAdd n) := by
  rw [π.poisson_action]
  unfold ProphetSecretary.Model.Policy.action HybridRule.asFinitePolicy
  dsimp only
  simp only [Fin.addCases_right, combinedValues, combinedClocks]
  rw [retainedHistory_history_erase_poisson, poissonHistory_history_erase_poisson]

/-- The pending Poisson execution retains every individual offer and its identity.
Only the distinguished anonymous occurrence is deleted, with the same rule and seed. -/
lemma HybridRule.pendingPoissonTime_eq_deleted (π : HybridRule n Seed) (r : Seed)
    (x u : Fin n → ℝ) (v : Fin (m + 1) → Point) (j : Fin (m + 1)) :
    (π.asFinitePolicy (m + 1)).pendingTime r (combinedValues x v) (combinedClocks u v) (j.natAdd n) =
      π.stoppingTime r x u (configurationMk m (fun k => v (j.succAbove k))) := by
  let ψ := π.asFinitePolicy (m + 1)
  let χ := π.asFinitePolicy m
  let q : Fin (n + (m + 1)) := j.natAdd n
  let D := Finset.univ.erase q
  let z := fun k : Fin m => v (j.succAbove k)
  let X := combinedValues x v
  let U := combinedClocks u v
  let Y := combinedValues x z
  let W := combinedClocks u z
  have hI (i : Fin n) : ψ.action r D X U (i.castAdd (m + 1)) = χ.action r Finset.univ Y W (i.castAdd m) :=
    π.pending_poisson_individual_action r x u v j i
  have hP (k : Fin m) : ψ.action r D X U ((j.succAbove k).natAdd n) = χ.action r Finset.univ Y W (k.natAdd n) :=
    π.pending_poisson_poisson_action r x u v j k
  have hIMem (i : Fin n) : i.castAdd (m + 1) ∈ ψ.accepted r D X U ↔ i.castAdd m ∈ χ.accepted r Finset.univ Y W := by
    constructor
    · intro hi
      exact (χ.mem_accepted _ _ _ _ _).mpr ⟨Finset.mem_univ _, (hI i).symm.trans ((ψ.mem_accepted _ _ _ _ _).mp hi).2⟩
    · intro hi
      exact (ψ.mem_accepted _ _ _ _ _).mpr
        ⟨Finset.mem_erase.mpr ⟨retainedIndex_ne_poissonIndex i j, Finset.mem_univ _⟩,
          (hI i).trans ((χ.mem_accepted _ _ _ _ _).mp hi).2⟩
  have hPMem (k : Fin m) : (j.succAbove k).natAdd n ∈ ψ.accepted r D X U ↔ k.natAdd n ∈ χ.accepted r Finset.univ Y W := by
    have hneq : (j.succAbove k).natAdd n ≠ q := by
      intro he
      exact (Fin.succAbove_ne j k) ((poissonIndex_eq_iff n (j.succAbove k) j).mp he)
    constructor
    · intro hk
      exact (χ.mem_accepted _ _ _ _ _).mpr ⟨Finset.mem_univ _, (hP k).symm.trans ((ψ.mem_accepted _ _ _ _ _).mp hk).2⟩
    · intro hk
      exact (ψ.mem_accepted _ _ _ _ _).mpr ⟨Finset.mem_erase.mpr ⟨hneq, Finset.mem_univ _⟩,
        (hP k).trans ((χ.mem_accepted _ _ _ _ _).mp hk).2⟩
  change ψ.stoppingTime r D X U = χ.stoppingTime r Finset.univ Y W
  apply le_antisymm
  · apply (χ.le_stoppingTime_iff _ _ _ _ _).mpr
    refine ⟨ψ.stoppingTime_le_one _ _ _ _, ?_⟩
    intro k hk
    revert hk
    refine Fin.addCases (fun i hi => ?_) (fun l hl => ?_) k
    · have he := ψ.stoppingTime_le_of_accepted r D X U (i.castAdd (m + 1)) ((hIMem i).mpr hi)
      simpa only [U, W, combinedClocks, Fin.addCases_left] using he
    · have he := ψ.stoppingTime_le_of_accepted r D X U ((j.succAbove l).natAdd n) ((hPMem l).mpr hl)
      simpa only [U, W, z, combinedClocks, Fin.addCases_right] using he
  · apply (ψ.le_stoppingTime_iff _ _ _ _ _).mpr
    refine ⟨χ.stoppingTime_le_one _ _ _ _, ?_⟩
    intro k hk
    revert hk
    refine Fin.addCases (fun i hi => ?_) (fun l hl => ?_) k
    · have he := χ.stoppingTime_le_of_accepted r Finset.univ Y W (i.castAdd m) ((hIMem i).mp hi)
      simpa only [U, W, combinedClocks, Fin.addCases_left] using he
    · have hneq : l.natAdd n ≠ q := (Finset.mem_erase.mp ((ψ.mem_accepted _ _ _ _ _).mp hl).1).1
      have hlj : l ≠ j := by
        intro h
        apply hneq
        simp only [h, q]
      obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hlj
      have hl' : (j.succAbove a).natAdd n ∈ ψ.accepted r D X U := by rw [ha]; exact hl
      have he := χ.stoppingTime_le_of_accepted r Finset.univ Y W (a.natAdd n) ((hPMem a).mp hl')
      simpa only [U, W, z, combinedClocks, Fin.addCases_right, ha] using he

lemma HybridRule.reachesPoisson_iff_le_deleted (π : HybridRule n Seed) (r : Seed)
    (x u : Fin n → ℝ) (ω : Configuration) (j : Fin ω.1) (ht : (ω.2 j).1 ≤ 1) :
    π.ReachesPoisson r x u ω j ↔ (ω.2 j).1 ≤ π.stoppingTime r x u (erasePoint ω j) := by
  rcases ω with ⟨N, v⟩
  cases N with
  | zero => exact Fin.elim0 j
  | succ m =>
    change (π.asFinitePolicy (m + 1)).Reaches r (combinedValues x v) (combinedClocks u v) (j.natAdd n) ↔ _
    rw [(π.asFinitePolicy (m + 1)).reaches_iff_le_pendingTime r _ _ (j.natAdd n)
      (by simpa only [combinedClocks, Fin.addCases_right] using ht), π.pendingPoissonTime_eq_deleted r x u v j]
    simp only [combinedClocks, Fin.addCases_right, erasePoint]

end ProphetSecretary.Limiting
