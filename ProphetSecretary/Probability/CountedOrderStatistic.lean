import ProphetSecretary.Probability.CountedMedian

/-!
# Counted finite order statistics

The same counted sort used for the planner median also implements the pilot
quantile and the minimum and maximum of finite training rounds.
-/

namespace ProphetSecretary.Probability

def countedOrderStatistic {α : Type*} [LinearOrder α] {n : ℕ}
    (k : Fin n) (x : Fin n → α) : α × ℕ :=
  let q := countedInsertionSort (fun a b => b ≤ a) (List.ofFn x)
  (q.1.get ⟨k.val, by
    rw [countedInsertionSort_value, List.length_insertionSort, List.length_ofFn]
    exact k.isLt⟩, q.2 + 3*n + 1)

lemma countedOrderStatistic_value {α : Type*} [LinearOrder α] {n : ℕ}
    (k : Fin n) (x : Fin n → α) :
    (countedOrderStatistic k x).1 = sampleOrderStatistic (k.val+1) (by omega) (by simp) x := by
  let q := countedInsertionSort (fun a b => b ≤ a) (List.ofFn x)
  have hq : q.1 = List.insertionSort (fun a b => b ≤ a) (List.ofFn x) :=
    countedInsertionSort_value _ _
  have hLen : q.1.length = n := by rw [hq, List.length_insertionSort, List.length_ofFn]
  have hSort : q.1.SortedGE := by
    rw [hq]
    exact (List.pairwise_insertionSort (fun a b : α => b ≤ a) _).sortedGE
  let j : Fin q.1.length := ⟨k.val, hLen.symm ▸ k.isLt⟩
  have he (c : α) : c ≤ (countedOrderStatistic k x).1 ↔
      k.val+1 ≤ (Finset.univ.filter (fun i => c ≤ x i)).card := by
    change c ≤ q.1.get j ↔ _
    rw [le_sorted_get_iff_countP _ hSort]
    have hp := (List.perm_insertionSort (fun a b : α => b ≤ a) (List.ofFn x)).countP_eq
      (fun a => decide (c ≤ a))
    rw [← hq] at hp
    rw [hp, countP_ofFn_eq_card]
  apply le_antisymm
  · apply (le_sampleOrderStatistic_iff (k.val+1) (by omega) (by simp) x _).2
    exact (he _).1 le_rfl
  · apply (he _).2
    exact (le_sampleOrderStatistic_iff (k.val+1) (by omega) (by simp) x _).1 le_rfl

lemma countedOrderStatistic_work {α : Type*} [LinearOrder α] {n : ℕ}
    (k : Fin n) (x : Fin n → α) :
    (countedOrderStatistic k x).2 ≤ 8*(n+1)^2 := by
  have h := countedInsertionSort_work (fun a b : α => b ≤ a) (List.ofFn x)
  simp only [List.length_ofFn] at h
  dsimp only [countedOrderStatistic]
  nlinarith

end ProphetSecretary.Probability
