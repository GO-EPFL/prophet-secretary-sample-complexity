import ProphetSecretary.Statistics.PlannerSamplerPhases

/-!
# A counted implementation of the complete planner transition

Lists represent active subsets. The program computes both fallback maxima,
constructs and evaluates its cumulative expressions, and counts every coin,
maximum, membership, and output-list traversal. Its interpretation as finite
sets is the fixed-uniform sampler proved in `PlannerUniformSampler`.
-/

open scoped Classical BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability
open ArithmeticExpression

abbrev PlannerFieldSeed (n : ℕ) (K : Type*) := (K × (Fin n → K)) × (K × ((Fin n → K) × (Fin n → K)))
abbrev PlannerListOutput (n : ℕ) (K : Type*) := Option (Fin n) × K × List (Fin n)

variable {n : ℕ}

lemma countedMaximumScan_mem_of_mem (l : List (Fin n)) (a : Fin n) (ha : a ∈ l) :
    (countedMaximumScan a l).1 ∈ l := by
  rcases List.mem_cons.mp (countedMaximumScan_mem a l) with h | h
  · rw [h]
    exact ha
  · exact h

lemma countedPlannerFirstChoice_mem {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (fallback : Fin n) (p : Fin n → K) (u : K) (hf : fallback ∈ l) :
    (countedPlannerFirstChoice l fallback p u).1 ∈ l := by
  rw [countedPlannerFirstChoice, arithmeticGeneratedMinimumScan_value]
  rcases List.mem_cons.mp (arithmeticMinimumScan_mem l
    (fun i => (countedPlannerFirstPrefix l i).1) p u fallback) with h | h
  · rw [h]
    exact hf
  · exact h

lemma countedPlannerUniformIdentity_mem {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (fallback : Fin n) (u : K) (hf : fallback ∈ l) :
    (countedPlannerUniformIdentity l fallback u).1 ∈ l := by
  rw [countedPlannerUniformIdentity, arithmeticGeneratedMinimumScan_value]
  rcases List.mem_cons.mp (arithmeticMinimumScan_mem l
    (fun i => (countedPlannerUniformPrefix l i).1) (fun _ : Fin n => (0 : K)) u fallback) with h | h
  · rw [h]
    exact hf
  · exact h

def countedPlannerFirstStage {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (a : Fin n) (p : Fin n → K) (seed : K × (Fin n → K)) :
    (Fin n × List (Fin n)) × ℕ :=
  let maximum := countedMaximumScan a l
  let first := countedPlannerFirstChoice l maximum.1 p seed.1
  let coins := countedPlannerFirstCoins l p first.1 seed.2
  ((first.1, first.1 :: coins.1), maximum.2 + first.2 + coins.2 + 2)

lemma countedPlannerFirstStage_invariants {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (hl : l.Nodup) (a : Fin n) (ha : a ∈ l)
    (p : Fin n → K) (seed : K × (Fin n → K)) :
    let D := (countedPlannerFirstStage l a p seed).1.2
    D.Nodup ∧ D.toFinset ⊆ l.toFinset ∧ D.length ≤ l.length := by
  let maximum := countedMaximumScan a l
  let first := countedPlannerFirstChoice l maximum.1 p seed.1
  let coins := countedPlannerFirstCoins l p first.1 seed.2
  have hFirst : first.1 ∈ l := countedPlannerFirstChoice_mem l maximum.1 p seed.1
    (countedMaximumScan_mem_of_mem l a ha)
  have hCoins : coins.1.Nodup := by
    rw [countedPlannerFirstCoins_value]
    exact hl.filter _
  have hNot : first.1 ∉ coins.1 := by
    rw [countedPlannerFirstCoins_value]
    simp
  have hD : (first.1 :: coins.1).Nodup := List.nodup_cons.mpr ⟨hNot, hCoins⟩
  have hSub : (first.1 :: coins.1).toFinset ⊆ l.toFinset := by
    intro i hi
    simp only [List.mem_toFinset, List.mem_cons] at hi
    rcases hi with h | h
    · rw [h]
      exact List.mem_toFinset.mpr hFirst
    · rw [countedPlannerFirstCoins_value] at h
      exact List.mem_toFinset.mpr (List.mem_filter.mp h).1
  have hLen := Finset.card_le_card hSub
  rw [List.toFinset_card_of_nodup hD, List.toFinset_card_of_nodup hl] at hLen
  change (first.1 :: coins.1).Nodup ∧ _ ∧ _
  exact ⟨hD, hSub, hLen⟩

lemma countedPlannerFirstStage_work {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (a : Fin n) (p : Fin n → K) (seed : K × (Fin n → K)) :
    (countedPlannerFirstStage l a p seed).2 ≤ 130 * (l.length + 1) ^ 3 := by
  have hm := countedMaximumScan_work a l
  have hf := countedPlannerFirstChoice_work l (countedMaximumScan a l).1 p seed.1
  have hc := countedPlannerFirstCoins_work l p
    (countedPlannerFirstChoice l (countedMaximumScan a l).1 p seed.1).1 seed.2
  dsimp only [countedPlannerFirstStage]
  rw [hm]
  nlinarith [Nat.zero_le (l.length ^ 2), Nat.zero_le (l.length ^ 3)]

def countedPlannerUniformSamplerBody {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (a : Fin n) (p : Fin n → K) (seed : PlannerFieldSeed n K) :
    PlannerListOutput n K × ℕ :=
  let first := countedPlannerFirstStage l a p seed.1
  let D := first.1.2
  let maximum := countedMaximumScan first.1.1 D
  let identity := countedPlannerUniformIdentity D maximum.1 seed.2.1
  let fraction := countedPlannerFraction D seed.2.2.1
  let tail := countedPlannerTailCoins l D fraction.1 seed.2.2.2
  let companions := countedPredicateFilter (fun j => j ≠ identity.1) D
  let output := countedAppend companions.1 tail.1
  ((some identity.1, fraction.1, output.1),
    first.2 + maximum.2 + identity.2 + fraction.2 + tail.2 + companions.2 + output.2 + 2)

def countedPlannerUniformSampler {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (p : Fin n → K) (seed : PlannerFieldSeed n K) : PlannerListOutput n K × ℕ :=
  match l with
  | [] => ((none, 0, []), 1)
  | a :: t => countedPlannerUniformSamplerBody (a :: t) a p seed

lemma countedPlannerUniformSamplerBody_work {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (hl : l.Nodup) (a : Fin n) (ha : a ∈ l)
    (p : Fin n → K) (seed : PlannerFieldSeed n K) :
    (countedPlannerUniformSamplerBody l a p seed).2 ≤ 1000 * (l.length + 1) ^ 3 := by
  let first := countedPlannerFirstStage l a p seed.1
  let D := first.1.2
  let maximum := countedMaximumScan first.1.1 D
  let identity := countedPlannerUniformIdentity D maximum.1 seed.2.1
  let fraction := countedPlannerFraction D seed.2.2.1
  let tail := countedPlannerTailCoins l D fraction.1 seed.2.2.2
  let companions := countedPredicateFilter (fun j => j ≠ identity.1) D
  let output := countedAppend companions.1 tail.1
  have hD : D.length ≤ l.length := (countedPlannerFirstStage_invariants l hl a ha p seed.1).2.2
  have hFirst := countedPlannerFirstStage_work l a p seed.1
  have hMax := countedMaximumScan_work first.1.1 D
  have hIdentity := countedPlannerUniformIdentity_work D maximum.1 seed.2.1
  have hFraction := countedPlannerFraction_work D seed.2.2.1
  have hTail := countedPlannerTailCoins_work l D fraction.1 seed.2.2.2
  have hCompanions := countedPredicateFilter_work (fun j => j ≠ identity.1) D
  have hOutput := countedAppend_work companions.1 tail.1
  have hCLen : companions.1.length ≤ D.length := by
    rw [countedPredicateFilter_value]
    exact List.length_filter_le _ _
  have hSquare : (D.length + 1) ^ 2 ≤ (l.length + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hIdentity' : identity.2 ≤ 30 * (l.length + 1) ^ 2 :=
    hIdentity.trans (Nat.mul_le_mul_left 30 hSquare)
  have hTail' : tail.2 ≤ 1 + l.length * (2 * l.length + 5) :=
    hTail.trans (Nat.add_le_add_left (Nat.mul_le_mul_left l.length (by omega)) 1)
  change first.2 + maximum.2 + identity.2 + fraction.2 + tail.2 + companions.2 + output.2 + 2 ≤ _
  nlinarith [Nat.zero_le (l.length ^ 2), Nat.zero_le (l.length ^ 3)]

/-- A deterministic arithmetic/comparison/random-read bound on every raw seed. -/
theorem countedPlannerUniformSampler_work {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (hl : l.Nodup) (p : Fin n → K) (seed : PlannerFieldSeed n K) :
    (countedPlannerUniformSampler l p seed).2 ≤ 1000 * (l.length + 1) ^ 3 := by
  cases l with
  | nil => norm_num [countedPlannerUniformSampler]
  | cons a t =>
    exact countedPlannerUniformSamplerBody_work (a :: t) hl a List.mem_cons_self p seed

lemma countedPlannerUniformSamplerBody_nodup {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (hl : l.Nodup) (a : Fin n) (ha : a ∈ l)
    (p : Fin n → K) (seed : PlannerFieldSeed n K) :
    (countedPlannerUniformSamplerBody l a p seed).1.2.2.Nodup := by
  let first := countedPlannerFirstStage l a p seed.1
  let D := first.1.2
  let maximum := countedMaximumScan first.1.1 D
  let identity := countedPlannerUniformIdentity D maximum.1 seed.2.1
  let fraction := countedPlannerFraction D seed.2.2.1
  let tail := countedPlannerTailCoins l D fraction.1 seed.2.2.2
  let companions := countedPredicateFilter (fun j => j ≠ identity.1) D
  have hD : D.Nodup := (countedPlannerFirstStage_invariants l hl a ha p seed.1).1
  change (countedAppend companions.1 tail.1).1.Nodup
  rw [countedAppend_value, countedPredicateFilter_value, countedPlannerTailCoins_value]
  apply List.nodup_append.mpr
  refine ⟨hD.filter _, hl.filter _, ?_⟩
  intro i hi j hj hij
  have hiD : i ∈ D := (List.mem_filter.mp hi).1
  have hjNot : j ∉ D := (of_decide_eq_true (List.mem_filter.mp hj).2).1
  exact hjNot (hij ▸ hiD)

lemma countedPlannerUniformSampler_nodup {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (hl : l.Nodup) (p : Fin n → K) (seed : PlannerFieldSeed n K) :
    (countedPlannerUniformSampler l p seed).1.2.2.Nodup := by
  cases l with
  | nil => exact List.nodup_nil
  | cons a t => exact countedPlannerUniformSamplerBody_nodup (a :: t) hl a List.mem_cons_self p seed

lemma countedPlannerFirstStage_first_value (l : List (Fin n)) (hl : l.Nodup)
    (a : Fin n) (ha : a ∈ l) (hA : l.toFinset.Nonempty)
    (p : Fin n → ℝ) (seed : ℝ × (Fin n → ℝ)) :
    (countedPlannerFirstStage l a p seed).1.1 = plannerFirstSuccessChoice l.toFinset p hA seed.1 := by
  change (countedPlannerFirstChoice l (countedMaximumScan a l).1 p seed.1).1 = _
  rw [countedMaximumScan_eq_finsetMax l hA a ha]
  exact countedPlannerFirstChoice_value l hl hA p seed.1

lemma countedPlannerFirstStage_set_value (l : List (Fin n)) (hl : l.Nodup)
    (a : Fin n) (ha : a ∈ l) (hA : l.toFinset.Nonempty)
    (p : Fin n → ℝ) (seed : ℝ × (Fin n → ℝ)) :
    (countedPlannerFirstStage l a p seed).1.2.toFinset = plannerFirstSuccessUniform l.toFinset p hA seed := by
  let k := (countedPlannerFirstChoice l (countedMaximumScan a l).1 p seed.1).1
  change (k :: (countedPlannerFirstCoins l p k seed.2).1).toFinset = _
  rw [countedPlannerFirstCoins_firstSuccess]
  have hk : k = plannerFirstSuccessChoice l.toFinset p hA seed.1 :=
    countedPlannerFirstStage_first_value l hl a ha hA p seed
  rw [hk]
  rfl

def plannerListOutputToSet (x : PlannerListOutput n ℝ) : PlannerUniformOutput n :=
  (x.1, x.2.1, x.2.2.toFinset)

lemma countedPlannerUniformSamplerBody_value (l : List (Fin n)) (hl : l.Nodup)
    (a : Fin n) (ha : a ∈ l) (p : Fin n → ℝ) (seed : PlannerUniformSeed n) :
    plannerListOutputToSet (countedPlannerUniformSamplerBody l a p seed).1 =
      plannerUniformTransition l.toFinset p seed := by
  let first := countedPlannerFirstStage l a p seed.1
  let D := first.1.2
  let maximum := countedMaximumScan first.1.1 D
  let identity := countedPlannerUniformIdentity D maximum.1 seed.2.1
  let fraction := countedPlannerFraction D seed.2.2.1
  let tail := countedPlannerTailCoins l D fraction.1 seed.2.2.2
  let companions := countedPredicateFilter (fun j => j ≠ identity.1) D
  let output := countedAppend companions.1 tail.1
  have hA : l.toFinset.Nonempty := ⟨a, List.mem_toFinset.mpr ha⟩
  have hDnodup : D.Nodup := (countedPlannerFirstStage_invariants l hl a ha p seed.1).1
  have hkD : first.1.1 ∈ D := List.mem_cons_self
  have hD : D.toFinset.Nonempty := ⟨_, List.mem_toFinset.mpr hkD⟩
  have hMax : maximum.1 = D.toFinset.max' hD := countedMaximumScan_eq_finsetMax D hD _ hkD
  have hIdentity : identity.1 = plannerUniformIdentity D.toFinset hD seed.2.1 := by
    change (countedPlannerUniformIdentity D maximum.1 seed.2.1).1 = _
    rw [hMax]
    exact countedPlannerUniformIdentity_value D hDnodup hD seed.2.1
  have hFraction : fraction.1 = plannerUnitFraction D.toFinset hD seed.2.2.1 :=
    countedPlannerFraction_value D hD seed.2.2.1
  have hTail : tail.1.toFinset = bernoulliSubset (l.toFinset \ D.toFinset) (fun _ => fraction.1) seed.2.2.2 :=
    countedPlannerTailCoins_toFinset l D fraction.1 seed.2.2.2
  have hComp : companions.1.toFinset = D.toFinset.erase identity.1 := by
    ext j
    simp [companions, countedPredicateFilter_value, and_comm]
  have hOut : output.1.toFinset = D.toFinset.erase identity.1 ∪
      bernoulliSubset (l.toFinset \ D.toFinset) (fun _ => fraction.1) seed.2.2.2 := by
    rw [countedAppend_value, List.toFinset_append, hComp, hTail]
  have hDset : D.toFinset = plannerFirstSuccessUniform l.toFinset p hA seed.1 :=
    countedPlannerFirstStage_set_value l hl a ha hA p seed.1
  change (some identity.1, fraction.1, output.1.toFinset) = _
  rw [hOut, hIdentity, hFraction]
  rw [plannerUniformTransition, dif_pos hA, ← hDset,
    plannerUniformAfterSubset, dif_pos hD]
  rfl

/-- The counted list program and the fixed-seed finite-set sampler agree
on every raw seed, not just almost surely. -/
theorem countedPlannerUniformSampler_value (l : List (Fin n)) (hl : l.Nodup)
    (p : Fin n → ℝ) (seed : PlannerUniformSeed n) :
    plannerListOutputToSet (countedPlannerUniformSampler l p seed).1 =
      plannerUniformTransition l.toFinset p seed := by
  cases l with
  | nil => simp [countedPlannerUniformSampler, plannerListOutputToSet, plannerUniformTransition]
  | cons a t => exact countedPlannerUniformSamplerBody_value (a :: t) hl a List.mem_cons_self p seed

/-- The concrete counted implementation has exactly the prescribed kernel
law, with its seed distribution fixed before the active state. -/
theorem map_countedPlannerUniformSampler {n : ℕ} (l : List (Fin n)) (hl : l.Nodup)
    (p : Fin n → ℝ) (hA : l.toFinset.Nonempty) (hp : ∀ i ∈ l.toFinset, 0 < p i) :
    (plannerUniformSeedLaw n).map (fun seed => plannerListOutputToSet (countedPlannerUniformSampler l p seed).1) =
      (plannerKernelLaw l.toFinset p).map plannerSomeTransition := by
  have hEq : (fun seed => plannerListOutputToSet (countedPlannerUniformSampler l p seed).1) =
      plannerUniformTransition l.toFinset p := by
    funext seed
    exact countedPlannerUniformSampler_value l hl p seed
  rw [hEq]
  exact map_plannerUniformTransition_of_nonempty l.toFinset p hA hp

/-- One polynomial bound applies uniformly to all active subsets of `[n]`. -/
theorem countedPlannerUniformSampler_work_le_dimension {K : Type*} [Field K] [LinearOrder K]
    (l : List (Fin n)) (hl : l.Nodup) (p : Fin n → K) (seed : PlannerFieldSeed n K) :
    (countedPlannerUniformSampler l p seed).2 ≤ 1000 * (n + 1) ^ 3 := by
  have hLen := Finset.card_le_univ l.toFinset
  rw [List.toFinset_card_of_nodup hl, Fintype.card_fin] at hLen
  exact (countedPlannerUniformSampler_work l hl p seed).trans
    (Nat.mul_le_mul_left 1000 (Nat.pow_le_pow_left (by omega) 3))

lemma countedPlannerUniformSampler_legal (l : List (Fin n)) (hl : l.Nodup)
    (p : Fin n → ℝ) (seed : PlannerUniformSeed n) {i : Fin n}
    (hSelect : (countedPlannerUniformSampler l p seed).1.1 = some i) :
    i ∈ l.toFinset ∧ (countedPlannerUniformSampler l p seed).1.2.1 ∈ Set.Icc (0 : ℝ) 1 ∧
      (countedPlannerUniformSampler l p seed).1.2.2.toFinset ⊆ l.toFinset.erase i := by
  have hEq := countedPlannerUniformSampler_value l hl p seed
  have hSelect' : (plannerUniformTransition l.toFinset p seed).1 = some i := by
    rw [← hEq]
    exact hSelect
  have h := plannerUniformTransition_legal l.toFinset p seed hSelect'
  rw [← hEq] at h
  exact h

lemma countedPlannerUniformSampler_child_length_lt (l : List (Fin n)) (hl : l.Nodup)
    (p : Fin n → ℝ) (seed : PlannerUniformSeed n) {i : Fin n}
    (hSelect : (countedPlannerUniformSampler l p seed).1.1 = some i) :
    (countedPlannerUniformSampler l p seed).1.2.2.length < l.length := by
  have hEq := countedPlannerUniformSampler_value l hl p seed
  have hSelect' : (plannerUniformTransition l.toFinset p seed).1 = some i := by
    rw [← hEq]
    exact hSelect
  have h := plannerUniformTransition_child_card_lt l.toFinset p seed hSelect'
  rw [← hEq] at h
  change (countedPlannerUniformSampler l p seed).1.2.2.toFinset.card < l.toFinset.card at h
  rwa [List.toFinset_card_of_nodup (countedPlannerUniformSampler_nodup l hl p seed),
    List.toFinset_card_of_nodup hl] at h

end ProphetSecretary.Statistics
