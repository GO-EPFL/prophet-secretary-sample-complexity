import ProphetSecretary.Probability.SortedDyadicClocks
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Prod.Lex

/-!
# Finite-bit validation permutations

Sorting independent grid keys with a deterministic identity tie break gives a
permutation for every outcome. Under the continuous-key coupling, it equals
the uniform continuous order whenever the grid keys are all distinct.
-/

open MeasureTheory Set Filter
open scoped BigOperators

namespace ProphetSecretary.Probability
open ProphetSecretary.Model

def countedValidationKeyPermutation {n N : ℕ} (x : Fin n → Fin N) : Equiv.Perm (Fin n) × ℕ :=
  let r := fun i j => toLex (x i,i) ≤ toLex (x j,j)
  let q := countedInsertionSort r (List.finRange n)
  have hp : List.Perm q.1 (List.finRange n) := by
    rw [countedInsertionSort_value]
    exact List.perm_insertionSort _ _
  have hlen : q.1.length = n := hp.length_eq.trans List.length_finRange
  ((finCongr hlen.symm).trans (List.Nodup.getEquivOfForallMemList q.1
    (hp.nodup_iff.mpr (List.nodup_finRange n)) (fun i => hp.mem_iff.mpr (List.mem_finRange i))), q.2)

lemma countedValidationKeyPermutation_work {n N : ℕ} (x : Fin n → Fin N) :
    (countedValidationKeyPermutation x).2 ≤ 4*(n+1)^2 := by
  simpa only [countedValidationKeyPermutation, List.length_finRange] using
    countedInsertionSort_work (fun i j => toLex (x i,i) ≤ toLex (x j,j)) (List.finRange n)

lemma countedValidationKeyPermutation_monotone {n N : ℕ} (x : Fin n → Fin N) :
    Monotone (fun i => x ((countedValidationKeyPermutation x).1 i)) := by
  let r := fun i j => toLex (x i,i) ≤ toLex (x j,j)
  let q := countedInsertionSort r (List.finRange n)
  have hs : q.1.Pairwise r := by
    rw [countedInsertionSort_value]
    apply List.pairwise_insertionSort
  have hl : q.1.length = n := by rw [countedInsertionSort_value, List.length_insertionSort, List.length_finRange]
  apply monotone_iff_forall_lt.mpr
  intro i j hij
  have hi : i.val < q.1.length := hl.symm ▸ i.isLt
  have hj : j.val < q.1.length := hl.symm ▸ j.isLt
  have h := List.pairwise_iff_getElem.mp hs i.val j.val hi hj hij
  change x q.1[i.val] ≤ x q.1[j.val]
  rcases Prod.Lex.le_iff.mp h with hlt | ⟨he,_⟩
  · exact hlt.le
  · exact he.le

noncomputable def roundedValidationPermutation {n N : ℕ} (hN : 0 < N) (u : Fin n → ℝ) :
    Equiv.Perm (Fin n) := (countedValidationKeyPermutation (fun i => uniformGridIndex N hN (u i))).1

lemma measurable_roundedValidationPermutation (n N : ℕ) (hN : 0 < N) :
    Measurable (roundedValidationPermutation (n := n) hN) :=
  (measurable_of_countable (fun x : Fin n → Fin N => (countedValidationKeyPermutation x).1)).comp
    (measurePreserving_gridIndexVector n N hN).measurable

lemma roundedValidationPermutation_eq_of_distinct {n N : ℕ} (hN : 0 < N) (u : Fin n → ℝ)
    (hu : Function.Injective (fun i => uniformGridIndex N hN (u i))) :
    roundedValidationPermutation hN u = Instance.arrivalPermutation u := by
  have hu' : Function.Injective u := fun _ _ h => hu (congrArg (uniformGridIndex N hN) h)
  apply Instance.arrivalOrder_unique _ (Instance.hasArrivalOrder_arrivalPermutation hu')
  let x := fun i => uniformGridIndex N hN (u i)
  let p := (countedValidationKeyPermutation x).1
  have h := (countedValidationKeyPermutation_monotone x).strictMono_of_injective (hu.comp p.injective)
  intro i j hij
  change u (p i) < u (p j)
  by_contra! hn
  exact (h hij).not_ge (monotone_uniformGridIndex N hN hn)

theorem roundedValidationPermutation_mismatch_probability (n N : ℕ) (hN : 0 < N) :
    (Instance.clocksLaw n).real {u | roundedValidationPermutation hN u ≠ Instance.arrivalPermutation u} ≤
      ((n:ℝ)*((n:ℝ)-1))/(2*(N:ℝ)) := by
  refine (measureReal_mono ?_).trans (roundedUniform_collision_probability n N hN)
  intro u hu h
  exact hu (roundedValidationPermutation_eq_of_distinct hN u h)

def countedDyadicValidationPermutation {n : ℕ} (b : ℕ) (bits : Fin n → Fin b → Bool) :
    Equiv.Perm (Fin n) × (ℕ × ℕ) :=
  let q := countedValidationKeyPermutation (fun i => (countedFairBitsIndex b (bits i)).1)
  (q.1,(∑ i : Fin n, (countedFairBitsIndex b (bits i)).2, q.2))

lemma countedDyadicValidationPermutation_reads_work {n : ℕ} (b : ℕ) (bits : Fin n → Fin b → Bool) :
    (countedDyadicValidationPermutation b bits).2.1 = n*b ∧
      (countedDyadicValidationPermutation b bits).2.2 ≤ 4*(n+1)^2 := by
  exact ⟨by simp [countedDyadicValidationPermutation, countedFairBitsIndex_reads],
    countedValidationKeyPermutation_work _⟩

theorem map_countedDyadicValidationPermutation (n b : ℕ) :
    (Measure.pi (fun _ : Fin n => fairBitVectorLaw b)).map
      (fun bits => (countedDyadicValidationPermutation b bits).1) =
      (Instance.clocksLaw n).map (roundedValidationPermutation (N := 2^b) (by positivity)) := by
  let f := fun x : Fin n → Fin (2^b) => (countedValidationKeyPermutation x).1
  let I := fun bits : Fin n → Fin b → Bool => fun i => fairBitsIndex b (bits i)
  let R := fun u : Fin n → ℝ => fun i => uniformGridIndex (2^b) (by positivity) (u i)
  have hf : Measurable f := measurable_of_countable _
  have hI := measurePreserving_fairIndexVector n b
  have hR := measurePreserving_gridIndexVector n (2^b) (by positivity)
  have he : (fun bits : Fin n → Fin b → Bool => (countedDyadicValidationPermutation b bits).1) = f ∘ I := by
    funext bits
    simp only [countedDyadicValidationPermutation, Function.comp_apply, f, I, countedFairBitsIndex_value]
  rw [he, ← Measure.map_map hf hI.measurable, hI.map_eq]
  change _ = (Instance.clocksLaw n).map (f ∘ R)
  rw [← Measure.map_map hf hR.measurable, hR.map_eq]

/-- The implemented validation permutation is within the stated total
variation bound of the independent uniform arrival order. -/
theorem dyadicValidationPermutation_totalVariation (n b : ℕ) (E : Set (Equiv.Perm (Fin n))) :
    |((Measure.pi (fun _ : Fin n => fairBitVectorLaw b)).map
        (fun bits => (countedDyadicValidationPermutation b bits).1)).real E -
      (Instance.uniformPermutationLaw n).real E| ≤ ((n:ℝ)*((n:ℝ)-1))/(2*(2^b:ℝ)) := by
  let μ := Instance.clocksLaw n
  let p := roundedValidationPermutation (n := n) (N := 2^b) (by positivity)
  let q := @Instance.arrivalPermutation n
  let B := {u | p u ≠ q u}
  have hE : MeasurableSet E := (Set.to_countable E).measurableSet
  rw [map_countedDyadicValidationPermutation, ← Instance.arrivalPermutation_map]
  simp only [Measure.real, Measure.map_apply (measurable_roundedValidationPermutation n (2^b) (by positivity)) hE,
    Measure.map_apply Instance.measurable_arrivalPermutation hE]
  change |μ.real (p ⁻¹' E)-μ.real (q ⁻¹' E)| ≤ _
  have hp : p ⁻¹' E ⊆ q ⁻¹' E ∪ B := by
    intro u hu
    by_cases he : p u = q u
    · exact Or.inl (by change q u ∈ E; rwa [← he])
    · exact Or.inr he
  have hq : q ⁻¹' E ⊆ p ⁻¹' E ∪ B := by
    intro u hu
    by_cases he : p u = q u
    · exact Or.inl (by change p u ∈ E; rwa [he])
    · exact Or.inr he
  have h1 := (measureReal_mono (μ := μ) hp).trans (measureReal_union_le _ _)
  have h2 := (measureReal_mono (μ := μ) hq).trans (measureReal_union_le _ _)
  have hB := roundedValidationPermutation_mismatch_probability n (2^b) (by positivity)
  push_cast at hB
  exact (abs_le.mpr ⟨by linarith, by linarith⟩ :
    |μ.real (p ⁻¹' E)-μ.real (q ⁻¹' E)| ≤ μ.real B).trans hB

theorem validationPermutationBatch_mismatch_probability (n N m : ℕ) (hN : 0 < N) :
    (Measure.pi (fun _ : Fin m => Instance.clocksLaw n)).real
      {u | ∃ i, roundedValidationPermutation hN (u i) ≠ Instance.arrivalPermutation (u i)} ≤
      (m:ℝ)*((n:ℝ)*((n:ℝ)-1))/(2*(N:ℝ)) := by
  let B := {u : Fin n → ℝ | roundedValidationPermutation hN u ≠ Instance.arrivalPermutation u}
  let μ := Measure.pi (fun _ : Fin m => Instance.clocksLaw n)
  have hB : MeasurableSet B := (measurableSet_eq_fun (measurable_roundedValidationPermutation n N hN)
    Instance.measurable_arrivalPermutation).compl
  have he : {u : Fin m → Fin n → ℝ | ∃ i, roundedValidationPermutation hN (u i) ≠ Instance.arrivalPermutation (u i)} =
      ⋃ i : Fin m, (fun u : Fin m → Fin n → ℝ => u i) ⁻¹' B := by ext u; simp [B]
  rw [he]
  calc
    _ ≤ ∑ i : Fin m, μ.real ((fun u : Fin m → Fin n → ℝ => u i) ⁻¹' B) := measureReal_iUnion_fintype_le _
    _ = ∑ _i : Fin m, (Instance.clocksLaw n).real B := by
      apply Finset.sum_congr rfl
      intro i _
      have hp := measurePreserving_eval (fun _ : Fin m => Instance.clocksLaw n) i
      exact congrArg ENNReal.toReal (hp.measure_preimage hB.nullMeasurableSet)
    _ ≤ ∑ _i : Fin m, ((n:ℝ)*((n:ℝ)-1))/(2*(N:ℝ)) := Finset.sum_le_sum (fun _ _ =>
      roundedValidationPermutation_mismatch_probability n N hN)
    _ = _ := by simp [nsmul_eq_mul, mul_div_assoc]

end ProphetSecretary.Probability
