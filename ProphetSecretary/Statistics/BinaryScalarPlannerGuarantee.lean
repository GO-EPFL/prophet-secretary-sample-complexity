import ProphetSecretary.Statistics.BinaryScalarQuery
import ProphetSecretary.Statistics.PlannerBitPrecision
import ProphetSecretary.Statistics.ScalarPlannerSeedBank

/-!
# Guarantees for the binary scalar estimator

The executable estimator on the canonical binary rational carrier inherits
the rounded planner's error bound by pointwise equality. The hard work bound
counts its binary arithmetic and comparison algorithms on every input tree.
-/

open MeasureTheory Set

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n : ℕ} {k : Fin n → ℕ}

lemma plannerStoredRows_valueMap {K L : Type*} (f : K → L)
    (y : (i : Fin n) → Fin (k i) → K) :
    plannerRowsValueMap f (plannerStoredRows y) = plannerStoredRows (fun i j => f (y i j)) := by
  apply Vector.ext
  intro i hi
  let j : Fin n := ⟨i,hi⟩
  change (plannerRowsValueMap f (plannerStoredRows y)).get j = (plannerStoredRows _).get j
  rw [show (plannerRowsValueMap f (plannerStoredRows y)).get j =
    ((plannerStoredRows y).get j).map f by simp [plannerRowsValueMap,Vector.get]]
  simp only [plannerStoredRows_get,List.map_ofFn]
  rfl

/-- The finite-bit estimator at a prescribed precision and level.
The two numerical inequalities respectively control stochastic and grid error. -/
theorem countedBinaryScalarQueryAtLevel_correct [∀ i, NeZero (k i)]
    (y : (i : Fin n) → Fin (k i) → BinaryRational)
    (hy : ∀ i j, 0 ≤ ((y i j).value : ℝ)) (hcap : ∀ i j, ((y i j).value : ℝ) ≤ 1)
    (x : ScalarPlannerListState n BinaryRational) (hx : x.1.Nodup) (b r : ℕ)
    (h : ℝ) (p : ℚ) (hh : 0 < h) (hp : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    (H : ∃ j : ℕ, (1/4 : ℚ)^j ≤ p)
    (hprec : 25*(scalarPlannerWeight (fun i j => ((y i j).value : ℝ)) x.1.toFinset)^2 *
      (1/2 : ℝ)^r ≤ (h/2)^2/64)
    (hgrid : scalarPlannerWeight (fun i j => ((y i j).value : ℝ)) x.1.toFinset *
      ((10*(n : ℝ)+4)/(3*((2^b : ℕ) : ℝ))) ≤ h/4)
    (m Y M U Z : ℕ) (hk : ∀ i, k i ≤ m) (hm : m ≤ 2^M)
    (hY : ∀ i j, RationalHeight (y i j).value Y)
    (hu : RationalHeight x.2.1.value U) (hz : RationalHeight x.2.2.value Z) (hZ : 2 ≤ Z) :
    let C := confidenceCopyCount p H
    let μ := Measure.pi (fun _ : Fin C => multilevelTreeLaw (plannerFairSeedLaw n b) r)
    let Q := countedBinaryScalarQueryAtLevel (plannerStoredRows y) x b r (countedConfidenceLevel p H).1
    let v := scalarPlannerValue (fun i j => ((y i j).value : ℝ)) hy
      (scalarPlannerListInterpret (x.1, (((x.2.1.value : ℚ) : ℝ), ((x.2.2.value : ℚ) : ℝ))))
    Measurable (fun seed => ((Q seed).value.value : ℝ)) ∧
      μ.real {seed | h < |((Q seed).value.value : ℝ)-v|} ≤ (p : ℝ) ∧
      ∀ seed, (Q seed).work ≤ binaryScalarQueryWorkBound n m Y M U Z b r (countedConfidenceLevel p H).1 ∧
        scalarPlannerFairReads b r seed ≤ C*(4*16^r)*((3*n+2)*b) := by
  dsimp only
  let y' := fun i j => (y i j).value
  let x' := scalarPlannerStateValueMap BinaryRational.value x
  have he (seed : Fin (confidenceCopyCount p H) → MultilevelTree (PlannerFairSeed n b) r) :
      (countedBinaryScalarQueryAtLevel (plannerStoredRows y) x b r (countedConfidenceLevel p H).1 seed).value.value =
        (countedRationalFairQueryAtLevel (plannerStoredRows y') x' r p H b seed).value := by
    rw [countedBinaryScalarQueryAtLevel_value,plannerStoredRows_valueMap]
  have hc := countedRationalFairQueryAtLevel_correct y' hy hcap x' hx r h p hh hp hp1 H b hprec hgrid
  refine ⟨?_, ?_, fun seed => ⟨?_, scalarPlannerFairReads_le b r seed⟩⟩
  · simp_rw [he]
    exact hc.1
  · simp_rw [he]
    exact hc.2
  · apply countedBinaryScalarQueryAtLevel_work _ x b r _ r m Y M U Z seed le_rfl hm _ _ hx hu hz hZ
    · intro i
      simpa only [plannerStoredRows_get,List.length_ofFn] using hk i
    · intro i a ha
      rw [plannerStoredRows_get] at ha
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
      exact hY i j

end ProphetSecretary.Statistics
