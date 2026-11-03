import ProphetSecretary.Statistics.ScalarPlannerValueMap
import ProphetSecretary.Statistics.ScalarPlannerRationalHeight
import ProphetSecretary.Statistics.PlannerDyadicBits
import ProphetSecretary.Analysis.BinaryRationalWork

/-!
# The counted scalar tree on the binary rational carrier

The same sampler and recursive estimator run on binary field values. Direct
decoding provides the dyadic words, and the value projection recovers the
rational program on every supplied tree.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis

variable {n : ℕ}

def binaryFairCoordinate (b : ℕ) (bits : Fin b → Bool) : BinaryRational :=
  BinaryRational.ofFraction (countedBinaryDyadicUniform b bits).1 (countedBinaryDyadicUniform_width b bits).1

lemma binaryFairCoordinate_value (b : ℕ) (bits : Fin b → Bool) :
    (binaryFairCoordinate b bits).value=(ProphetSecretary.Probability.countedDyadicUniform b bits).1 :=
  (BinaryRational.ofFraction_value _ _).trans (countedBinaryDyadicUniform_value b bits)

def binaryScalarPlannerSeed (b : ℕ) (s : PlannerFairSeed n b) : PlannerFieldSeed n BinaryRational :=
  plannerMapSeed (binaryFairCoordinate b) s

lemma binaryScalarPlannerSeed_value (b : ℕ) (s : PlannerFairSeed n b) :
    plannerMapSeed BinaryRational.value (binaryScalarPlannerSeed b s) = (countedPlannerFairSeed b s).1 := by
  simp only [binaryScalarPlannerSeed,countedPlannerFairSeed,plannerMapSeed,binaryFairCoordinate_value]

def countedBinaryScalarPlannerEstimate (rows : Vector (List BinaryRational) n) (p : Fin n → BinaryRational)
    (b r : ℕ) (x : ScalarPlannerListState n BinaryRational) (t : MultilevelTree (PlannerFairSeed n b) r) :
    BinaryRational × ℕ :=
  (countedScalarPlannerRecursion rows p).estimate r x (multilevelTreeMap (binaryScalarPlannerSeed b) r t)

theorem countedBinaryScalarPlannerEstimate_value (rows : Vector (List BinaryRational) n)
    (p : Fin n → BinaryRational) (b r : ℕ) (x : ScalarPlannerListState n BinaryRational)
    (t : MultilevelTree (PlannerFairSeed n b) r) :
    (countedBinaryScalarPlannerEstimate rows p b r x t).1.value =
      ((countedScalarPlannerRecursion (plannerRowsValueMap BinaryRational.value rows) (fun i => (p i).value)).estimate
        r (scalarPlannerStateValueMap BinaryRational.value x)
        (multilevelTreeMap (fun s => (countedPlannerFairSeed b s).1) r t)).1 := by
  have h := countedScalarPlannerEstimate_valueMap BinaryRational.valueHom BinaryRational.value_strictMono rows p r x
    (multilevelTreeMap (binaryScalarPlannerSeed b) r t)
  have hs : plannerMapSeed BinaryRational.valueHom ∘ binaryScalarPlannerSeed (n := n) b =
      fun s : PlannerFairSeed n b => (countedPlannerFairSeed b s).1 := funext (binaryScalarPlannerSeed_value b)
  rw [multilevelTreeMap_comp,hs] at h
  exact h

theorem countedBinaryScalarPlannerEstimate_width (rows : Vector (List BinaryRational) n)
    (p : Fin n → BinaryRational) (m Y P Pp U Z b r : ℕ)
    (hm : ∀ i, (rows.get i).length≤m) (hP : m≤2^P)
    (hY : ∀ i q, q∈rows.get i → RationalHeight q.value Y) (hp : ∀ i, RationalHeight (p i).value Pp)
    (hZ : 2≤Z) (x : ScalarPlannerListState n BinaryRational) (hx : x.1.Nodup)
    (hu : RationalHeight x.2.1.value U) (hz : RationalHeight x.2.2.value Z)
    (t : MultilevelTree (PlannerFairSeed n b) r) :
    (countedBinaryScalarPlannerEstimate rows p b r x t).1.storage.width≤
      64*(plannerPrimitiveHeight n m Y P Pp U Z b r+r+1)*16^r+1 := by
  apply BinaryRational.storage_width
  rw [countedBinaryScalarPlannerEstimate_value]
  let q := plannerRowsValueMap BinaryRational.value rows
  have hq (i : Fin n) : q.get i = (rows.get i).map BinaryRational.value := by
    simp [q,plannerRowsValueMap,Vector.get]
  have hm' (i : Fin n) : (q.get i).length≤m := by rw [hq,List.length_map]; exact hm i
  have hY' (i : Fin n) (a : ℚ) (ha : a∈q.get i) : RationalHeight a Y := by
    rw [hq] at ha
    obtain ⟨u,hu',rfl⟩ := List.mem_map.mp ha
    exact hY i u hu'
  exact countedScalarPlannerRecursion_fair_height q (fun i => (p i).value) m Y P Pp U Z b r hm' hP hY' hp hZ
    (scalarPlannerStateValueMap BinaryRational.value x) hx hu hz t

end ProphetSecretary.Statistics
