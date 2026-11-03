import ProphetSecretary.Statistics.BinaryPlannerCallbacksWork
import ProphetSecretary.Statistics.CanonicalBitTreeWork
import ProphetSecretary.Statistics.BinaryScalarPlanner

/-!
# The empirical multilevel tree with an executed bit counter

Raw dyadic words are decoded once per sampled transition. All scalar
operations of the transition and recursive tree use the measured binary
primitives. The output agrees pointwise with the rational estimator.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis

variable {n : ℕ}

def countedBinaryFairCoordinate (b : ℕ) (bits : Fin b → Bool) : BinaryRational × ℕ :=
  let q := countedBinaryDyadicUniform b bits
  (binaryFairCoordinate b bits,q.2+q.1.countedReduce.2+b+5)

lemma countedBinaryFairCoordinate_work (b : ℕ) (bits : Fin b → Bool) :
    (countedBinaryFairCoordinate b bits).2≤2*b+100*(b+2)^3+5 := by
  have h : (countedBinaryDyadicUniform b bits).1.countedReduce.2≤100*(b+2)^3 :=
    (BinaryFraction.countedReduce_work (countedBinaryDyadicUniform b bits).1).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
      (Nat.add_le_add_right (countedBinaryDyadicUniform_width b bits).2 1) 3))
  change b+(countedBinaryDyadicUniform b bits).1.countedReduce.2+b+5≤_
  omega

def countedBinaryFairSeed (b : ℕ) (s : PlannerFairSeed n b) : PlannerFieldSeed n BinaryRational × ℕ :=
  let q := plannerMapSeed (countedBinaryFairCoordinate b) s
  (plannerMapSeed Prod.fst q,q.1.1.2+(∑ i : Fin n,(q.1.2 i).2)+q.2.1.2+
    (∑ i : Fin n,(q.2.2.1 i).2)+(∑ i : Fin n,(q.2.2.2 i).2)+15*(n+1))

lemma countedBinaryFairSeed_value (b : ℕ) (s : PlannerFairSeed n b) :
    (countedBinaryFairSeed b s).1=binaryScalarPlannerSeed b s := rfl

def binaryFairSeedWorkBound (n b : ℕ) : ℕ := (3*n+2)*(2*b+100*(b+2)^3+5)+15*(n+1)

lemma countedBinaryFairSeed_work (b : ℕ) (s : PlannerFairSeed n b) :
    (countedBinaryFairSeed b s).2≤binaryFairSeedWorkBound n b := by
  let W := 2*b+100*(b+2)^3+5
  have h (u : Fin n → Fin b → Bool) : (∑ i,(countedBinaryFairCoordinate b (u i)).2)≤n*W := by
    calc
      _ ≤ ∑ _ : Fin n,W := Finset.sum_le_sum (fun i _ => countedBinaryFairCoordinate_work b (u i))
      _ = _ := by simp
  have h₁ : (countedBinaryFairCoordinate b s.1.1).2≤W := countedBinaryFairCoordinate_work b s.1.1
  have h₂ : (countedBinaryFairCoordinate b s.2.1).2≤W := countedBinaryFairCoordinate_work b s.2.1
  have h₃ := h s.1.2
  have h₄ := h s.2.2.1
  have h₅ := h s.2.2.2
  simp only [countedBinaryFairSeed,plannerMapSeed]
  change _≤(3*n+2)*W+15*(n+1)
  rw [Nat.add_mul,Nat.mul_assoc]
  omega

lemma binaryFairCoordinate_height (b : ℕ) (bits : Fin b → Bool) :
    RationalHeight (binaryFairCoordinate b bits).value b := by
  rw [binaryFairCoordinate_value]
  exact gridPoint_height b _

private lemma outputMap_injective {K L : Type*} [Field K] [Field L] [LinearOrder K] [LinearOrder L]
    (f : K→L) (hf : Function.Injective f) : Function.Injective (plannerListOutputMap (n := n) f) := by
  rintro ⟨i,s,A⟩ ⟨j,t,B⟩ h
  have h₁ : i=j := congrArg Prod.fst h
  have h₂ : s=t := hf (congrArg (fun q : PlannerListOutput n L => q.2.1) h)
  have h₃ : A=B := congrArg (fun q : PlannerListOutput n L => q.2.2) h
  simp [h₁,h₂,h₃]

lemma countedBinaryUniformSampler_native_value (l : List (Fin n)) (p : Fin n → BinaryRational)
    (s : PlannerFieldSeed n BinaryRational) :
    (countedBinaryUniformSampler l p s).1=(countedPlannerUniformSampler l p s).1 := by
  apply outputMap_injective BinaryRational.value BinaryRational.value_injective
  rw [countedBinaryUniformSampler_value]
  exact congrArg Prod.fst (countedPlannerUniformSampler_valueMap BinaryRational.valueHom
    BinaryRational.value_strictMono l p s)

def binaryEmpiricalRecursion (rows : Vector (List BinaryRational) n) (p : Fin n → BinaryRational) (b : ℕ) :
    CountedPlannerRecursion (ScalarPlannerListState n BinaryRational) (ScalarPlannerFrame n BinaryRational)
      (PlannerFairSeed n b) (PlannerListOutput n BinaryRational) BinaryRational where
  prepare x :=
    let q := countedBinaryPlannerFrame p x
    (⟨q.1,q.1.active.isEmpty,q.1.emptyValue,q.1.offset,q.1.coefficient⟩,q.2+3)
  sample q seed :=
    let u := countedBinaryFairSeed b seed
    let o := countedBinaryUniformSampler q.active p u.1
    (o.1,u.2+o.2+3)
  child := countedBinaryPlannerChild
  payoff _ := countedBinaryPlannerPayoff rows p

theorem binaryEmpiricalRecursion_estimate_value (rows : Vector (List BinaryRational) n)
    (p : Fin n → BinaryRational) (b r : ℕ) (x : ScalarPlannerListState n BinaryRational)
    (t : MultilevelTree (PlannerFairSeed n b) r) :
    ((binaryEmpiricalRecursion rows p b).estimate r x t).1=(countedBinaryScalarPlannerEstimate rows p b r x t).1 := by
  unfold countedBinaryScalarPlannerEstimate
  rw [CountedPlannerRecursion.estimate_value,CountedPlannerRecursion.estimate_value,← multilevelEstimate_mapSeed]
  apply multilevelEstimate_transport _ _ id (fun _ => True)
  all_goals
    intros
    simp only [binaryEmpiricalRecursion,countedScalarPlannerRecursion,CountedPlannerRecursion.toRecursion,
      MultilevelRecursion.mapSeed,id_eq,countedBinaryPlannerFrame_value,countedBinaryFairSeed_value,
      countedBinaryUniformSampler_native_value,countedScalarPlannerSample,countedBinaryPlannerChild_value,
      countedBinaryPlannerPayoff_value]

theorem binaryEmpiricalRecursion_value (rows : Vector (List BinaryRational) n)
    (p : Fin n → BinaryRational) (b r : ℕ) (x : ScalarPlannerListState n BinaryRational)
    (t : MultilevelTree (PlannerFairSeed n b) r) :
    ((binaryEmpiricalRecursion rows p b).canonicalEstimate r x t).1.value=
      ((countedScalarPlannerRecursion (plannerRowsValueMap BinaryRational.value rows) (fun i => (p i).value)).estimate
        r (scalarPlannerStateValueMap BinaryRational.value x)
        (multilevelTreeMap (fun s => (countedPlannerFairSeed b s).1) r t)).1 := by
  rw [CountedPlannerRecursion.canonicalEstimate_value,binaryEmpiricalRecursion_estimate_value]
  exact countedBinaryScalarPlannerEstimate_value rows p b r x t

end ProphetSecretary.Statistics
