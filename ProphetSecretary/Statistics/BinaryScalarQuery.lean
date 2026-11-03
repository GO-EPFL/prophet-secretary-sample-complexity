import ProphetSecretary.Statistics.BinaryEmpiricalTreeWork
import ProphetSecretary.Statistics.BinaryPlannerProbability
import ProphetSecretary.Probability.BinaryMedian
import ProphetSecretary.Statistics.ScalarPlannerQueryValueMap
import ProphetSecretary.Statistics.ScalarPlannerRationalFairQuery

/-!
# The scalar query with a measured binary work counter

The empirical rows and root weights are prepared once. Each independent
tree is evaluated once, then a measured binary sorting median is clipped.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n : ℕ}

def countedBinarySinglePrepared (rows : Vector (List BinaryRational) n) (p : Fin n → BinaryRational)
    (β : BinaryRational) (x : ScalarPlannerListState n BinaryRational) (b r : ℕ)
    (t : MultilevelTree (PlannerFairSeed n b) r) : BinaryRational × ℕ :=
  let q := (binaryEmpiricalRecursion rows p b).canonicalEstimate r x t
  let v := BinaryRational.countedOperation .mul β q.1
  (v.1,q.2+v.2+3)

lemma countedBinarySinglePrepared_value (rows : Vector (List BinaryRational) n) (p : Fin n → BinaryRational)
    (β : BinaryRational) (x : ScalarPlannerListState n BinaryRational) (b r : ℕ)
    (t : MultilevelTree (PlannerFairSeed n b) r) :
    (countedBinarySinglePrepared rows p β x b r t).1.value =
      (countedScalarPlannerSinglePrepared (plannerRowsValueMap BinaryRational.value rows) (fun i => (p i).value)
        β.value (scalarPlannerStateValueMap BinaryRational.value x) r
        (multilevelTreeMap (fun s => (countedPlannerFairSeed b s).1) r t)).1 := by
  simp only [countedBinarySinglePrepared,BinaryRational.countedOperation_value,BinaryRational.applyOperation,
    countedScalarPlannerSinglePrepared]
  change (BinaryRational.mul β ((binaryEmpiricalRecursion rows p b).canonicalEstimate r x t).1).value = _
  rw [BinaryRational.mul_value,binaryEmpiricalRecursion_value]

def countedBinaryScalarQueryAtLevel (rows : Vector (List BinaryRational) n)
    (x : ScalarPlannerListState n BinaryRational) (b r a : ℕ)
    (seed : Fin (2*a+1) → MultilevelTree (PlannerFairSeed n b) r) : MedianCopiesResult BinaryRational :=
  let q := countedBinaryPlannerProbabilities rows
  let p := plannerProbabilityRead q.1
  let f := countedBinaryPlannerFrame p x
  if f.1.active.isEmpty then
    {value := f.1.emptyValue,work := q.2+f.2+2,copies := 0}
  else
    let med := countedBinaryMedianCopies a (countedBinarySinglePrepared rows p f.1.weight x b r) seed
    let c := countedBinaryClamp 0 5 med.value
    {value := c.1,work := q.2+f.2+med.work+c.2+5,copies := med.copies}

theorem countedBinaryScalarQueryAtLevel_value (rows : Vector (List BinaryRational) n)
    (x : ScalarPlannerListState n BinaryRational) (b r : ℕ) (pFail : ℚ)
    (H : ∃ j : ℕ, (1/4:ℚ)^j≤pFail)
    (seed : Fin (confidenceCopyCount pFail H) → MultilevelTree (PlannerFairSeed n b) r) :
    (countedBinaryScalarQueryAtLevel rows x b r (countedConfidenceLevel pFail H).1 seed).value.value =
      (countedRationalFairQueryAtLevel (plannerRowsValueMap BinaryRational.value rows)
        (scalarPlannerStateValueMap BinaryRational.value x) r pFail H b seed).value := by
  let a := (countedConfidenceLevel pFail H).1
  let p := plannerProbabilityRead (countedBinaryPlannerProbabilities rows).1
  let f := (countedBinaryPlannerFrame p x).1
  let rows' := plannerRowsValueMap BinaryRational.value rows
  let x' := scalarPlannerStateValueMap BinaryRational.value x
  let p' := plannerProbabilityRead (countedPlannerProbabilities rows').1
  let f' := (countedScalarPlannerFrame p' x').1
  have hP : p'=fun i => (p i).value := by
    funext i
    exact (plannerProbabilityRead_valueMap BinaryRational.valueHom BinaryRational.value_strictMono rows i).trans
      (congrArg BinaryRational.value (countedBinaryPlannerProbabilities_value rows i).symm)
  have hF : f'=scalarPlannerFrameValueMap BinaryRational.value f := by
    dsimp only [f']
    rw [hP]
    have h := countedScalarPlannerFrame_valueMap BinaryRational.valueHom BinaryRational.value_strictMono p x
    rw [← countedBinaryPlannerFrame_value] at h
    exact h
  let call := countedBinarySinglePrepared rows p f.weight x b r
  let call' := countedScalarPlannerSinglePrepared rows' p' f'.weight x' r
  let ts := fun j => multilevelTreeMap (fun s => (countedStoredPlannerFairSeed b s).1) r (seed j)
  have hCall (i : Fin (2*a+1)) : (call (seed i)).1.value=(call' (ts i)).1 := by
    dsimp only [call',ts]
    rw [hP,hF]
    simpa only [countedStoredPlannerFairSeed_value,scalarPlannerFrameValueMap] using
      countedBinarySinglePrepared_value rows p f.weight x b r (seed i)
  unfold countedBinaryScalarQueryAtLevel countedRationalFairQueryAtLevel countedScalarPlannerQueryAtLevel
  change ((if f.active.isEmpty then _ else _ : MedianCopiesResult BinaryRational).value).value =
    (if f'.active.isEmpty then _ else _ : MedianCopiesResult ℚ).value
  have hflag : f'.active.isEmpty=f.active.isEmpty := by rw [hF]; rfl
  by_cases he : f.active.isEmpty=true
  · rw [if_pos he,if_pos (hflag.trans he)]
    change f.emptyValue.value=f'.emptyValue
    rw [hF]
    rfl
  · have he' : ¬f'.active.isEmpty=true := fun h => he (hflag.symm.trans h)
    rw [if_neg he,if_neg he']
    change (countedBinaryClamp 0 5 (countedBinaryMedianCopies a call seed).value).1.value=
      clipFive (confidenceMedianCopies pFail H call' ts).value
    rw [countedBinaryClamp_value,BinaryRational.max_value,BinaryRational.min_value,BinaryRational.zero_value,
      show (5:BinaryRational).value=(5:ℚ) from BinaryRational.ofRat_value 5,
      countedBinaryMedianCopies_value,confidenceMedianCopies_value]
    change clipFive ((sortedMedian a (fun i => (call (seed i)).1)).value)=_
    apply congrArg clipFive
    have hm := sortedMedian_valueMap BinaryRational.valueHom BinaryRational.value_strictMono a
      (fun i => (call (seed i)).1)
    change sortedMedian a (fun i => (call (seed i)).1.value) = (sortedMedian a (fun i => (call (seed i)).1)).value at hm
    rw [←hm]
    exact congrArg (sortedMedian a) (funext hCall)

def binaryScalarQueryValueHeight (n m Y M U Z b R : ℕ) : ℕ :=
  n*(2*M+3)+binaryEmpiricalValueHeight n m Y M (2*M) U Z b R+U+Z+3

def binaryScalarQueryWorkBound (n m Y M U Z b R a : ℕ) : ℕ :=
  let V := binaryScalarQueryValueHeight n m Y M U Z b R
  let S := binaryEmpiricalTreeWorkBound n m Y M (2*M) U Z b R+3600*(V+2)^3+3
  n*binaryRowProbabilityWorkBound m Y M+3*n+1+binaryFrameWorkBound n (2*M) U Z+
    2*(2*a+2)^2*(3400*(V+2)^3+5)+(2*a+1)*S+6*(2*a+2)+2+2*(3600*(V+2)^3)+7

theorem countedBinaryScalarQueryAtLevel_work (rows : Vector (List BinaryRational) n)
    (x : ScalarPlannerListState n BinaryRational) (b r a R m Y M U Z : ℕ)
    (seed : Fin (2*a+1) → MultilevelTree (PlannerFairSeed n b) r)
    (hr : r≤R) (hm : m≤2^M) (hRows : ∀ i, (rows.get i).length≤m)
    (hy : ∀ i u, u∈rows.get i → RationalHeight u.value Y)
    (hx : x.1.Nodup) (hu : RationalHeight x.2.1.value U) (hz : RationalHeight x.2.2.value Z) (hZ : 2≤Z) :
    (countedBinaryScalarQueryAtLevel rows x b r a seed).work≤binaryScalarQueryWorkBound n m Y M U Z b R a := by
  let V := binaryScalarQueryValueHeight n m Y M U Z b R
  let E := binaryEmpiricalValueHeight n m Y M (2*M) U Z b R
  let W := n*(2*M+3)
  let S := binaryEmpiricalTreeWorkBound n m Y M (2*M) U Z b R+3600*(V+2)^3+3
  let q := countedBinaryPlannerProbabilities rows
  let p := plannerProbabilityRead q.1
  let f := countedBinaryPlannerFrame p x
  have hq : q.2≤n*binaryRowProbabilityWorkBound m Y M+3*n+1 :=
    countedBinaryPlannerProbabilities_work rows m Y M hRows hm hy
  have hp (i : Fin n) : RationalHeight (p i).value (2*M) := by
    change RationalHeight (plannerProbabilityRead (countedBinaryPlannerProbabilities rows).1 i).value _
    have he : plannerProbabilityRead (countedBinaryPlannerProbabilities rows).1 i =
        (countedBinaryRowProbability (rows.get i)).1 := by simp [plannerProbabilityRead,countedBinaryPlannerProbabilities,Vector.get]
    rw [he]
    exact countedBinaryRowProbability_height (rows.get i) M ((hRows i).trans hm)
  have hf : f.2≤binaryFrameWorkBound n (2*M) U Z := countedBinaryPlannerFrame_work p x (2*M) U Z hx hp hu hz hZ
  have hβ : RationalHeight f.1.weight.value W := by
    change RationalHeight (countedBinaryPlannerWeight p (countedBinaryPlannerActive p x.1).1).1.value _
    have hL : x.1.length≤n := by
      simpa only [List.toFinset_card_of_nodup hx,Fintype.card_fin] using Finset.card_le_univ x.1.toFinset
    have hA : (countedBinaryPlannerActive p x.1).1.length≤n := by
      rw [countedBinaryPlannerActive_value]
      exact (countedPlannerActive_length p x.1).trans hL
    exact (countedBinaryPlannerWeight_height p _ (2*M) hp).mono (Nat.mul_le_mul_right _ hA)
  let call := countedBinarySinglePrepared rows p f.1.weight x b r
  have hCall (t : MultilevelTree (PlannerFairSeed n b) r) : RationalHeight (call t).1.value V ∧ (call t).2≤S := by
    let a := (binaryEmpiricalRecursion rows p b).canonicalEstimate r x t
    let z := BinaryRational.countedOperation .mul f.1.weight a.1
    have ha : RationalHeight a.1.value E := by
      rw [CountedPlannerRecursion.canonicalEstimate_value]
      exact binaryEmpiricalRecursion_height rows p m Y M (2*M) U Z b R r hr hm hRows hy hp hZ x hx
        (hu.mono (by omega)) hz t
    have hA := binaryEmpiricalRecursion_bit_work rows p m Y M (2*M) U Z b R r hr hm hRows hy hp hZ x hx hu hz t
    have hZ' : z.2≤3600*(V+2)^3 := BinaryRational.countedOperation_work .mul _ _ V
      (hβ.mono (by dsimp [V,binaryScalarQueryValueHeight]; omega)) (ha.mono (by dsimp [V,binaryScalarQueryValueHeight,E]; omega))
    refine ⟨?_,Nat.add_le_add_right (Nat.add_le_add hA hZ') 3⟩
    change RationalHeight z.1.value V
    rw [BinaryRational.countedOperation_value]
    change RationalHeight (BinaryRational.mul f.1.weight a.1).value _
    rw [BinaryRational.mul_value]
    exact (hβ.mul ha).mono (by dsimp [V,binaryScalarQueryValueHeight,E,W]; omega)
  change (if f.1.active.isEmpty then _ else _ : MedianCopiesResult BinaryRational).work≤_
  by_cases hEmpty : f.1.active.isEmpty=true
  · rw [if_pos hEmpty]
    change q.2+f.2+2≤_
    dsimp only [binaryScalarQueryWorkBound]
    omega
  · rw [if_neg hEmpty]
    let med := countedBinaryMedianCopies a call seed
    have hMed := countedBinaryMedianCopies_work a call seed V S (fun i => hCall (seed i))
    have hmH : RationalHeight med.value.value V := by
      rw [show med.value=sortedMedian a (fun i => (call (seed i)).1) from countedBinaryMedianCopies_value a call seed]
      let l := List.insertionSort (fun a b : BinaryRational => b≤a) (List.ofFn (fun i => (call (seed i)).1))
      have hL : sortedMedian a (fun i => (call (seed i)).1)∈l := List.get_mem _ _
      rw [show l=List.insertionSort (fun a b : BinaryRational => b≤a) (List.ofFn (fun i => (call (seed i)).1)) from rfl,
        List.mem_insertionSort] at hL
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hL
      rw [←hi]
      exact (hCall (seed i)).1
    have h0 : RationalHeight (0:BinaryRational).value V := by
      rw [BinaryRational.zero_value]; exact rationalHeight_zero.mono (Nat.zero_le _)
    have h5 : RationalHeight (5:BinaryRational).value V := by
      rw [show (5:BinaryRational).value=(5:ℚ) from BinaryRational.ofRat_value 5]
      exact rationalHeight_five.mono (by dsimp [V,binaryScalarQueryValueHeight]; omega)
    have hClip := countedBinaryClamp_work 0 5 med.value V h0 h5 hmH
    change q.2+f.2+med.work+(countedBinaryClamp 0 5 med.value).2+5≤_
    change med.work≤2*(2*a+2)^2*(3400*(V+2)^3+5)+(2*a+1)*S+6*(2*a+2)+2 at hMed
    change _≤n*binaryRowProbabilityWorkBound m Y M+3*n+1+binaryFrameWorkBound n (2*M) U Z+
      2*(2*a+2)^2*(3400*(V+2)^3+5)+(2*a+1)*S+6*(2*a+2)+2+2*(3600*(V+2)^3)+7
    omega

end ProphetSecretary.Statistics
