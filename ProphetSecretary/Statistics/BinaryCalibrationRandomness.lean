import ProphetSecretary.Statistics.BinaryFairWords
import ProphetSecretary.Statistics.CalibrationRankDecode

/-!
# Binary validation order and assigned clocks

A stable comparison sort breaks ties by identity when sorting validation
keys. Clock values are sorted separately and then assigned in exogenous
rank order. The comparator calls the actual binary rational comparison.
-/

open scoped Classical BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n m J : ℕ}

private lemma vector_get_ofFn {A : Type*} {N : ℕ} (f : Fin N → A) (k : Fin N) :
    (Vector.ofFn f).get k=f k := Vector.getElem_ofFn k.isLt

def countedInsertBy {A : Type*} (cmp : A → A → Bool × ℕ) (a : A) :
    List A → List A × ℕ
  | [] => ([a],1)
  | b :: l =>
    let t := cmp a b
    if t.1 then (a::b::l,t.2+3)
    else let q := countedInsertBy cmp a l; (b::q.1,t.2+q.2+3)

def countedSortBy {A : Type*} (cmp : A → A → Bool × ℕ) :
    List A → List A × ℕ
  | [] => ([],1)
  | a :: l =>
    let q := countedSortBy cmp l
    let t := countedInsertBy cmp a q.1
    (t.1,q.2+t.2+2)

lemma countedInsertBy_value {A : Type*} (cmp : A → A → Bool × ℕ) (r : A → A → Prop)
    [DecidableRel r] (hr : ∀ a b, (cmp a b).1=decide (r a b)) (a : A) (l : List A) :
    (countedInsertBy cmp a l).1=List.orderedInsert r a l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    by_cases h : r a b <;> simp [countedInsertBy,List.orderedInsert,hr,h,ih]

lemma countedSortBy_value {A : Type*} (cmp : A → A → Bool × ℕ) (r : A → A → Prop)
    [DecidableRel r] (hr : ∀ a b, (cmp a b).1=decide (r a b)) (l : List A) :
    (countedSortBy cmp l).1=List.insertionSort r l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [countedSortBy,List.insertionSort_cons,countedInsertBy_value cmp r hr,ih]

lemma countedInsertBy_work {A : Type*} (cmp : A → A → Bool × ℕ) (a : A) (l : List A) (W : ℕ)
    (hW : ∀ b∈l, (cmp a b).2≤W) :
    (countedInsertBy cmp a l).2≤(W+4)*(l.length+1) := by
  induction l with
  | nil => simp [countedInsertBy]
  | cons b l ih =>
    have h1 := hW b (List.mem_cons_self)
    have h2 := ih (fun v hv => hW v (List.mem_cons_of_mem _ hv))
    simp only [countedInsertBy,List.length_cons]
    split_ifs <;> dsimp only <;> nlinarith only [h1,h2,Nat.zero_le (W*l.length)]

lemma countedSortBy_work {A : Type*} (cmp : A → A → Bool × ℕ) (r : A → A → Prop)
    [DecidableRel r] (hr : ∀ a b, (cmp a b).1=decide (r a b)) (l : List A) (W : ℕ)
    (hW : ∀ a∈l, ∀ b∈l, (cmp a b).2≤W) :
    (countedSortBy cmp l).2≤(W+7)*(l.length+1)^2 := by
  induction l with
  | nil => simp [countedSortBy]
  | cons a l ih =>
    let q := countedSortBy cmp l
    have hq : q.1=List.insertionSort r l := countedSortBy_value cmp r hr l
    have hLen : q.1.length=l.length := by rw [hq,List.length_insertionSort]
    have hI := countedInsertBy_work cmp a q.1 W (fun b hb => by
      rw [hq] at hb
      exact hW a (List.mem_cons_self) b (List.mem_cons_of_mem _
        ((List.perm_insertionSort r l).mem_iff.mp hb)))
    have hQ := ih (fun a ha b hb =>
      hW a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
    rw [hLen] at hI
    change q.2+(countedInsertBy cmp a q.1).2+2≤(W+7)*((a::l).length+1)^2
    simp only [List.length_cons]
    nlinarith only [hI,hQ,Nat.zero_le (W*l.length)]

private lemma orderedInsert_rel_eq {A : Type*} (r s : A → A → Prop)
    [DecidableRel r] [DecidableRel s] (a : A) (l : List A)
    (h : ∀ b∈l, r a b ↔ s a b) :
    List.orderedInsert r a l=List.orderedInsert s a l := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hb := h b (List.mem_cons_self)
    by_cases he : r a b
    · simp only [List.orderedInsert,if_pos he,if_pos (hb.mp he)]
    · simp only [List.orderedInsert,if_neg he,if_neg (mt hb.mpr he)]
      exact congrArg (List.cons b) (ih (fun j hj => h j (List.mem_cons_of_mem _ hj)))

private lemma insertionSort_rel_eq {A : Type*} (r s : A → A → Prop)
    [DecidableRel r] [DecidableRel s] (h : ∀ a b, r a b ↔ s a b) (l : List A) :
    List.insertionSort r l=List.insertionSort s l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.insertionSort_cons,List.insertionSort_cons,ih]
    exact orderedInsert_rel_eq r s a _ (fun b _ => h a b)

private lemma stable_key_sort {A K : Type*} [LinearOrder A] [LinearOrder K]
    (key : A → K) (l : List A) (hl : l.Pairwise (·<·)) :
    List.insertionSort (fun a b => key a≤key b) l =
      List.insertionSort (fun a b => toLex (key a,a)≤toLex (key b,b)) l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have h := List.pairwise_cons.mp hl
    rw [List.insertionSort_cons,List.insertionSort_cons,ih h.2]
    apply orderedInsert_rel_eq
    intro b hb
    have hab := h.1 b ((List.perm_insertionSort _ l).mem_iff.mp hb)
    rw [Prod.Lex.le_iff]
    exact ⟨fun h => (lt_or_eq_of_le h).elim Or.inl (fun he => Or.inr ⟨he,hab.le⟩),
      fun h => h.elim le_of_lt (fun h => h.1.le)⟩

private def binaryKeyLE {A : Type*} (key : A → BinaryRational) (a b : A) : Bool × ℕ :=
  (key a).storage.countedLE (key b).storage

private lemma binaryKeyLE_value {A : Type*} (key : A → BinaryRational) (a b : A) :
    (binaryKeyLE key a b).1=decide ((key a).value≤(key b).value) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  exact BinaryFraction.countedLE_correct _ _ (BinaryRational.storage_denominator_pos _)
    (BinaryRational.storage_denominator_pos _)

def countedBinaryRankOrder (b : ℕ) (bits : RankCalibrationClockBits n b) :
    (Equiv.Perm (Fin n) × (Fin n → BinaryRational)) × ℕ :=
  let q := countedCanonicalFairWords b bits
  let s := countedSortBy (binaryKeyLE q.1) (List.finRange n)
  have hp : List.Perm s.1 (List.finRange n) := by
    rw [countedSortBy_value _ _ (binaryKeyLE_value q.1)]
    exact List.perm_insertionSort _ _
  have hLen : s.1.length=n := hp.length_eq.trans List.length_finRange
  let p := vectorPermutation ((finCongr hLen.symm).trans (List.Nodup.getEquivOfForallMemList s.1
    (hp.nodup_iff.mpr (List.nodup_finRange n)) (fun i => hp.mem_iff.mpr (List.mem_finRange i))))
  let clocks := Vector.ofFn fun k => q.1 (p k)
  ((p,clocks.get),q.2+s.2+10*(n+1)^2)

lemma countedBinaryRankOrder_permutation (b : ℕ) (bits : RankCalibrationClockBits n b) :
    (countedBinaryRankOrder b bits).1.1=(countedRationalValidationOrder b bits).1 := by
  let q := countedCanonicalFairWords b bits
  let key := fun i => (q.1 i).value
  let d := fun i => fairBitsIndex b (bits i)
  have hk (i j : Fin n) : toLex (key i,i)≤toLex (key j,j) ↔ toLex (d i,i)≤toLex (d j,j) := by
    rw [Prod.Lex.le_iff,Prod.Lex.le_iff]
    have hn : (0 : ℚ)<(2^b : ℕ) := by positivity
    have hi : key i=gridPoint (2^b) (d i) := countedCanonicalFairWords_value b bits i
    have hj : key j=gridPoint (2^b) (d j) := countedCanonicalFairWords_value b bits j
    simp only [ofLex_toLex]
    rw [hi,hj]
    simp only [gridPoint,div_lt_div_iff_of_pos_right hn,div_left_inj' hn.ne',
      Nat.cast_lt,Nat.cast_inj,Fin.ext_iff,Fin.lt_def]
  have h := countedSortBy_value (binaryKeyLE q.1) (fun a b => key a≤key b) (binaryKeyLE_value q.1)
    (List.finRange n)
  rw [stable_key_sort key _ (List.pairwise_lt_finRange n)] at h
  have hs : (countedSortBy (binaryKeyLE q.1) (List.finRange n)).1 =
      (countedInsertionSort (fun i j => toLex (d i,i)≤toLex (d j,j)) (List.finRange n)).1 := by
    rw [h,countedInsertionSort_value]
    exact insertionSort_rel_eq _ _ hk _
  rw [countedRationalValidationOrder_value]
  unfold countedDyadicValidationPermutation
  dsimp only
  have hd : (fun i : Fin n => (countedFairBitsIndex b (bits i)).1)=d := by
    funext i
    exact countedFairBitsIndex_value b (bits i)
  rw [hd]
  apply Equiv.ext
  intro k
  simp only [countedBinaryRankOrder,countedValidationKeyPermutation,vectorPermutation_eq]
  have he := congrArg (fun l : List (Fin n) => l[k.val]?) hs
  rw [List.getElem?_eq_getElem (by
    rw [h,List.length_insertionSort,List.length_finRange]; exact k.isLt),
    List.getElem?_eq_getElem (by
      rw [countedInsertionSort_value,List.length_insertionSort,List.length_finRange]; exact k.isLt)] at he
  exact Option.some.inj he

lemma countedBinaryRankOrder_times (b : ℕ) (bits : RankCalibrationClockBits n b) :
    (fun k => ((countedBinaryRankOrder b bits).1.2 k).value)=(countedRationalRankClocks b bits).1.get := by
  rw [countedRationalRankClocks_value]
  let p := (countedBinaryRankOrder b bits).1.1
  let key := fun i => fairBitsIndex b (bits i)
  have hp : p=(countedValidationKeyPermutation key).1 := by
    rw [show p=(countedRationalValidationOrder b bits).1 from countedBinaryRankOrder_permutation b bits,
      countedRationalValidationOrder_value]
    simp only [countedDyadicValidationPermutation,countedFairBitsIndex_value,key]
  have hMono : Monotone (key ∘ p) := by
    rw [hp]
    exact countedValidationKeyPermutation_monotone key
  have hSorted := countedSortVector_eq_of_sorted_permutation key p hMono
  funext k
  have hL : ((countedBinaryRankOrder b bits).1.2 k).value=gridPoint (2^b) (key (p k)) := by
    change ((Vector.ofFn (fun k => (countedCanonicalFairWords b bits).1 (p k))).get k).value=_
    rw [vector_get_ofFn,countedCanonicalFairWords_value]
  rw [hL]
  simp only [countedDyadicSortedClocks,countedFairBitsIndex_value,key]
  rw [show (countedSortVector key).1 k=key (p k) from congrFun hSorted k]

def binaryRankOrderWorkBound (n b : ℕ) : ℕ :=
  n*(110*(b+2)^3+3)+2+(3400*(b+2)^3+7)*(n+1)^2+10*(n+1)^2

lemma countedBinaryRankOrder_work (b : ℕ) (bits : RankCalibrationClockBits n b) :
    (countedBinaryRankOrder b bits).2≤binaryRankOrderWorkBound n b := by
  let q := countedCanonicalFairWords b bits
  have hh (i : Fin n) : RationalHeight (q.1 i).value b := by
    rw [countedCanonicalFairWords_value,← countedCanonicalFairWord_value]
    exact countedCanonicalFairWord_height b (bits i)
  have hCmp (i j : Fin n) : (binaryKeyLE q.1 i j).2≤3400*(b+2)^3 :=
    BinaryFraction.countedLE_work _ _ (b+1)
      (BinaryRational.storage_width _ b (hh i)) (BinaryRational.storage_width _ b (hh j))
      (BinaryRational.storage_denominator_pos _) (BinaryRational.storage_denominator_pos _)
  have hSort := countedSortBy_work (binaryKeyLE q.1) _ (binaryKeyLE_value q.1)
    (List.finRange n) (3400*(b+2)^3) (fun a _ b _ => hCmp a b)
  simp only [List.length_finRange] at hSort
  exact Nat.add_le_add_right (Nat.add_le_add (countedCanonicalFairWords_work b bits) hSort) _

def countedBinaryWordInteger (x : List Bool) : BinaryRational × ℕ :=
  let q : BinaryFraction := ⟨false,x,[true]⟩
  let r := q.countedReduce
  have h : 0<binaryWordValue q.denominator := by change 0<binaryWordValue [true]; decide
  (⟨r.1.normalizeSign,by rw [BinaryFraction.countedReduce_normalization q h,BinaryFraction.encode_value]⟩,
    r.2+x.length+5)

lemma countedBinaryWordInteger_value (x : List Bool) :
    (countedBinaryWordInteger x).1.value=(binaryWordValue x : ℚ) := by
  unfold countedBinaryWordInteger
  dsimp only
  let q : BinaryFraction := ⟨false,x,[true]⟩
  have h : 0<binaryWordValue q.denominator := by change 0<binaryWordValue [true]; decide
  change q.countedReduce.1.normalizeSign.value=_
  rw [BinaryFraction.normalizeSign_value,(q.countedReduce_correct h).1]
  simp [q,BinaryFraction.value,binaryWordValue,bitDigit]

lemma countedBinaryWordInteger_work (x : List Bool) :
    (countedBinaryWordInteger x).2≤110*(x.length+2)^3 := by
  let q : BinaryFraction := ⟨false,x,[true]⟩
  have hQ : q.width+1≤x.length+2 := by
    change max x.length 1+1≤_
    omega
  have h := q.countedReduce_work
  have h' := h.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hQ 3))
  have hL : x.length+2≤(x.length+2)^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<x.length+2) (by omega : 1≤3)
  change q.countedReduce.2+x.length+5≤_
  omega

lemma binaryAllOnes_value (c : ℕ) : binaryWordValue (List.replicate c true)=2^c-1 := by
  induction c with
  | zero => simp [binaryWordValue]
  | succ c ih =>
    rw [List.replicate_succ,binaryWordValue,ih,pow_succ]
    change 1+2*((2:ℕ)^c-1)=(2:ℕ)^c*2-1
    have h : 0<(2:ℕ)^c := by positivity
    generalize (2:ℕ)^c = k at h ⊢
    omega

structure BinaryRankCalibrationSeed (n m J : ℕ) (T P : Type) where
  target : TargetGrid m → T
  validation : Fin m → Equiv.Perm (Fin n) × ((Fin n → BinaryRational) × PolicyQueryArray n J P)
  onlineTimes : Fin n → BinaryRational
  onlineQueries : PolicyQueryArray n J P
  coinGrid : BinaryRational
  coinLast : List Bool
  coinWord : List Bool
  work : ℕ

def countedBinaryRankCalibrationSeed {T P : Type} (b c : ℕ) (bits : RankCalibrationBits n m J b c T P) :
    BinaryRankCalibrationSeed n m J T P :=
  let rows := Vector.ofFn (fun j : Fin m =>
    let r := bits.2.1 j
    let p := countedBinaryRankOrder b r.1
    let s := countedBinaryRankOrder b r.2.1
    ((p.1.1,s.1.2,r.2.2),p.2+s.2+6))
  let online := countedBinaryRankOrder b bits.2.2.1
  let coinGrid := countedBinaryWordInteger (binaryPowerTwo c)
  ⟨bits.1,fun j => (rows.get j).1,online.1.2,bits.2.2.2.1,coinGrid.1,
    List.replicate c true,List.ofFn bits.2.2.2.2,
    (∑ j : Fin m, (rows.get j).2)+online.2+coinGrid.2+4*c+10⟩

lemma countedBinaryRankCalibrationSeed_work {T P : Type} (b c : ℕ)
    (bits : RankCalibrationBits n m J b c T P) :
    (countedBinaryRankCalibrationSeed b c bits).work ≤
      m*(2*binaryRankOrderWorkBound n b+6)+binaryRankOrderWorkBound n b+110*(c+3)^3+4*c+10 := by
  unfold countedBinaryRankCalibrationSeed
  dsimp only
  simp only [vector_get_ofFn]
  have hRows : (∑ j : Fin m, ((countedBinaryRankOrder b (bits.2.1 j).1).2+
        (countedBinaryRankOrder b (bits.2.1 j).2.1).2+6))≤m*(2*binaryRankOrderWorkBound n b+6) := by
    calc
      _ ≤ ∑ _j : Fin m, (2*binaryRankOrderWorkBound n b+6) := by
        apply Finset.sum_le_sum
        intro j _
        have hP := countedBinaryRankOrder_work b (bits.2.1 j).1
        have hS := countedBinaryRankOrder_work b (bits.2.1 j).2.1
        omega
      _ = _ := by simp
  have hOn := countedBinaryRankOrder_work b bits.2.2.1
  have hC := countedBinaryWordInteger_work (binaryPowerTwo c)
  have hLen : (binaryPowerTwo c).length=c+1 := by simp [binaryPowerTwo]
  rw [hLen,show c+1+2=c+3 by omega] at hC
  omega

lemma countedBinaryRankCalibrationSeed_validation {T P : Type} (b c : ℕ)
    (bits : RankCalibrationBits n m J b c T P) (j : Fin m) :
    let q := (countedBinaryRankCalibrationSeed b c bits).validation j
    let r := (countedDecodeRankCalibrationBits b c bits).1.2.1 j
    q.1=r.1 ∧ (fun i => (q.2.1 i).value)=r.2.1 ∧ q.2.2=r.2.2 := by
  dsimp only
  simp only [countedBinaryRankCalibrationSeed,vector_get_ofFn]
  simp only [countedDecodeRankCalibrationBits,vector_get_ofFn]
  exact ⟨countedBinaryRankOrder_permutation b (bits.2.1 j).1,
    countedBinaryRankOrder_times b (bits.2.1 j).2.1,rfl⟩

lemma countedBinaryRankCalibrationSeed_online {T P : Type} (b c : ℕ)
    (bits : RankCalibrationBits n m J b c T P) :
    let q := countedBinaryRankCalibrationSeed b c bits
    (fun i => (q.onlineTimes i).value)=(countedDecodeRankCalibrationBits b c bits).1.2.2.1 ∧
      q.onlineQueries=bits.2.2.2.1 ∧ q.coinGrid.value=(2^c : ℕ) ∧
      binaryWordValue q.coinLast=2^c-1 ∧
      binaryWordValue q.coinWord=(fairBitsIndex c bits.2.2.2.2).val := by
  dsimp only
  refine ⟨countedBinaryRankOrder_times b bits.2.2.1,rfl,?_,binaryAllOnes_value c,
    binaryWordValue_ofFn_fairBits c bits.2.2.2.2⟩
  simp only [countedBinaryRankCalibrationSeed,countedBinaryWordInteger_value,binaryPowerTwo_value]

end ProphetSecretary.Statistics.Calibration
