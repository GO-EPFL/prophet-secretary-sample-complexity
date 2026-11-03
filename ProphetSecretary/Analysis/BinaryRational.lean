import ProphetSecretary.Analysis.ArithmeticExpressionBits

/-!
# Canonical binary rational values

The stored representation consists of a sign and two trimmed binary words.
The invariant is an erased proof. Normalization of a fraction uses the
counted Euclidean reduction, with a separate canonical sign for zero.
-/

namespace ProphetSecretary.Analysis

namespace BinaryFraction

def encode (x : ℚ) : BinaryFraction :=
  ⟨decide (x.num<0),x.num.natAbs.bits,x.den.bits⟩

lemma encode_value (x : ℚ) : (encode x).value = x := by
  have hn : (if decide (x.num<0) then -(x.num.natAbs:ℚ) else (x.num.natAbs:ℚ)) = (x.num:ℚ) := by
    have h := ofInt_value x.num
    simpa only [ofInt,value,binaryWordValue_bits,show binaryWordValue [true]=1 by decide,Nat.cast_one,div_one] using h
  simp only [encode,value,binaryWordValue_bits,hn,Rat.num_div_den]

lemma encode_denominator_pos (x : ℚ) : 0 < binaryWordValue (encode x).denominator := by
  simpa only [encode,binaryWordValue_bits] using x.pos

def normalizeSign (q : BinaryFraction) : BinaryFraction :=
  {q with negative := q.negative && !q.numerator.isEmpty}

lemma normalizeSign_value (q : BinaryFraction) : q.normalizeSign.value = q.value := by
  cases h : q.numerator.isEmpty
  · simp [normalizeSign,value,h]
  · have he : q.numerator=[] := by cases hn : q.numerator <;> simp_all
    simp [normalizeSign,value,he,binaryWordValue]

private lemma eq_fields (q r : BinaryFraction) (hs : q.negative=r.negative)
    (hn : q.numerator=r.numerator) (hd : q.denominator=r.denominator) : q=r := by
  cases q; cases r; simp_all

theorem countedReduce_normalization (q : BinaryFraction) (hq : 0 < binaryWordValue q.denominator) :
    q.countedReduce.1.normalizeSign = encode q.value := by
  let t := q.countedReduce.1
  let n := binaryWordValue t.numerator
  let d := binaryWordValue t.denominator
  let z : ℤ := if t.negative then -(n:ℤ) else (n:ℤ)
  have hc := countedReduce_value_components q hq
  have hn : n = binaryWordValue q.numerator / (binaryWordValue q.numerator).gcd (binaryWordValue q.denominator) := by
    dsimp [n,t]
    rw [hc.1,binaryWordValue_bits]
  have hd : d = binaryWordValue q.denominator / (binaryWordValue q.numerator).gcd (binaryWordValue q.denominator) := by
    dsimp [d,t]
    rw [hc.2,binaryWordValue_bits]
  have hD : 0<d := (countedReduce_correct q hq).2
  have hz : z.natAbs=n := by cases ht : t.negative <;> simp [z,ht]
  have hCop : Nat.Coprime z.natAbs (d:ℤ).natAbs := by
    rw [hz,Int.natAbs_natCast,hn,hd]
    exact Nat.gcd_div_gcd_div_gcd_of_pos_right hq
  have hVal : (z:ℚ)/(d:ℤ) = q.value := by
    rw [← (countedReduce_correct q hq).1]
    change (z:ℚ)/(d:ℤ) = t.value
    cases ht : t.negative <;> simp [z,ht,value,n,d]
  have hNum := Rat.num_div_eq_of_coprime (by exact_mod_cast hD : (0:ℤ)<d) hCop
  have hDen := Rat.den_div_eq_of_coprime (by exact_mod_cast hD : (0:ℤ)<d) hCop
  rw [hVal] at hNum hDen
  have hDen' : q.value.den=d := by exact_mod_cast hDen
  have hN : t.numerator=n.bits := by change q.countedReduce.1.numerator=n.bits; rw [hc.1,hn]
  have hE : t.numerator.isEmpty = decide (n=0) := by
    cases ht : t.numerator.isEmpty
    · have hne : n ≠ 0 := by
        intro h0
        rw [h0] at hN
        simp [hN] at ht
      simp [hne]
    · have he : t.numerator=[] := by cases hn' : t.numerator <;> simp_all
      have h0 : n=0 := by simp [n,he,binaryWordValue]
      simp [h0]
  apply eq_fields
  · change (t.negative && !t.numerator.isEmpty) = decide (q.value.num<0)
    rw [hE,hNum]
    cases ht : t.negative <;> by_cases h0 : n=0 <;> simp [z,ht,h0,Int.natCast_pos,Nat.pos_iff_ne_zero]
  · change t.numerator=q.value.num.natAbs.bits
    rw [hNum,hz,hN]
  · change t.denominator=q.value.den.bits
    rw [hDen']
    change q.countedReduce.1.denominator=d.bits
    rw [hc.2,hd]

end BinaryFraction

/-- Binary fractions in canonical storage form. -/
structure BinaryRational where
  storage : BinaryFraction
  canonical : storage = BinaryFraction.encode storage.value

namespace BinaryRational

def value (q : BinaryRational) : ℚ := q.storage.value

theorem value_injective : Function.Injective value := by
  rintro ⟨a,ha⟩ ⟨b,hb⟩ h
  have he : a.value=b.value := h
  have h' : a=b := ha.trans ((congrArg BinaryFraction.encode he).trans hb.symm)
  subst b
  rfl

def ofRat (x : ℚ) : BinaryRational := ⟨BinaryFraction.encode x,by rw [BinaryFraction.encode_value]⟩

@[simp] lemma ofRat_value (x : ℚ) : (ofRat x).value=x := BinaryFraction.encode_value x

lemma storage_denominator_pos (x : BinaryRational) : 0 < binaryWordValue x.storage.denominator := by
  rw [x.canonical]
  exact BinaryFraction.encode_denominator_pos _

lemma storage_width (x : BinaryRational) (B : ℕ) (h : RationalHeight x.value B) : x.storage.width≤B+1 := by
  have hW (n : ℕ) (hn : n≤2^B) : n.bits.length≤B+1 := by
    rw [Nat.size_eq_bits_len,Nat.size_le,pow_succ]
    have hp : 0<(2:ℕ)^B := by positivity
    omega
  rw [x.canonical]
  exact max_le (hW _ h.1) (hW _ h.2)

def ofFraction (q : BinaryFraction) (h : 0 < binaryWordValue q.denominator) : BinaryRational :=
  ⟨q.countedReduce.1.normalizeSign,by
    rw [BinaryFraction.countedReduce_normalization q h,BinaryFraction.encode_value]⟩

lemma ofFraction_value (q : BinaryFraction) (h : 0 < binaryWordValue q.denominator) :
    (ofFraction q h).value=q.value := by
  change q.countedReduce.1.normalizeSign.value=q.value
  rw [BinaryFraction.normalizeSign_value,(BinaryFraction.countedReduce_correct q h).1]

private def addRaw (x y : BinaryFraction) : BinaryFraction :=
  let a := countedBinaryMultiply x.numerator y.denominator
  let b := countedBinaryMultiply y.numerator x.denominator
  let d := countedBinaryMultiply x.denominator y.denominator
  let n := countedSignedBinaryAdd x.negative a.1 y.negative b.1
  ⟨n.1.1,n.1.2,d.1⟩

private lemma addRaw_denominator_pos (x y : BinaryFraction) (hx : 0<binaryWordValue x.denominator)
    (hy : 0<binaryWordValue y.denominator) : 0<binaryWordValue (addRaw x y).denominator := by
  change 0<binaryWordValue (countedBinaryMultiply x.denominator y.denominator).1
  rw [countedBinaryMultiply_value]
  exact Nat.mul_pos hx hy

private def mulRaw (x y : BinaryFraction) : BinaryFraction :=
  let a := countedBinaryMultiply x.numerator y.numerator
  let d := countedBinaryMultiply x.denominator y.denominator
  ⟨x.negative ^^ y.negative,a.1,d.1⟩

private lemma mulRaw_denominator_pos (x y : BinaryFraction) (hx : 0<binaryWordValue x.denominator)
    (hy : 0<binaryWordValue y.denominator) : 0<binaryWordValue (mulRaw x y).denominator :=
  addRaw_denominator_pos x y hx hy

def add (x y : BinaryRational) : BinaryRational := ofFraction (addRaw x.storage y.storage)
  (addRaw_denominator_pos _ _ (storage_denominator_pos x) (storage_denominator_pos y))

def sub (x y : BinaryRational) : BinaryRational := ofFraction (addRaw x.storage y.storage.neg)
  (addRaw_denominator_pos _ _ (storage_denominator_pos x) (storage_denominator_pos y))

def mul (x y : BinaryRational) : BinaryRational := ofFraction (mulRaw x.storage y.storage)
  (mulRaw_denominator_pos _ _ (storage_denominator_pos x) (storage_denominator_pos y))

def div (x y : BinaryRational) : BinaryRational := ofFraction (mulRaw x.storage y.storage.countedInv.1)
  (mulRaw_denominator_pos _ _ (storage_denominator_pos x)
    (BinaryFraction.countedInv_correct y.storage (storage_denominator_pos y)).2)

@[simp] lemma add_value (x y : BinaryRational) : (add x y).value=x.value+y.value := by
  change (x.storage.countedAdd y.storage).1.normalizeSign.value=x.value+y.value
  rw [BinaryFraction.normalizeSign_value,(BinaryFraction.countedAdd_correct _ _
    (storage_denominator_pos x) (storage_denominator_pos y)).1]
  rfl

@[simp] lemma sub_value (x y : BinaryRational) : (sub x y).value=x.value-y.value := by
  change (x.storage.countedSub y.storage).1.normalizeSign.value=x.value-y.value
  rw [BinaryFraction.normalizeSign_value,(BinaryFraction.countedSub_correct _ _
    (storage_denominator_pos x) (storage_denominator_pos y)).1]
  rfl

@[simp] lemma mul_value (x y : BinaryRational) : (mul x y).value=x.value*y.value := by
  change (x.storage.countedMul y.storage).1.normalizeSign.value=x.value*y.value
  rw [BinaryFraction.normalizeSign_value,(BinaryFraction.countedMul_correct _ _
    (storage_denominator_pos x) (storage_denominator_pos y)).1]
  rfl

@[simp] lemma div_value (x y : BinaryRational) : (div x y).value=x.value/y.value := by
  change (x.storage.countedDiv y.storage).1.normalizeSign.value=x.value/y.value
  rw [BinaryFraction.normalizeSign_value,(BinaryFraction.countedDiv_correct _ _
    (storage_denominator_pos x) (storage_denominator_pos y)).1]
  rfl

end BinaryRational

end ProphetSecretary.Analysis
