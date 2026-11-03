import ProphetSecretary.Statistics.BinaryEmpiricalTree

/-!
# A hard bit bound for the actual empirical tree

Along an edge only one dyadic factor is appended to the horizon. The
remaining-level invariant supplies all callback widths. The computed work
counter then uses the hard bound on every recursive branch.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis

variable {n : ℕ}

private lemma binaryFrame_heights (p : Fin n → BinaryRational) (P U Z : ℕ)
    (hp : ∀ i, RationalHeight (p i).value P) (x : ScalarPlannerListState n BinaryRational)
    (hx : x.1.Nodup) (hu : RationalHeight x.2.1.value U) (hz : RationalHeight x.2.2.value Z) (hZ : 2≤Z) :
    let q := (countedBinaryPlannerFrame p x).1
    RationalHeight q.time.value U ∧ RationalHeight q.durationWeight.value Z ∧
      RationalHeight q.weight.value (n*(P+3)) ∧ RationalHeight q.emptyValue.value (Z+U) ∧
      RationalHeight q.offset.value (Z+U+n*(P+3)) ∧ RationalHeight q.coefficient.value (2*(n*(P+3))+3) := by
  have h := countedScalarPlannerFrame_height (fun i => (p i).value) P U Z hp
    (scalarPlannerStateValueMap BinaryRational.value x) hx hu hz hZ
  have he := countedScalarPlannerFrame_valueMap BinaryRational.valueHom BinaryRational.value_strictMono p x
  change (countedScalarPlannerFrame (fun i => (p i).value) (scalarPlannerStateValueMap BinaryRational.value x)).1 = _ at he
  dsimp only at h
  rw [he,← countedBinaryPlannerFrame_value] at h
  exact h

private lemma binarySampler_fraction_height (l : List (Fin n)) (p : Fin n → BinaryRational)
    (s : PlannerFieldSeed n BinaryRational) (B : ℕ) (h : ∀ i, RationalHeight (s.2.2.1 i).value B) :
    RationalHeight (countedBinaryUniformSampler l p s).1.2.1.value B := by
  cases l with
  | nil =>
    change RationalHeight (BinaryRational.ofRat 0).value B
    rw [BinaryRational.ofRat_value]
    exact rationalHeight_zero.mono (Nat.zero_le _)
  | cons i l =>
    change RationalHeight (countedBinaryPlannerFraction _ s.2.2.1).1.value B
    rw [countedBinaryPlannerFraction_value]
    exact countedPlannerFraction_height _ _ B h

def binaryEmpiricalValueHeight (n m Y M P U Z b R : ℕ) : ℕ :=
  64*(plannerPrimitiveHeight n m Y M P U Z b R+R+1)*16^R

theorem binaryEmpiricalRecursion_height (rows : Vector (List BinaryRational) n) (p : Fin n → BinaryRational)
    (m Y M P U Z b R r : ℕ) (hr : r≤R) (hm : m≤2^M) (hRows : ∀ i, (rows.get i).length≤m)
    (hy : ∀ i x, x∈rows.get i → RationalHeight x.value Y) (hp : ∀ i, RationalHeight (p i).value P)
    (hZ : 2≤Z) (x : ScalarPlannerListState n BinaryRational) (hx : x.1.Nodup)
    (hu : RationalHeight x.2.1.value (U+(R-r)*b)) (hz : RationalHeight x.2.2.value Z)
    (t : MultilevelTree (PlannerFairSeed n b) r) :
    RationalHeight ((binaryEmpiricalRecursion rows p b).estimate r x t).1.value
      (binaryEmpiricalValueHeight n m Y M P U Z b R) := by
  rw [binaryEmpiricalRecursion_estimate_value,countedBinaryScalarPlannerEstimate_value]
  let qr := plannerRowsValueMap BinaryRational.value rows
  let pr := fun i => (p i).value
  have hrEq (i : Fin n) : qr.get i=(rows.get i).map BinaryRational.value := by simp [qr,plannerRowsValueMap,Vector.get]
  have hrLen (i : Fin n) : (qr.get i).length≤m := by rw [hrEq,List.length_map]; exact hRows i
  have hrH (i : Fin n) (a : ℚ) (ha : a∈qr.get i) : RationalHeight a Y := by
    rw [hrEq] at ha
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    exact hy i x hx
  have h := countedScalarPlannerRecursion_height qr pr (fun s => (countedPlannerFairSeed b s).1)
    m Y M P U Z b R hrLen hm hrH hp hZ (countedPlannerFairSeed_fraction_height b)
    r hr (scalarPlannerStateValueMap BinaryRational.value x) hx hu hz t
  have hW : multilevelTreeWork r t≤4*16^R :=
    (by exact_mod_cast multilevelTreeWork_le r t : multilevelTreeWork r t≤4*16^r).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hr))
  exact h.mono ((Nat.mul_le_mul_left _ hW).trans_eq (by unfold binaryEmpiricalValueHeight; ring))

def binaryEmpiricalOperandHeight (n m Y M P U Z b R : ℕ) : ℕ :=
  U+R*b+Z+4*(n*(P+3))+m*(Y+1)+2*M+binaryEmpiricalValueHeight n m Y M P U Z b R+11

def binaryEmpiricalCallbackWork (n m Y M P U Z b R : ℕ) : ℕ :=
  binaryFrameWorkBound n P (U+R*b) Z + binarySamplerWorkBound n (P+b) + binaryFairSeedWorkBound n b +
    3*(3600*(U+R*b+b+2)^3)+8+
    binaryPayoffWorkBound n m P M Y (binaryEmpiricalValueHeight n m Y M P U Z b R)+20

def binaryEmpiricalTreeWorkBound (n m Y M P U Z b R : ℕ) : ℕ :=
  canonicalTreeBitUnit R (binaryEmpiricalOperandHeight n m Y M P U Z b R)
    (binaryEmpiricalCallbackWork n m Y M P U Z b R)*(4*16^R)

theorem binaryEmpiricalRecursion_bit_work (rows : Vector (List BinaryRational) n) (p : Fin n → BinaryRational)
    (m Y M P U Z b R r : ℕ) (hr : r≤R) (hm : m≤2^M) (hRows : ∀ i, (rows.get i).length≤m)
    (hy : ∀ i x, x∈rows.get i → RationalHeight x.value Y) (hp : ∀ i, RationalHeight (p i).value P)
    (hZ : 2≤Z) (x : ScalarPlannerListState n BinaryRational) (hx : x.1.Nodup)
    (hu : RationalHeight x.2.1.value U) (hz : RationalHeight x.2.2.value Z)
    (t : MultilevelTree (PlannerFairSeed n b) r) :
    ((binaryEmpiricalRecursion rows p b).canonicalEstimate r x t).2≤
      binaryEmpiricalTreeWorkBound n m Y M P U Z b R := by
  let D := binaryEmpiricalRecursion rows p b
  let W := n*(P+3)
  let V := binaryEmpiricalValueHeight n m Y M P U Z b R
  let B := binaryEmpiricalOperandHeight n m Y M P U Z b R
  let C := binaryEmpiricalCallbackWork n m Y M P U Z b R
  let G := fun (k : ℕ) (q : ScalarPlannerListState n BinaryRational) =>
    q.1.Nodup ∧ RationalHeight q.2.1.value (U+(R-k)*b) ∧ RationalHeight q.2.2.value Z
  let qr := plannerRowsValueMap BinaryRational.value rows
  let pr := fun i => (p i).value
  have hrEq (i : Fin n) : qr.get i=(rows.get i).map BinaryRational.value := by simp [qr,plannerRowsValueMap,Vector.get]
  have hrLen (i : Fin n) : (qr.get i).length≤m := by rw [hrEq,List.length_map]; exact hRows i
  have hrH (i : Fin n) (a : ℚ) (ha : a∈qr.get i) : RationalHeight a Y := by
    rw [hrEq] at ha
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    exact hy i x hx
  have hValue (k : ℕ) (q : ScalarPlannerListState n BinaryRational) (t' : MultilevelTree (PlannerFairSeed n b) k)
      (hk : k≤R) (hq : G k q) : RationalHeight (D.estimate k q t').1.value V :=
    binaryEmpiricalRecursion_height rows p m Y M P U Z b R k hk hm hRows hy hp hZ q hq.1 hq.2.1 hq.2.2 t'
  have hF (k : ℕ) (q : ScalarPlannerListState n BinaryRational) (hq : G k q) :=
    binaryFrame_heights p P _ Z hp q hq.1 hq.2.1 hq.2.2 hZ
  have hPrepare (k : ℕ) (q : ScalarPlannerListState n BinaryRational) (_ : k≤R) (hq : G k q) :
      (D.prepare q).2≤C ∧ RationalHeight (D.prepare q).1.offset.value B ∧
        RationalHeight (D.prepare q).1.coefficient.value B := by
    have hTime : U+(R-k)*b≤U+R*b := Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.sub_le _ _)) _
    have hw := countedBinaryPlannerFrame_work p q P (U+R*b) Z hq.1 hp (hq.2.1.mono hTime) hq.2.2 hZ
    have hh := hF k q hq
    refine ⟨?_,hh.2.2.2.2.1.mono ?_,hh.2.2.2.2.2.mono ?_⟩
    · change (countedBinaryPlannerFrame p q).2+3≤_
      dsimp only [C,binaryEmpiricalCallbackWork]
      omega
    · dsimp only [B,binaryEmpiricalOperandHeight]
      omega
    · dsimp only [B,binaryEmpiricalOperandHeight]
      omega
  have hActive (k : ℕ) (q : ScalarPlannerListState n BinaryRational) (hq : G k q) :
      (D.prepare q).1.context.active.Nodup := by
    change (countedBinaryPlannerFrame p q).1.active.Nodup
    rw [countedBinaryPlannerFrame_value]
    exact countedScalarPlannerFrame_active_nodup p q hq.1
  have hSample (k : ℕ) (q : ScalarPlannerListState n BinaryRational) (s : PlannerFairSeed n b) (_ : k≤R)
      (hq : G k q) : (D.sample (D.prepare q).1.context s).2≤C := by
    let u := (countedBinaryFairSeed b s).1
    have hB (bits : Fin b → Bool) : RationalHeight (binaryFairCoordinate b bits).value (P+b) :=
      (binaryFairCoordinate_height b bits).mono (by omega)
    have hU : RationalHeight u.1.1.value (P+b) ∧ (∀ i,RationalHeight (u.1.2 i).value (P+b)) ∧
        RationalHeight u.2.1.value (P+b) ∧ (∀ i,RationalHeight (u.2.2.1 i).value (P+b)) ∧
        ∀ i,RationalHeight (u.2.2.2 i).value (P+b) :=
      ⟨hB s.1.1,fun i => hB (s.1.2 i),hB s.2.1,fun i => hB (s.2.2.1 i),fun i => hB (s.2.2.2 i)⟩
    have hw := countedBinaryUniformSampler_work (D.prepare q).1.context.active (hActive k q hq) p u (P+b)
      (fun i => (hp i).mono (by omega)) hU
    have hb := countedBinaryFairSeed_work b s
    change (countedBinaryFairSeed b s).2+(countedBinaryUniformSampler (D.prepare q).1.context.active p u).2+3≤_
    dsimp only [C,binaryEmpiricalCallbackWork]
    omega
  have hOut (k : ℕ) (q : ScalarPlannerListState n BinaryRational) (s : PlannerFairSeed n b) (hq : G k q) :
      let o := (D.sample (D.prepare q).1.context s).1
      o.2.2.Nodup ∧ RationalHeight o.2.1.value b := by
    let u := (countedBinaryFairSeed b s).1
    let l := (D.prepare q).1.context.active
    change (countedBinaryUniformSampler l p u).1.2.2.Nodup ∧
      RationalHeight (countedBinaryUniformSampler l p u).1.2.1.value b
    exact ⟨by rw [countedBinaryUniformSampler_native_value]; exact countedPlannerUniformSampler_nodup l (hActive k q hq) p u,
      binarySampler_fraction_height l p u b (fun i => binaryFairCoordinate_height b (s.2.2.1 i))⟩
  have hChild (k : ℕ) (q : ScalarPlannerListState n BinaryRational) (s : PlannerFairSeed n b) (j : ℕ)
      (hk : k≤R) (hq : G k q) (hj : j<k) :
      let a := (D.prepare q).1.context
      let out := D.child a (D.sample a s).1
      out.2≤C ∧ G j out.1 := by
    let a := (D.prepare q).1.context
    let o := (D.sample a s).1
    have hf := hF k q hq
    have hOut' := hOut k q s hq
    have ht : RationalHeight a.time.value (U+(R-k)*b) := hf.1
    have hd : RationalHeight a.durationWeight.value Z := hf.2.1
    have hW := countedBinaryPlannerChild_work a o (U+R*b+b)
      (ht.mono (by have h := Nat.mul_le_mul_right b (Nat.sub_le R k); omega)) (hOut'.2.mono (by omega))
    constructor
    · change (countedBinaryPlannerChild a o).2≤_
      dsimp only [C,binaryEmpiricalCallbackWork]
      omega
    · change G j (countedBinaryPlannerChild a o).1
      rw [countedBinaryPlannerChild_value]
      refine ⟨hOut'.1,?_,hd⟩
      change RationalHeight (BinaryRational.mul a.time (max 0 (min 1 o.2.1))).value _
      rw [BinaryRational.mul_value,BinaryRational.max_value,BinaryRational.min_value,BinaryRational.zero_value,
        BinaryRational.one_value]
      have h := ht.mul (rationalHeight_unitClamp hOut'.2)
      have hM := Nat.mul_le_mul_right b (show R-k+1≤R-j by omega)
      rw [Nat.add_mul,Nat.one_mul] at hM
      exact h.mono (by omega)
  have hPay (k : ℕ) (q : ScalarPlannerListState n BinaryRational) (s : PlannerFairSeed n b) (a : BinaryRational)
      (_ : k≤R) (hq : G k q) (ha : RationalHeight a.value V) :
      let c := (D.prepare q).1.context
      let f := D.payoff c (D.sample c s).1 a
      f.2≤C ∧ RationalHeight f.1.value B := by
    let o := (D.sample (D.prepare q).1.context s).1
    have hOut' := hOut k q s hq
    have hw := countedBinaryPlannerPayoff_work rows p o a m P M Y V hRows hm hy hp hOut'.1 ha
    refine ⟨?_,?_⟩
    · change (countedBinaryPlannerPayoff rows p o a).2≤_
      have hw' : (countedBinaryPlannerPayoff rows p o a).2≤
          binaryPayoffWorkBound n m P M Y (binaryEmpiricalValueHeight n m Y M P U Z b R) := hw
      dsimp only [C,binaryEmpiricalCallbackWork]
      omega
    · change RationalHeight (countedBinaryPlannerPayoff rows p o a).1.value _
      rw [countedBinaryPlannerPayoff_value]
      have he := countedScalarPlannerPayoff_valueMap BinaryRational.valueHom BinaryRational.value_strictMono rows p o a
      change (countedScalarPlannerPayoff qr pr (plannerListOutputMap BinaryRational.value o) a.value).1 =
        (countedScalarPlannerPayoff rows p o a).1.value at he
      rw [← he]
      exact (countedScalarPlannerPayoff_height qr pr _ a.value m Y M P V hrLen hm hrH hp hOut'.1 ha).mono
        (by dsimp only [B,binaryEmpiricalOperandHeight]; omega)
  have hG : G r x := ⟨hx,hu.mono (by omega),hz⟩
  have h := CountedPlannerRecursion.canonicalEstimate_work D G R B V C hPrepare hSample hChild hPay hValue r hr x hG t
  have hW : multilevelTreeWork r t≤4*16^R :=
    (by exact_mod_cast multilevelTreeWork_le r t : multilevelTreeWork r t≤4*16^r).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hr))
  exact h.trans (Nat.mul_le_mul_left _ hW)

end ProphetSecretary.Statistics
