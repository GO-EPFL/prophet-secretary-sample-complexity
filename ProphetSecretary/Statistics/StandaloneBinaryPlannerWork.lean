import ProphetSecretary.Statistics.BinaryScalarWorkPolynomial
import ProphetSecretary.Statistics.StandaloneBinaryPlanner
import ProphetSecretary.Statistics.PlannerFairTape
import ProphetSecretary.Statistics.CalibratedPolynomialWork

/-!
# The binary scalar query's work envelope

The exact operation counters are polynomials in the dimensions, operand
height, precision, copy count, and full tree factor.
-/

open MeasureTheory

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Statistics.Calibration ProphetSecretary.Probability

def standaloneBinaryTotalWorkBound (n m B b r a : ℕ) : ℕ :=
  standaloneBinaryPlanWorkBound n m B + binaryScalarQueryWorkBound n m B m B B b r a+3+
    fairQueryBankWorkBound n b (2*a+1) r+5*(2*a+1)*16^r*((3*n+2)*b)

private structure StandaloneShape where
  n : ℕ
  m : ℕ
  B : ℕ
  b : ℕ
  r : ℕ
  a : ℕ

private def standaloneShapeSize (s : StandaloneShape) : ℕ :=
  s.n+s.m+s.B+s.b+16^s.r+s.a+2

private lemma standaloneShapeSize_pos (s : StandaloneShape) : 0<standaloneShapeSize s := by
  have h := Nat.zero_le ((16:ℕ)^s.r)
  unfold standaloneShapeSize
  omega

private lemma standaloneWorkAdd {F G : StandaloneShape → ℕ}
    (hF : HasPolynomialWorkBound standaloneShapeSize F) (hG : HasPolynomialWorkBound standaloneShapeSize G) :
    HasPolynomialWorkBound standaloneShapeSize (fun s => F s+G s) :=
  HasPolynomialWorkBound.add standaloneShapeSize_pos hF hG

local infixl:65 " +ₚ " => standaloneWorkAdd
local infixl:70 " *ₚ " => HasPolynomialWorkBound.mul
local infixr:80 " ^ₚ " => HasPolynomialWorkBound.pow

private lemma standaloneShape_polynomial :
    HasPolynomialWorkBound standaloneShapeSize
      (fun s => standaloneBinaryTotalWorkBound s.n s.m s.B s.b s.r s.a) := by
  let N := standaloneShapeSize
  let c := HasPolynomialWorkBound.const N
  have hN := HasPolynomialWorkBound.size N
  have hn : HasPolynomialWorkBound N StandaloneShape.n :=
    hN.of_le (fun x => by have h := Nat.zero_le ((16:ℕ)^x.r); unfold N standaloneShapeSize; omega)
  have hm : HasPolynomialWorkBound N StandaloneShape.m :=
    hN.of_le (fun x => by have h := Nat.zero_le ((16:ℕ)^x.r); unfold N standaloneShapeSize; omega)
  have hB : HasPolynomialWorkBound N StandaloneShape.B :=
    hN.of_le (fun x => by have h := Nat.zero_le ((16:ℕ)^x.r); unfold N standaloneShapeSize; omega)
  have hb : HasPolynomialWorkBound N StandaloneShape.b :=
    hN.of_le (fun x => by have h := Nat.zero_le ((16:ℕ)^x.r); unfold N standaloneShapeSize; omega)
  have ha : HasPolynomialWorkBound N StandaloneShape.a :=
    hN.of_le (fun x => by have h := Nat.zero_le ((16:ℕ)^x.r); unfold N standaloneShapeSize; omega)
  have hExp : HasPolynomialWorkBound N (fun s => (16:ℕ)^s.r) :=
    hN.of_le (fun x => by have h := Nat.zero_le ((16:ℕ)^x.r); unfold N standaloneShapeSize; omega)
  have hR4 : HasPolynomialWorkBound N (fun s => (s.r+1)^4) :=
    hExp.of_le (fun _ => levelAllocator_poly _)
  have hn1 := hn +ₚ c 1
  have hm1 := hm +ₚ c 1
  have hP := c 2 *ₚ hm
  have hW := hn *ₚ (hP +ₚ c 3)
  have hRow := c 1 +ₚ hm *ₚ (c 3400 *ₚ (hB +ₚ c 2) ^ₚ 3 +ₚ c 5) +ₚ
    c 2 *ₚ (c 1 +ₚ c 2 *ₚ hm) +ₚ c 3600 *ₚ (hm +ₚ c 2) ^ₚ 3 +ₚ c 10
  have hA := c 1 +ₚ hn *ₚ (c 3400 *ₚ (hP +ₚ c 2) ^ₚ 3 +ₚ c 5)
  have hWeight := c 1 +ₚ hn *ₚ (c 3 *ₚ (c 3600 *ₚ (hW +ₚ hP +ₚ c 5) ^ₚ 3) +ₚ c 5)
  have hFrame := hA +ₚ hWeight +ₚ c 9 *ₚ
    (c 3600 *ₚ (hB +ₚ hB +ₚ c 2 *ₚ hW +ₚ hP +ₚ c 10 +ₚ c 2) ^ₚ 3) +ₚ c 24
  have hG := hW +ₚ hB +ₚ (c 10 *ₚ hn +ₚ c 4) +ₚ c 2
  have hD := c 2 *ₚ hB +ₚ c 2 *ₚ hW +ₚ c 13
  have hQ := hD +ₚ c 9 *ₚ (hG +ₚ c 1) +ₚ hB +ₚ c 1
  have hPublic := c 3 *ₚ hQ *ₚ (c 7000 *ₚ (c 2 *ₚ hQ +ₚ c 4) ^ₚ 3 +ₚ c 5) +ₚ
    c 12 *ₚ hQ +ₚ c 35
  have hPlan : HasPolynomialWorkBound N (fun s => standaloneBinaryPlanWorkBound s.n s.m s.B) :=
    hn *ₚ hRow +ₚ c 3 *ₚ hn +ₚ c 1 +ₚ hFrame +ₚ (c 5 *ₚ (c 3600 *ₚ (hD +ₚ c 2) ^ₚ 3) +ₚ c 8) +ₚ
    (c 3 *ₚ (c 10 *ₚ hn +ₚ c 4 +ₚ c 1) +ₚ c 3 +ₚ
      c 9 *ₚ (c 3600 *ₚ (c 9 *ₚ (hG +ₚ c 1) +ₚ c 2) ^ₚ 3 +ₚ c 1) +ₚ c 5) +ₚ hPublic +ₚ c 7
  have hQuery := binaryScalarQueryWorkBound_polynomial standaloneShapeSize_pos
    hn hm hB hm hB hB hb ha hExp
  have hCopies := c 2 *ₚ ha +ₚ c 1
  have hCoordinates := c 3 *ₚ hn +ₚ c 2
  have hStorage := c 540 *ₚ hR4 +ₚ hCopies *ₚ hExp *ₚ
    (c 15 +ₚ c 5 *ₚ (hCoordinates *ₚ (c 5 *ₚ hb +ₚ c 10) +ₚ c 30))
  have hBits := c 5 *ₚ hCopies *ₚ hExp *ₚ (hCoordinates *ₚ hb)
  exact hPlan +ₚ hQuery +ₚ c 3 +ₚ hStorage +ₚ hBits

theorem standaloneBinaryTotalWorkBound_polynomial :
    ∃ C d : ℕ, ∀ n m B b r a : ℕ,
      standaloneBinaryTotalWorkBound n m B b r a≤C*(n+m+B+b+16^r+a+2)^d := by
  obtain ⟨C,d,h⟩ := standaloneShape_polynomial
  exact ⟨C,d,fun n m B b r a => h ⟨n,m,B,b,r,a⟩⟩

abbrev StandaloneRawBits (n : ℕ) (q : BinaryPublicSearchResult) :=
  Fin (multilevelBankSlots (2*q.halfCopies+1) q.level) → Fin (3*n+2) → Fin q.precision → Bool

noncomputable def standaloneRawBitLaw (n : ℕ) (q : BinaryPublicSearchResult) :
    Measure (StandaloneRawBits n q) :=
  Measure.pi fun _ => Measure.pi fun _ => fairBitVectorLaw q.precision

def standaloneSeedFromBits (n : ℕ) (q : BinaryPublicSearchResult)
    (bits : StandaloneRawBits n q) : StandaloneBinarySeed n q :=
  (plannerFairBankFromBitTape n q.precision (2*q.halfCopies+1) q.level bits) (Fin.last q.level)

theorem measurePreserving_standaloneSeedFromBits (n : ℕ) (q : BinaryPublicSearchResult) :
    MeasurePreserving (standaloneSeedFromBits n q) (standaloneRawBitLaw n q) (standaloneBinarySeedLaw n q) :=
  (measurePreserving_eval (fun r : Fin (q.level+1) =>
    Measure.pi fun _ : Fin (2*q.halfCopies+1) =>
      multilevelTreeLaw (plannerFairSeedLaw n q.precision) r.val) (Fin.last q.level)).comp
        (measurePreserving_plannerFairBankFromBitTape n q.precision (2*q.halfCopies+1) q.level)

/-- Copy the primitive bits into direct-access arrays, then use the
counted tape layout to read the selected tree block. -/
def countedStandaloneRawSeed (n : ℕ) (q : BinaryPublicSearchResult)
    (bits : StandaloneRawBits n q) : StandaloneBinarySeed n q × ℕ :=
  let raw := Vector.ofFn (fun i => Vector.ofFn (fun j => Vector.ofFn (bits i j)))
  let read := fun i => plannerSeedFromCoordinates n (fun j => ((raw.get i).get j).get)
  let bank := countedMultilevelBankFromTape (2*q.halfCopies+1) q.level read
  let size := countedMultilevelBankSize (2*q.halfCopies+1) q.level
  (bank.1 ⟨q.level,Nat.lt_succ_self _⟩,
    bank.2+size.2+size.1*(plannerFairSeedStorageWork n q.precision+3)+10+
      size.1*((3*n+2)*q.precision))

lemma countedStandaloneRawSeed_value (n : ℕ) (q : BinaryPublicSearchResult)
    (bits : StandaloneRawBits n q) :
    (countedStandaloneRawSeed n q bits).1=standaloneSeedFromBits n q bits := by
  have h (i) (j) : (Vector.ofFn (bits i j)).get = bits i j :=
    funext (calibrationVectorGet_ofFn (bits i j))
  simp only [countedStandaloneRawSeed,standaloneSeedFromBits,plannerFairBankFromBitTape,
    calibrationVectorGet_ofFn,Fin.last,h]

lemma countedStandaloneRawSeed_work (n : ℕ) (q : BinaryPublicSearchResult)
    (bits : StandaloneRawBits n q) :
    (countedStandaloneRawSeed n q bits).2≤
      fairQueryBankWorkBound n q.precision (2*q.halfCopies+1) q.level+
        5*(2*q.halfCopies+1)*16^q.level*((3*n+2)*q.precision) := by
  let C := 2*q.halfCopies+1
  let R := q.level
  let B := plannerFairSeedStorageWork n q.precision
  let D := (3*n+2)*q.precision
  let s := countedMultilevelBankSize C R
  let raw := Vector.ofFn (fun i => Vector.ofFn (fun j => Vector.ofFn (bits i j)))
  let read := fun i => plannerSeedFromCoordinates n (fun j => ((raw.get i).get j).get)
  let bank := countedMultilevelBankFromTape C R read
  have hBank : bank.2≤360*(R+1)^4 := countedMultilevelBankFromTape_work C R read
  have hSize : s.2≤80*(R+1)^2 := countedMultilevelBankSize_work C R
  have hSlots : s.1≤5*C*16^R := (countedMultilevelBankSize_value C R).le.trans (multilevelBankSlots_le C R)
  have hR : 360*(R+1)^4+80*(R+1)^2+10≤540*(R+1)^4 := by
    nlinarith [Nat.zero_le (R^4),Nat.zero_le (R^3),Nat.zero_le (R^2)]
  have hb := Nat.mul_le_mul_right (B+3) hSlots
  have hd := Nat.mul_le_mul_right D hSlots
  change bank.2+s.2+s.1*(B+3)+10+s.1*D≤540*(R+1)^4+C*16^R*(15+5*B)+5*C*16^R*D
  rw [show C*16^R*(15+5*B)=(5*C*16^R)*(B+3) by ring]
  omega

def countedBinaryStandaloneFromBits {n : ℕ} (rows : Vector (List BinaryRational) n)
    (x : ScalarPlannerListState n BinaryRational) (h p : BinaryRational)
    (bits : StandaloneRawBits n (countedBinaryStandalonePlan rows x h p)) :
    MedianCopiesResult BinaryRational :=
  let q := countedBinaryStandalonePlan rows x h p
  let tape := countedStandaloneRawSeed n q bits
  let out := countedBinaryScalarQueryAtLevel rows x q.precision q.level q.halfCopies tape.1
  {out with work:=q.work+out.work+3+tape.2}

lemma countedBinaryStandaloneFromBits_value {n : ℕ} (rows : Vector (List BinaryRational) n)
    (x : ScalarPlannerListState n BinaryRational) (h p : BinaryRational)
    (bits : StandaloneRawBits n (countedBinaryStandalonePlan rows x h p)) :
    (countedBinaryStandaloneFromBits rows x h p bits).value=
      (countedBinaryStandaloneQuery rows x h p
        (standaloneSeedFromBits n (countedBinaryStandalonePlan rows x h p) bits)).value := by
  simp only [countedBinaryStandaloneFromBits,countedBinaryStandaloneQuery,countedStandaloneRawSeed_value]

theorem countedBinaryStandaloneFromBits_work {n : ℕ} (rows : Vector (List BinaryRational) n)
    (x : ScalarPlannerListState n BinaryRational) (h p : BinaryRational) (m B : ℕ) (hB : 2≤B)
    (hRows : ∀ i, (rows.get i).length≤m) (hy : ∀ i y, y∈rows.get i → RationalHeight y.value B)
    (hx : x.1.Nodup) (hu : RationalHeight x.2.1.value B) (hz : RationalHeight x.2.2.value B)
    (hh : RationalHeight h.value B) (hp : RationalHeight p.value B)
    (bits : StandaloneRawBits n (countedBinaryStandalonePlan rows x h p)) :
    let q := countedBinaryStandalonePlan rows x h p
    (countedBinaryStandaloneFromBits rows x h p bits).work≤
      standaloneBinaryTotalWorkBound n m B q.precision q.level q.halfCopies := by
  dsimp only
  let q := countedBinaryStandalonePlan rows x h p
  let tape := countedStandaloneRawSeed n q bits
  have ht := countedStandaloneRawSeed_work n q bits
  have hQ := countedBinaryStandaloneQuery_work rows x h p m B hB hRows hy hx hu hz hh hp tape.1
  dsimp only at hQ
  change (countedBinaryStandaloneQuery rows x h p tape.1).work+tape.2≤_
  unfold standaloneBinaryTotalWorkBound
  exact (Nat.add_le_add hQ ht).trans_eq (Nat.add_assoc _ _ _).symm

universe v
variable {n : ℕ}

def sampleStandaloneSeedM {M : Type → Type v} [Monad M] (n : ℕ)
    (q : BinaryPublicSearchResult) (draw : M Bool) : M (StandaloneBinarySeed n q × ℕ) := do
  let bank ← sampleCountedPlannerFairBankM n q.precision (2*q.halfCopies+1) q.level draw
  pure (bank.1 ⟨q.level,Nat.lt_succ_self _⟩,bank.2)

def sampleBinaryStandaloneQueryM {M : Type → Type v} [Monad M] (rows : Vector (List BinaryRational) n)
    (x : ScalarPlannerListState n BinaryRational) (h p : BinaryRational) (draw : M Bool) :
    M (MedianCopiesResult BinaryRational) := do
  let q := countedBinaryStandalonePlan rows x h p
  let bank ← sampleStandaloneSeedM n q draw
  let out := countedBinaryScalarQueryAtLevel rows x q.precision q.level q.halfCopies bank.1
  pure {out with work:=q.work+out.work+3+bank.2}

private lemma standaloneCounter_bind {A B : Type} (x : StateM ℕ A) (f : A → StateM ℕ B) (c : ℕ) :
    (x >>= f).run c = (f (x.run c).1).run (x.run c).2 := by
  change (let (a,s) := x.run c; (f a).run s) = _
  cases x.run c
  rfl

private lemma standaloneCounter_pure {A : Type} (x : A) (c : ℕ) :
    (pure x : StateM ℕ A).run c = (x,c) := rfl

private theorem sampleStandaloneSeedM_counter (n : ℕ) (q : BinaryPublicSearchResult)
    (draw : StateM ℕ Bool) (hDraw : ∀ c, (draw.run c).2=c+1) (c : ℕ) :
    ((sampleStandaloneSeedM n q draw).run c).2 =
      c+multilevelBankSlots (2*q.halfCopies+1) q.level*((3*n+2)*q.precision) := by
  simp only [sampleStandaloneSeedM,standaloneCounter_bind,standaloneCounter_pure,
    sampleCountedPlannerFairBankM_counter _ _ _ _ draw hDraw]

private theorem sampleStandaloneSeedM_work (n : ℕ) (q : BinaryPublicSearchResult)
    (draw : StateM ℕ Bool) (c : ℕ) :
    ((sampleStandaloneSeedM n q draw).run c).1.2 ≤
      fairQueryBankWorkBound n q.precision (2*q.halfCopies+1) q.level := by
  simp only [sampleStandaloneSeedM,standaloneCounter_bind,standaloneCounter_pure]
  exact sampleCountedPlannerFairBankM_work n q.precision (2*q.halfCopies+1) q.level draw c

theorem sampleBinaryStandaloneQueryM_counter (rows : Vector (List BinaryRational) n)
    (x : ScalarPlannerListState n BinaryRational) (h p : BinaryRational) (draw : StateM ℕ Bool)
    (hDraw : ∀ c, (draw.run c).2=c+1) (c : ℕ) :
    let q := countedBinaryStandalonePlan rows x h p
    ((sampleBinaryStandaloneQueryM rows x h p draw).run c).2 =
      c+multilevelBankSlots (2*q.halfCopies+1) q.level*((3*n+2)*q.precision) := by
  dsimp only
  simp only [sampleBinaryStandaloneQueryM,standaloneCounter_bind,standaloneCounter_pure,
    sampleStandaloneSeedM_counter n _ draw hDraw]

theorem sampleBinaryStandaloneQueryM_work (rows : Vector (List BinaryRational) n)
    (x : ScalarPlannerListState n BinaryRational) (h p : BinaryRational) (m B : ℕ) (hB : 2≤B)
    (hRows : ∀ i, (rows.get i).length≤m) (hy : ∀ i y, y∈rows.get i → RationalHeight y.value B)
    (hx : x.1.Nodup) (hu : RationalHeight x.2.1.value B) (hz : RationalHeight x.2.2.value B)
    (hh : RationalHeight h.value B) (hp : RationalHeight p.value B) (draw : StateM ℕ Bool)
    (hDraw : ∀ c, (draw.run c).2=c+1) (c : ℕ) :
    let q := countedBinaryStandalonePlan rows x h p
    let run := (sampleBinaryStandaloneQueryM rows x h p draw).run c
    run.1.work+(run.2-c)≤standaloneBinaryTotalWorkBound n m B q.precision q.level q.halfCopies := by
  dsimp only
  let q := countedBinaryStandalonePlan rows x h p
  let bank := (sampleStandaloneSeedM n q draw).run c
  let seed := bank.1.1
  have hQ := countedBinaryStandaloneQuery_work rows x h p m B hB hRows hy hx hu hz hh hp seed
  dsimp only at hQ
  have hBank := sampleStandaloneSeedM_work n q draw c
  have hBits : multilevelBankSlots (2*q.halfCopies+1) q.level*((3*n+2)*q.precision)≤
      5*(2*q.halfCopies+1)*16^q.level*((3*n+2)*q.precision) :=
    Nat.mul_le_mul_right _ (multilevelBankSlots_le _ _)
  rw [sampleBinaryStandaloneQueryM_counter rows x h p draw hDraw c]
  simp only [sampleBinaryStandaloneQueryM,standaloneCounter_bind,standaloneCounter_pure,
    Nat.add_sub_cancel_left]
  change (countedBinaryStandaloneQuery rows x h p seed).work+bank.1.2+
    multilevelBankSlots (2*q.halfCopies+1) q.level*((3*n+2)*q.precision)≤_
  exact Nat.add_le_add (Nat.add_le_add hQ hBank) hBits

end ProphetSecretary.Statistics
