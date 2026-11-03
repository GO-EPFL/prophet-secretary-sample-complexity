import ProphetSecretary.Statistics.CalibrationQueryTapes
import ProphetSecretary.Statistics.RankCalibrationBits

/-!
# Allocating randomness for the rank calibration

Every validation profile gets independent key and clock arrays. The
online run only needs its clock array because the arrival order is
exogenous. The mixture uses a separate bit vector.
-/

open MeasureTheory

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability ProphetSecretary.Model

variable {n m J : ℕ}

def mapRankCalibrationQueries {T P T' P' : Type} (b c : ℕ) (f : T → T') (g : P → P')
    (r : RankCalibrationBits n m J b c T P) : RankCalibrationBits n m J b c T' P' :=
  (fun j => f (r.1 j),
    (fun l => ((r.2.1 l).1, (r.2.1 l).2.1, fun j => g ((r.2.1 l).2.2 j)),
      (r.2.2.1, (fun j => g (r.2.2.2.1 j)), r.2.2.2.2)))

/-- Decoding query tapes leaves the keys, clocks, and mixture coin
independent of the query banks. -/
theorem measurePreserving_mapRankCalibrationQueries {T P T' P' : Type}
    [MeasurableSpace T] [MeasurableSpace P] [MeasurableSpace T'] [MeasurableSpace P']
    (b c : ℕ) {μT : Measure T} {μP : Measure P} {νT : Measure T'} {νP : Measure P'}
    [IsProbabilityMeasure μT] [IsProbabilityMeasure μP] [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
    {f : T → T'} {g : P → P'} (hf : MeasurePreserving f μT νT) (hg : MeasurePreserving g μP νP) :
    MeasurePreserving (mapRankCalibrationQueries (n := n) (m := m) (J := J) b c f g)
      (rankCalibrationBitsLaw b c μT μP) (rankCalibrationBitsLaw b c νT νP) := by
  have hT := measurePreserving_pi _ _ (fun _ : TargetGrid m => hf)
  have hP := measurePreserving_pi _ _ (fun _ : Fin n × Fin (J+1) => hg)
  have hK := MeasurePreserving.id (rankCalibrationClockBitsLaw n b)
  have hC := MeasurePreserving.id (fairBitVectorLaw c)
  have hV := measurePreserving_pi _ _ (fun _ : Fin m => hK.prod (hK.prod hP))
  exact hT.prod (hV.prod (hK.prod (hP.prod hC)))

universe v

def sampleRankClockBitsM {M : Type → Type v} [Monad M] (n b : ℕ) (drawBit : M Bool) :
    M (RankCalibrationClockBits n b) := do
  let bits ← Vector.ofFnM (fun _ : Fin n => Vector.ofFnM (fun _ : Fin b => drawBit))
  pure (fun i => (bits.get i).get)

private lemma rankCounter_bind {A B : Type} (x : StateM ℕ A) (f : A → StateM ℕ B) (c : ℕ) :
    (x >>= f).run c = (f (x.run c).1).run (x.run c).2 := by
  change (let (a,s) := x.run c; (f a).run s) = _
  cases x.run c
  rfl

private lemma rankCounter_pure {A : Type} (x : A) (c : ℕ) :
    (pure x : StateM ℕ A).run c = (x,c) := rfl

lemma sampleRankClockBitsM_counter (n b : ℕ) (drawBit : StateM ℕ Bool)
    (h : ∀ c, (drawBit.run c).2 = c+1) (c : ℕ) :
    ((sampleRankClockBitsM n b drawBit).run c).2 = c+n*b := by
  have hb (a : ℕ) : ((Vector.ofFnM (fun _ : Fin b => drawBit)).run a).2 = a+b := by
    simpa only [Nat.mul_one] using uniformVectorM_counter drawBit 1 h b a
  simp only [sampleRankClockBitsM, rankCounter_bind, rankCounter_pure, uniformVectorM_counter _ b hb]

private def sampleRankValidationClocksM {M : Type → Type v} [Monad M]
    (n b : ℕ) (drawBit : M Bool) : M (RankCalibrationClockBits n b × RankCalibrationClockBits n b) := do
  let keys ← sampleRankClockBitsM n b drawBit
  let clocks ← sampleRankClockBitsM n b drawBit
  pure (keys,clocks)

private lemma sampleRankValidationClocksM_counter (n b : ℕ) (drawBit : StateM ℕ Bool)
    (h : ∀ c, (drawBit.run c).2 = c+1) (c : ℕ) :
    ((sampleRankValidationClocksM n b drawBit).run c).2 = c+2*n*b := by
  simp only [sampleRankValidationClocksM, rankCounter_bind, rankCounter_pure,
    sampleRankClockBitsM_counter n b drawBit h]
  ring

def rankClockBitStorageWork (n b : ℕ) : ℕ := n*(5*b+10)+5

def rankAuxiliaryBitStorageWork (n m b c : ℕ) : ℕ :=
  (2*m+1)*rankClockBitStorageWork n b + 10*(m+1) + 5*c+15

def sampleRankCalibrationAuxBitsM {M : Type → Type v} [Monad M] {T P : Type}
    (b c : ℕ) (q : CalibrationQueryArrays n m J T P) (drawBit : M Bool) :
    M (RankCalibrationBits n m J b c T P × ℕ) := do
  let validation ← Vector.ofFnM (fun _ : Fin m => sampleRankValidationClocksM n b drawBit)
  let online ← sampleRankClockBitsM n b drawBit
  let coin ← Vector.ofFnM (fun _ : Fin c => drawBit)
  let seed := (q.1, (fun l =>
    let v := validation.get l
    (v.1,v.2,q.2.1 l)), (online,q.2.2,coin.get))
  pure (seed,rankAuxiliaryBitStorageWork n m b c)

theorem sampleRankCalibrationAuxBitsM_counter {T P : Type}
    (b c : ℕ) (q : CalibrationQueryArrays n m J T P) (drawBit : StateM ℕ Bool)
    (h : ∀ d, (drawBit.run d).2 = d+1) (d : ℕ) :
    ((sampleRankCalibrationAuxBitsM b c q drawBit).run d).2 = d+(2*m+1)*n*b+c := by
  simp only [sampleRankCalibrationAuxBitsM, rankCounter_bind, rankCounter_pure,
    uniformVectorM_counter _ 1 h, Nat.mul_one, sampleRankClockBitsM_counter n b drawBit h,
    uniformVectorM_counter _ (2*n*b) (sampleRankValidationClocksM_counter n b drawBit h)]
  ring

def sampleRankCalibrationBitsM {M : Type → Type v} [Monad M]
    (n m J bT CT RT bP CP RP b c : ℕ) (drawBit : M Bool) :
    M (RankCalibrationBits n m J b c (FairQueryBank n bT CT RT) (FairQueryBank n bP CP RP) × ℕ) := do
  let q ← sampleCalibrationQueryArraysM n m J bT CT RT bP CP RP drawBit
  let aux ← sampleRankCalibrationAuxBitsM b c q.1 drawBit
  pure (aux.1,q.2+aux.2+2)

/-- The training and online clock, key, and mixture draws add exactly
the displayed amount to the independent query tape budget. -/
theorem sampleRankCalibrationBitsM_counter (n m J bT CT RT bP CP RP b c : ℕ)
    (drawBit : StateM ℕ Bool) (h : ∀ d, (drawBit.run d).2 = d+1) (d : ℕ) :
    ((sampleRankCalibrationBitsM n m J bT CT RT bP CP RP b c drawBit).run d).2 =
      d + (4*m+1)*fairQueryBankBitCount n bT CT RT +
        (m+1)*n*(J+1)*fairQueryBankBitCount n bP CP RP + (2*m+1)*n*b+c := by
  simp only [sampleRankCalibrationBitsM, rankCounter_bind, rankCounter_pure,
    sampleRankCalibrationAuxBitsM_counter b c _ drawBit h,
    sampleCalibrationQueryArraysM_counter _ _ _ _ _ _ _ _ _ drawBit h]

theorem sampleRankCalibrationBitsM_work (n m J bT CT RT bP CP RP b c : ℕ)
    (drawBit : StateM ℕ Bool) (d : ℕ) :
    ((sampleRankCalibrationBitsM n m J bT CT RT bP CP RP b c drawBit).run d).1.2 ≤
      (4*m+1)*fairQueryBankWorkBound n bT CT RT +
        (m+1)*n*(J+1)*fairQueryBankWorkBound n bP CP RP +
        10*((4*m+1)+(m+1)*(n*(J+1))+m+1)+6 + rankAuxiliaryBitStorageWork n m b c+2 := by
  have h := sampleCalibrationQueryArraysM_work n m J bT CT RT bP CP RP drawBit d
  simp only [sampleRankCalibrationBitsM, rankCounter_bind, rankCounter_pure,
    sampleRankCalibrationAuxBitsM, sampleRankValidationClocksM, sampleRankClockBitsM]
  exact Nat.add_le_add_right (Nat.add_le_add_right h _) _

/-- Real arithmetic validation uses one independent clock per identity
in each profile. -/
def sampleArithmeticValidationClocksM {M : Type → Type v} [Monad M] {K : Type}
    (n m : ℕ) (uniform : M K) : M ((Fin m → Fin n → K) × ℕ) := do
  let clocks ← Vector.ofFnM (fun _ : Fin m => Vector.ofFnM (fun _ : Fin n => uniform))
  pure ((fun j => (clocks.get j).get), m*(5*n+8)+6)

theorem sampleArithmeticValidationClocksM_counter {K : Type} (n m : ℕ) (uniform : StateM ℕ K)
    (h : ∀ d, (uniform.run d).2 = d+1) (d : ℕ) :
    ((sampleArithmeticValidationClocksM n m uniform).run d).2 = d+m*n := by
  have hn (a : ℕ) : ((Vector.ofFnM (fun _ : Fin n => uniform)).run a).2 = a+n := by
    simpa only [Nat.mul_one] using uniformVectorM_counter uniform 1 h n a
  simp only [sampleArithmeticValidationClocksM, rankCounter_bind, rankCounter_pure,
    uniformVectorM_counter _ n hn]

theorem sampleArithmeticValidationClocksM_work {K : Type} (n m : ℕ) (uniform : StateM ℕ K) (d : ℕ) :
    ((sampleArithmeticValidationClocksM n m uniform).run d).1.2 = m*(5*n+8)+6 := by
  simp only [sampleArithmeticValidationClocksM, rankCounter_bind, rankCounter_pure]

end ProphetSecretary.Statistics.Calibration
