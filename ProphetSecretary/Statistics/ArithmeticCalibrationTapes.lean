import ProphetSecretary.Statistics.CalibrationQueryTapes
import ProphetSecretary.Statistics.ScalarPlannerWorkData

/-!
# Arithmetic query tapes

An arithmetic transition consumes two scalar uniforms and three vectors
of uniforms. The target and continuation tapes use separate allocations.
-/

open MeasureTheory
open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Model

abbrev ArithmeticSeedBank (n C R : ℕ) (K : Type) := MultilevelSeedBank (PlannerFieldSeed n K) C R

universe v

private lemma arithmeticTapeCounter_bind {A B : Type} (x : StateM ℕ A) (f : A → StateM ℕ B) (c : ℕ) :
    (x >>= f).run c = (f (x.run c).1).run (x.run c).2 := by
  change (let (a,s) := x.run c; (f a).run s) = _
  cases x.run c
  rfl

private lemma arithmeticTapeCounter_pure {A : Type} (x : A) (c : ℕ) :
    (pure x : StateM ℕ A).run c = (x,c) := rfl

lemma plannerFullSeedM_counter {K : Type} (n : ℕ) (uniform : StateM ℕ K)
    (h : ∀ c, (uniform.run c).2 = c+1) (c : ℕ) :
    ((plannerFullSeedM n uniform).run c).2 = c+3*n+2 := by
  simp only [plannerFullSeedM, arithmeticTapeCounter_bind, arithmeticTapeCounter_pure, h,
    uniformVectorM_counter _ 1 h,Nat.mul_one]
  omega

def arithmeticTransitionSeedWork (n : ℕ) : ℕ := 20*(n+1)+3*n+2

def sampleArithmeticPlannerBankM {M : Type → Type v} [Monad M] {K : Type}
    (n C R : ℕ) (uniform : M K) : M (ArithmeticSeedBank n C R K × ℕ) := do
  let bank ← sampleCountedMultilevelSeedBankM C R (plannerFullSeedM n uniform)
  let size := countedMultilevelBankSize C R
  pure (bank.1,bank.2+size.2+size.1*arithmeticTransitionSeedWork n+5)

def arithmeticPlannerBankAllocationBound (n C R : ℕ) : ℕ :=
  540*(R+1)^4+C*16^R*(15+5*arithmeticTransitionSeedWork n)

lemma sampleArithmeticPlannerBankM_counter {K : Type} (n C R : ℕ) (uniform : StateM ℕ K)
    (h : ∀ c, (uniform.run c).2 = c+1) (c : ℕ) :
    ((sampleArithmeticPlannerBankM n C R uniform).run c).2 =
      c+multilevelBankSlots C R*(3*n+2) := by
  have h' (c : ℕ) : ((plannerFullSeedM n uniform).run c).2 = c+(3*n+2) := by
    rw [plannerFullSeedM_counter n uniform h]
    omega
  simp only [sampleArithmeticPlannerBankM, arithmeticTapeCounter_bind, arithmeticTapeCounter_pure,
    sampleCountedMultilevelSeedBankM_counter _ _ h']

lemma sampleArithmeticPlannerBankM_work {K : Type} (n C R : ℕ) (uniform : StateM ℕ K) (c : ℕ) :
    ((sampleArithmeticPlannerBankM n C R uniform).run c).1.2 ≤ arithmeticPlannerBankAllocationBound n C R := by
  let B := arithmeticTransitionSeedWork n
  let size := countedMultilevelBankSize C R
  let q := ((sampleCountedMultilevelSeedBankM C R (plannerFullSeedM n uniform)).run c).1
  have hq : q.2 ≤ 450*(R+1)^4+15*C*16^R :=
    sampleCountedMultilevelSeedBankM_work (plannerFullSeedM n uniform) C R c
  have hs : size.2≤80*(R+1)^2 := countedMultilevelBankSize_work C R
  have hN : size.1*B≤(5*C*16^R)*B := Nat.mul_le_mul_right _ (by
    rw [countedMultilevelBankSize_value]; exact multilevelBankSlots_le C R)
  have hr : 450*(R+1)^4+80*(R+1)^2+5≤540*(R+1)^4 := by
    nlinarith [Nat.zero_le (R^4),Nat.zero_le (R^3),Nat.zero_le (R^2)]
  simp only [sampleArithmeticPlannerBankM,arithmeticTapeCounter_bind,arithmeticTapeCounter_pure]
  change q.2+size.2+size.1*B+5≤540*(R+1)^4+C*16^R*(15+5*B)
  rw [show C*16^R*(15+5*B)=15*C*16^R+(5*C*16^R)*B by ring]
  omega

def arithmeticContinuationTapeCount (n m J : ℕ) : ℕ := (m+1)*(n*(J+1))

private def arithmeticContinuationTapeIndex {n m J : ℕ} (l : Fin (m+1))
    (i : Fin n × Fin (J+1)) : Fin (arithmeticContinuationTapeCount n m J) :=
  finProdFinEquiv (l,finProdFinEquiv i)

/-- The two dense arrays store one bank per target and continuation slot.
A validation or online query reads its bank by direct arithmetic index. -/
def sampleArithmeticCalibrationQueryTapesM {M : Type → Type v} [Monad M] {K : Type}
    (n m J CT RT CP RP : ℕ) (uniform : M K) :
    M (CalibrationQueryArrays n m J (ArithmeticSeedBank n CT RT K) (ArithmeticSeedBank n CP RP K) × ℕ) := do
  let T := 4*m+1
  let P := arithmeticContinuationTapeCount n m J
  let target ← Vector.ofFnM (fun _ : Fin T => sampleArithmeticPlannerBankM n CT RT uniform)
  let policy ← Vector.ofFnM (fun _ : Fin P => sampleArithmeticPlannerBankM n CP RP uniform)
  let seeds := (fun i => (target.get i).1,
    (fun l i => (policy.get (arithmeticContinuationTapeIndex l.castSucc i)).1,
      fun i => (policy.get (arithmeticContinuationTapeIndex (Fin.last m) i)).1))
  pure (seeds,(∑ i : Fin T, (target.get i).2)+(∑ i : Fin P, (policy.get i).2)+10*(T+P+1)+6)

theorem sampleArithmeticCalibrationQueryTapesM_counter {K : Type} (n m J CT RT CP RP : ℕ)
    (uniform : StateM ℕ K) (h : ∀ c, (uniform.run c).2 = c+1) (c : ℕ) :
    ((sampleArithmeticCalibrationQueryTapesM n m J CT RT CP RP uniform).run c).2 =
      c+(4*m+1)*(multilevelBankSlots CT RT*(3*n+2))+
        arithmeticContinuationTapeCount n m J*(multilevelBankSlots CP RP*(3*n+2)) := by
  simp only [sampleArithmeticCalibrationQueryTapesM,arithmeticTapeCounter_bind,arithmeticTapeCounter_pure,
    uniformVectorM_counter _ _ (sampleArithmeticPlannerBankM_counter _ _ _ _ h)]

private lemma arithmeticTapeVector_work {A : Type} (draw : StateM ℕ (A × ℕ)) (W : ℕ)
    (h : ∀ c, (draw.run c).1.2≤W) (N c : ℕ) (i : Fin N) :
    (((Vector.ofFnM (fun _ : Fin N => draw)).run c).1.get i).2≤W := by
  induction N generalizing c with
  | zero => exact i.elim0
  | succ N ih =>
    rw [Vector.ofFnM_succ,arithmeticTapeCounter_bind,arithmeticTapeCounter_bind,arithmeticTapeCounter_pure]
    let w := (Vector.ofFnM (fun _ : Fin N => draw)).run c
    let a := (draw.run w.2).1
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change ((w.1.push a)[N]).2≤W
      rw [Vector.getElem_push_eq]
      exact h w.2
    · change ((w.1.push a)[j.val]).2≤W
      rw [Vector.getElem_push_lt j.isLt]
      exact ih c j

theorem sampleArithmeticCalibrationQueryTapesM_work {K : Type} (n m J CT RT CP RP : ℕ)
    (uniform : StateM ℕ K) (c : ℕ) :
    ((sampleArithmeticCalibrationQueryTapesM n m J CT RT CP RP uniform).run c).1.2 ≤
      (4*m+1)*arithmeticPlannerBankAllocationBound n CT RT +
        arithmeticContinuationTapeCount n m J*arithmeticPlannerBankAllocationBound n CP RP +
          10*((4*m+1)+arithmeticContinuationTapeCount n m J+1)+6 := by
  let T := 4*m+1
  let P := arithmeticContinuationTapeCount n m J
  let WT := arithmeticPlannerBankAllocationBound n CT RT
  let WP := arithmeticPlannerBankAllocationBound n CP RP
  let f := sampleArithmeticPlannerBankM n CT RT uniform
  let g := sampleArithmeticPlannerBankM n CP RP uniform
  let tf := (Vector.ofFnM (fun _ : Fin T => f)).run c
  let pg := (Vector.ofFnM (fun _ : Fin P => g)).run tf.2
  have ht : ∑ i : Fin T, (tf.1.get i).2≤T*WT := by
    calc
      _ ≤ ∑ _i : Fin T, WT := Finset.sum_le_sum fun i _ =>
        arithmeticTapeVector_work f WT (sampleArithmeticPlannerBankM_work _ _ _ _) T c i
      _ = _ := by simp
  have hp : ∑ i : Fin P, (pg.1.get i).2≤P*WP := by
    calc
      _ ≤ ∑ _i : Fin P, WP := Finset.sum_le_sum fun i _ =>
        arithmeticTapeVector_work g WP (sampleArithmeticPlannerBankM_work _ _ _ _) P tf.2 i
      _ = _ := by simp
  simp only [sampleArithmeticCalibrationQueryTapesM,arithmeticTapeCounter_bind,arithmeticTapeCounter_pure]
  change (∑ i : Fin T, (tf.1.get i).2)+(∑ i : Fin P, (pg.1.get i).2)+10*(T+P+1)+6≤
    T*WT+P*WP+10*(T+P+1)+6
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add ht hp) _) _

lemma arithmeticPlannerBankAllocationBound_le (n C R : ℕ) :
    arithmeticPlannerBankAllocationBound n C R ≤
      12*(450*(R+1)^4+15*C*16^R+5*C*16^R*(3*n+2)) := by
  have hn : arithmeticTransitionSeedWork n≤11*(3*n+2) := by
    unfold arithmeticTransitionSeedWork
    omega
  have hW : 5*C*16^R*arithmeticTransitionSeedWork n≤11*(5*C*16^R*(3*n+2)) := by
    calc
      _ ≤ (5*C*16^R)*(11*(3*n+2)) := Nat.mul_le_mul_left _ hn
      _ = _ := by ring
  unfold arithmeticPlannerBankAllocationBound
  rw [show C*16^R*(15+5*arithmeticTransitionSeedWork n) =
    15*C*16^R+5*C*16^R*arithmeticTransitionSeedWork n by ring]
  omega

abbrev ArithmeticPlannerUniformTape (n C R : ℕ) :=
  Fin (multilevelBankSlots C R) → Fin (3*n+2) → ℝ

def arithmeticPlannerBankFromUniformTape (n C R : ℕ) (t : ArithmeticPlannerUniformTape n C R) :
    ArithmeticSeedBank n C R ℝ :=
  (countedMultilevelBankFromTape C R (fun i => plannerSeedFromCoordinates n (t i))).1

theorem measurePreserving_arithmeticPlannerBankFromUniformTape (n C R : ℕ) :
    MeasurePreserving (arithmeticPlannerBankFromUniformTape n C R)
      (Measure.pi (fun _ : Fin (multilevelBankSlots C R) =>
        Measure.pi (fun _ : Fin (3*n+2) => Instance.uniformClock)))
      (Measure.pi (fun l : Fin (R+1) => Measure.pi (fun _ : Fin C =>
        multilevelTreeLaw (plannerUniformSeedLaw n) l.val))) :=
  (measurePreserving_countedMultilevelBankFromTape (plannerUniformSeedLaw n) C R).comp
    (measurePreserving_pi _ _ (fun _ : Fin (multilevelBankSlots C R) =>
      measurePreserving_plannerSeedFromCoordinates Instance.uniformClock n))

end ProphetSecretary.Statistics.Calibration
