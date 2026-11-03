import ProphetSecretary.Statistics.PlannerFairSeed
import ProphetSecretary.Analysis.MultilevelTapeLayout

/-!
# Fair-bit arrays for the scalar planner

The primitive tape uses one disjoint block of bits for each sampler
coordinate and one disjoint coordinate array for each transition.
-/

open MeasureTheory
open scoped BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability

abbrev PlannerSeedCoordinate (n : ℕ) := (Fin 1 ⊕ Fin n) ⊕ (Fin 1 ⊕ (Fin n ⊕ Fin n))

def plannerSeedCoordinateEquiv (n : ℕ) : PlannerSeedCoordinate n ≃ Fin (3*n+2) :=
  (finSumFinEquiv.sumCongr ((Equiv.refl (Fin 1)).sumCongr finSumFinEquiv |>.trans finSumFinEquiv)
    |>.trans finSumFinEquiv).trans (finCongr (by omega))

def plannerSeedFromCoordinates {K : Type*} (n : ℕ) (tape : Fin (3*n+2) → K) :
    PlannerFieldSeed n K :=
  let read := fun i => tape (plannerSeedCoordinateEquiv n i)
  ((read (.inl (.inl 0)), fun i => read (.inl (.inr i))),
    (read (.inr (.inl 0)), (fun i => read (.inr (.inr (.inl i))),
      fun i => read (.inr (.inr (.inr i))))))

private lemma splitSeedCoordinates {A B K : Type*} [Fintype A] [Fintype B] [MeasurableSpace K]
    (μ : Measure K) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun (x : A ⊕ B → K) => (fun a => x (.inl a), fun b => x (.inr b)))
      (Measure.pi (fun _ : A ⊕ B => μ))
      ((Measure.pi (fun _ : A => μ)).prod (Measure.pi (fun _ : B => μ))) :=
  measurePreserving_sumPiEquivProdPi (fun _ : A ⊕ B => μ)

theorem measurePreserving_plannerSeedFromCoordinates {K : Type*} [MeasurableSpace K]
    (μ : Measure K) [IsProbabilityMeasure μ] (n : ℕ) :
    MeasurePreserving (plannerSeedFromCoordinates n)
      (Measure.pi (fun _ : Fin (3*n+2) => μ)) (plannerSeedProduct n μ) := by
  have h1 : MeasurePreserving (fun (x : Fin 1 → K) => x 0)
      (Measure.pi (fun _ : Fin 1 => μ)) μ :=
    measurePreserving_piUnique (fun _ : Fin 1 => μ)
  have hn := MeasurePreserving.id (Measure.pi (fun _ : Fin n => μ))
  have hleft := (h1.prod hn).comp (splitSeedCoordinates (A := Fin 1) (B := Fin n) μ)
  have hright := (h1.prod (splitSeedCoordinates (A := Fin n) (B := Fin n) μ)).comp
    (splitSeedCoordinates (A := Fin 1) (B := Fin n ⊕ Fin n) μ)
  exact ((hleft.prod hright).comp (splitSeedCoordinates
    (A := Fin 1 ⊕ Fin n) (B := Fin 1 ⊕ (Fin n ⊕ Fin n)) μ)).comp
    ((measurePreserving_piCongrLeft (fun _ : Fin (3*n+2) => μ) (plannerSeedCoordinateEquiv n)).symm)

def plannerFairBankFromBitTape (n b C R : ℕ)
    (bits : Fin (multilevelBankSlots C R) → Fin (3*n+2) → Fin b → Bool) :
    MultilevelSeedBank (PlannerFairSeed n b) C R :=
  (countedMultilevelBankFromTape C R (fun i => plannerSeedFromCoordinates n (bits i))).1

/-- Independent input bits give the exact product law of the bank
used by the finite precision planner. -/
theorem measurePreserving_plannerFairBankFromBitTape (n b C R : ℕ) :
    MeasurePreserving (plannerFairBankFromBitTape n b C R)
      (Measure.pi (fun _ : Fin (multilevelBankSlots C R) =>
        Measure.pi (fun _ : Fin (3*n+2) => fairBitVectorLaw b)))
      (Measure.pi (fun l : Fin (R+1) => Measure.pi
        (fun _ : Fin C => multilevelTreeLaw (plannerFairSeedLaw n b) l.val))) :=
  (measurePreserving_countedMultilevelBankFromTape (plannerFairSeedLaw n b) C R).comp
    (measurePreserving_pi _ _ (fun _ : Fin (multilevelBankSlots C R) =>
      measurePreserving_plannerSeedFromCoordinates (fairBitVectorLaw b) n))

universe u v

def samplePlannerFairSeedM {M : Type → Type v} [Monad M]
    (n b : ℕ) (drawBit : M Bool) : M (PlannerFairSeed n b) := do
  let tape ← Vector.ofFnM (fun _ : Fin (3*n+2) => Vector.ofFnM (fun _ : Fin b => drawBit))
  pure (plannerSeedFromCoordinates n (fun i => (tape.get i).get))

private lemma plannerCounter_bind {A B : Type} (x : StateM ℕ A) (f : A → StateM ℕ B) (c : ℕ) :
    (x >>= f).run c = (f (x.run c).1).run (x.run c).2 := by
  change (let (a,s) := x.run c; (f a).run s) = _
  cases x.run c
  rfl

private lemma plannerCounter_pure {A : Type} (x : A) (c : ℕ) :
    (pure x : StateM ℕ A).run c = (x,c) := rfl

lemma samplePlannerFairSeedM_counter (n b : ℕ) (drawBit : StateM ℕ Bool)
    (h : ∀ c, (drawBit.run c).2 = c+1) (c : ℕ) :
    ((samplePlannerFairSeedM n b drawBit).run c).2 = c+(3*n+2)*b := by
  have hOne (c : ℕ) : ((Vector.ofFnM (fun _ : Fin b => drawBit)).run c).2 = c+b := by
    simpa only [Nat.mul_one] using uniformVectorM_counter drawBit 1 h b c
  simp only [samplePlannerFairSeedM, plannerCounter_bind, plannerCounter_pure,
    uniformVectorM_counter _ b hOne]

def samplePlannerFairBankM {M : Type → Type v} [Monad M]
    (n b C R : ℕ) (drawBit : M Bool) : M (MultilevelSeedBank (PlannerFairSeed n b) C R × ℕ) :=
  sampleCountedMultilevelSeedBankM C R (samplePlannerFairSeedM n b drawBit)

theorem samplePlannerFairBankM_counter (n b C R : ℕ) (drawBit : StateM ℕ Bool)
    (h : ∀ c, (drawBit.run c).2 = c+1) (c : ℕ) :
    ((samplePlannerFairBankM n b C R drawBit).run c).2 =
      c + multilevelBankSlots C R * ((3*n+2)*b) :=
  sampleCountedMultilevelSeedBankM_counter _ _ (samplePlannerFairSeedM_counter n b drawBit h) C R c

theorem samplePlannerFairBankM_counter_le (n b C R : ℕ) (drawBit : StateM ℕ Bool)
    (h : ∀ c, (drawBit.run c).2 = c+1) (c : ℕ) :
    ((samplePlannerFairBankM n b C R drawBit).run c).2 ≤
      c + 5*C*16^R * ((3*n+2)*b) := by
  rw [samplePlannerFairBankM_counter n b C R drawBit h]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (multilevelBankSlots_le C R)) c

/-- Loop, array, and index work for allocating the coordinate tape of a
single transition. The draws themselves are counted separately. -/
def plannerFairSeedStorageWork (n b : ℕ) : ℕ := (3*n+2)*(5*b+10)+30

def sampleCountedPlannerFairBankM {M : Type → Type v} [Monad M]
    (n b C R : ℕ) (drawBit : M Bool) : M (MultilevelSeedBank (PlannerFairSeed n b) C R × ℕ) := do
  let bank ← samplePlannerFairBankM n b C R drawBit
  let size := countedMultilevelBankSize C R
  pure (bank.1, bank.2+size.2+size.1*plannerFairSeedStorageWork n b+5)

theorem sampleCountedPlannerFairBankM_counter (n b C R : ℕ) (drawBit : StateM ℕ Bool)
    (h : ∀ c, (drawBit.run c).2 = c+1) (c : ℕ) :
    ((sampleCountedPlannerFairBankM n b C R drawBit).run c).2 =
      c + multilevelBankSlots C R * ((3*n+2)*b) := by
  simp only [sampleCountedPlannerFairBankM, plannerCounter_bind, plannerCounter_pure,
    samplePlannerFairBankM_counter n b C R drawBit h]

theorem sampleCountedPlannerFairBankM_work (n b C R : ℕ) (drawBit : StateM ℕ Bool) (c : ℕ) :
    ((sampleCountedPlannerFairBankM n b C R drawBit).run c).1.2 ≤
      540*(R+1)^4 + C*16^R*(15+5*plannerFairSeedStorageWork n b) := by
  let B := plannerFairSeedStorageWork n b
  let s := countedMultilevelBankSize C R
  let q := ((samplePlannerFairBankM n b C R drawBit).run c).1
  have hq : q.2 ≤ 450*(R+1)^4 + 15*C*16^R :=
    sampleCountedMultilevelSeedBankM_work (samplePlannerFairSeedM n b drawBit) C R c
  have hs : s.2 ≤ 80*(R+1)^2 := countedMultilevelBankSize_work C R
  have hslots : s.1 ≤ 5*C*16^R :=
    (countedMultilevelBankSize_value C R).le.trans (multilevelBankSlots_le C R)
  have hsm : s.1*B ≤ (5*C*16^R)*B := Nat.mul_le_mul_right B hslots
  have hr : 450*(R+1)^4 + 80*(R+1)^2 + 5 ≤ 540*(R+1)^4 := by
    nlinarith [Nat.zero_le (R^4), Nat.zero_le (R^3), Nat.zero_le (R^2)]
  simp only [sampleCountedPlannerFairBankM, plannerCounter_bind, plannerCounter_pure]
  change q.2+s.2+s.1*B+5 ≤ 540*(R+1)^4 + C*16^R*(15+5*B)
  rw [show C*16^R*(15+5*B) = 15*C*16^R+(5*C*16^R)*B by ring]
  omega

end ProphetSecretary.Statistics
