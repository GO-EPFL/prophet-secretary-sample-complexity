import ProphetSecretary.Statistics.PlannerFairTape

/-!
# Independent query tapes for calibration

Target queries, validation queries, and online queries receive separate
banks. Each group is allocated by finite loops with sizes fixed before
any training values or online observations are read.
-/

open MeasureTheory
open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability

abbrev CalibrationQueryArrays (n m J : ℕ) (T P : Type*) :=
  (Fin (4*m+1) → T) ×
    ((Fin m → (Fin n × Fin (J+1)) → P) × ((Fin n × Fin (J+1)) → P))

abbrev PlannerQueryBitTape (n b C R : ℕ) :=
  Fin (multilevelBankSlots C R) → Fin (3*n+2) → Fin b → Bool

abbrev FairQueryBank (n b C R : ℕ) := MultilevelSeedBank (PlannerFairSeed n b) C R

local instance fairQueryBankMeasurableSpace (n b C R : ℕ) : MeasurableSpace (FairQueryBank n b C R) := by
  unfold FairQueryBank MultilevelSeedBank
  infer_instance

local instance calibrationQueryArraysMeasurableSpace (n m J : ℕ) (T P : Type*)
    [MeasurableSpace T] [MeasurableSpace P] : MeasurableSpace (CalibrationQueryArrays n m J T P) := by
  unfold CalibrationQueryArrays
  infer_instance

noncomputable def plannerQueryBitTapeLaw (n b C R : ℕ) : Measure (PlannerQueryBitTape n b C R) :=
  Measure.pi fun _ => Measure.pi fun _ => fairBitVectorLaw b

instance (n b C R : ℕ) : IsProbabilityMeasure (plannerQueryBitTapeLaw n b C R) := by
  unfold plannerQueryBitTapeLaw
  infer_instance

noncomputable def fairQueryBankLaw (n b C R : ℕ) : Measure (FairQueryBank n b C R) :=
  Measure.pi fun l => Measure.pi fun _ => multilevelTreeLaw (plannerFairSeedLaw n b) l.val

instance (n b C R : ℕ) : IsProbabilityMeasure (fairQueryBankLaw n b C R) := by
  have h : MeasurePreserving (plannerFairBankFromBitTape n b C R)
      (plannerQueryBitTapeLaw n b C R) (fairQueryBankLaw n b C R) :=
    measurePreserving_plannerFairBankFromBitTape n b C R
  rw [← h.map_eq]
  exact Measure.isProbabilityMeasure_map h.measurable.aemeasurable

abbrev CalibrationQueryBitTapes (n m J bT CT RT bP CP RP : ℕ) :=
  (Fin (4*m+1) → PlannerQueryBitTape n bT CT RT) ×
    ((Fin m → Fin (n*(J+1)) → PlannerQueryBitTape n bP CP RP) ×
      (Fin (n*(J+1)) → PlannerQueryBitTape n bP CP RP))

def calibrationQueryBanksFromBitTapes (n m J bT CT RT bP CP RP : ℕ)
    (t : CalibrationQueryBitTapes n m J bT CT RT bP CP RP) :
    CalibrationQueryArrays n m J (FairQueryBank n bT CT RT) (FairQueryBank n bP CP RP) :=
  (fun i => plannerFairBankFromBitTape n bT CT RT (t.1 i),
    (fun l j => plannerFairBankFromBitTape n bP CP RP (t.2.1 l (finProdFinEquiv j)),
      fun j => plannerFairBankFromBitTape n bP CP RP (t.2.2 (finProdFinEquiv j))))

noncomputable def calibrationQueryBitTapesLaw (n m J bT CT RT bP CP RP : ℕ) :
    Measure (CalibrationQueryBitTapes n m J bT CT RT bP CP RP) :=
  let T := plannerQueryBitTapeLaw n bT CT RT
  let P := plannerQueryBitTapeLaw n bP CP RP
  (Measure.pi fun _ => T).prod ((Measure.pi fun _ => Measure.pi fun _ => P).prod (Measure.pi fun _ => P))

noncomputable def calibrationQueryArraysLaw {n m J : ℕ} {T P : Type*}
    [MeasurableSpace T] [MeasurableSpace P] (μT : Measure T) (μP : Measure P) :
    Measure (CalibrationQueryArrays n m J T P) :=
  (Measure.pi fun _ => μT).prod
    ((Measure.pi fun _ => Measure.pi fun _ => μP).prod (Measure.pi fun _ => μP))

set_option synthInstance.maxSize 512 in
/-- The separate finite arrays have the required independent laws, including
the arrays for validation profiles and the final online run. -/
theorem measurePreserving_calibrationQueryBanksFromBitTapes (n m J bT CT RT bP CP RP : ℕ) :
    MeasurePreserving (calibrationQueryBanksFromBitTapes n m J bT CT RT bP CP RP)
      (calibrationQueryBitTapesLaw n m J bT CT RT bP CP RP)
      (calibrationQueryArraysLaw (fairQueryBankLaw n bT CT RT) (fairQueryBankLaw n bP CP RP)) := by
  let P := plannerQueryBitTapeLaw n bP CP RP
  let e : Fin n × Fin (J+1) ≃ Fin (n*(J+1)) := finProdFinEquiv
  have hT : MeasurePreserving (plannerFairBankFromBitTape n bT CT RT)
      (plannerQueryBitTapeLaw n bT CT RT) (fairQueryBankLaw n bT CT RT) :=
    measurePreserving_plannerFairBankFromBitTape _ _ _ _
  have hP : MeasurePreserving (plannerFairBankFromBitTape n bP CP RP)
      P (fairQueryBankLaw n bP CP RP) :=
    measurePreserving_plannerFairBankFromBitTape _ _ _ _
  have hTP := measurePreserving_pi _ _ (fun _ : Fin (4*m+1) => hT)
  have hPArray := (measurePreserving_pi _ _ (fun _ : Fin n × Fin (J+1) => hP)).comp
    ((measurePreserving_piCongrLeft (fun _ : Fin (n*(J+1)) => P) e).symm)
  have hValidation := measurePreserving_pi _ _ (fun _ : Fin m => hPArray)
  letI : MeasurableSpace ((Fin n × Fin (J+1)) → FairQueryBank n bP CP RP) := MeasurableSpace.pi
  letI : MeasurableSpace (Fin m → (Fin n × Fin (J+1)) → FairQueryBank n bP CP RP) := MeasurableSpace.pi
  exact hTP.prod (hValidation.prod hPArray)

universe v

def sampleCalibrationQueryArraysM {M : Type → Type v} [Monad M]
    (n m J bT CT RT bP CP RP : ℕ) (drawBit : M Bool) :
    M (CalibrationQueryArrays n m J (FairQueryBank n bT CT RT) (FairQueryBank n bP CP RP) × ℕ) := do
  let T := 4*m+1
  let N := n*(J+1)
  let drawT := sampleCountedPlannerFairBankM n bT CT RT drawBit
  let drawP := sampleCountedPlannerFairBankM n bP CP RP drawBit
  let target ← Vector.ofFnM (fun _ : Fin T => drawT)
  let validation ← Vector.ofFnM (fun _ : Fin m => Vector.ofFnM (fun _ : Fin N => drawP))
  let online ← Vector.ofFnM (fun _ : Fin N => drawP)
  let seeds := (fun i => (target.get i).1,
    (fun l j => ((validation.get l).get (finProdFinEquiv j)).1,
      fun j => (online.get (finProdFinEquiv j)).1))
  let work := (∑ i : Fin T, (target.get i).2) +
    (∑ l : Fin m, ∑ j : Fin N, ((validation.get l).get j).2) + (∑ j : Fin N, (online.get j).2)
  pure (seeds, work+10*(T+(m+1)*N+m+1)+6)

private lemma queryCounter_bind {A B : Type} (x : StateM ℕ A) (f : A → StateM ℕ B) (c : ℕ) :
    (x >>= f).run c = (f (x.run c).1).run (x.run c).2 := by
  change (let (a,s) := x.run c; (f a).run s) = _
  cases x.run c
  rfl

private lemma queryCounter_pure {A : Type} (x : A) (c : ℕ) :
    (pure x : StateM ℕ A).run c = (x,c) := rfl

def fairQueryBankBitCount (n b C R : ℕ) : ℕ :=
  multilevelBankSlots C R*((3*n+2)*b)

lemma fairQueryBankBitCount_le (n b C R : ℕ) :
    fairQueryBankBitCount n b C R ≤ 5*C*16^R*((3*n+2)*b) :=
  Nat.mul_le_mul_right _ (multilevelBankSlots_le C R)

def fairQueryBankWorkBound (n b C R : ℕ) : ℕ :=
  540*(R+1)^4+C*16^R*(15+5*plannerFairSeedStorageWork n b)

/-- The bit budget counts exactly all target and continuation arrays.
It is independent of the values of the bits and of the training data. -/
theorem sampleCalibrationQueryArraysM_counter (n m J bT CT RT bP CP RP : ℕ)
    (drawBit : StateM ℕ Bool) (h : ∀ c, (drawBit.run c).2 = c+1) (c : ℕ) :
    ((sampleCalibrationQueryArraysM n m J bT CT RT bP CP RP drawBit).run c).2 =
      c + (4*m+1)*fairQueryBankBitCount n bT CT RT +
        (m+1)*n*(J+1)*fairQueryBankBitCount n bP CP RP := by
  let T := fairQueryBankBitCount n bT CT RT
  let P := fairQueryBankBitCount n bP CP RP
  let f := sampleCountedPlannerFairBankM n bT CT RT drawBit
  let g := sampleCountedPlannerFairBankM n bP CP RP drawBit
  have hf : ∀ a, (f.run a).2 = a+T := sampleCountedPlannerFairBankM_counter _ _ _ _ _ h
  have hg : ∀ a, (g.run a).2 = a+P := sampleCountedPlannerFairBankM_counter _ _ _ _ _ h
  have hP := uniformVectorM_counter g P hg (n*(J+1))
  simp only [sampleCalibrationQueryArraysM, queryCounter_bind, queryCounter_pure]
  change ((Vector.ofFnM (fun _ : Fin (n*(J+1)) => g)).run
    ((Vector.ofFnM (fun _ : Fin m => Vector.ofFnM (fun _ : Fin (n*(J+1)) => g))).run
      ((Vector.ofFnM (fun _ : Fin (4*m+1) => f)).run c).2).2).2 = _
  rw [hP, uniformVectorM_counter _ _ hP, uniformVectorM_counter f T hf]
  change c+(4*m+1)*T + m*(n*(J+1)*P) + n*(J+1)*P = c+(4*m+1)*T+(m+1)*n*(J+1)*P
  ring

theorem sampleCalibrationQueryArraysM_counter_le (n m J bT CT RT bP CP RP : ℕ)
    (drawBit : StateM ℕ Bool) (h : ∀ c, (drawBit.run c).2 = c+1) (c : ℕ) :
    ((sampleCalibrationQueryArraysM n m J bT CT RT bP CP RP drawBit).run c).2 ≤
      c + (4*m+1)*(5*CT*16^RT*((3*n+2)*bT)) +
        (m+1)*n*(J+1)*(5*CP*16^RP*((3*n+2)*bP)) := by
  rw [sampleCalibrationQueryArraysM_counter _ _ _ _ _ _ _ _ _ drawBit h]
  exact Nat.add_le_add
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (fairQueryBankBitCount_le _ _ _ _)) _)
    (Nat.mul_le_mul_left _ (fairQueryBankBitCount_le _ _ _ _))

private lemma vectorDraw_get_property {A : Type} (draw : StateM ℕ A) (P : A → Prop)
    (h : ∀ c, P (draw.run c).1) (N c : ℕ) (i : Fin N) :
    P (((Vector.ofFnM (fun _ : Fin N => draw)).run c).1.get i) := by
  induction N generalizing c with
  | zero => exact i.elim0
  | succ N ih =>
    rw [Vector.ofFnM_succ, queryCounter_bind, queryCounter_bind, queryCounter_pure]
    let w := (Vector.ofFnM (fun _ : Fin N => draw)).run c
    let a := (draw.run w.2).1
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change P ((w.1.push a)[N])
      rw [Vector.getElem_push_eq]
      exact h w.2
    · change P ((w.1.push a)[j.val])
      rw [Vector.getElem_push_lt j.isLt]
      exact ih c j

/-- Storage and arithmetic work for allocation of all query banks. The
separate exact bit count accounts for the calls to the random primitive. -/
theorem sampleCalibrationQueryArraysM_work (n m J bT CT RT bP CP RP : ℕ)
    (drawBit : StateM ℕ Bool) (c : ℕ) :
    ((sampleCalibrationQueryArraysM n m J bT CT RT bP CP RP drawBit).run c).1.2 ≤
      (4*m+1)*fairQueryBankWorkBound n bT CT RT +
        (m+1)*n*(J+1)*fairQueryBankWorkBound n bP CP RP +
        10*((4*m+1)+(m+1)*(n*(J+1))+m+1)+6 := by
  let T := 4*m+1
  let N := n*(J+1)
  let WT := fairQueryBankWorkBound n bT CT RT
  let WP := fairQueryBankWorkBound n bP CP RP
  let f := sampleCountedPlannerFairBankM n bT CT RT drawBit
  let g := sampleCountedPlannerFairBankM n bP CP RP drawBit
  let gvec := Vector.ofFnM (fun _ : Fin N => g)
  let tt := (Vector.ofFnM (fun _ : Fin T => f)).run c
  let vv := (Vector.ofFnM (fun _ : Fin m => gvec)).run tt.2
  let oo := gvec.run vv.2
  have hf (a : ℕ) : (f.run a).1.2 ≤ WT := sampleCountedPlannerFairBankM_work _ _ _ _ _ _
  have hg (a : ℕ) : (g.run a).1.2 ≤ WP := sampleCountedPlannerFairBankM_work _ _ _ _ _ _
  have ht : ∑ i : Fin T, (tt.1.get i).2 ≤ T*WT := by
    calc
      _ ≤ ∑ _i : Fin T, WT := Finset.sum_le_sum fun i _ =>
        vectorDraw_get_property f (fun a => a.2 ≤ WT) hf T c i
      _ = _ := by simp
  have hv : ∑ l : Fin m, ∑ j : Fin N, ((vv.1.get l).get j).2 ≤ m*(N*WP) := by
    have hVec (a : ℕ) (j : Fin N) : ((gvec.run a).1.get j).2 ≤ WP :=
      vectorDraw_get_property g (fun a => a.2 ≤ WP) hg N a j
    calc
      _ ≤ ∑ _l : Fin m, ∑ _j : Fin N, WP := by
        apply Finset.sum_le_sum
        intro l _
        apply Finset.sum_le_sum
        intro j _
        exact vectorDraw_get_property gvec (fun a => (a.get j).2 ≤ WP)
          (fun a => hVec a j) m tt.2 l
      _ = _ := by simp
  have ho : ∑ j : Fin N, (oo.1.get j).2 ≤ N*WP := by
    calc
      _ ≤ ∑ _j : Fin N, WP := Finset.sum_le_sum fun j _ =>
        vectorDraw_get_property g (fun a => a.2 ≤ WP) hg N vv.2 j
      _ = _ := by simp
  simp only [sampleCalibrationQueryArraysM, queryCounter_bind, queryCounter_pure]
  change (∑ i : Fin T, (tt.1.get i).2) + (∑ l : Fin m, ∑ j : Fin N, ((vv.1.get l).get j).2) +
      (∑ j : Fin N, (oo.1.get j).2) + 10*(T+(m+1)*N+m+1)+6 ≤
    T*WT+(m+1)*n*(J+1)*WP+10*(T+(m+1)*N+m+1)+6
  have he : (m+1)*n*(J+1)*WP = m*(N*WP)+N*WP := by dsimp only [N]; ring
  rw [he]
  omega

end ProphetSecretary.Statistics.Calibration
