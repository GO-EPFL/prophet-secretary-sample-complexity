import ProphetSecretary.Statistics.CalibratedOuter.ArithmeticUniformTape
import ProphetSecretary.Statistics.CalibratedOuter.ArithmeticProgram
import ProphetSecretary.Statistics.ArithmeticLearningTotal

/-!
# Joint input law for the arithmetic learner

The sequential allocator draws independent uniform coordinates for the
query banks, validation clocks, mixing coin, and outer marks. Its
measured decoder supplies the same input as the statistical learner.
-/

open MeasureTheory Set

set_option synthInstance.maxSize 2048

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Model ProphetSecretary.Probability

private lemma tapeBindRun {A B : Type} (x : StateM ℕ A) (f : A → StateM ℕ B) (c : ℕ) :
    (x >>= f).run c = (f (x.run c).1).run (x.run c).2 := rfl

private lemma tapePureRun {A : Type} (x : A) (c : ℕ) :
    (pure x : StateM ℕ A).run c = (x,c) := rfl

private noncomputable def plannerTransitionTapeModel (n : ℕ) :
    UniformTapeModel (fun u => plannerFullSeedM n (uniformTapeRead u)) id (3*n+2) (plannerUniformSeedLaw n) := by
  let S := UniformTapeModel.read
  let V := S.array n
  let F := (S.product V).product (S.product (V.product V))
  let G := F.map
    (fun a => ((a.1.1,a.1.2.get),(a.2.1,(a.2.2.1.get,a.2.2.2.get))))
    id id (MeasurePreserving.id (plannerUniformSeedLaw n)) (fun _ => rfl)
  exact (G.resize (by simp; omega)).transfer _ _ (fun _ _ => rfl) (fun _ _ => rfl)

private noncomputable def arithmeticBankLaw (n C R : ℕ) : Measure (ArithmeticSeedBank n C R ℝ) :=
  Measure.pi fun l : Fin (R+1) => Measure.pi (fun _ : Fin C => multilevelTreeLaw (plannerUniformSeedLaw n) l.val)

private instance arithmeticBankLaw_probability (n C R : ℕ) : IsProbabilityMeasure (arithmeticBankLaw n C R) := by
  unfold arithmeticBankLaw
  infer_instance

private lemma arrayCastLaw {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {a b : ℕ} (h : a=b) :
    MeasurePreserving (fun (u : Fin a → α) i => u (Fin.cast h.symm i))
      (Measure.pi fun _ : Fin a => μ) (Measure.pi fun _ : Fin b => μ) := by
  subst b
  exact MeasurePreserving.id _

private noncomputable def arithmeticBankTapeModel (n C R : ℕ) :
    UniformTapeModel (fun u => sampleArithmeticPlannerBankM n C R (uniformTapeRead u))
      Prod.fst (multilevelBankSlots C R*(3*n+2)) (arithmeticBankLaw n C R) := by
  let N := countedMultilevelBankSize C R
  let hN : N.1=multilevelBankSlots C R := countedMultilevelBankSize_value C R
  let A := (plannerTransitionTapeModel n).array N.1
  let f := fun t : Fin N.1 → PlannerUniformSeed n =>
    (countedMultilevelBankFromTape C R (fun i => t (Fin.cast hN.symm i))).1
  have h : MeasurePreserving f (Measure.pi fun _ : Fin N.1 => plannerUniformSeedLaw n)
      (arithmeticBankLaw n C R) :=
    (measurePreserving_countedMultilevelBankFromTape (plannerUniformSeedLaw n) C R).comp
      (arrayCastLaw _ hN)
  let A' := A.map (fun v =>
    let q := countedMultilevelBankFromTape C R (fun i => v.get (Fin.cast hN.symm i))
    (q.1,q.2+N.2+3*N.1+5+N.2+N.1*arithmeticTransitionSeedWork n+5))
    Prod.fst f h (fun _ => rfl)
  exact (A'.resize (congrArg (fun k => k*(3*n+2)) hN)).transfer _ _
    (fun _ _ => rfl) (fun _ _ => rfl)

private theorem productRowsLaw {ι κ α : Type*} [Fintype ι] [Fintype κ] [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun (a : ι × κ → α) i j => a (i,j))
      (Measure.pi (fun _ : ι × κ => μ)) (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => μ))) := by
  let e := MeasurableEquiv.curry ι κ α
  have h : MeasurePreserving e.symm
      (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => μ))) (Measure.pi (fun _ : ι × κ => μ)) := by
    refine ⟨e.symm.measurable,(Measure.pi_eq (fun s _ => ?_)).symm⟩
    rw [MeasurableEquiv.map_apply]
    have hpre : e.symm ⁻¹' (Set.univ.pi s) =
        Set.univ.pi (fun i : ι => Set.univ.pi (fun j : κ => s (i,j))) := by
      ext a
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
      exact ⟨fun h i j => h (i,j),fun h p => h p.1 p.2⟩
    rw [hpre,Measure.pi_pi]
    simp only [Measure.pi_pi]
    rw [← Finset.univ_product_univ,Finset.prod_product]
  exact h.symm

private def continuationTapeEquiv (n m J : ℕ) :
    Fin (m+1) × (Fin n × Fin (J+1)) ≃ Fin (arithmeticContinuationTapeCount n m J) :=
  (Equiv.prodCongr (Equiv.refl (Fin (m+1))) finProdFinEquiv).trans finProdFinEquiv

private def splitLastRows {A : Type*} {m : ℕ} (f : Fin (m+1) → A) : (Fin m → A) × A :=
  (fun j => f j.castSucc,f (Fin.last m))

private theorem splitLastRows_law {A : Type*} [MeasurableSpace A] (μ : Measure A)
    [IsProbabilityMeasure μ] (m : ℕ) :
    MeasurePreserving (splitLastRows (m := m)) (Measure.pi (fun _ : Fin (m+1) => μ))
      ((Measure.pi (fun _ : Fin m => μ)).prod μ) := by
  let ν := Measure.pi (fun _ : Fin m => μ)
  have h := (Measure.measurePreserving_swap (μ := μ) (ν := ν)).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => μ) (Fin.last m))
  have he : (Prod.swap ∘ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => A) (Fin.last m))) =
      splitLastRows (m := m) := by
    funext f
    change ((fun i => f ((Fin.last m).succAbove i)),f (Fin.last m))=_
    simp only [Fin.succAbove_last,splitLastRows]
  rw [←he]
  exact h

private def continuationTapeSplit {A : Type*} (n m J : ℕ)
    (t : Fin (arithmeticContinuationTapeCount n m J) → A) :
    (Fin m → PolicyQueryArray n J A) × PolicyQueryArray n J A :=
  splitLastRows (fun l i => t (continuationTapeEquiv n m J (l,i)))

private theorem continuationTapeSplit_law {A : Type*} [MeasurableSpace A] (μ : Measure A)
    [IsProbabilityMeasure μ] (n m J : ℕ) :
    MeasurePreserving (continuationTapeSplit n m J)
      (Measure.pi fun _ : Fin (arithmeticContinuationTapeCount n m J) => μ)
      ((Measure.pi fun _ : Fin m => policyQueryArrayLaw (n := n) (J := J) μ).prod
        (policyQueryArrayLaw (n := n) (J := J) μ)) :=
  (splitLastRows_law (policyQueryArrayLaw (n := n) (J := J) μ) m).comp
    ((productRowsLaw μ).comp
      ((measurePreserving_piCongrLeft (fun _ => μ) (continuationTapeEquiv n m J)).symm))

private noncomputable def arithmeticQueryTapeModel (n m J CT RT CP RP : ℕ) :
    UniformTapeModel (fun u => sampleArithmeticCalibrationQueryTapesM n m J CT RT CP RP (uniformTapeRead u))
      Prod.fst ((4*m+1)*(multilevelBankSlots CT RT*(3*n+2))+
        arithmeticContinuationTapeCount n m J*(multilevelBankSlots CP RP*(3*n+2)))
      (calibrationQueryArraysLaw (n := n) (m := m) (J := J) (arithmeticBankLaw n CT RT) (arithmeticBankLaw n CP RP)) := by
  let F := (arithmeticBankTapeModel n CT RT).array (4*m+1)
  let G := (arithmeticBankTapeModel n CP RP).array (arithmeticContinuationTapeCount n m J)
  let H := F.pair G (fun x y =>
    ((fun i => (x.get i).1,continuationTapeSplit n m J (fun i => (y.get i).1)),0))
    Prod.fst (Prod.map id (continuationTapeSplit n m J))
    ((MeasurePreserving.id _).prod (continuationTapeSplit_law (arithmeticBankLaw n CP RP) n m J))
    (fun _ _ => rfl)
  exact H.transfer _ _ (fun _ _ => rfl) (fun _ _ => rfl)

private noncomputable def arithmeticValidationClocksModel (n m : ℕ) :
    UniformTapeModel (fun u => sampleArithmeticValidationClocksM n m (uniformTapeRead u))
      Prod.fst (m*n) (Measure.pi fun _ : Fin m => Instance.clocksLaw n) := by
  let F := ((UniformTapeModel.read.array n).array m).map
    (fun v => (fun i j => (v.get i).get j,m*(5*n+8)+6))
    Prod.fst id (MeasurePreserving.id (Measure.pi fun _ : Fin m => Instance.clocksLaw n)) (fun _ => rfl)
  exact (F.resize (by simp)).transfer _ _ (fun _ _ => rfl) (fun _ _ => rfl)

private def arithmeticAuxSeed {n m J CT RT CP RP : ℕ}
    (q : ArithmeticCalibrationAux n m J CT RT CP RP ℝ) :
    CalibratedSeed n m J (ArithmeticSeedBank n CT RT ℝ) (ArithmeticSeedBank n CP RP ℝ) :=
  (q.banks.1,fun j => (q.clocks j,q.banks.2.1 j),q.banks.2.2,q.coin)

private theorem arithmeticAuxJoinLaw {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (n m J : ℕ) (νT : Measure A) (νP : Measure B) [IsProbabilityMeasure νT] [IsProbabilityMeasure νP] :
    MeasurePreserving (fun a : CalibrationQueryArrays n m J A B × ((Fin m → Fin n → ℝ) × ℝ) =>
      (a.1.1, (fun j => (a.2.1 j,a.1.2.1 j)), a.1.2.2,a.2.2) : _ → CalibratedSeed n m J A B)
      ((calibrationQueryArraysLaw νT νP).prod ((Measure.pi fun _ : Fin m => Instance.clocksLaw n).prod Instance.uniformClock))
      (calibratedSeedLaw νT νP) := by
  let T := targetQueryArrayLaw (m := m) νT
  let P := policyQueryArrayLaw (n := n) (J := J) νP
  let V := Measure.pi (fun _ : Fin m => P)
  let K := Measure.pi (fun _ : Fin m => Instance.clocksLaw n)
  let U := Instance.uniformClock
  have hV := (measurePreserving_arrowProdEquivProdArrow (Fin n → ℝ) (PolicyQueryArray n J B)
    (Fin m) (fun _ => Instance.clocksLaw n) (fun _ => P)).symm
    (MeasurableEquiv.arrowProdEquivProdArrow _ _ _)
  have h₀ := measurePreserving_prodAssoc T (V.prod P) (K.prod U)
  have h₁ := (MeasurePreserving.id T).prod (productPairShuffle_measurePreserving V P K U)
  have h₂ := (MeasurePreserving.id T).prod
    ((hV.comp (Measure.measurePreserving_swap (μ := V) (ν := K))).prod (MeasurePreserving.id (P.prod U)))
  exact h₂.comp (h₁.comp h₀)

private noncomputable def arithmeticAuxTapeModel (n m J CT RT CP RP : ℕ) :
    UniformTapeModel (fun u => sampleArithmeticCalibrationAuxM n m J CT RT CP RP (uniformTapeRead u))
      arithmeticAuxSeed ((4*m+1)*(multilevelBankSlots CT RT*(3*n+2))+
        arithmeticContinuationTapeCount n m J*(multilevelBankSlots CP RP*(3*n+2))+m*n+1)
      (calibratedSeedLaw (n := n) (m := m) (J := J) (arithmeticBankLaw n CT RT) (arithmeticBankLaw n CP RP)) := by
  let F := arithmeticQueryTapeModel n m J CT RT CP RP
  letI : IsProbabilityMeasure (calibrationQueryArraysLaw (n := n) (m := m) (J := J)
      (arithmeticBankLaw n CT RT) (arithmeticBankLaw n CP RP)) := ⟨by
    simpa only [Set.preimage_univ,measure_univ] using
      (F.preserves.measure_preimage (s := Set.univ) MeasurableSet.univ.nullMeasurableSet).symm⟩
  let G := (arithmeticValidationClocksModel n m).product UniformTapeModel.read
  let H := F.pair G (fun q a => (⟨q.1,a.1.1,a.2,q.2+a.1.2+4⟩ :
      ArithmeticCalibrationAux n m J CT RT CP RP ℝ))
    arithmeticAuxSeed _ (arithmeticAuxJoinLaw n m J _ _) (fun _ _ => rfl)
  exact (H.resize (by omega)).transfer _ _ (fun _ _ => rfl) (fun _ _ => rfl)

private noncomputable def scaleCopies (s : ArithmeticCalibrationScale) : ℕ :=
  confidenceCopyCount s.failure (exists_confidence_level s.failure_mem.1 s.failure_mem.2)

private noncomputable def scaleLevel (m : ℕ) (s : ArithmeticCalibrationScale) : ℕ :=
  calibrationPlannerLevel m s.accuracy

def arithmeticAuxUniformCount (n m J CT RT CP RP : ℕ) : ℕ :=
  (4*m+1)*(multilevelBankSlots CT RT*(3*n+2))+
    arithmeticContinuationTapeCount n m J*(multilevelBankSlots CP RP*(3*n+2))+m*n+1

noncomputable def arithmeticOuterUniformCount (n m J : ℕ) (T P : ArithmeticCalibrationScale) : ℕ :=
  outerMarkSlotCount n m+arithmeticAuxUniformCount n m J (scaleCopies T) (scaleLevel m T)
    (scaleCopies P) (scaleLevel m P)

variable {n m : ℕ} [NeZero m]

/-- Allocate the outer marks followed by the complete arithmetic query
and validation reservoirs. The two work counters are retained. -/
noncomputable def sampleArithmeticOuterSeedM {M : Type → Type} [Monad M]
    (J : ℕ) (T P : ArithmeticCalibrationScale) (mu zlo zhi : ℝ) (uniform : M ℝ) :
    M (OuterLearnerSeed m (arithmeticLearnerForScales (n := n) (m := m) J T P mu zlo zhi) × ℕ) := do
  let marks ← sampleOuterMarksM n m uniform
  let aux ← sampleArithmeticCalibrationAuxM n m J (scaleCopies T) (scaleLevel m T)
    (scaleCopies P) (scaleLevel m P) uniform
  let L := arithmeticLearnerForScales (n := n) (m := m) J T P mu zlo zhi
  pure (outerSeedFromMarks L (unpackOuterMarks marks.1) (arithmeticAuxSeed aux),marks.2+aux.work+2)

private noncomputable def arithmeticMarkTapeModel (n m : ℕ) :
    UniformTapeModel (fun u => sampleOuterMarksM n m (uniformTapeRead u)) Prod.fst
      (outerMarkSlotCount n m) (Instance.clocksLaw (outerMarkSlotCount n m)) := by
  let F := (UniformTapeModel.read.array (outerMarkSlotCount n m)).map
    (fun v => (v.get,4*(outerMarkSlotCount n m+1))) Prod.fst id
    (MeasurePreserving.id (Instance.clocksLaw (outerMarkSlotCount n m))) (fun _ => rfl)
  exact (F.resize (Nat.mul_one _)).transfer _ _ (fun _ _ => rfl) (fun _ _ => rfl)

private noncomputable def arithmeticOuterTapeModel (J : ℕ)
    (T P : ArithmeticCalibrationScale) (mu zlo zhi : ℝ) :
    let L := arithmeticLearnerForScales (n := n) (m := m) J T P mu zlo zhi
    UniformTapeModel (fun u => sampleArithmeticOuterSeedM (n := n) (m := m) J T P mu zlo zhi (uniformTapeRead u))
      Prod.fst (arithmeticOuterUniformCount n m J T P) (outerLearnerSeedLaw m L) := by
  dsimp only
  let L := arithmeticLearnerForScales (n := n) (m := m) J T P mu zlo zhi
  let F := arithmeticMarkTapeModel n m
  let G := arithmeticAuxTapeModel n m J (scaleCopies T) (scaleLevel m T) (scaleCopies P) (scaleLevel m P)
  have hMarks : MeasurePreserving (unpackOuterMarks (n := n) (m := m) (K := ℝ))
      (Instance.clocksLaw (outerMarkSlotCount n m)) (outerMarksLaw n m) := by
    exact measurePreserving_unpackOuterMarks n m
  have hLaw := (outerSeedFromMarks_measurePreserving L).comp
    (hMarks.prod (MeasurePreserving.id L.seedLaw))
  exact F.pair G (fun marks aux => (outerSeedFromMarks L (unpackOuterMarks marks.1) (arithmeticAuxSeed aux),
    marks.2+aux.work+2)) Prod.fst _ hLaw (fun _ _ => rfl)

noncomputable def arithmeticOuterSeedFromTape (J : ℕ) (T P : ArithmeticCalibrationScale)
    (mu zlo zhi : ℝ) (t : Fin (arithmeticOuterUniformCount n m J T P) → ℝ) :
    OuterLearnerSeed m (arithmeticLearnerForScales (n := n) (m := m) J T P mu zlo zhi) :=
  (arithmeticOuterTapeModel (n := n) (m := m) J T P mu zlo zhi).decode t

/-- The exact seed and number of reads returned by the sequential
allocator, on every tape and at any starting position. -/
theorem sampleArithmeticOuterSeedM_tape (J : ℕ) (T P : ArithmeticCalibrationScale)
    (mu zlo zhi : ℝ) (u : ℕ → ℝ) (c : ℕ) :
    let N := arithmeticOuterUniformCount n m J T P
    let r := ((sampleArithmeticOuterSeedM (n := n) (m := m) J T P mu zlo zhi (uniformTapeRead u)).run c)
    r.1.1=arithmeticOuterSeedFromTape J T P mu zlo zhi (uniformTapeBlock u c N) ∧ r.2=c+N :=
  let q := arithmeticOuterTapeModel (n := n) (m := m) J T P mu zlo zhi
  ⟨q.run_value u c,q.run_counter u c⟩

theorem measurePreserving_arithmeticOuterSeedFromTape (J : ℕ) (T P : ArithmeticCalibrationScale)
    (mu zlo zhi : ℝ) :
    let L := arithmeticLearnerForScales (n := n) (m := m) J T P mu zlo zhi
    MeasurePreserving (arithmeticOuterSeedFromTape J T P mu zlo zhi)
      (Instance.clocksLaw (arithmeticOuterUniformCount n m J T P)) (outerLearnerSeedLaw m L) :=
  (arithmeticOuterTapeModel (n := n) (m := m) J T P mu zlo zhi).preserves

def extendUniformTape {N : ℕ} (t : Fin N → ℝ) (i : ℕ) : ℝ :=
  if h : i<N then t ⟨i,h⟩ else 0

private lemma uniformTapeBlock_extend {N : ℕ} (t : Fin N → ℝ) :
    uniformTapeBlock (extendUniformTape t) 0 N=t := by
  funext i
  simp only [uniformTapeBlock,Nat.zero_add,extendUniformTape,dif_pos i.isLt,Fin.eta]

/-- Running the counted allocator directly on a finite tape has the
product seed law. The extension is never read beyond the tape. -/
theorem measurePreserving_sampleArithmeticOuterSeedM (J : ℕ) (T P : ArithmeticCalibrationScale)
    (mu zlo zhi : ℝ) :
    let L := arithmeticLearnerForScales (n := n) (m := m) J T P mu zlo zhi
    let N := arithmeticOuterUniformCount n m J T P
    MeasurePreserving (fun t : Fin N → ℝ => ((sampleArithmeticOuterSeedM (n := n) (m := m)
      J T P mu zlo zhi (uniformTapeRead (extendUniformTape t))).run 0).1.1)
      (Instance.clocksLaw N) (outerLearnerSeedLaw m L) := by
  dsimp only
  let N := arithmeticOuterUniformCount n m J T P
  have he : (fun t : Fin N → ℝ => ((sampleArithmeticOuterSeedM (n := n) (m := m)
      J T P mu zlo zhi (uniformTapeRead (extendUniformTape t))).run 0).1.1)=
        arithmeticOuterSeedFromTape J T P mu zlo zhi := by
    funext t
    have hr := (sampleArithmeticOuterSeedM_tape (n := n) (m := m)
      J T P mu zlo zhi (extendUniformTape t) 0).1
    rw [uniformTapeBlock_extend] at hr
    exact hr
  rw [he]
  exact measurePreserving_arithmeticOuterSeedFromTape J T P mu zlo zhi

theorem sampleArithmeticOuterSeedM_work (J : ℕ) (T P : ArithmeticCalibrationScale)
    (mu zlo zhi : ℝ) (u : StateM ℕ ℝ) (c : ℕ) :
    ((sampleArithmeticOuterSeedM (n := n) (m := m) J T P mu zlo zhi u).run c).1.2 ≤
      4*(outerMarkSlotCount n m+1)+arithmeticCalibrationAuxBound n m J (scaleCopies T) (scaleLevel m T)
        (scaleCopies P) (scaleLevel m P)+2 := by
  unfold sampleArithmeticOuterSeedM
  simp only [tapeBindRun,tapePureRun,sampleOuterMarksM_work]
  exact Nat.add_le_add_right (Nat.add_le_add_left (sampleArithmeticCalibrationAuxM_work
    _ _ _ _ _ _ _ u _) _) _

noncomputable def arithmeticOuterInputFromTape (J : ℕ) (T P : ArithmeticCalibrationScale)
    (mu zlo zhi : ℝ) (r : Reservoir n (outerSampleBudget m) ×
      (Fin (arithmeticOuterUniformCount n m J T P) → ℝ)) :
    OuterLearnerInput m (arithmeticLearnerForScales (n := n) (m := m) J T P mu zlo zhi) :=
  (r.1,arithmeticOuterSeedFromTape J T P mu zlo zhi r.2)

theorem arithmeticOuterInputFromTape_eq_allocator (J : ℕ) (T P : ArithmeticCalibrationScale)
    (mu zlo zhi : ℝ) (y : Reservoir n (outerSampleBudget m))
    (t : Fin (arithmeticOuterUniformCount n m J T P) → ℝ) :
    arithmeticOuterInputFromTape J T P mu zlo zhi (y,t)=
      (y,((sampleArithmeticOuterSeedM (n := n) (m := m) J T P mu zlo zhi
        (uniformTapeRead (extendUniformTape t))).run 0).1.1) := by
  have h := (sampleArithmeticOuterSeedM_tape (n := n) (m := m)
    J T P mu zlo zhi (extendUniformTape t) 0).1
  rw [uniformTapeBlock_extend] at h
  exact congrArg (fun r => (y,r)) h.symm

/-- The sequential allocator's independent uniform tape, together with
the independent training reservoir, produces the learner's full input law. -/
theorem measurePreserving_arithmeticOuterInputFromTape (Q : Instance n)
    (J : ℕ) (T P : ArithmeticCalibrationScale) (mu zlo zhi : ℝ) :
    let L := arithmeticLearnerForScales (n := n) (m := m) J T P mu zlo zhi
    MeasurePreserving (arithmeticOuterInputFromTape J T P mu zlo zhi)
      ((Q.reservoirLaw (outerSampleBudget m)).prod (Instance.clocksLaw (arithmeticOuterUniformCount n m J T P)))
      (outerLearnerInputLaw Q m L) :=
  (MeasurePreserving.id _).prod (measurePreserving_arithmeticOuterSeedFromTape J T P mu zlo zhi)

/-- The output of the counted allocator, paired with independent
training data, has exactly the law supplied to the outer policy. -/
theorem measurePreserving_allocatedArithmeticOuterInput (Q : Instance n)
    (J : ℕ) (T P : ArithmeticCalibrationScale) (mu zlo zhi : ℝ) :
    let L := arithmeticLearnerForScales (n := n) (m := m) J T P mu zlo zhi
    let N := arithmeticOuterUniformCount n m J T P
    MeasurePreserving (fun r : Reservoir n (outerSampleBudget m) × (Fin N → ℝ) =>
      (r.1,((sampleArithmeticOuterSeedM (n := n) (m := m) J T P mu zlo zhi
        (uniformTapeRead (extendUniformTape r.2))).run 0).1.1))
      ((Q.reservoirLaw (outerSampleBudget m)).prod (Instance.clocksLaw N))
      (outerLearnerInputLaw Q m L) :=
  (MeasurePreserving.id _).prod (measurePreserving_sampleArithmeticOuterSeedM J T P mu zlo zhi)

theorem arithmeticLearnerForScales_eq (mu : ℝ) (b : ℚ) (hb : (b : ℝ)∈Ioo (4/5 : ℝ) 1)
    (hn : 0<n) (hm : 2≤m) :
    let zlo := (1-(b : ℝ))/(b : ℝ)
    let J := familyGridSize m zlo (1/4)
    let T := arithmeticTargetScale m hm
    let P := arithmeticThresholdScale n m J hn hm zlo (calibrationEndpoint_coefficient_bounds hb)
    arithmeticLearnerForScales (n := n) (m := m) J T P mu zlo (1/4)=
      arithmeticCalibratedLearner mu b hb n m := by
  rw [arithmeticCalibratedLearner,dif_pos ⟨hn,hm⟩]
  rfl

omit [NeZero m] in
private lemma outerLearnerInput_castLaw (Q : Instance n) {L L' : Learner n (2*m)} (e : L=L') :
    MeasurePreserving (fun p : OuterLearnerInput m L => cast (congrArg (OuterLearnerInput m) e) p)
      (outerLearnerInputLaw Q m L) (outerLearnerInputLaw Q m L') := by
  subst L'
  exact MeasurePreserving.id _

/-- Specialization to the two public accuracies and the failure
probabilities of the arithmetic learner in the paper. -/
theorem measurePreserving_originalArithmeticOuterInput (Q : Instance n) (mu : ℝ)
    (b : ℚ) (hb : (b : ℝ)∈Ioo (4/5 : ℝ) 1) (hn : 0<n) (hm : 2≤m) :
    let zlo := (1-(b : ℝ))/(b : ℝ)
    let J := familyGridSize m zlo (1/4)
    let T := arithmeticTargetScale m hm
    let P := arithmeticThresholdScale n m J hn hm zlo (calibrationEndpoint_coefficient_bounds hb)
    let L := arithmeticCalibratedLearner mu b hb n m
    let e : arithmeticLearnerForScales (n := n) (m := m) J T P mu zlo (1/4)=L :=
      arithmeticLearnerForScales_eq (n := n) (m := m) mu b hb hn hm
    MeasurePreserving (fun r => cast (congrArg (OuterLearnerInput m) e)
      (arithmeticOuterInputFromTape (n := n) (m := m) J T P mu zlo (1/4) r))
      ((Q.reservoirLaw (outerSampleBudget m)).prod (Instance.clocksLaw (arithmeticOuterUniformCount n m J T P)))
      (outerLearnerInputLaw Q m L) :=
  (outerLearnerInput_castLaw Q (arithmeticLearnerForScales_eq (n := n) (m := m) mu b hb hn hm)).comp
    (measurePreserving_arithmeticOuterInputFromTape Q _ _ _ _ _ _)

/-- The counted callback agrees almost surely with the measured policy
under the law of its primitive input tape and the training reservoir. -/
theorem decideArithmeticOuter_fromTape_ae (Q : Instance n) (J : ℕ) (hm : 1≤m)
    (T P : ArithmeticCalibrationScale) (mu zlo zhi : ℝ) :
    let L := arithmeticLearnerForScales (n := n) (m := m) J T P mu zlo zhi
    let p := arithmeticOuterInputFromTape (n := n) (m := m) J T P mu zlo zhi
    ∀ᵐ r ∂(Q.reservoirLaw (outerSampleBudget m)).prod (Instance.clocksLaw (arithmeticOuterUniformCount n m J T P)),
      ∀ t i x H,
        (decideArithmeticOuter P (prepareArithmeticOuter J hm T P mu zlo zhi (p r))
          (outerOnlineTags m L (p r)) t i x H).1=(outerPolicy m hm L).decide (p r) t i x H :=
  (measurePreserving_arithmeticOuterInputFromTape Q J T P mu zlo zhi).quasiMeasurePreserving.ae
    (decideArithmeticOuter_ae J hm T P mu zlo zhi Q)

end ProphetSecretary.Statistics.Calibration
