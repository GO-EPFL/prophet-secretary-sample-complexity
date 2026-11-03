import ProphetSecretary.Statistics.CalibratedOuter.MarkCoupling
import ProphetSecretary.Statistics.CalibratedOuter.MarkAllocation

/-!
# Sequential reads of independent uniforms

A fixed-length reader is modeled by its action on a finite block. The
composition rules preserve both the product law of disjoint blocks and
the exact value returned by the sequential reader.
-/

open MeasureTheory

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

def uniformTapeRead (u : ℕ → ℝ) : StateM ℕ ℝ := fun c => (u c,c+1)

def uniformTapeBlock (u : ℕ → ℝ) (c d : ℕ) : Fin d → ℝ := fun i => u (c+i.val)

private def uniformTapeSplit {a b : ℕ} (t : Fin (a+b) → ℝ) :
    (Fin a → ℝ) × (Fin b → ℝ) :=
  (fun i => t (i.castAdd b),fun i => t (i.natAdd a))

private lemma uniformTapeSplit_law (a b : ℕ) :
    MeasurePreserving (uniformTapeSplit (a := a) (b := b))
      (Instance.clocksLaw (a+b)) ((Instance.clocksLaw a).prod (Instance.clocksLaw b)) :=
  (measurePreserving_sumPiEquivProdPi (fun _ : Fin a ⊕ Fin b => Instance.uniformClock)).comp
    ((measurePreserving_piCongrLeft (fun _ : Fin (a+b) => Instance.uniformClock) finSumFinEquiv).symm)

private def uniformTapeRows {k d : ℕ} (t : Fin (k*d) → ℝ) (i : Fin k) (j : Fin d) : ℝ :=
  t (finProdFinEquiv (i,j))

private lemma uniformTapeRows_law (k d : ℕ) :
    MeasurePreserving (uniformTapeRows (k := k) (d := d)) (Instance.clocksLaw (k*d))
      (Measure.pi (fun _ : Fin k => Instance.clocksLaw d)) := by
  let μ := Instance.uniformClock
  have h₀ := (measurePreserving_piCongrLeft (fun _ : Fin (k*d) => μ)
    (finProdFinEquiv : Fin k × Fin d ≃ Fin (k*d))).symm
  have h₁ := (measurePreserving_piCongrLeft (fun _ : Fin k × Fin d => μ)
    (Equiv.prodComm (Fin d) (Fin k))).symm
  have h₂ := (outerRoundCoordinates_measurePreserving (uniformOfferInstance d) k).symm
    (outerRoundCoordinates d k)
  exact h₂.comp (h₁.comp h₀)

/-- A reader's projected output agrees with a function of exactly the
specified number of successive tape entries. -/
structure UniformTapeModel {A B : Type} [MeasurableSpace B]
    (f : (ℕ → ℝ) → StateM ℕ A) (out : A → B) (d : ℕ) (ν : Measure B) where
  decode : (Fin d → ℝ) → B
  preserves : MeasurePreserving decode (Instance.clocksLaw d) ν
  run_value : ∀ u c, out ((f u).run c).1=decode (uniformTapeBlock u c d)
  run_counter : ∀ u c, ((f u).run c).2=c+d

namespace UniformTapeModel

variable {A B C D E : Type} [MeasurableSpace B] [MeasurableSpace D]

protected noncomputable def read : UniformTapeModel uniformTapeRead id 1 Instance.uniformClock where
  decode t := t 0
  preserves := measurePreserving_piUnique (fun _ : Fin 1 => Instance.uniformClock)
  run_value _ _ := rfl
  run_counter _ _ := rfl

protected noncomputable def map {f : (ℕ → ℝ) → StateM ℕ A} {out : A → B} {d : ℕ} {ν : Measure B}
    [MeasurableSpace E] (F : UniformTapeModel f out d ν) (value : A → C) (proj : C → E) (g : B → E) {ξ : Measure E}
    (hLaw : MeasurePreserving g ν ξ) (hValue : ∀ a, proj (value a)=g (out a)) :
    UniformTapeModel (fun u => do let a ← f u; pure (value a)) proj d ξ where
  decode t := g (F.decode t)
  preserves := hLaw.comp F.preserves
  run_value u c := by
    change proj (value ((f u).run c).1)=_
    rw [hValue,F.run_value]
  run_counter := F.run_counter

protected noncomputable def pair {f : (ℕ → ℝ) → StateM ℕ A} {g : (ℕ → ℝ) → StateM ℕ C}
    {out : A → B} {proj : C → D} {a b : ℕ} {ν : Measure B} {ξ : Measure D}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]
    (F : UniformTapeModel f out a ν) (G : UniformTapeModel g proj b ξ) (value : A → C → E)
    {H : Type} [MeasurableSpace H] (result : E → H) {η : Measure H} (post : B × D → H)
    (hLaw : MeasurePreserving post (ν.prod ξ) η)
    (hValue : ∀ x y, result (value x y)=post (out x,proj y)) :
    UniformTapeModel (fun u => do let x ← f u; let y ← g u; pure (value x y)) result (a+b) η where
  decode t := post (F.decode (uniformTapeSplit t).1,G.decode (uniformTapeSplit t).2)
  preserves := hLaw.comp ((F.preserves.prod G.preserves).comp (uniformTapeSplit_law a b))
  run_value u c := by
    change result (value ((f u).run c).1 ((g u).run ((f u).run c).2).1)=_
    rw [F.run_counter,hValue,F.run_value,G.run_value]
    have h₁ : (uniformTapeSplit (uniformTapeBlock u c (a+b))).1=uniformTapeBlock u c a := by
      funext i
      rfl
    have h₂ : (uniformTapeSplit (uniformTapeBlock u c (a+b))).2=uniformTapeBlock u (c+a) b := by
      funext i
      simp only [uniformTapeBlock,uniformTapeSplit,Fin.val_natAdd,Nat.add_assoc]
    rw [h₁,h₂]
  run_counter u c := by
    change ((g u).run ((f u).run c).2).2=c+(a+b)
    rw [F.run_counter,G.run_counter,Nat.add_assoc]

private lemma vector_run_value {f : (ℕ → ℝ) → StateM ℕ A} {out : A → B} {d : ℕ} {ν : Measure B}
    (F : UniformTapeModel f out d ν) (u : ℕ → ℝ) (c : ℕ) (k : ℕ) (i : Fin k) :
    out (((Vector.ofFnM (fun _ : Fin k => f u)).run c).1.get i)=
      F.decode (uniformTapeBlock u (c+i.val*d) d) := by
  induction k with
  | zero => exact i.elim0
  | succ k ih =>
    rw [Vector.ofFnM_succ]
    let w := (Vector.ofFnM (fun _ : Fin k => f u)).run c
    let x := ((f u).run w.2).1
    change out ((w.1.push x).get i)=_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change out ((w.1.push x)[k])=_
      rw [Vector.getElem_push_eq]
      unfold x w
      rw [ProphetSecretary.Analysis.uniformVectorM_counter _ d (F.run_counter u),F.run_value]
      rfl
    · change out ((w.1.push x)[j.val])=_
      rw [Vector.getElem_push_lt j.isLt]
      exact ih j

protected noncomputable def array {f : (ℕ → ℝ) → StateM ℕ A} {out : A → B} {d : ℕ} {ν : Measure B}
    [IsProbabilityMeasure ν] (F : UniformTapeModel f out d ν) (k : ℕ) :
    UniformTapeModel (fun u => Vector.ofFnM (fun _ : Fin k => f u))
      (fun q i => out (q.get i)) (k*d) (Measure.pi (fun _ : Fin k => ν)) where
  decode t i := F.decode (uniformTapeRows t i)
  preserves := (measurePreserving_pi _ _ (fun _ : Fin k => F.preserves)).comp (uniformTapeRows_law k d)
  run_value u c := by
    funext i
    rw [vector_run_value F]
    apply congrArg F.decode
    funext j
    apply congrArg u
    change c+i.val*d+j.val=c+(j.val+d*i.val)
    ring
  run_counter u c := ProphetSecretary.Analysis.uniformVectorM_counter _ d (F.run_counter u) k c

protected noncomputable def product {f : (ℕ → ℝ) → StateM ℕ A} {g : (ℕ → ℝ) → StateM ℕ C}
    {out : A → B} {proj : C → D} {a b : ℕ} {ν : Measure B} {ξ : Measure D}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ξ]
    (F : UniformTapeModel f out a ν) (G : UniformTapeModel g proj b ξ) :
    UniformTapeModel (fun u => do let x ← f u; let y ← g u; pure (x,y))
      (fun r => (out r.1,proj r.2)) (a+b) (ν.prod ξ) :=
  F.pair G Prod.mk _ id (MeasurePreserving.id _) (fun _ _ => rfl)

protected noncomputable def resize {f : (ℕ → ℝ) → StateM ℕ A} {out : A → B} {d e : ℕ} {ν : Measure B}
    (F : UniformTapeModel f out d ν) (h : d=e) : UniformTapeModel f out e ν := h ▸ F

protected noncomputable def transfer {f : (ℕ → ℝ) → StateM ℕ A} {out : A → B} {d : ℕ} {ν : Measure B}
    (F : UniformTapeModel f out d ν) (g : (ℕ → ℝ) → StateM ℕ C) (proj : C → B)
    (hValue : ∀ u c, proj ((g u).run c).1=out ((f u).run c).1)
    (hCount : ∀ u c, ((g u).run c).2=((f u).run c).2) :
    UniformTapeModel g proj d ν where
  decode := F.decode
  preserves := F.preserves
  run_value u c := (hValue u c).trans (F.run_value u c)
  run_counter u c := (hCount u c).trans (F.run_counter u c)

end UniformTapeModel
end ProphetSecretary.Statistics.Calibration
