import ProphetSecretary.Analysis.MultilevelSeedSlots

/-!
# An independent seed tape for the multilevel estimator

The tape is partitioned into base, transition, upper, and lower arrays.
Every recursive subtree uses a disjoint tape segment. The two evaluations
of a paired difference still use the same transition seed.
-/

open scoped BigOperators
open MeasureTheory

namespace ProphetSecretary.Analysis

abbrev MultilevelGroupSize (d : ℕ) (l : Fin d) := 4 ^ (d - l.val)

abbrev MultilevelBaseSlot (d : ℕ) := Fin (4 ^ (d + 1))
abbrev MultilevelTransitionSlot (d : ℕ) := Σ l : Fin d, Fin (MultilevelGroupSize d l)
abbrev MultilevelUpperSlot (d : ℕ) :=
  Σ l : Fin d, Fin (MultilevelGroupSize d l) × Fin (multilevelSeedSlots (l.val + 1))
abbrev MultilevelLowerSlot (d : ℕ) :=
  Σ l : Fin d, Fin (MultilevelGroupSize d l) × Fin (multilevelSeedSlots l.val)

abbrev MultilevelNodeSlot (d : ℕ) :=
  MultilevelBaseSlot d ⊕ (MultilevelTransitionSlot d ⊕ (MultilevelUpperSlot d ⊕ MultilevelLowerSlot d))

private lemma multilevelSeedSlots_partition (d : ℕ) :
    4 ^ (d + 1) + ((∑ l : Fin d, MultilevelGroupSize d l) +
      ((∑ l : Fin d, MultilevelGroupSize d l * multilevelSeedSlots (l.val + 1)) +
        ∑ l : Fin d, MultilevelGroupSize d l * multilevelSeedSlots l.val)) =
      multilevelSeedSlots (d + 1) := by
  rw [multilevelSeedSlots_split]
  simp_rw [Nat.mul_add, Nat.mul_one, Finset.sum_add_distrib]
  ring

def multilevelNodeSlotEquiv (d : ℕ) : MultilevelNodeSlot d ≃ Fin (multilevelSeedSlots (d + 1)) :=
  let tr := finSigmaFinEquiv (n := MultilevelGroupSize d)
  let up := (Equiv.sigmaCongrRight (fun _ : Fin d => finProdFinEquiv)).trans
    (finSigmaFinEquiv (n := fun l => MultilevelGroupSize d l * multilevelSeedSlots (l.val + 1)))
  let lo := (Equiv.sigmaCongrRight (fun _ : Fin d => finProdFinEquiv)).trans
    (finSigmaFinEquiv (n := fun l => MultilevelGroupSize d l * multilevelSeedSlots l.val))
  let upLo := (up.sumCongr lo).trans finSumFinEquiv
  let correction := (tr.sumCongr upLo).trans finSumFinEquiv
  (((Equiv.refl (MultilevelBaseSlot d)).sumCongr correction).trans finSumFinEquiv).trans
    (finCongr (multilevelSeedSlots_partition d))

/-- The tape is read by index, so no recursive suffix of the tape is
copied when constructing a subtree view. -/
def multilevelTreeFromTape {Seed : Type*} :
    (r : ℕ) → (Fin (multilevelSeedSlots r) → Seed) → MultilevelTree Seed r
  | 0, _ => .zero
  | d + 1, tape =>
    let read := fun j => tape (multilevelNodeSlotEquiv d j)
    .node (fun j => read (.inl j))
      (fun l j => read (.inr (.inl ⟨l,j⟩)))
      (fun l j => multilevelTreeFromTape (l.val + 1) (fun s => read (.inr (.inr (.inl ⟨l,j,s⟩)))))
      (fun l j => multilevelTreeFromTape l.val (fun s => read (.inr (.inr (.inr ⟨l,j,s⟩)))))
termination_by r => r
decreasing_by all_goals have := l.isLt; omega

private theorem measurePreserving_piCurry_const {ι : Type*} {κ : ι → Type*} [Fintype ι]
    [∀ i, Fintype (κ i)] {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] :
    MeasurePreserving (MeasurableEquiv.piCurry (fun (_i : ι) (_j : κ _i) => Seed))
      (Measure.pi (fun _ : Sigma κ => μ))
      (Measure.pi (fun i : ι => Measure.pi (fun _ : κ i => μ))) := by
  let e := MeasurableEquiv.piCurry (fun (_i : ι) (_j : κ _i) => Seed)
  have h : MeasurePreserving e.symm
      (Measure.pi (fun i : ι => Measure.pi (fun _ : κ i => μ)))
      (Measure.pi (fun _ : Sigma κ => μ)) := by
    refine ⟨e.symm.measurable, (Measure.pi_eq (fun s _ => ?_)).symm⟩
    rw [MeasurableEquiv.map_apply]
    have hpre : e.symm ⁻¹' (Set.univ.pi s) =
        Set.univ.pi (fun i => Set.univ.pi (fun j => s ⟨i,j⟩)) := by
      ext a
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_const]
      change (∀ ij : Sigma κ, a ij.1 ij.2 ∈ s ij) ↔ _
      exact Sigma.forall
    rw [hpre, Measure.pi_pi, Fintype.prod_sigma]
    simp only [Measure.pi_pi]
  exact h.symm

private theorem measurePreserving_prodCurry_const {ι κ Seed : Type*} [Fintype ι] [Fintype κ]
    [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun (a : ι × κ → Seed) i j => a (i,j))
      (Measure.pi (fun _ : ι × κ => μ))
      (Measure.pi (fun _ : ι => Measure.pi (fun _ : κ => μ))) := by
  exact (measurePreserving_piCurry_const (ι := ι) (κ := fun _ => κ) μ).comp
    ((measurePreserving_piCongrLeft (fun _ : ι × κ => μ) (Equiv.sigmaEquivProd ι κ)).symm)

private theorem measurePreserving_splitSeedArray {I J Seed : Type*} [Fintype I] [Fintype J]
    [MeasurableSpace Seed] (μ : Measure Seed) [IsProbabilityMeasure μ] :
    MeasurePreserving (fun (t : I ⊕ J → Seed) => (fun i => t (.inl i), fun j => t (.inr j)))
      (Measure.pi (fun _ : I ⊕ J => μ))
      ((Measure.pi (fun _ : I => μ)).prod (Measure.pi (fun _ : J => μ))) :=
  measurePreserving_sumPiEquivProdPi (fun _ : I ⊕ J => μ)

/-- Feeding a tape of independent primitive seeds to the executable tree
view gives exactly the independent-array tree law. -/
theorem measurePreserving_multilevelTreeFromTape {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) :
    MeasurePreserving (multilevelTreeFromTape r)
      (Measure.pi (fun _ : Fin (multilevelSeedSlots r) => μ)) (multilevelTreeLaw μ r) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero =>
      rw [show multilevelTreeFromTape (Seed := Seed) 0 = fun _ => .zero from by
        funext a
        rw [multilevelTreeFromTape], multilevelTreeLaw]
      exact ⟨measurable_const, by simp [Measure.map_const]⟩
    | succ d =>
      let B := MultilevelBaseSlot d
      let T := MultilevelTransitionSlot d
      let U := MultilevelUpperSlot d
      let L := MultilevelLowerSlot d
      have hRead : MeasurePreserving (fun (a : Fin (multilevelSeedSlots (d+1)) → Seed)
          (i : B ⊕ (T ⊕ (U ⊕ L))) => a (multilevelNodeSlotEquiv d i))
          (Measure.pi (fun _ : Fin (multilevelSeedSlots (d+1)) => μ))
          (Measure.pi (fun _ : B ⊕ (T ⊕ (U ⊕ L)) => μ)) := by
        exact (measurePreserving_piCongrLeft (fun _ : Fin (multilevelSeedSlots (d+1)) => μ)
          (multilevelNodeSlotEquiv d)).symm
      have hT := measurePreserving_piCurry_const (ι := Fin d) (κ := fun l => Fin (MultilevelGroupSize d l)) μ
      have hU := measurePreserving_piCurry_const (ι := Fin d)
        (κ := fun l => Fin (MultilevelGroupSize d l) × Fin (multilevelSeedSlots (l.val + 1))) μ
      have hL := measurePreserving_piCurry_const (ι := Fin d)
        (κ := fun l => Fin (MultilevelGroupSize d l) × Fin (multilevelSeedSlots l.val)) μ
      have hUpper (l : Fin d) : MeasurePreserving
          (fun (a : Fin (MultilevelGroupSize d l) × Fin (multilevelSeedSlots (l.val+1)) → Seed)
            (j : Fin (MultilevelGroupSize d l)) =>
              multilevelTreeFromTape (l.val+1) (fun s => a (j,s)))
          (Measure.pi (fun _ => μ))
          (Measure.pi (fun _ : Fin (MultilevelGroupSize d l) => multilevelTreeLaw μ (l.val+1))) :=
        (measurePreserving_pi _ _ (fun _ : Fin (MultilevelGroupSize d l) =>
          ih (l.val+1) (by have := l.isLt; omega))).comp (measurePreserving_prodCurry_const μ)
      have hLower (l : Fin d) : MeasurePreserving
          (fun (a : Fin (MultilevelGroupSize d l) × Fin (multilevelSeedSlots l.val) → Seed)
            (j : Fin (MultilevelGroupSize d l)) =>
              multilevelTreeFromTape l.val (fun s => a (j,s)))
          (Measure.pi (fun _ => μ))
          (Measure.pi (fun _ : Fin (MultilevelGroupSize d l) => multilevelTreeLaw μ l.val)) :=
        (measurePreserving_pi _ _ (fun _ : Fin (MultilevelGroupSize d l) =>
          ih l.val (by have := l.isLt; omega))).comp (measurePreserving_prodCurry_const μ)
      have hUp := (measurePreserving_pi _ _ hUpper).comp hU
      have hLo := (measurePreserving_pi _ _ hLower).comp hL
      have hUL := (hUp.prod hLo).comp (measurePreserving_splitSeedArray (I := U) (J := L) μ)
      have hTUL := (hT.prod hUL).comp (measurePreserving_splitSeedArray (I := T) (J := U ⊕ L) μ)
      have hAll := ((MeasurePreserving.id (Measure.pi (fun _ : B => μ))).prod hTUL).comp
        ((measurePreserving_splitSeedArray (I := B) (J := T ⊕ (U ⊕ L)) μ).comp hRead)
      have hNode : MeasurePreserving (multilevelNodeMeasurableEquiv Seed d).symm
          (multilevelNodeLaw μ d) (multilevelTreeLaw μ (d+1)) :=
        (multilevelNode_measurePreserving μ d).symm
      convert hNode.comp hAll using 1
      funext a
      rw [multilevelTreeFromTape]
      rfl

universe u v

/-- Fill the finite tape exactly once, before taking the tree view. -/
def sampleMultilevelTreeM {M : Type u → Type v} [Monad M] {Seed : Type u}
    (r : ℕ) (draw : M Seed) : M (MultilevelTree Seed r) := do
  let a ← Vector.ofFnM (fun _ : Fin (multilevelSeedSlots r) => draw)
  pure (multilevelTreeFromTape r a.get)

def sampleMultilevelCopiesM {M : Type u → Type v} [Monad M] {Seed : Type u}
    (C r : ℕ) (draw : M Seed) : M (Vector (MultilevelTree Seed r) C) :=
  Vector.ofFnM (fun _ : Fin C => sampleMultilevelTreeM r draw)

private lemma counter_bind {A B : Type} (x : StateM ℕ A) (f : A → StateM ℕ B) (c : ℕ) :
    (x >>= f).run c = (f (x.run c).1).run (x.run c).2 := by
  change (let (a, s) := x.run c; (f a).run s) = _
  cases x.run c
  rfl

private lemma counter_pure {A : Type} (x : A) (c : ℕ) :
    (pure x : StateM ℕ A).run c = (x,c) := rfl

lemma uniformVectorM_counter {A : Type} (draw : StateM ℕ A) (D : ℕ)
    (h : ∀ c, (draw.run c).2 = c + D) (n c : ℕ) :
    ((Vector.ofFnM (fun _ : Fin n => draw)).run c).2 = c + n * D := by
  induction n generalizing c with
  | zero =>
    rw [Vector.ofFnM_zero, counter_pure]
    simp
  | succ n ih =>
    rw [Vector.ofFnM_succ, counter_bind, counter_bind, counter_pure, h]
    change ((Vector.ofFnM (fun _ : Fin n => draw)).run c).2 + D = _
    rw [ih]
    ring

/-- Each slot accounts for one call to the draw primitive, including
slots unused by an empty-state branch. -/
theorem sampleMultilevelTreeM_counter {Seed : Type} (draw : StateM ℕ Seed) (D : ℕ)
    (h : ∀ c, (draw.run c).2 = c + D) (r c : ℕ) :
    ((sampleMultilevelTreeM r draw).run c).2 = c + multilevelSeedSlots r * D := by
  simp only [sampleMultilevelTreeM, counter_bind, counter_pure, uniformVectorM_counter draw D h]

theorem sampleMultilevelCopiesM_counter {Seed : Type} (draw : StateM ℕ Seed) (D : ℕ)
    (h : ∀ c, (draw.run c).2 = c + D) (C r c : ℕ) :
    ((sampleMultilevelCopiesM C r draw).run c).2 = c + C * multilevelSeedSlots r * D := by
  unfold sampleMultilevelCopiesM
  rw [uniformVectorM_counter _ (multilevelSeedSlots r * D) (sampleMultilevelTreeM_counter draw D h r)]
  ring

theorem sampleMultilevelCopiesM_counter_le {Seed : Type} (draw : StateM ℕ Seed) (D : ℕ)
    (h : ∀ c, (draw.run c).2 = c + D) (C r c : ℕ) :
    ((sampleMultilevelCopiesM C r draw).run c).2 ≤ c + 4 * C * 16^r * D := by
  rw [sampleMultilevelCopiesM_counter draw D h]
  calc
    _ ≤ c + C * (4 * 16^r) * D :=
      Nat.add_le_add_left (Nat.mul_le_mul_right D (Nat.mul_le_mul_left C (multilevelSeedSlots_le r))) c
    _ = _ := by ring

theorem measurePreserving_multilevelCopiesFromTape {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (C r : ℕ) :
    MeasurePreserving
      (fun (a : Fin C → Fin (multilevelSeedSlots r) → Seed) j => multilevelTreeFromTape r (a j))
      (Measure.pi (fun _ : Fin C => Measure.pi (fun _ : Fin (multilevelSeedSlots r) => μ)))
      (Measure.pi (fun _ : Fin C => multilevelTreeLaw μ r)) :=
  measurePreserving_pi _ _ (fun _ : Fin C => measurePreserving_multilevelTreeFromTape μ r)

abbrev MultilevelSeedBank (Seed : Type*) (C R : ℕ) :=
  (l : Fin (R+1)) → Fin C → MultilevelTree Seed l.val

def multilevelBankSlots (C R : ℕ) : ℕ :=
  C * ∑ l : Fin (R+1), multilevelSeedSlots l.val

def multilevelBankSlotEquiv (C R : ℕ) :
    (Σ l : Fin (R+1), Fin C × Fin (multilevelSeedSlots l.val)) ≃ Fin (multilevelBankSlots C R) :=
  ((Equiv.sigmaCongrRight (fun _ : Fin (R+1) => finProdFinEquiv)).trans finSigmaFinEquiv).trans
    (finCongr (by rw [multilevelBankSlots, Finset.mul_sum]))

def multilevelBankFromTape {Seed : Type*} (C R : ℕ)
    (tape : Fin (multilevelBankSlots C R) → Seed) : MultilevelSeedBank Seed C R :=
  fun l j => multilevelTreeFromTape l.val (fun s => tape (multilevelBankSlotEquiv C R ⟨l,j,s⟩))

/-- This tape permits a level to be chosen from data independently of
the seeds. All levels remain independent even if only one is evaluated. -/
theorem measurePreserving_multilevelBankFromTape {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (C R : ℕ) :
    MeasurePreserving (multilevelBankFromTape C R)
      (Measure.pi (fun _ : Fin (multilevelBankSlots C R) => μ))
      (Measure.pi (fun l : Fin (R+1) => Measure.pi (fun _ : Fin C => multilevelTreeLaw μ l.val))) := by
  have hRead : MeasurePreserving (fun (tape : Fin (multilevelBankSlots C R) → Seed)
      (s : Σ l : Fin (R+1), Fin C × Fin (multilevelSeedSlots l.val)) => tape (multilevelBankSlotEquiv C R s))
      (Measure.pi (fun _ : Fin (multilevelBankSlots C R) => μ))
      (Measure.pi (fun _ : Σ l : Fin (R+1), Fin C × Fin (multilevelSeedSlots l.val) => μ)) :=
    (measurePreserving_piCongrLeft (fun _ : Fin (multilevelBankSlots C R) => μ)
      (multilevelBankSlotEquiv C R)).symm
  have hGroup := measurePreserving_piCurry_const (ι := Fin (R+1))
    (κ := fun l => Fin C × Fin (multilevelSeedSlots l.val)) μ
  have hLevel (l : Fin (R+1)) :=
    (measurePreserving_multilevelCopiesFromTape μ C l.val).comp (measurePreserving_prodCurry_const μ)
  exact ((measurePreserving_pi _ _ hLevel).comp hGroup).comp hRead

def sampleMultilevelSeedBankM {M : Type u → Type v} [Monad M] {Seed : Type u}
    (C R : ℕ) (draw : M Seed) : M (MultilevelSeedBank Seed C R) := do
  let a ← Vector.ofFnM (fun _ : Fin (multilevelBankSlots C R) => draw)
  pure (multilevelBankFromTape C R a.get)

theorem sampleMultilevelSeedBankM_counter {Seed : Type} (draw : StateM ℕ Seed) (D : ℕ)
    (h : ∀ c, (draw.run c).2 = c + D) (C R c : ℕ) :
    ((sampleMultilevelSeedBankM C R draw).run c).2 = c + multilevelBankSlots C R * D := by
  simp only [sampleMultilevelSeedBankM, counter_bind, counter_pure, uniformVectorM_counter draw D h]

theorem multilevelBankSlots_le (C R : ℕ) :
    multilevelBankSlots C R ≤ 5 * C * 16^R := by
  have hs : ∑ l : Fin (R+1), multilevelSeedSlots l.val ≤ 5 * 16^R := by
    induction R with
    | zero => simp [multilevelSeedSlots_zero]
    | succ R ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      have hl := multilevelSeedSlots_le (R+1)
      rw [pow_succ] at hl ⊢
      omega
  unfold multilevelBankSlots
  calc
    _ ≤ C * (5 * 16^R) := Nat.mul_le_mul_left C hs
    _ = _ := by ring

theorem sampleMultilevelSeedBankM_counter_le {Seed : Type} (draw : StateM ℕ Seed) (D : ℕ)
    (h : ∀ c, (draw.run c).2 = c + D) (C R c : ℕ) :
    ((sampleMultilevelSeedBankM C R draw).run c).2 ≤ c + 5 * C * 16^R * D := by
  rw [sampleMultilevelSeedBankM_counter draw D h]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right D (multilevelBankSlots_le C R)) c

end ProphetSecretary.Analysis
