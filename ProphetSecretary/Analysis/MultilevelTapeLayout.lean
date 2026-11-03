import ProphetSecretary.Analysis.MultilevelSeedTape

/-!
# Computed tape offsets

The layout stores the offsets of every level group before evaluating
any recursive estimator. A child view keeps an absolute origin in the
original array, so reading its next transition needs no ancestor scan.
-/

open scoped BigOperators
open MeasureTheory

namespace ProphetSecretary.Analysis

private def countedNatTapeSum {n : ℕ} (f : Fin n → ℕ × ℕ) : ℕ × ℕ :=
  let q := List.ofFn f
  ((q.map Prod.fst).sum, (q.map Prod.snd).sum + 5*n+2)

private lemma countedNatTapeSum_value {n : ℕ} (f : Fin n → ℕ × ℕ) :
    (countedNatTapeSum f).1 = ∑ j, (f j).1 := by
  simp [countedNatTapeSum, List.map_ofFn, List.sum_ofFn, Function.comp_def]

private lemma countedNatTapeSum_work {n : ℕ} (f : Fin n → ℕ × ℕ) :
    (countedNatTapeSum f).2 = (∑ j, (f j).2) + 5*n+2 := by
  simp [countedNatTapeSum, List.map_ofFn, List.sum_ofFn, Function.comp_def]

private def countedTapePower : ℕ → ℕ × ℕ
  | 0 => (1,1)
  | r+1 =>
    let q := countedTapePower r
    (4*q.1, q.2+2)

private lemma countedTapePower_spec (r : ℕ) :
    countedTapePower r = (4^r, 2*r+1) := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [countedTapePower, ih, pow_succ]; congr 1; omega

private def countedGroupWidth (d j : ℕ) (kind : Fin 3) : ℕ × ℕ :=
  let q := countedTapePower (d-j)
  let s := multilevelSeedSlotPair (j+1)
  let t := multilevelSeedSlotPair j
  let w := if kind = 0 then q.1 else q.1 * (if kind = 1 then s.1.1 else t.1.1)
  (w, q.2 + s.2 + t.2 + 7)

private def groupWidth (d j : ℕ) (kind : Fin 3) : ℕ :=
  4^(d-j) * (if kind = 0 then 1 else if kind = 1 then multilevelSeedSlots (j+1) else multilevelSeedSlots j)

private lemma countedGroupWidth_value (d j : ℕ) (kind : Fin 3) :
    (countedGroupWidth d j kind).1 = groupWidth d j kind := by
  by_cases h : kind = 0 <;> simp [countedGroupWidth, groupWidth, countedTapePower_spec, h, multilevelSeedSlots]

private lemma countedGroupWidth_work (d j : ℕ) (kind : Fin 3) (hj : j ≤ d) :
    (countedGroupWidth d j kind).2 ≤ 30*(d+1) := by
  simp only [countedGroupWidth, countedTapePower_spec, multilevelSeedSlotPair_work]
  omega

private def countedGroupPrefix (d l : ℕ) (kind : Fin 3) : ℕ × ℕ :=
  countedNatTapeSum (fun j : Fin l => countedGroupWidth d j.val kind)

private lemma countedGroupPrefix_value (d l : ℕ) (kind : Fin 3) :
    (countedGroupPrefix d l kind).1 = ∑ j : Fin l, groupWidth d j.val kind := by
  simp only [countedGroupPrefix, countedNatTapeSum_value, countedGroupWidth_value]

private lemma countedGroupPrefix_work (d l : ℕ) (kind : Fin 3) (hl : l ≤ d) :
    (countedGroupPrefix d l kind).2 ≤ 40*(d+1)^2 := by
  rw [countedGroupPrefix, countedNatTapeSum_work]
  have hs : ∑ j : Fin l, (countedGroupWidth d j.val kind).2 ≤ l * (30*(d+1)) := by
    calc
      _ ≤ ∑ _j : Fin l, 30*(d+1) := Finset.sum_le_sum fun j _ =>
        countedGroupWidth_work d j.val kind (j.isLt.le.trans hl)
      _ = _ := by simp
  nlinarith [Nat.mul_le_mul_right (d+1) hl]

structure MultilevelTapeColumn where
  transition : ℕ
  upper : ℕ
  lower : ℕ
  upperWidth : ℕ
  lowerWidth : ℕ

private def countedTapeColumn (d j b tr up : ℕ) : MultilevelTapeColumn × ℕ :=
  let t := countedGroupPrefix d j 0
  let u := countedGroupPrefix d j 1
  let l := countedGroupPrefix d j 2
  let s := multilevelSeedSlotPair j
  (⟨b+t.1, b+tr+u.1, b+tr+up+l.1, s.1.2, s.1.1⟩, t.2+u.2+l.2+s.2+10)

private lemma countedTapeColumn_work (d j b tr up : ℕ) (hj : j ≤ d) :
    (countedTapeColumn d j b tr up).2 ≤ 150*(d+1)^2 := by
  have ht := countedGroupPrefix_work d j 0 hj
  have hu := countedGroupPrefix_work d j 1 hj
  have hl := countedGroupPrefix_work d j 2 hj
  dsimp only [countedTapeColumn]
  rw [multilevelSeedSlotPair_work]
  nlinarith

/-- Row d stores the group offsets for level d+1. -/
def countedMultilevelTapeRow (R d : ℕ) : Vector MultilevelTapeColumn (R+1) × ℕ :=
  let b := countedTapePower (d+1)
  let tr := countedGroupPrefix d d 0
  let up := countedGroupPrefix d d 1
  let q := Vector.ofFn (fun j : Fin (R+1) => if j.val < d then
      countedTapeColumn d j.val b.1 tr.1 up.1 else (⟨0,0,0,0,0⟩,1))
  (q.map Prod.fst, (∑ j : Fin (R+1), (q.get j).2) + b.2 + tr.2 + up.2 + 4*(R+1)+3)

def countedMultilevelTapeLayout (R : ℕ) :
    Vector (Vector MultilevelTapeColumn (R+1)) (R+1) × ℕ :=
  let q := Vector.ofFn (fun d : Fin (R+1) => countedMultilevelTapeRow R d.val)
  (q.map Prod.fst, (∑ d : Fin (R+1), (q.get d).2) + 4*(R+1)+1)

private lemma tapeVectorGet_ofFn {A : Type*} {d : ℕ} (f : Fin d → A) (i : Fin d) :
    (Vector.ofFn f).get i = f i := by
  simp [Vector.get]

private lemma tapeVectorGet_map {A B : Type*} {d : ℕ} (f : A → B) (x : Vector A d) (i : Fin d) :
    (x.map f).get i = f (x.get i) := by
  simp [Vector.get]

lemma countedMultilevelTapeRow_work (R d : ℕ) (hd : d ≤ R) :
    (countedMultilevelTapeRow R d).2 ≤ 300*(R+1)^3 := by
  have hEach (j : Fin (R+1)) :
      (if j.val < d then countedTapeColumn d j.val (countedTapePower (d+1)).1
        (countedGroupPrefix d d 0).1 (countedGroupPrefix d d 1).1
      else (⟨0,0,0,0,0⟩,1)).2 ≤ 150*(R+1)^2 := by
    split_ifs with h
    · exact (countedTapeColumn_work _ _ _ _ _ h.le).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
    · have := Nat.one_le_pow 2 (R+1) (by omega)
      omega
  have hs : (∑ j : Fin (R+1), (if j.val < d then countedTapeColumn d j.val (countedTapePower (d+1)).1
        (countedGroupPrefix d d 0).1 (countedGroupPrefix d d 1).1
      else (⟨0,0,0,0,0⟩,1)).2) ≤ (R+1)*(150*(R+1)^2) := by
    calc
      _ ≤ ∑ _j : Fin (R+1), 150*(R+1)^2 := Finset.sum_le_sum fun j _ => hEach j
      _ = _ := by simp
  have ht := countedGroupPrefix_work d d 0 le_rfl
  have hu := countedGroupPrefix_work d d 1 le_rfl
  have hSq : (d+1)^2 ≤ (R+1)^2 := Nat.pow_le_pow_left (by omega) 2
  simp only [countedMultilevelTapeRow, tapeVectorGet_ofFn, countedTapePower_spec] at hs ⊢
  nlinarith

theorem countedMultilevelTapeLayout_work (R : ℕ) :
    (countedMultilevelTapeLayout R).2 ≤ 310*(R+1)^4 := by
  have hs : ∑ d : Fin (R+1), (countedMultilevelTapeRow R d.val).2 ≤ (R+1)*(300*(R+1)^3) := by
    calc
      _ ≤ ∑ _d : Fin (R+1), 300*(R+1)^3 := Finset.sum_le_sum fun d _ =>
        countedMultilevelTapeRow_work R d.val (by omega)
      _ = _ := by simp
  simp only [countedMultilevelTapeLayout, tapeVectorGet_ofFn]
  nlinarith [Nat.zero_le (R^4), Nat.zero_le (R^3), Nat.zero_le (R^2)]

abbrev MultilevelTapeLayout (R : ℕ) := Vector (Vector MultilevelTapeColumn (R+1)) (R+1)

private def tapeColumnAt {R d : ℕ} (q : MultilevelTapeLayout R) (hd : d ≤ R) (l : Fin d) :
    MultilevelTapeColumn :=
  (q.get ⟨d, by omega⟩).get (l.castLE (by omega))

private lemma tapeColumnAt_value {R d : ℕ} (hd : d ≤ R) (l : Fin d) :
    tapeColumnAt (countedMultilevelTapeLayout R).1 hd l =
      (countedTapeColumn d l.val (4^(d+1))
        (∑ j : Fin d, groupWidth d j.val 0) (∑ j : Fin d, groupWidth d j.val 1)).1 := by
  simp only [tapeColumnAt, countedMultilevelTapeLayout, countedMultilevelTapeRow,
    tapeVectorGet_map, tapeVectorGet_ofFn, Fin.val_castLE, l.isLt, if_true,
    countedTapePower_spec, countedGroupPrefix_value]

/-- Local addressing uses two array lookups and a fixed number of
integer operations. -/
def countedMultilevelLocalAddress {R d : ℕ} (q : MultilevelTapeLayout R)
    (hd : d ≤ R) : MultilevelNodeSlot d → ℕ × ℕ
  | .inl j => (j.val, 1)
  | .inr (.inl ⟨l,j⟩) =>
    let a := tapeColumnAt q hd l
    (a.transition + j.val, 7)
  | .inr (.inr (.inl ⟨l,j,s⟩)) =>
    let a := tapeColumnAt q hd l
    (a.upper + a.upperWidth * j.val + s.val, 9)
  | .inr (.inr (.inr ⟨l,j,s⟩)) =>
    let a := tapeColumnAt q hd l
    (a.lower + a.lowerWidth * j.val + s.val, 9)

lemma countedMultilevelLocalAddress_work {R d : ℕ} (q : MultilevelTapeLayout R)
    (hd : d ≤ R) (j : MultilevelNodeSlot d) :
    (countedMultilevelLocalAddress q hd j).2 ≤ 9 := by
  rcases j with j | (⟨l,j⟩ | (⟨l,j,s⟩ | ⟨l,j,s⟩)) <;> simp [countedMultilevelLocalAddress]

lemma countedMultilevelLocalAddress_value {R d : ℕ} (hd : d ≤ R) (j : MultilevelNodeSlot d) :
    (countedMultilevelLocalAddress (countedMultilevelTapeLayout R).1 hd j).1 =
      (multilevelNodeSlotEquiv d j).val := by
  rcases j with j | (⟨l,j⟩ | (⟨l,j,s⟩ | ⟨l,j,s⟩))
  · rfl
  · change _ = 4^(d+1) + (finSigmaFinEquiv (n := MultilevelGroupSize d) ⟨l,j⟩).val
    simp [countedMultilevelLocalAddress, tapeColumnAt_value, countedTapeColumn,
      countedGroupPrefix_value, groupWidth, MultilevelGroupSize, Nat.add_assoc]
  · change _ = 4^(d+1) + ((∑ k : Fin d, MultilevelGroupSize d k) +
      (finSigmaFinEquiv (n := fun k => MultilevelGroupSize d k * multilevelSeedSlots (k.val+1))
        ⟨l,finProdFinEquiv (j,s)⟩).val)
    have h10 : (1 : Fin 3) ≠ 0 := by decide
    simp [countedMultilevelLocalAddress, tapeColumnAt_value, countedTapeColumn,
      countedGroupPrefix_value, groupWidth, MultilevelGroupSize, h10]
    rw [show (multilevelSeedSlotPair l.val).1.2 = multilevelSeedSlots (1+l.val) by
      rw [Nat.add_comm]; rfl]
    ac_rfl
  · change _ = 4^(d+1) + ((∑ k : Fin d, MultilevelGroupSize d k) +
      ((∑ k : Fin d, MultilevelGroupSize d k * multilevelSeedSlots (k.val+1)) +
        (finSigmaFinEquiv (n := fun k => MultilevelGroupSize d k * multilevelSeedSlots k.val)
          ⟨l,finProdFinEquiv (j,s)⟩).val))
    have h10 : (1 : Fin 3) ≠ 0 := by decide
    have h20 : (2 : Fin 3) ≠ 0 := by decide
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    simp [countedMultilevelLocalAddress, tapeColumnAt_value, countedTapeColumn,
      countedGroupPrefix_value, groupWidth, MultilevelGroupSize, h10, h20, h21]
    unfold multilevelSeedSlots
    ring_nf

def countedMultilevelChildOrigin {R d : ℕ} (q : MultilevelTapeLayout R) (hd : d ≤ R)
    (origin : ℕ) (l : Fin d) (j : Fin (MultilevelGroupSize d l)) (upper : Bool) : ℕ × ℕ :=
  let a := tapeColumnAt q hd l
  let width := if upper then a.upperWidth else a.lowerWidth
  let block := if upper then a.upper else a.lower
  (origin + (block + width * j.val), 10)

lemma countedMultilevelChildOrigin_work {R d : ℕ} (q : MultilevelTapeLayout R) (hd : d ≤ R)
    (origin : ℕ) (l : Fin d) (j : Fin (MultilevelGroupSize d l)) (upper : Bool) :
    (countedMultilevelChildOrigin q hd origin l j upper).2 = 10 := rfl

private lemma upperTapeOrigin_value {R d : ℕ} (hd : d ≤ R) (origin : ℕ) (l : Fin d)
    (j : Fin (MultilevelGroupSize d l)) (s : Fin (multilevelSeedSlots (l.val+1))) :
    (countedMultilevelChildOrigin (countedMultilevelTapeLayout R).1 hd origin l j true).1 + s.val =
      origin + (multilevelNodeSlotEquiv d (.inr (.inr (.inl ⟨l,j,s⟩)))).val := by
  rw [← countedMultilevelLocalAddress_value hd]
  simp [countedMultilevelChildOrigin, countedMultilevelLocalAddress, Nat.add_assoc]

private lemma lowerTapeOrigin_value {R d : ℕ} (hd : d ≤ R) (origin : ℕ) (l : Fin d)
    (j : Fin (MultilevelGroupSize d l)) (s : Fin (multilevelSeedSlots l.val)) :
    (countedMultilevelChildOrigin (countedMultilevelTapeLayout R).1 hd origin l j false).1 + s.val =
      origin + (multilevelNodeSlotEquiv d (.inr (.inr (.inr ⟨l,j,s⟩)))).val := by
  rw [← countedMultilevelLocalAddress_value hd]
  simp [countedMultilevelChildOrigin, countedMultilevelLocalAddress, Nat.add_assoc]

def countedMultilevelTapeRead {Seed : Type*} {R d S : ℕ} (q : MultilevelTapeLayout R)
    (hq : q = (countedMultilevelTapeLayout R).1) (hd : d ≤ R) (tape : Fin S → Seed)
    (origin : ℕ) (hBound : ∀ a : Fin (multilevelSeedSlots (d+1)), origin + a.val < S)
    (i : MultilevelNodeSlot d) : Seed × ℕ :=
  let p := countedMultilevelLocalAddress q hd i
  let idx : Fin S := ⟨origin + p.1, by
    dsimp only [p]
    rw [hq, countedMultilevelLocalAddress_value]
    exact hBound _⟩
  (tape idx, p.2+3)

lemma countedMultilevelTapeRead_work {Seed : Type*} {R d S : ℕ} (q : MultilevelTapeLayout R)
    (hq : q = (countedMultilevelTapeLayout R).1) (hd : d ≤ R) (tape : Fin S → Seed)
    (origin : ℕ) (hBound : ∀ a : Fin (multilevelSeedSlots (d+1)), origin + a.val < S)
    (i : MultilevelNodeSlot d) :
    (countedMultilevelTapeRead q hq hd tape origin hBound i).2 ≤ 12 := by
  exact Nat.add_le_add_right (countedMultilevelLocalAddress_work q hd i) 3

private lemma countedMultilevelTapeRead_value {Seed : Type*} {R d S : ℕ} (q : MultilevelTapeLayout R)
    (hq : q = (countedMultilevelTapeLayout R).1) (hd : d ≤ R) (tape : Fin S → Seed)
    (origin : ℕ) (hBound : ∀ a : Fin (multilevelSeedSlots (d+1)), origin + a.val < S)
    (i : MultilevelNodeSlot d) :
    (countedMultilevelTapeRead q hq hd tape origin hBound i).1 =
      tape ⟨origin + (multilevelNodeSlotEquiv d i).val, hBound _⟩ := by
  subst q
  unfold countedMultilevelTapeRead
  apply congrArg tape
  apply Fin.ext
  exact congrArg (origin + ·) (countedMultilevelLocalAddress_value hd i)

def multilevelTreeAtTapeOrigin {Seed : Type*} {R S : ℕ} (q : MultilevelTapeLayout R)
    (hq : q = (countedMultilevelTapeLayout R).1) (tape : Fin S → Seed) :
    (r : ℕ) → r ≤ R → (origin : ℕ) →
      (∀ a : Fin (multilevelSeedSlots r), origin+a.val < S) → MultilevelTree Seed r
  | 0, _, _, _ => .zero
  | d+1, hr, origin, hBound =>
    let hd : d ≤ R := by omega
    let read := countedMultilevelTapeRead q hq hd tape origin hBound
    .node (fun j => (read (.inl j)).1) (fun l j => (read (.inr (.inl ⟨l,j⟩))).1)
      (fun l j =>
        let child := (countedMultilevelChildOrigin q hd origin l j true).1
        multilevelTreeAtTapeOrigin q hq tape (l.val+1) (by have := l.isLt; omega) child (by
          intro s
          dsimp only [child]
          rw [hq, upperTapeOrigin_value]
          exact hBound _))
      (fun l j =>
        let child := (countedMultilevelChildOrigin q hd origin l j false).1
        multilevelTreeAtTapeOrigin q hq tape l.val (by have := l.isLt; omega) child (by
          intro s
          dsimp only [child]
          rw [hq, lowerTapeOrigin_value]
          exact hBound _))
termination_by r _ _ _ => r
decreasing_by all_goals have := l.isLt; omega

theorem multilevelTreeAtTapeOrigin_eq {Seed : Type*} {R S : ℕ} (q : MultilevelTapeLayout R)
    (hq : q = (countedMultilevelTapeLayout R).1) (tape : Fin S → Seed)
    (r : ℕ) (hr : r ≤ R) (origin : ℕ)
    (hBound : ∀ a : Fin (multilevelSeedSlots r), origin+a.val < S) :
    multilevelTreeAtTapeOrigin q hq tape r hr origin hBound =
      multilevelTreeFromTape r (fun j => tape ⟨origin+j.val,hBound j⟩) := by
  subst q
  induction r using Nat.strong_induction_on generalizing origin with
  | h r ih =>
    cases r with
    | zero => rw [multilevelTreeAtTapeOrigin, multilevelTreeFromTape]
    | succ d =>
      rw [multilevelTreeAtTapeOrigin, multilevelTreeFromTape]
      congr 1
      · funext l j
        apply countedMultilevelTapeRead_value
      · funext l j
        dsimp only
        rw [ih (l.val+1) (by have := l.isLt; omega)]
        congr 1
        funext s
        apply congrArg tape
        apply Fin.ext
        apply upperTapeOrigin_value
      · funext l j
        dsimp only
        rw [ih l.val (by have := l.isLt; omega)]
        congr 1
        funext s
        apply congrArg tape
        apply Fin.ext
        apply lowerTapeOrigin_value

private def countedBankPrefix (C l : ℕ) : ℕ × ℕ :=
  countedNatTapeSum (fun j : Fin l =>
    let q := multilevelSeedSlotPair j.val
    (C*q.1.1,q.2+3))

private lemma countedBankPrefix_value (C l : ℕ) :
    (countedBankPrefix C l).1 = ∑ j : Fin l, C * multilevelSeedSlots j.val := by
  rw [countedBankPrefix, countedNatTapeSum_value]
  rfl

private lemma countedBankPrefix_work (C l : ℕ) :
    (countedBankPrefix C l).2 ≤ 20*(l+1)^2 := by
  rw [countedBankPrefix, countedNatTapeSum_work]
  have h : ∑ j : Fin l, ((multilevelSeedSlotPair j.val).2+3) ≤ l*(6*l+4) := by
    calc
      _ ≤ ∑ _j : Fin l, (6*l+4) := Finset.sum_le_sum fun j _ => by
        rw [multilevelSeedSlotPair_work]
        have := j.isLt
        omega
      _ = _ := by simp
  dsimp only
  nlinarith

private def countedBankRow (C l : ℕ) : (ℕ × ℕ) × ℕ :=
  let p := countedBankPrefix C l
  let q := multilevelSeedSlotPair l
  ((p.1,q.1.1),p.2+q.2+2)

def countedBankOffsets (C R : ℕ) : Vector (ℕ × ℕ) (R+1) × ℕ :=
  let rows := Vector.ofFn (fun l : Fin (R+1) => countedBankRow C l.val)
  (rows.map Prod.fst,(∑ l : Fin (R+1), (rows.get l).2)+4*(R+1)+1)

lemma countedBankOffsets_work (C R : ℕ) :
    (countedBankOffsets C R).2 ≤ 40*(R+1)^3 := by
  have hs : ∑ l : Fin (R+1), (countedBankRow C l.val).2 ≤ (R+1)*(30*(R+1)^2) := by
    calc
      _ ≤ ∑ _l : Fin (R+1), 30*(R+1)^2 := Finset.sum_le_sum fun l _ => by
        have hp := countedBankPrefix_work C l.val
        have hs : (l.val+1)^2 ≤ (R+1)^2 := Nat.pow_le_pow_left l.isLt 2
        dsimp only [countedBankRow]
        rw [multilevelSeedSlotPair_work]
        have := l.isLt
        nlinarith
      _ = _ := by simp
  simp only [countedBankOffsets, tapeVectorGet_ofFn]
  nlinarith

def countedBankOrigin {C R : ℕ} (offsets : Vector (ℕ × ℕ) (R+1))
    (l : Fin (R+1)) (j : Fin C) : ℕ × ℕ :=
  let a := offsets.get l
  (a.1+a.2*j.val, 5)

private lemma countedBankOrigin_value {C R : ℕ} (l : Fin (R+1)) (j : Fin C)
    (s : Fin (multilevelSeedSlots l.val)) :
    (countedBankOrigin (countedBankOffsets C R).1 l j).1 + s.val =
      (multilevelBankSlotEquiv C R ⟨l,j,s⟩).val := by
  change _ = (finSigmaFinEquiv (n := fun k : Fin (R+1) => C * multilevelSeedSlots k.val)
    ⟨l,finProdFinEquiv (j,s)⟩).val
  rw [finSigmaFinEquiv_apply]
  simp [countedBankOrigin, countedBankOffsets, countedBankRow, tapeVectorGet_ofFn,
    countedBankPrefix_value]
  unfold multilevelSeedSlots
  omega

/-- Precompute the small tables once. Each tree in the bank then uses
constant-length arithmetic to obtain its absolute origin. -/
def countedMultilevelBankFromTape {Seed : Type*} (C R : ℕ)
    (tape : Fin (multilevelBankSlots C R) → Seed) : MultilevelSeedBank Seed C R × ℕ :=
  let q := countedMultilevelTapeLayout R
  let offsets := countedBankOffsets C R
  (fun l j =>
    let origin := (countedBankOrigin offsets.1 l j).1
    multilevelTreeAtTapeOrigin q.1 rfl tape l.val (by omega) origin (by
      intro s
      dsimp only [origin, offsets]
      rw [countedBankOrigin_value]
      exact (multilevelBankSlotEquiv C R ⟨l,j,s⟩).isLt),
    q.2+offsets.2+5)

theorem countedMultilevelBankFromTape_value {Seed : Type*} (C R : ℕ)
    (tape : Fin (multilevelBankSlots C R) → Seed) :
    (countedMultilevelBankFromTape C R tape).1 = multilevelBankFromTape C R tape := by
  funext l j
  dsimp only [countedMultilevelBankFromTape, multilevelBankFromTape]
  rw [multilevelTreeAtTapeOrigin_eq]
  congr 1
  funext s
  apply congrArg tape
  apply Fin.ext
  exact countedBankOrigin_value l j s

theorem countedMultilevelBankFromTape_work {Seed : Type*} (C R : ℕ)
    (tape : Fin (multilevelBankSlots C R) → Seed) :
    (countedMultilevelBankFromTape C R tape).2 ≤ 360*(R+1)^4 := by
  have h1 := countedMultilevelTapeLayout_work R
  have h2 := countedBankOffsets_work C R
  dsimp only [countedMultilevelBankFromTape]
  nlinarith [Nat.zero_le (R^4), Nat.zero_le (R^3), Nat.zero_le (R^2)]

theorem measurePreserving_countedMultilevelBankFromTape {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (C R : ℕ) :
    MeasurePreserving (fun tape => (countedMultilevelBankFromTape C R tape).1)
      (Measure.pi (fun _ : Fin (multilevelBankSlots C R) => μ))
      (Measure.pi (fun l : Fin (R+1) => Measure.pi (fun _ : Fin C => multilevelTreeLaw μ l.val))) := by
  simp_rw [countedMultilevelBankFromTape_value]
  exact measurePreserving_multilevelBankFromTape μ C R

def countedMultilevelBankSize (C R : ℕ) : ℕ × ℕ := countedBankPrefix C (R+1)

lemma countedMultilevelBankSize_value (C R : ℕ) :
    (countedMultilevelBankSize C R).1 = multilevelBankSlots C R := by
  rw [countedMultilevelBankSize, countedBankPrefix_value, multilevelBankSlots, Finset.mul_sum]

lemma countedMultilevelBankSize_work (C R : ℕ) :
    (countedMultilevelBankSize C R).2 ≤ 80*(R+1)^2 := by
  have h := countedBankPrefix_work C (R+1)
  unfold countedMultilevelBankSize
  calc
    _ ≤ 20 * (R+1+1)^2 := h
    _ ≤ 20 * (2*(R+1))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    _ = _ := by ring

universe u v

/-- The tape allocator fills a single array. Its work includes layout
construction and array writes; the draw primitive has its own counter. -/
def sampleCountedMultilevelSeedBankM {M : Type u → Type v} [Monad M] {Seed : Type u}
    (C R : ℕ) (draw : M Seed) : M (MultilevelSeedBank Seed C R × ℕ) := do
  let size := countedMultilevelBankSize C R
  let tape ← Vector.ofFnM (fun _ : Fin size.1 => draw)
  let bank := countedMultilevelBankFromTape C R (fun i =>
    tape.get (Fin.cast (countedMultilevelBankSize_value C R).symm i))
  pure (bank.1, bank.2+size.2+3*size.1+5)

private lemma tapeCounter_bind {A B : Type} (x : StateM ℕ A) (f : A → StateM ℕ B) (c : ℕ) :
    (x >>= f).run c = (f (x.run c).1).run (x.run c).2 := by
  change (let (a,s) := x.run c; (f a).run s) = _
  cases x.run c
  rfl

private lemma tapeCounter_pure {A : Type} (x : A) (c : ℕ) :
    (pure x : StateM ℕ A).run c = (x,c) := rfl

theorem sampleCountedMultilevelSeedBankM_counter {Seed : Type}
    (draw : StateM ℕ Seed) (D : ℕ) (h : ∀ c, (draw.run c).2 = c+D) (C R c : ℕ) :
    ((sampleCountedMultilevelSeedBankM C R draw).run c).2 = c + multilevelBankSlots C R*D := by
  simp only [sampleCountedMultilevelSeedBankM, tapeCounter_bind, tapeCounter_pure,
    uniformVectorM_counter draw D h, countedMultilevelBankSize_value]

theorem sampleCountedMultilevelSeedBankM_work {Seed : Type}
    (draw : StateM ℕ Seed) (C R c : ℕ) :
    ((sampleCountedMultilevelSeedBankM C R draw).run c).1.2 ≤
      450*(R+1)^4 + 15*C*16^R := by
  let size := countedMultilevelBankSize C R
  let tape := ((Vector.ofFnM (fun _ : Fin size.1 => draw)).run c).1
  let read := fun i : Fin (multilevelBankSlots C R) =>
    tape.get (Fin.cast (countedMultilevelBankSize_value C R).symm i)
  have h1 := countedMultilevelBankFromTape_work C R read
  have h2 : size.2 ≤ 80*(R+1)^2 := countedMultilevelBankSize_work C R
  have h3 : size.1 ≤ 5*C*16^R := (countedMultilevelBankSize_value C R).le.trans (multilevelBankSlots_le C R)
  simp only [sampleCountedMultilevelSeedBankM, tapeCounter_bind, tapeCounter_pure]
  change (countedMultilevelBankFromTape C R read).2 + size.2 + 3*size.1 + 5 ≤ _
  have h4 : 360*(R+1)^4 + 80*(R+1)^2 + 5 ≤ 450*(R+1)^4 := by
    nlinarith [Nat.zero_le (R^4), Nat.zero_le (R^3), Nat.zero_le (R^2)]
  rw [show 15*C*16^R = 3*(5*C*16^R) by ring]
  omega

/-- A full traversal charges one node view, each tape read, and the two
absolute origins in each pair. Early returns use at most this work. -/
def multilevelTapeTraversalWork {Seed : Type*} : (r : ℕ) → MultilevelTree Seed r → ℕ
  | 0, .zero => 1
  | d+1, .node _ _ up lo =>
    1 + 12 * 4^(d+1) + ∑ l : Fin d, ∑ j : Fin (MultilevelGroupSize d l),
      (32 + multilevelTapeTraversalWork (l.val+1) (up l j) + multilevelTapeTraversalWork l.val (lo l j))
termination_by r => r
decreasing_by all_goals have := l.isLt; omega

theorem multilevelTapeTraversalWork_le {Seed : Type*} (r : ℕ) (t : MultilevelTree Seed r) :
    multilevelTapeTraversalWork r t ≤ 32 * multilevelTreeWork r t := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases t with
    | zero => simp [multilevelTapeTraversalWork, multilevelTreeWork]
    | @node d b tr up lo =>
      simp only [multilevelTapeTraversalWork, multilevelTreeWork, Nat.mul_add, Finset.mul_sum]
      apply Nat.add_le_add
      · omega
      · apply Finset.sum_le_sum
        intro l _
        apply Finset.sum_le_sum
        intro j _
        have hu := ih (l.val+1) (by have := l.isLt; omega) (up l j)
        have hl := ih l.val (by have := l.isLt; omega) (lo l j)
        omega

end ProphetSecretary.Analysis
