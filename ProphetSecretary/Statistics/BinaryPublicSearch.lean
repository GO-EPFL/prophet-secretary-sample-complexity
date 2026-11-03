import ProphetSecretary.Statistics.BinaryFairBankCall
import ProphetSecretary.Statistics.ScalarPlannerRationalQuery

/-!
# Counted binary search for public query levels

A positive rational of height (B) is at least (2^{-B}). Thus the
binary half-power search can be capped from the operand size. Its least
level also determines the least quarter-power confidence level.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability

lemma rationalHeight_ge_halfPow {q : ℚ} {B : ℕ} (hq : 0<q) (hB : RationalHeight q B) :
    (1/2 : ℚ)^B≤q := by
  have hD : (0 : ℚ)<q.den := by exact_mod_cast q.pos
  have hP : (0 : ℚ)<(2 : ℚ)^B := by positivity
  have hDB : (q.den : ℚ)≤(2 : ℚ)^B := by exact_mod_cast hB.2
  have hN : (1 : ℚ)≤q.num := by
    have h := Rat.num_pos.mpr hq
    exact_mod_cast (show (1 : ℤ)≤q.num by omega)
  rw [one_div_pow]
  calc
    _ ≤ 1/(q.den : ℚ) := (one_div_le_one_div hP hD).mpr hDB
    _ ≤ (q.num : ℚ)/(q.den : ℚ) := div_le_div_of_nonneg_right hN hD.le
    _ = q := q.num_div_den

def countedBinaryPublicHalf (q : BinaryRational) (B : ℕ) : ℕ × ℕ :=
  countedBinaryHalfSearch q 1 B

theorem countedBinaryPublicHalf_spec (q : BinaryRational) (B : ℕ)
    (hq : 0<q.value) (hB : RationalHeight q.value B) :
    let r := (countedBinaryPublicHalf q B).1
    (1/2 : ℚ)^r≤q.value ∧ (∀ j<r, q.value<(1/2 : ℚ)^j) ∧ r≤B := by
  dsimp only
  unfold countedBinaryPublicHalf
  rw [countedBinaryHalfSearch_value,BinaryRational.one_value]
  have h := countedHalfPrecisionSearch_spec q.value 1 B
  dsimp only at h
  refine ⟨?_,fun j hj => ?_,h.1⟩
  · by_cases he : (countedHalfPrecisionSearch q.value 1 B).1<B
    · simpa only [one_mul] using h.2.2.2 he
    · have hb : (countedHalfPrecisionSearch q.value 1 B).1=B := by omega
      rw [hb]
      exact rationalHeight_ge_halfPow hq hB
  · simpa only [one_mul] using h.2.2.1 j hj

lemma countedBinaryPublicHalf_work (q : BinaryRational) (B : ℕ)
    (hB : RationalHeight q.value B) :
    (countedBinaryPublicHalf q B).2≤1+B*(7000*(B+0+B+4)^3+5) :=
  countedBinaryHalfSearch_work q 1 B B 0 hB (by rw [BinaryRational.one_value]; exact rationalHeight_one)

def countedBinaryPublicQuarter (q : BinaryRational) (B : ℕ) : ℕ × ℕ :=
  let r := countedBinaryPublicHalf q B
  ((r.1+1)/2,r.2+6)

private lemma quarterPower_eq_half (k : ℕ) :
    (1/4 : ℚ)^k=(1/2 : ℚ)^(2*k) := by
  rw [pow_mul]
  norm_num

theorem countedBinaryPublicQuarter_value (q : BinaryRational) (B : ℕ)
    (hq : 0<q.value) (hB : RationalHeight q.value B) (H : ∃ j : ℕ, (1/4 : ℚ)^j≤q.value) :
    (countedBinaryPublicQuarter q B).1=(countedConfidenceLevel q.value H).1 := by
  let r := (countedBinaryPublicHalf q B).1
  let k := (r+1)/2
  have h := countedBinaryPublicHalf_spec q B hq hB
  dsimp only at h
  have hAnti := pow_right_anti₀ (by norm_num : (0 : ℚ)≤1/2) (by norm_num : (1/2 : ℚ)≤1)
  have hk : (1/4 : ℚ)^k≤q.value := by
    rw [quarterPower_eq_half]
    exact (hAnti (show r≤2*k by dsimp only [k]; omega)).trans h.1
  have hBefore (l : ℕ) (hl : l<k) : q.value<(1/4 : ℚ)^l := by
    rw [quarterPower_eq_half]
    exact h.2.1 (2*l) (by dsimp only [k] at hl; omega)
  change k=(countedConfidenceLevel q.value H).1
  rw [(countedConfidenceLevel_spec _ H).1]
  exact le_antisymm (le_of_not_gt (fun hc => (not_lt_of_ge (Nat.find_spec H)) (hBefore _ hc)))
    (Nat.find_min' H hk)

lemma countedBinaryPublicQuarter_work (q : BinaryRational) (B : ℕ)
    (hB : RationalHeight q.value B) :
    (countedBinaryPublicQuarter q B).2≤7+B*(7000*(B+0+B+4)^3+5) := by
  have h := countedBinaryPublicHalf_work q B hB
  unfold countedBinaryPublicQuarter
  dsimp only
  omega

lemma binaryStoredWidth_height (q : BinaryRational) : RationalHeight q.value q.storage.width := by
  have h (a : ℕ) : a≤2^a.bits.length := by
    have h := Nat.size_le.mp (show a.size≤a.size from le_rfl)
    rw [Nat.size_eq_bits_len]
    exact h.le
  rw [q.canonical]
  exact ⟨(h _).trans (Nat.pow_le_pow_right (by decide) (le_max_left _ _)),
    (h _).trans (Nat.pow_le_pow_right (by decide) (le_max_right _ _))⟩

structure BinaryPublicSearchResult where
  level : ℕ
  precision : ℕ
  halfCopies : ℕ
  work : ℕ

def countedBinaryPublicSearch (rho delta p : BinaryRational) : BinaryPublicSearchResult :=
  let r := countedBinaryPublicHalf rho rho.storage.width
  let b := countedBinaryPublicQuarter delta delta.storage.width
  let k := countedBinaryPublicQuarter p p.storage.width
  ⟨r.1,2*b.1+1,k.1,r.2+b.2+k.2+4*(rho.storage.width+delta.storage.width+p.storage.width)+20⟩

theorem countedBinaryPublicSearch_spec (rho delta p : BinaryRational)
    (hr : 0<rho.value) (hb : 0<delta.value) (hp : 0<p.value)
    (HB : ∃ j : ℕ, (1/4 : ℚ)^j≤delta.value) (HP : ∃ j : ℕ, (1/4 : ℚ)^j≤p.value) :
    let q := countedBinaryPublicSearch rho delta p
    (1/2 : ℚ)^q.level≤rho.value ∧ (∀ j<q.level, rho.value<(1/2 : ℚ)^j) ∧
      q.precision=2*(countedConfidenceLevel delta.value HB).1+1 ∧
      q.halfCopies=(countedConfidenceLevel p.value HP).1 := by
  have h := countedBinaryPublicHalf_spec rho rho.storage.width hr (binaryStoredWidth_height rho)
  dsimp only at h ⊢
  unfold countedBinaryPublicSearch
  dsimp only
  exact ⟨h.1,h.2.1,
    by rw [countedBinaryPublicQuarter_value delta _ hb (binaryStoredWidth_height delta) HB],
    countedBinaryPublicQuarter_value p _ hp (binaryStoredWidth_height p) HP⟩

def binaryPublicSearchWorkBound (B : ℕ) : ℕ :=
  3*(B+1)*(7000*(2*(B+1)+4)^3+5)+12*(B+1)+35

theorem countedBinaryPublicSearch_work (rho delta p : BinaryRational) (B : ℕ)
    (hr : RationalHeight rho.value B) (hb : RationalHeight delta.value B) (hp : RationalHeight p.value B) :
    (countedBinaryPublicSearch rho delta p).work≤binaryPublicSearchWorkBound B := by
  let Q := B+1
  let W := Q*(7000*(2*Q+4)^3+5)
  have hrW := BinaryRational.storage_width rho B hr
  have hbW := BinaryRational.storage_width delta B hb
  have hpW := BinaryRational.storage_width p B hp
  have hBound (w : ℕ) (hw : w≤Q) : w*(7000*(w+0+w+4)^3+5)≤W := by
    apply Nat.mul_le_mul hw
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_left (by omega) _
  have hR := (countedBinaryPublicHalf_work rho rho.storage.width (binaryStoredWidth_height rho)).trans
    (Nat.add_le_add_left (hBound _ hrW) 1)
  have hB := (countedBinaryPublicQuarter_work delta delta.storage.width (binaryStoredWidth_height delta)).trans
    (Nat.add_le_add_left (hBound _ hbW) 7)
  have hP := (countedBinaryPublicQuarter_work p p.storage.width (binaryStoredWidth_height p)).trans
    (Nat.add_le_add_left (hBound _ hpW) 7)
  change (countedBinaryPublicHalf rho rho.storage.width).2+
    (countedBinaryPublicQuarter delta delta.storage.width).2+
    (countedBinaryPublicQuarter p p.storage.width).2+
    4*(rho.storage.width+delta.storage.width+p.storage.width)+20≤_
  have he : binaryPublicSearchWorkBound B=3*W+12*Q+35 := by
    unfold binaryPublicSearchWorkBound
    dsimp only [W,Q]
    ring
  rw [he]
  omega

end ProphetSecretary.Statistics.Calibration
