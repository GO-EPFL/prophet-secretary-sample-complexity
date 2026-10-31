import ProphetSecretary.Limiting.CountableValuePolicy
import ProphetSecretary.Limiting.CountableMaskOrder
import ProphetSecretary.Limiting.CountableHorizonOrder
import ProphetSecretary.Limiting.CountableHorizonSecant

/-!
# Analytical whole-clock profiles of the countable rule

At each time the clock mask contains exactly the identities not yet observed.
Whole clock vectors are analytical parameters for null-set comparisons; the
actual callback receives only its observed history. Additional elapsed time
removes unseen options and reduces the remaining horizon.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal Classical

namespace ProphetSecretary.Limiting
open CountableInstance

noncomputable def clockMask (clocks : ℕ → ℝ) (t : ℝ) : IndividualMask :=
  unseenMask (individualHistory (fun _ => 0) clocks t)

def candidateMask (keep : IndividualMask) (candidate : Option ℕ) : IndividualMask :=
  candidate.elim keep (fun i => eraseMask keep i)

lemma maskLe_eraseMask {left right : IndividualMask} (h : MaskLe left right) (i : ℕ) :
    MaskLe (eraseMask left i) (eraseMask right i) := by
  intro j hj
  by_cases hji : j = i
  · subst j
    simp only [eraseMask,Function.update_self,reduceCtorEq] at hj
  · have hj' : left j = true := by simpa only [eraseMask,Function.update_of_ne hji] using hj
    simpa only [eraseMask,Function.update_of_ne hji] using h j hj'

lemma maskLe_candidateMask {left right : IndividualMask} (h : MaskLe left right) (candidate : Option ℕ) :
    MaskLe (candidateMask left candidate) (candidateMask right candidate) := by
  cases candidate with
  | none => exact h
  | some i => exact maskLe_eraseMask h i

lemma clockMask_antitone (clocks : ℕ → ℝ) {s t : ℝ} (hst : s ≤ t) : MaskLe (clockMask clocks t) (clockMask clocks s) := by
  intro i hi
  have hi' : decide (t ≤ clocks i) = true := by
    simpa only [clockMask,unseenMask_individualHistory] using hi
  change unseenMask (individualHistory (fun _ => 0) clocks s) i = true
  rw [unseenMask_individualHistory]
  exact decide_eq_true (hst.trans (of_decide_eq_true hi'))

lemma measurable_clockMask : Measurable (fun z : (ℕ → ℝ) × ℝ => clockMask z.1 z.2) :=
  measurable_unseenMask.comp (measurable_individualHistory (fun _ => measurable_const)
    (fun i => (measurable_pi_apply i).comp measurable_fst) measurable_snd)

noncomputable def CountableInstance.clockProfile (B : CountableInstance) (clocks : ℕ → ℝ)
    (candidate : Option ℕ) (w c t : ℝ) : ℝ :=
  B.continuationValue (candidateMask (clockMask clocks t) candidate) w c (remainingTime t)

lemma CountableInstance.measurable_clockProfile (B : CountableInstance) {w c : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (candidate : Option ℕ) :
    Measurable (fun z : (ℕ → ℝ) × ℝ => B.clockProfile z.1 candidate w c z.2) := by
  have hMask : Measurable (fun z : (ℕ → ℝ) × ℝ => candidateMask (clockMask z.1 z.2) candidate) := by
    cases candidate with
    | none => exact measurable_clockMask
    | some i => exact measurable_eraseMask.comp (measurable_clockMask.prodMk measurable_const)
  exact (B.measurable_continuationValue hw hc).comp
    (hMask.prodMk (continuous_remainingTime.measurable.comp measurable_snd))

lemma CountableInstance.clockProfile_antitone (B : CountableInstance) (hZero : B.terminal = 0)
    (clocks : ℕ → ℝ) (candidate : Option ℕ) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Antitone (B.clockProfile clocks candidate w c) := by
  intro s t hst
  have hMasks := maskLe_candidateMask (clockMask_antitone clocks hst) candidate
  have hRem : remainingTime t ≤ remainingTime s := Real.toNNReal_le_toNNReal (sub_le_sub_left hst 1)
  have hMask := B.remainingState_value_mono_mask hZero _ _ hMasks (remainingTime t) hw
    (mul_nonneg hc (remainingTime t).property)
  exact hMask.trans (B.continuationValue_mono _ hw hc hRem)

lemma CountableInstance.clockProfile_pos (B : CountableInstance) (clocks : ℕ → ℝ) (candidate : Option ℕ)
    {w c t : ℝ} (hw : 0 < w) (hc : 0 < c) (ht : t < 1) : 0 < B.clockProfile clocks candidate w c t := by
  have hWait := B.continuationValue_waiting_le (candidateMask (clockMask clocks t) candidate) w c (remainingTime t)
  have hPos : 0 < (remainingTime t : ℝ) := by rw [coe_remainingTime ht.le]; exact sub_pos.mpr ht
  exact (add_pos_of_nonneg_of_pos (mul_nonneg hw.le B.terminal.property) (mul_pos hc hPos)).trans_le hWait

lemma CountableInstance.clockProfile_update_candidate (B : CountableInstance) (clocks : ℕ → ℝ)
    (i : ℕ) (r w c t : ℝ) : B.clockProfile (Function.update clocks i r) (some i) w c t = B.clockProfile clocks (some i) w c t := by
  have hMask : candidateMask (clockMask (Function.update clocks i r) t) (some i) = candidateMask (clockMask clocks t) (some i) := by
    funext j
    by_cases hji : j = i
    · subst j
      simp only [candidateMask,Option.elim_some,eraseMask,Function.update_self]
    · change eraseMask (clockMask (Function.update clocks i r) t) i j = eraseMask (clockMask clocks t) i j
      simp only [eraseMask,Function.update_of_ne hji]
      change unseenMask (individualHistory (fun _ => 0) (Function.update clocks i r) t) j =
        unseenMask (individualHistory (fun _ => 0) clocks t) j
      rw [unseenMask_individualHistory,unseenMask_individualHistory,Function.update_of_ne hji]
  exact congrArg (fun keep => B.continuationValue keep w c (remainingTime t)) hMask

lemma CountableInstance.clockProfile_secant (B : CountableInstance) (hZero : B.terminal = 0)
    (clocks : ℕ → ℝ) (candidate : Option ℕ) {w c b s t : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hb : 0 < b) (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1)
    (hBand : b ≤ B.clockProfile clocks candidate w c t) :
    c*B.continuationBandFloor hZero w c b hw hb*(t-s) ≤
      B.clockProfile clocks candidate w c s-B.clockProfile clocks candidate w c t := by
  have hRem : remainingTime t ≤ remainingTime s := Real.toNNReal_le_toNNReal (sub_le_sub_left hst 1)
  have hSecant := B.continuationValue_secant_lower hZero (candidateMask (clockMask clocks t) candidate)
    hw hc hb hRem (remainingTime_le_one hs) hBand
  have hTime : (remainingTime s : ℝ)-(remainingTime t : ℝ) = t-s := by
    rw [coe_remainingTime (hst.trans ht),coe_remainingTime ht]
    ring
  rw [hTime] at hSecant
  have hMasks := maskLe_candidateMask (clockMask_antitone clocks hst) candidate
  have hDelete := B.remainingState_value_mono_mask hZero _ _ hMasks (remainingTime s) hw.le
    (mul_nonneg hc.le (remainingTime s).property)
  exact hSecant.trans (sub_le_sub_right hDelete _)

end ProphetSecretary.Limiting
