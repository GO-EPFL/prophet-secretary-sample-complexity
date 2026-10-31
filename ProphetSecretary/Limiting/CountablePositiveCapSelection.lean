import ProphetSecretary.Limiting.CountableCapAcceptance
import ProphetSecretary.Limiting.CountableCapping
import ProphetSecretary.Limiting.CountableCapExcess
import ProphetSecretary.Limiting.CountableDurationPositive

/-!
# Positive selection probability of an individual carrying cap excess

Positive expected excess implies positive original upper-tail mass. After
capping, that tail is an atom at K. Canonical positive reach, actual cap
acceptance and reach-value independence then give positive selection mass.
-/

open MeasureTheory Set
open scoped NNReal Classical
namespace ProphetSecretary.Limiting.CountableInstance

lemma capAt_individual_atom (B : CountableInstance) (hZero : B.terminal=0) (K : ℝ≥0) (hK : 0<K) (i : ℕ) :
    ((B.capAt hZero K hK).individuals i : Measure ℝ).real {(K:ℝ)}=(B.individuals i : Measure ℝ).real (Ici (K:ℝ)) := by
  change ((B.individuals i : Measure ℝ).map (Model.capValue K)).real {(K:ℝ)}=_
  rw [map_measureReal_apply (Model.measurable_capValue K) (measurableSet_singleton (K:ℝ))]
  congr 1
  ext x
  simp only [Set.mem_preimage,Set.mem_singleton_iff,Set.mem_Ici,Model.capValue,min_eq_right_iff]

lemma capAt_individual_atom_positive_of_excess (B : CountableInstance) (hZero : B.terminal=0)
    (K : ℝ≥0) (hK : 0<K) (i : ℕ) (hE : 0<B.individualCapExcess K i) :
    0<((B.capAt hZero K hK).individuals i : Measure ℝ).real {(K:ℝ)} := by
  have hTail : 0<(B.individuals i : Measure ℝ).real (Ioi (K:ℝ)) := by
    by_contra h
    have hZeroTail : (B.individuals i : Measure ℝ).real (Ioi (K:ℝ))=0 :=
      le_antisymm (le_of_not_gt h) measureReal_nonneg
    have hBound := B.individualCapExcess_le_cap_mul_tail K i
    rw [hZeroTail,mul_zero] at hBound
    exact (not_lt_of_ge hBound) hE
  rw [B.capAt_individual_atom hZero K hK i]
  have hSub : Ioi (K:ℝ)⊆Ici (K:ℝ) := by
    intro x hx
    change (K:ℝ)≤x
    exact (show (K:ℝ)<x from hx).le
  exact hTail.trans_le (measureReal_mono hSub (measure_ne_top _ _))

theorem capAt_valuePolicy_selection_positive (B : CountableInstance) (hZero : B.terminal=0)
    (K : ℝ≥0) (hK : 0<K) {e : ℝ} (he : 0<e) (i : ℕ)
    (hValue : (B.capAt hZero K hK).optimalScalarValue 1 e≤(K:ℝ))
    (hE : 0<B.individualCapExcess K i) :
    0<((B.capAt hZero K hK).valuePolicy zero_lt_one he).individualSelectionProbability i := by
  let Q := B.capAt hZero K hK
  have hQZero : Q.terminal=0 := rfl
  have hReach := Q.valuePolicy_individualReachProbability_positive hQZero zero_lt_one he i
  have hAtom := B.capAt_individual_atom_positive_of_excess hZero K hK i hE
  have hSel := Q.valuePolicy_selectionProbability_ge_cap_mass hQZero zero_lt_one he i (K:ℝ) (by simpa only [one_mul] using hValue)
  exact (mul_pos hReach hAtom).trans_le hSel

end ProphetSecretary.Limiting.CountableInstance
