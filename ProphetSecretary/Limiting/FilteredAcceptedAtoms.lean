import ProphetSecretary.Limiting.AcceptedPointSums

/-!
# Order and upper-mark restrictions of accepted atoms

These nonnegative measure identities permit infinitely many omitted accepted
atoms. They compare analytical eligibility sets and do not stop copying the
original callback after an omitted acceptance.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Limiting

lemma acceptedAtom_gate_le (p : Point) (A : Prop) [Decidable A] (a : ℝ) :
    (if a < p.2 ∧ A then Measure.dirac p else 0) ≤ (if A then Measure.dirac p else 0) := by
  by_cases h : a < p.2 ∧ A
  · rw [if_pos h,if_pos h.2]
  · rw [if_neg h]
    exact bot_le

lemma acceptedAtom_gate_high_eq (p : Point) (A : Prop) [Decidable A] {a d : ℝ} (had : a ≤ d) :
    (if a < p.2 ∧ A then Measure.dirac p else 0).restrict {q : Point | d < q.2} =
      (if A then Measure.dirac p else 0).restrict {q : Point | d < q.2} := by
  by_cases hx : d < p.2
  · have ha := had.trans_lt hx
    simp only [ha,true_and]
  · have hdir : (Measure.dirac p).restrict {q : Point | d < q.2} = 0 := by
      rw [restrict_dirac,if_neg (show p ∉ {q : Point | d < q.2} from hx)]
    split_ifs <;> simp only [Measure.restrict_zero,hdir]

lemma acceptedAtom_high_zero (p : Point) (A : Prop) [Decidable A] {d : ℝ} (hx : p.2 ≤ d) :
    (if A then Measure.dirac p else 0).restrict {q : Point | d < q.2} = 0 := by
  split_ifs
  · rw [restrict_dirac,if_neg (show p ∉ {q : Point | d < q.2} from not_lt_of_ge hx)]
  · exact Measure.restrict_zero _

lemma measureSum_mono {ι α : Type*} [MeasurableSpace α] {μ ν : ι → Measure α}
    (h : ∀ i, μ i ≤ ν i) : Measure.sum μ ≤ Measure.sum ν := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.sum_apply _ hS,Measure.sum_apply _ hS]
  exact ENNReal.tsum_le_tsum (fun i => Measure.le_iff.mp (h i) S hS)

lemma finitePrefix_measure_le {α : Type*} [MeasurableSpace α] (N : ℕ)
    (μ : Fin N → Measure α) (ν : ℕ → Measure α) (h : ∀ i, μ i ≤ ν i.val) :
    (∑ i : Fin N, μ i) ≤ Measure.sum ν := by
  rw [← measureSum_natPrefix N μ]
  apply measureSum_mono
  intro i
  by_cases hi : i < N
  · rw [dif_pos hi]
    exact h ⟨i,hi⟩
  · rw [dif_neg hi]
    exact bot_le

lemma finitePrefix_restrict_eq {α : Type*} [MeasurableSpace α] (N : ℕ)
    (μ : Fin N → Measure α) (ν : ℕ → Measure α) {H : Set α} (hH : MeasurableSet H)
    (hPrefix : ∀ i, (μ i).restrict H = (ν i.val).restrict H)
    (hTail : ∀ j, N ≤ j → (ν j).restrict H = 0) :
    (∑ i : Fin N, μ i).restrict H = (Measure.sum ν).restrict H := by
  rw [← measureSum_natPrefix N μ,Measure.restrict_sum _ hH,Measure.restrict_sum _ hH]
  apply congrArg Measure.sum
  funext j
  by_cases hj : j < N
  · rw [dif_pos hj]
    exact hPrefix ⟨j,hj⟩
  · rw [dif_neg hj,Measure.restrict_zero,hTail j (Nat.le_of_not_gt hj)]

lemma gatedCloud_le (M L : Measure Point) (A : Set Point) (a : ℝ) :
    M.restrict ({p : Point | a < p.2} ∩ A) ≤ (M+L).restrict A :=
  Measure.restrict_mono inter_subset_right (Measure.le_add_right le_rfl)

lemma gatedCloud_high_eq (M L : Measure Point) (A : Set Point) {a d : ℝ} (had : a ≤ d)
    (hLow : L.restrict {p : Point | d < p.2} = 0) :
    (M.restrict ({p : Point | a < p.2} ∩ A)).restrict {p : Point | d < p.2} =
      ((M+L).restrict A).restrict {p : Point | d < p.2} := by
  let H := {p : Point | d < p.2}
  let G := {p : Point | a < p.2}
  have hH : MeasurableSet H := measurableSet_lt measurable_const measurable_snd
  have hSet : H ∩ (G ∩ A) = H ∩ A := by
    ext p
    constructor
    · exact fun hp => ⟨hp.1,hp.2.2⟩
    · exact fun hp => ⟨hp.1,had.trans_lt hp.1,hp.2⟩
  have hL : (L.restrict A).restrict H = 0 := by
    rw [Measure.restrict_restrict hH]
    have hle := Measure.restrict_mono_set L (show H ∩ A ⊆ H from inter_subset_left)
    rw [hLow] at hle
    exact le_antisymm hle bot_le
  change (M.restrict (G ∩ A)).restrict H = ((M+L).restrict A).restrict H
  rw [Measure.restrict_add,Measure.restrict_add,hL,add_zero,
    Measure.restrict_restrict hH,Measure.restrict_restrict hH,hSet]

end ProphetSecretary.Limiting
