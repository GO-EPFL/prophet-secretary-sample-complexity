import ProphetSecretary.Model.ProphetMarginalTail
import ProphetSecretary.Analysis.TailEnvelope

/-!
# The aggregate measure of positive offers

This is Λ=Σᵢ Pᵢ restricted to (0,1], used in `upmom:atomeq` and
`upmom:logtail`. It is a finite measure, not a probability law. For instances
bounded by one, its open tails equal the expected tail counts L_x.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.aggregatePositiveMeasure (P : Instance n) : Measure ℝ :=
  ∑ i, (P.law i).restrict (Ioc (0 : ℝ) 1)

instance Instance.aggregatePositiveMeasure_finite (P : Instance n) : IsFiniteMeasure P.aggregatePositiveMeasure := by
  unfold aggregatePositiveMeasure
  infer_instance

lemma Instance.aggregatePositiveMeasure_real_apply (P : Instance n) {s : Set ℝ} (hs : MeasurableSet s) :
    P.aggregatePositiveMeasure.real s = ∑ i, (P.law i).real (s ∩ Ioc (0 : ℝ) 1) := by
  unfold aggregatePositiveMeasure Measure.real
  rw [Measure.finsetSum_apply, ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.restrict_apply hs]

lemma Instance.aggregatePositiveMeasure_real_apply_of_subset (P : Instance n)
    {s : Set ℝ} (hs : MeasurableSet s) (hsub : s ⊆ Ioc (0 : ℝ) 1) :
    P.aggregatePositiveMeasure.real s = ∑ i, (P.law i).real s := by
  rw [P.aggregatePositiveMeasure_real_apply hs, Set.inter_eq_left.mpr hsub]

lemma Instance.aggregatePositiveMeasure_singleton (P : Instance n) {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) :
    P.aggregatePositiveMeasure.real {a} = P.aggregateAtomMass a := by
  exact P.aggregatePositiveMeasure_real_apply_of_subset (measurableSet_singleton a)
    (by intro x hx; simpa only [Set.mem_singleton_iff.mp hx] using ha)

lemma Instance.aggregatePositiveMeasure_openTail (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {a : ℝ} (ha : 0 ≤ a) :
    P.aggregatePositiveMeasure.real (Ioi a) = P.tailCount a := by
  rw [P.aggregatePositiveMeasure_real_apply measurableSet_Ioi]
  unfold Instance.tailCount
  apply Finset.sum_congr rfl
  intro i _
  have heq : (Ioi a ∩ Ioc (0 : ℝ) 1 : Set ℝ) =ᵐ[P.law i] (Ioi a : Set ℝ) := by
    filter_upwards [hcap i] with x hx
    exact propext ⟨fun h => h.1, fun h => ⟨h, lt_of_le_of_lt ha h, hx⟩⟩
  exact congrArg ENNReal.toReal (measure_congr heq)

lemma Instance.aggregatePositiveMeasure_closedTail (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {a : ℝ} (ha : a ∈ Ioc (0 : ℝ) 1) :
    P.aggregatePositiveMeasure.real (Ici a) = P.tailCount a + P.aggregateAtomMass a := by
  have heq : Ici a = Ioi a ∪ {a} := by
    ext x
    simp only [mem_Ici, mem_union, mem_Ioi, mem_singleton_iff]
    constructor
    · intro hx
      rcases lt_or_eq_of_le hx with h | h
      · exact Or.inl h
      · exact Or.inr h.symm
    · rintro (h | rfl)
      · exact h.le
      · exact le_rfl
  rw [heq, measureReal_union (by simp : Disjoint (Ioi a) {a}) (measurableSet_singleton a),
    P.aggregatePositiveMeasure_openTail hcap ha.1.le, P.aggregatePositiveMeasure_singleton ha]

lemma Instance.measurable_tailCount (P : Instance n) : Measurable P.tailCount := P.tailCount_antitone.measurable

/-- The endpoint argument in `upmom:logtail`, including the case that the
lower endpoint is absent from the set. -/
theorem Instance.aggregatePositiveMeasure_tailEnvelope (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {s : Set ℝ} {a B : ℝ}
    (ha : 0 < a) (hsub : s ⊆ Icc a 1) (hB : 0 ≤ B + 2)
    (htail : ∀ x ∈ s, P.tailCount x < B)
    (hatom : ∀ x ∈ s, P.aggregateAtomMass x < 2) :
    P.aggregatePositiveMeasure.real s ≤ B + 2 := by
  apply ProphetSecretary.Analysis.measureReal_set_le_of_upperTail P.aggregatePositiveMeasure
    ⟨a, fun x hx => (hsub hx).1⟩ hB
  intro x hx
  rw [P.aggregatePositiveMeasure_closedTail hcap ⟨ha.trans_le (hsub hx).1, (hsub hx).2⟩]
  linarith only [htail x hx, hatom x hx]

end ProphetSecretary.Model
