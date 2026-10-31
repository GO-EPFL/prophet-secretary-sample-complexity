import ProphetSecretary.Model.Policy
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Measurable observation histories and executions

An observation is absent, or carries its time and value. Its σ-algebra is the usual
disjoint-union σ-algebra. Admissibility requires joint measurability of the decision in
its seed, current observation, and complete past history. No Markov restriction is imposed.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

private def observationCode : Option (ℝ × ℝ) → Unit ⊕ (ℝ × ℝ)
  | none => Sum.inl ()
  | some p => Sum.inr p

instance observationMeasurableSpace : MeasurableSpace (Option (ℝ × ℝ)) :=
  MeasurableSpace.comap observationCode inferInstance

/-- Joint measurability is the regularity condition on an online policy. -/
def Policy.IsMeasurable {Seed : Type*} [MeasurableSpace Seed] {n : ℕ}
    (π : Policy Seed n) : Prop :=
  Measurable (fun z : Seed × (ℝ × (Fin n × (ℝ × History n))) =>
    π.decide z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2)

variable {Ω Seed : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed] {n : ℕ}

/-- Histories expose exactly the identities that have already arrived, including zeros. -/
theorem measurable_history (D : Finset (Fin n)) {x u : Ω → Fin n → ℝ} {t : Ω → ℝ}
    (hx : ∀ j, Measurable fun ω => x ω j) (hu : ∀ j, Measurable fun ω => u ω j)
    (ht : Measurable t) : Measurable fun ω => history D (x ω) (u ω) (t ω) := by
  classical
  apply measurable_pi_lambda
  intro j
  rw [measurable_comap_iff]
  have hcond : MeasurableSet {ω | j ∈ D ∧ u ω j < t ω} :=
    (if hj : j ∈ D then by simpa [hj] using measurableSet_lt (hu j) ht
      else by simp [hj])
  change Measurable (fun ω => observationCode (if j ∈ D ∧ u ω j < t ω then
    some (u ω j, x ω j) else none))
  have heq : (fun ω => observationCode (if j ∈ D ∧ u ω j < t ω then
      some (u ω j, x ω j) else none)) =
      (fun ω => if j ∈ D ∧ u ω j < t ω then Sum.inr (u ω j, x ω j) else
        (Sum.inl () : Unit ⊕ (ℝ × ℝ))) := by
    funext ω
    split <;> rfl
  rw [heq]
  exact Measurable.ite hcond (measurable_inr.comp ((hu j).prodMk (hx j))) measurable_const

theorem Policy.measurable_action (π : Policy Seed n) (hπ : π.IsMeasurable)
    {r : Ω → Seed} {x u : Ω → Fin n → ℝ} (hr : Measurable r)
    (hx : ∀ j, Measurable fun ω => x ω j) (hu : ∀ j, Measurable fun ω => u ω j)
    (D : Finset (Fin n)) (j : Fin n) :
    Measurable fun ω => π.action (r ω) D (x ω) (u ω) j := by
  exact hπ.comp (hr.prodMk ((hu j).prodMk (measurable_const.prodMk
    ((hx j).prodMk (measurable_history D hx hu (hu j))))))

/-- A fixed finite family of candidate times, with `none` encoding the terminal time. -/
noncomputable def Policy.candidateTime (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) : Option (Fin n) → ℝ
  | none => 1
  | some j => if j ∈ π.accepted r D x u then u j else 1

omit [MeasurableSpace Seed] in
theorem Policy.stoppingTime_eq_iInf (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    π.stoppingTime r D x u = ⨅ j, π.candidateTime r D x u j := by
  classical
  have hb : BddBelow (range (π.candidateTime r D x u)) := (finite_range _).bddBelow
  apply le_antisymm
  · apply le_ciInf
    intro j
    cases j with
    | none => exact π.stoppingTime_le_one r D x u
    | some j =>
      simp only [Policy.candidateTime]
      split
      · exact π.stoppingTime_le_of_accepted r D x u j ‹_›
      · exact π.stoppingTime_le_one r D x u
  · apply (π.le_stoppingTime_iff r D x u _).mpr
    constructor
    · exact ciInf_le hb none
    · intro j hj
      exact (ciInf_le hb (some j)).trans_eq (if_pos hj)

theorem Policy.measurable_stoppingTime (π : Policy Seed n) (hπ : π.IsMeasurable)
    {r : Ω → Seed} {x u : Ω → Fin n → ℝ} (hr : Measurable r)
    (hx : ∀ j, Measurable fun ω => x ω j) (hu : ∀ j, Measurable fun ω => u ω j)
    (D : Finset (Fin n)) :
    Measurable fun ω => π.stoppingTime (r ω) D (x ω) (u ω) := by
  classical
  simp only [Policy.stoppingTime_eq_iInf]
  apply Measurable.iInf
  intro j
  cases j with
  | none => exact measurable_const
  | some j =>
    apply Measurable.ite _ (hu j) measurable_const
    have hm := π.measurable_action hπ hr hx hu D j
    have he : MeasurableSet {ω | π.action (r ω) D (x ω) (u ω) j = true} :=
      hm (measurableSet_singleton true)
    by_cases hj : j ∈ D
    · simpa only [Policy.mem_accepted, hj, true_and] using he
    · simp only [Policy.mem_accepted, hj, false_and, setOf_false]
      exact MeasurableSet.empty

theorem Policy.measurableSet_reaches (π : Policy Seed n) (hπ : π.IsMeasurable)
    {r : Ω → Seed} {x u : Ω → Fin n → ℝ} (hr : Measurable r)
    (hx : ∀ j, Measurable fun ω => x ω j) (hu : ∀ j, Measurable fun ω => u ω j)
    (i : Fin n) : MeasurableSet {ω | π.Reaches (r ω) (x ω) (u ω) i} :=
  measurableSet_le (hu i) (π.measurable_stoppingTime hπ hr hx hu Finset.univ)

theorem Policy.measurableSet_selects (π : Policy Seed n) (hπ : π.IsMeasurable)
    {r : Ω → Seed} {x u : Ω → Fin n → ℝ} (hr : Measurable r)
    (hx : ∀ j, Measurable fun ω => x ω j) (hu : ∀ j, Measurable fun ω => u ω j)
    (D : Finset (Fin n)) (i : Fin n) :
    MeasurableSet {ω | π.Selects (r ω) D (x ω) (u ω) i} := by
  have ha : MeasurableSet {ω | π.action (r ω) D (x ω) (u ω) i = true} :=
    (π.measurable_action hπ hr hx hu D i) (measurableSet_singleton true)
  have hm : MeasurableSet {ω | i ∈ π.accepted (r ω) D (x ω) (u ω)} := by
    by_cases hi : i ∈ D
    · simpa only [Policy.mem_accepted, hi, true_and] using ha
    · simp only [Policy.mem_accepted, hi, false_and, setOf_false]
      exact MeasurableSet.empty
  exact hm.inter (measurableSet_eq_fun (hu i) (π.measurable_stoppingTime hπ hr hx hu D))

end ProphetSecretary.Model
