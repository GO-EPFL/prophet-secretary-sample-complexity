import ProphetSecretary.Analysis.MultilevelPrimitiveLaw
import ProphetSecretary.Analysis.MultilevelRawMean

/-!
# Independence of the multilevel summands

Every base summand reads one primitive seed. Every paired summand reads its
transition seed and its two recursive trees. These coordinate groups are
disjoint for distinct summands.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Analysis

abbrev MultilevelSummandIndex (r : ℕ) := Fin (4 ^ (r + 1)) ⊕ MultilevelPairIndex r

noncomputable def multilevelSummandGroup (r : ℕ) :
    MultilevelSummandIndex r → Finset (MultilevelPrimitiveIndex r)
  | .inl j => {.inl j}
  | .inr q => {.inr (.inl q), .inr (.inr (.inl q)), .inr (.inr (.inr q))}

lemma multilevelSummandGroup_disjoint (r : ℕ) (i j : MultilevelSummandIndex r)
    (hij : i ≠ j) : Disjoint (multilevelSummandGroup r i) (multilevelSummandGroup r j) := by
  rcases i with b | p <;> rcases j with c | q <;>
    simp_all [multilevelSummandGroup, Finset.disjoint_left]

@[simp] lemma multilevelPrimitiveCoordinates_base {Seed : Type*} [MeasurableSpace Seed]
    (r : ℕ) (t : MultilevelTree Seed (r + 1)) (j : Fin (4 ^ (r + 1))) :
    multilevelPrimitiveCoordinates Seed r t (.inl j) =
      (multilevelNodeMeasurableEquiv Seed r t).1 j := rfl

@[simp] lemma multilevelPrimitiveCoordinates_seed {Seed : Type*} [MeasurableSpace Seed]
    (r : ℕ) (t : MultilevelTree Seed (r + 1)) (q : MultilevelPairIndex r) :
    multilevelPrimitiveCoordinates Seed r t (.inr (.inl q)) =
      (multilevelNodeMeasurableEquiv Seed r t).2.1 q.1 q.2 := rfl

@[simp] lemma multilevelPrimitiveCoordinates_upper {Seed : Type*} [MeasurableSpace Seed]
    (r : ℕ) (t : MultilevelTree Seed (r + 1)) (q : MultilevelPairIndex r) :
    multilevelPrimitiveCoordinates Seed r t (.inr (.inr (.inl q))) =
      (multilevelNodeMeasurableEquiv Seed r t).2.2.1 q.1 q.2 := rfl

@[simp] lemma multilevelPrimitiveCoordinates_lower {Seed : Type*} [MeasurableSpace Seed]
    (r : ℕ) (t : MultilevelTree Seed (r + 1)) (q : MultilevelPairIndex r) :
    multilevelPrimitiveCoordinates Seed r t (.inr (.inr (.inr q))) =
      (multilevelNodeMeasurableEquiv Seed r t).2.2.2 q.1 q.2 := rfl

noncomputable def multilevelSummandTerm {State Seed Transition : Type*} [MeasurableSpace Seed]
    (D : MultilevelRecursion State Seed Transition ℝ) (r : ℕ) (x : State) :
    MultilevelSummandIndex r → MultilevelTree Seed (r + 1) → ℝ
  | .inl j => multilevelBaseTerm D r x j
  | .inr q => multilevelPairTerm D r x q.1 q.2

noncomputable def multilevelBaseFunction {State Seed Transition : Type*}
    (D : MultilevelRecursion State Seed Transition ℝ) (r : ℕ) (x : State)
    (j : Fin (4 ^ (r + 1)))
    (a : (i : multilevelSummandGroup r (.inl j)) → MultilevelPrimitiveType Seed r i) : ℝ :=
  D.payoff x (D.sample x (a ⟨.inl j, by simp [multilevelSummandGroup]⟩)) 0

noncomputable def multilevelPairFunction {State Seed Transition : Type*}
    (D : MultilevelRecursion State Seed Transition ℝ) (r : ℕ) (x : State)
    (q : MultilevelPairIndex r)
    (a : (i : multilevelSummandGroup r (.inr q)) → MultilevelPrimitiveType Seed r i) : ℝ :=
  let seed := a ⟨.inr (.inl q), by simp [multilevelSummandGroup]⟩
  let upper := a ⟨.inr (.inr (.inl q)), by simp [multilevelSummandGroup]⟩
  let lower := a ⟨.inr (.inr (.inr q)), by simp [multilevelSummandGroup]⟩
  let y := D.sample x seed
  let child := D.child x y
  D.payoff x y (multilevelEstimate D (q.1.val + 1) child upper) -
    D.payoff x y (multilevelEstimate D q.1.val child lower)

noncomputable def multilevelSummandFunction {State Seed Transition : Type*}
    (D : MultilevelRecursion State Seed Transition ℝ) (r : ℕ) (x : State) :
    (j : MultilevelSummandIndex r) →
      ((i : multilevelSummandGroup r j) → MultilevelPrimitiveType Seed r i) → ℝ
  | .inl j => multilevelBaseFunction D r x j
  | .inr q => multilevelPairFunction D r x q

abbrev MultilevelSummandData (Seed : Type*) (r : ℕ) (j : MultilevelSummandIndex r) :=
  (i : multilevelSummandGroup r j) → MultilevelPrimitiveType Seed r i

lemma measurable_multilevelBaseFunction {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (r : ℕ) (x : State) (j : Fin (4 ^ (r + 1))) :
    Measurable (multilevelBaseFunction D r x j) := by
  have hs : Measurable (fun a : MultilevelSummandData Seed r (.inl j) =>
      a ⟨.inl j, by simp [multilevelSummandGroup]⟩) := measurable_pi_apply _
  exact hD.payoff.comp
    ((measurable_const.prodMk (hD.sample.comp (measurable_const.prodMk hs))).prodMk measurable_const)

lemma measurable_multilevelPairFunction {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (r : ℕ) (x : State) (q : MultilevelPairIndex r) :
    Measurable (multilevelPairFunction D r x q) := by
  have hs : Measurable (fun a : MultilevelSummandData Seed r (.inr q) =>
      a ⟨.inr (.inl q), by simp [multilevelSummandGroup]⟩) := measurable_pi_apply _
  have hu : Measurable (fun a : MultilevelSummandData Seed r (.inr q) =>
      a ⟨.inr (.inr (.inl q)), by simp [multilevelSummandGroup]⟩) := measurable_pi_apply _
  have hl : Measurable (fun a : MultilevelSummandData Seed r (.inr q) =>
      a ⟨.inr (.inr (.inr q)), by simp [multilevelSummandGroup]⟩) := measurable_pi_apply _
  have hy := hD.sample.comp ((measurable_const (a := x)).prodMk hs)
  have hc := hD.child.comp ((measurable_const (a := x)).prodMk hy)
  have heU := (measurable_multilevelEstimate D hD (q.1.val + 1)).comp (hc.prodMk hu)
  have heL := (measurable_multilevelEstimate D hD q.1.val).comp (hc.prodMk hl)
  exact (hD.payoff.comp ((measurable_const.prodMk hy).prodMk heU)).sub
    (hD.payoff.comp ((measurable_const.prodMk hy).prodMk heL))

lemma measurable_multilevelSummandFunction {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (r : ℕ) (x : State) (j : MultilevelSummandIndex r) :
    Measurable (multilevelSummandFunction D r x j) := by
  rcases j with b | q
  · exact measurable_multilevelBaseFunction D hD r x b
  · exact measurable_multilevelPairFunction D hD r x q

lemma multilevelSummandFunction_coordinates {State Seed Transition : Type*}
    [MeasurableSpace Seed] (D : MultilevelRecursion State Seed Transition ℝ)
    (r : ℕ) (x : State) (j : MultilevelSummandIndex r) (t : MultilevelTree Seed (r + 1)) :
    multilevelSummandFunction D r x j (fun i => multilevelPrimitiveCoordinates Seed r t i) =
      multilevelSummandTerm D r x j t := by
  rcases j with b | q <;> rfl

/-- Distinct summands are independent for the actual finite random tree.
The shared transition inside one pair does not couple different summands. -/
theorem multilevelSummandTerm_indepFun {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (x : State)
    (i j : MultilevelSummandIndex r) (hij : i ≠ j) :
    ProbabilityTheory.IndepFun (multilevelSummandTerm D r x i) (multilevelSummandTerm D r x j)
      (multilevelTreeLaw μ (r + 1)) := by
  have hp : MeasurePreserving (multilevelPrimitiveCoordinates Seed r)
      (multilevelTreeLaw μ (r + 1)) (Measure.pi (multilevelPrimitiveMeasure μ r)) :=
    multilevelTreeToPrimitive_measurePreserving μ r
  have hcoords (k : MultilevelPrimitiveIndex r) : Measurable
      (fun t : MultilevelTree Seed (r + 1) => multilevelPrimitiveCoordinates Seed r t k) :=
    (measurable_pi_apply k).comp hp.measurable
  have hg := (multilevelPrimitiveCoordinates_iIndepFun μ r).indepFun_finset
    (multilevelSummandGroup r i) (multilevelSummandGroup r j)
    (multilevelSummandGroup_disjoint r i j hij) hcoords
  have hc := hg.comp (measurable_multilevelSummandFunction D hD r x i)
    (measurable_multilevelSummandFunction D hD r x j)
  simpa only [Function.comp_def, multilevelSummandFunction_coordinates] using hc

end ProphetSecretary.Analysis
