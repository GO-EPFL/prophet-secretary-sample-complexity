import ProphetSecretary.Analysis.MultilevelEstimatorMoments

/-!
# Changing the source of a transition seed

Mapping each seed preserves the recursive product law when it preserves the
single-seed law. A paired difference still uses the same mapped transition.
-/

open MeasureTheory

namespace ProphetSecretary.Analysis

def multilevelTreeMap {Seed Seed' : Type*} (f : Seed → Seed') :
    (r : ℕ) → MultilevelTree Seed r → MultilevelTree Seed' r
  | 0, .zero => .zero
  | r+1, .node base tr up lo => .node (fun i => f (base i)) (fun l j => f (tr l j))
      (fun l j => multilevelTreeMap f (l.val+1) (up l j))
      (fun l j => multilevelTreeMap f l.val (lo l j))
termination_by r => r
decreasing_by all_goals have := l.isLt; omega

lemma multilevelTreeMap_comp {Seed Seed' Seed'' : Type*} (f : Seed → Seed') (g : Seed' → Seed'')
    (r : ℕ) (t : MultilevelTree Seed r) :
    multilevelTreeMap g r (multilevelTreeMap f r t) = multilevelTreeMap (g ∘ f) r t := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases t with
    | zero => simp [multilevelTreeMap]
    | @node d base tr up lo =>
      have hu (l : Fin d) (t' : MultilevelTree Seed (l.val+1)) :=
        ih (l.val+1) (by have := l.isLt; omega) t'
      have hl (l : Fin d) (t' : MultilevelTree Seed l.val) :=
        ih l.val (by have := l.isLt; omega) t'
      simp only [multilevelTreeMap, hu, hl, Function.comp_apply]

/-- Only the source of the transition seed changes. -/
def MultilevelRecursion.mapSeed {State Seed Seed' Transition Value : Type*}
    (D : MultilevelRecursion State Seed' Transition Value) (f : Seed → Seed') :
    MultilevelRecursion State Seed Transition Value where
  isEmpty := D.isEmpty
  emptyValue := D.emptyValue
  offset := D.offset
  coefficient := D.coefficient
  sample x s := D.sample x (f s)
  child := D.child
  payoff := D.payoff

lemma multilevelEstimate_mapSeed {State Seed Seed' Transition Value : Type*} [Field Value]
    [LinearOrder Value] (D : MultilevelRecursion State Seed' Transition Value) (f : Seed → Seed')
    (r : ℕ) (x : State) (t : MultilevelTree Seed r) :
    multilevelEstimate (D.mapSeed f) r x t = multilevelEstimate D r x (multilevelTreeMap f r t) := by
  induction r using Nat.strong_induction_on generalizing x with
  | h r ih =>
    cases t with
    | zero => simp [multilevelEstimate_zero]
    | @node d base tr up lo =>
      have hu (l : Fin d) (x' : State) (t' : MultilevelTree Seed (l.val+1)) :=
        ih (l.val+1) (by have := l.isLt; omega) x' t'
      have hl (l : Fin d) (x' : State) (t' : MultilevelTree Seed l.val) :=
        ih l.val (by have := l.isLt; omega) x' t'
      simp only [MultilevelRecursion.mapSeed] at hu hl
      simp only [multilevelTreeMap, multilevelEstimate, MultilevelRecursion.mapSeed, hu, hl]

lemma multilevelTreeMap_work {Seed Seed' : Type*} (f : Seed → Seed')
    (r : ℕ) (t : MultilevelTree Seed r) :
    multilevelTreeWork r (multilevelTreeMap f r t) = multilevelTreeWork r t := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases t with
    | zero => simp [multilevelTreeMap, multilevelTreeWork]
    | @node d base tr up lo =>
      have hu (l : Fin d) (t' : MultilevelTree Seed (l.val+1)) :=
        ih (l.val+1) (by have := l.isLt; omega) t'
      have hl (l : Fin d) (t' : MultilevelTree Seed l.val) :=
        ih l.val (by have := l.isLt; omega) t'
      simp only [multilevelTreeMap, multilevelTreeWork, hu, hl]

theorem measurePreserving_multilevelTreeMap {Seed Seed' : Type*}
    [MeasurableSpace Seed] [MeasurableSpace Seed']
    {μ : Measure Seed} {ν : Measure Seed'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Seed → Seed'} (hf : MeasurePreserving f μ ν) (r : ℕ) :
    MeasurePreserving (multilevelTreeMap f r) (multilevelTreeLaw μ r) (multilevelTreeLaw ν r) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero =>
      have he : multilevelTreeMap f 0 = fun _ => MultilevelTree.zero := by
        funext t; cases t; simp [multilevelTreeMap]
      rw [he, multilevelTreeLaw, multilevelTreeLaw]
      exact ⟨measurable_const, Measure.map_dirac' (measurable_const (a := MultilevelTree.zero)) _⟩
    | succ d =>
      have hu (l : Fin d) := ih (l.val+1) (by have := l.isLt; omega)
      have hl (l : Fin d) := ih l.val (by have := l.isLt; omega)
      have hbase := measurePreserving_pi (fun _ : Fin (4^(d+1)) => μ) (fun _ => ν) (fun _ => hf)
      have htr := measurePreserving_pi
        (fun l : Fin d => Measure.pi (fun _ : Fin (4^(d-l.val)) => μ))
        (fun l : Fin d => Measure.pi (fun _ : Fin (4^(d-l.val)) => ν))
        (fun _ => measurePreserving_pi _ _ (fun _ => hf))
      have hup := measurePreserving_pi
        (fun l : Fin d => Measure.pi (fun _ : Fin (4^(d-l.val)) => multilevelTreeLaw μ (l.val+1)))
        (fun l : Fin d => Measure.pi (fun _ : Fin (4^(d-l.val)) => multilevelTreeLaw ν (l.val+1)))
        (fun l => measurePreserving_pi _ _ (fun _ => hu l))
      have hlo := measurePreserving_pi
        (fun l : Fin d => Measure.pi (fun _ : Fin (4^(d-l.val)) => multilevelTreeLaw μ l.val))
        (fun l : Fin d => Measure.pi (fun _ : Fin (4^(d-l.val)) => multilevelTreeLaw ν l.val))
        (fun l => measurePreserving_pi _ _ (fun _ => hl l))
      have hout : MeasurePreserving (multilevelNodeMeasurableEquiv Seed' d).symm
          (multilevelNodeLaw ν d) (multilevelTreeLaw ν (d+1)) := by
        refine ⟨(multilevelNodeMeasurableEquiv Seed' d).symm.measurable, ?_⟩
        rw [multilevelTreeLaw]
        rfl
      have hall := hout.comp ((hbase.prod (htr.prod (hup.prod hlo))).comp (multilevelNode_measurePreserving μ d))
      convert hall using 1
      funext t
      cases t
      simp only [multilevelTreeMap]
      rfl

/-- Number of primitive seeds in a full tree, including unused branches. -/
def multilevelTreeSeedCount {Seed : Type*} : (r : ℕ) → MultilevelTree Seed r → ℕ
  | 0, .zero => 0
  | r+1, .node _ _ up lo => 4^(r+1) +
      ∑ l : Fin r, ∑ j : Fin (4^(r-l.val)),
        (1 + multilevelTreeSeedCount (l.val+1) (up l j) + multilevelTreeSeedCount l.val (lo l j))
termination_by r => r
decreasing_by all_goals have := l.isLt; omega

lemma multilevelTreeSeedCount_le_work {Seed : Type*} (r : ℕ) (t : MultilevelTree Seed r) :
    multilevelTreeSeedCount r t ≤ multilevelTreeWork r t := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases t with
    | zero => simp [multilevelTreeSeedCount, multilevelTreeWork]
    | @node d base tr up lo =>
      simp only [multilevelTreeSeedCount, multilevelTreeWork]
      apply Nat.add_le_add (by omega)
      apply Finset.sum_le_sum
      intro l _
      apply Finset.sum_le_sum
      intro j _
      have hu := ih (l.val+1) (by have := l.isLt; omega) (up l j)
      have hl := ih l.val (by have := l.isLt; omega) (lo l j)
      omega

lemma multilevelTreeSeedCount_le {Seed : Type*} (r : ℕ) (t : MultilevelTree Seed r) :
    multilevelTreeSeedCount r t ≤ 4 * 16^r := by
  refine (multilevelTreeSeedCount_le_work r t).trans ?_
  exact_mod_cast multilevelTreeWork_le r t

end ProphetSecretary.Analysis
