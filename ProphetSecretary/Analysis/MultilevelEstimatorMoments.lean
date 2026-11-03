import ProphetSecretary.Analysis.MultilevelEstimator
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.FunProp

/-!
# Independent finite trees for the multilevel estimator

Each node uses a finite product law. Base and paired transitions are
independent, and the two recursive copies within a pair are independent
conditional on its shared transition.
-/

open MeasureTheory

namespace ProphetSecretary.Analysis

/-- The four finite arrays stored at a nonzero level. -/
abbrev MultilevelNodeData (Seed : Type*) (r : ℕ) :=
  (Fin (4 ^ (r + 1)) → Seed) ×
    (((l : Fin r) → Fin (4 ^ (r - l.val)) → Seed) ×
      (((l : Fin r) → Fin (4 ^ (r - l.val)) → MultilevelTree Seed (l.val + 1)) ×
        ((l : Fin r) → Fin (4 ^ (r - l.val)) → MultilevelTree Seed l.val)))

def multilevelNodeEquiv (Seed : Type*) (r : ℕ) :
    MultilevelTree Seed (r + 1) ≃ MultilevelNodeData Seed r where
  toFun t := match t with
    | .node b tr u lo => (b, tr, u, lo)
  invFun d := .node d.1 d.2.1 d.2.2.1 d.2.2.2
  left_inv t := by cases t; rfl
  right_inv d := by rcases d with ⟨b, tr, u, lo⟩; rfl

/-- The product measurable structure on the finite tree. -/
def multilevelTreeMeasurableSpace (Seed : Type*) [MeasurableSpace Seed] :
    (r : ℕ) → MeasurableSpace (MultilevelTree Seed r)
  | 0 => ⊤
  | r + 1 =>
      letI upperSpace (l : Fin r) : MeasurableSpace (MultilevelTree Seed (l.val + 1)) :=
        multilevelTreeMeasurableSpace Seed (l.val + 1)
      letI lowerSpace (l : Fin r) : MeasurableSpace (MultilevelTree Seed l.val) :=
        multilevelTreeMeasurableSpace Seed l.val
      MeasurableSpace.comap (multilevelNodeEquiv Seed r) inferInstance
termination_by r => r
decreasing_by all_goals have := l.isLt; omega

instance {Seed : Type*} [MeasurableSpace Seed] (r : ℕ) :
    MeasurableSpace (MultilevelTree Seed r) := multilevelTreeMeasurableSpace Seed r

def multilevelNodeMeasurableEquiv (Seed : Type*) [MeasurableSpace Seed] (r : ℕ) :
    MultilevelTree Seed (r + 1) ≃ᵐ MultilevelNodeData Seed r where
  toEquiv := multilevelNodeEquiv Seed r
  measurable_toFun := by
    change Measurable[multilevelTreeMeasurableSpace Seed (r + 1), _]
      (multilevelNodeEquiv Seed r)
    rw [multilevelTreeMeasurableSpace]
    exact comap_measurable _
  measurable_invFun := by
    change Measurable[_, multilevelTreeMeasurableSpace Seed (r + 1)]
      (multilevelNodeEquiv Seed r).symm
    rw [multilevelTreeMeasurableSpace]
    apply measurable_comap_iff.mpr
    convert measurable_id using 1
    funext d
    exact (multilevelNodeEquiv Seed r).apply_symm_apply d

/-- Independent node arrays, built from the recursive subtree laws. -/
noncomputable def multilevelTreeLaw {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) : (r : ℕ) → Measure (MultilevelTree Seed r)
  | 0 => Measure.dirac .zero
  | r + 1 =>
      let b := Measure.pi (fun _ : Fin (4 ^ (r + 1)) => μ)
      let tr := Measure.pi (fun l : Fin r => Measure.pi
        (fun _ : Fin (4 ^ (r - l.val)) => μ))
      let up := Measure.pi (fun l : Fin r => Measure.pi
        (fun _ : Fin (4 ^ (r - l.val)) => multilevelTreeLaw μ (l.val + 1)))
      let lo := Measure.pi (fun l : Fin r => Measure.pi
        (fun _ : Fin (4 ^ (r - l.val)) => multilevelTreeLaw μ l.val))
      Measure.map (multilevelNodeMeasurableEquiv Seed r).symm
        (b.prod (tr.prod (up.prod lo)))
termination_by r => r
decreasing_by all_goals have := l.isLt; omega

instance multilevelTreeLaw_probability {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) :
    IsProbabilityMeasure (multilevelTreeLaw μ r) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero =>
      rw [multilevelTreeLaw]
      infer_instance
    | succ n =>
      letI upperProbability (l : Fin n) :
          IsProbabilityMeasure (multilevelTreeLaw μ (l.val + 1)) :=
        ih (l.val + 1) (by have := l.isLt; omega)
      letI lowerProbability (l : Fin n) :
          IsProbabilityMeasure (multilevelTreeLaw μ l.val) :=
        ih l.val (by have := l.isLt; omega)
      rw [multilevelTreeLaw]
      exact Measure.isProbabilityMeasure_map
        (multilevelNodeMeasurableEquiv Seed n).symm.measurable.aemeasurable

/-- The literal product distribution of a nonzero node's four arrays. -/
noncomputable def multilevelNodeLaw {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) (r : ℕ) : Measure (MultilevelNodeData Seed r) :=
  (Measure.pi (fun _ : Fin (4 ^ (r + 1)) => μ)).prod
    ((Measure.pi (fun l : Fin r => Measure.pi
      (fun _ : Fin (4 ^ (r - l.val)) => μ))).prod
      ((Measure.pi (fun l : Fin r => Measure.pi
        (fun _ : Fin (4 ^ (r - l.val)) => multilevelTreeLaw μ (l.val + 1)))).prod
        (Measure.pi (fun l : Fin r => Measure.pi
          (fun _ : Fin (4 ^ (r - l.val)) => multilevelTreeLaw μ l.val)))))

instance multilevelNodeLaw_probability {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) :
    IsProbabilityMeasure (multilevelNodeLaw μ r) := by
  unfold multilevelNodeLaw
  infer_instance

/-- The independent-array law is derived from the constructed tree law. -/
theorem multilevelTreeLaw_map_node {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) (r : ℕ) :
    Measure.map (multilevelNodeMeasurableEquiv Seed r) (multilevelTreeLaw μ (r + 1)) =
      multilevelNodeLaw μ r := by
  rw [multilevelTreeLaw]
  rw [Measure.map_map (multilevelNodeMeasurableEquiv Seed r).measurable
    (multilevelNodeMeasurableEquiv Seed r).symm.measurable]
  simp [Function.comp_def, multilevelNodeLaw]

theorem multilevelNode_measurePreserving {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) (r : ℕ) :
    MeasurePreserving (multilevelNodeMeasurableEquiv Seed r)
      (multilevelTreeLaw μ (r + 1)) (multilevelNodeLaw μ r) :=
  ⟨(multilevelNodeMeasurableEquiv Seed r).measurable, multilevelTreeLaw_map_node μ r⟩

/-- A paired summand really has one independent transition seed and two
independent recursive trees; its two evaluations subsequently share that seed. -/
theorem multilevelPair_measurePreserving {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (l : Fin r)
    (j : Fin (4 ^ (r - l.val))) :
    MeasurePreserving
      (fun t : MultilevelTree Seed (r + 1) =>
        let d := multilevelNodeMeasurableEquiv Seed r t
        (d.2.1 l j, (d.2.2.1 l j, d.2.2.2 l j)))
      (multilevelTreeLaw μ (r + 1))
      (μ.prod ((multilevelTreeLaw μ (l.val + 1)).prod (multilevelTreeLaw μ l.val))) := by
  have htr := (measurePreserving_eval (fun _ : Fin (4 ^ (r - l.val)) => μ) j).comp
    (measurePreserving_eval (fun k : Fin r => Measure.pi
      (fun _ : Fin (4 ^ (r - k.val)) => μ)) l)
  have hup := (measurePreserving_eval
      (fun _ : Fin (4 ^ (r - l.val)) => multilevelTreeLaw μ (l.val + 1)) j).comp
    (measurePreserving_eval (fun k : Fin r => Measure.pi
      (fun _ : Fin (4 ^ (r - k.val)) => multilevelTreeLaw μ (k.val + 1))) l)
  have hlo := (measurePreserving_eval
      (fun _ : Fin (4 ^ (r - l.val)) => multilevelTreeLaw μ l.val) j).comp
    (measurePreserving_eval (fun k : Fin r => Measure.pi
      (fun _ : Fin (4 ^ (r - k.val)) => multilevelTreeLaw μ k.val)) l)
  have hprod := htr.prod (hup.prod hlo)
  have hdrop : MeasurePreserving Prod.snd (multilevelNodeLaw μ r)
      ((Measure.pi (fun k : Fin r => Measure.pi
        (fun _ : Fin (4 ^ (r - k.val)) => μ))).prod
        ((Measure.pi (fun k : Fin r => Measure.pi
          (fun _ : Fin (4 ^ (r - k.val)) => multilevelTreeLaw μ (k.val + 1)))).prod
          (Measure.pi (fun k : Fin r => Measure.pi
            (fun _ : Fin (4 ^ (r - k.val)) => multilevelTreeLaw μ k.val))))) :=
    measurePreserving_snd
  exact (hprod.comp hdrop).comp (multilevelNode_measurePreserving μ r)

theorem multilevelBase_measurePreserving {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (j : Fin (4 ^ (r + 1))) :
    MeasurePreserving
      (fun t : MultilevelTree Seed (r + 1) => (multilevelNodeMeasurableEquiv Seed r t).1 j)
      (multilevelTreeLaw μ (r + 1)) μ := by
  have hdrop : MeasurePreserving Prod.fst (multilevelNodeLaw μ r)
      (Measure.pi (fun _ : Fin (4 ^ (r + 1)) => μ)) := measurePreserving_fst
  exact ((measurePreserving_eval (fun _ : Fin (4 ^ (r + 1)) => μ) j).comp hdrop).comp
    (multilevelNode_measurePreserving μ r)

lemma integral_multilevelTreeLaw_node {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) (r : ℕ) (f : MultilevelTree Seed (r + 1) → ℝ) :
    (∫ t, f t ∂multilevelTreeLaw μ (r + 1)) =
      ∫ d, f ((multilevelNodeMeasurableEquiv Seed r).symm d) ∂multilevelNodeLaw μ r := by
  rw [multilevelTreeLaw]
  exact integral_map_equiv (multilevelNodeMeasurableEquiv Seed r).symm f

/-- Joint measurability of the primitive computational maps. -/
structure MultilevelRecursion.IsMeasurable {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) : Prop where
  isEmpty : Measurable D.isEmpty
  emptyValue : Measurable D.emptyValue
  offset : Measurable D.offset
  coefficient : Measurable D.coefficient
  sample : Measurable (fun z : State × Seed => D.sample z.1 z.2)
  child : Measurable (fun z : State × Transition => D.child z.1 z.2)
  payoff : Measurable (fun z : (State × Transition) × ℝ => D.payoff z.1.1 z.1.2 z.2)

/-- Measurability is proved for the actual recursive evaluator jointly in
the state and finite random tree. -/
theorem measurable_multilevelEstimate {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable) (r : ℕ) :
    Measurable (fun z : State × MultilevelTree Seed r => multilevelEstimate D r z.1 z.2) := by
  induction r using Nat.strong_induction_on with
  | h r ih =>
    cases r with
    | zero =>
      have hzero : (fun z : State × MultilevelTree Seed 0 => multilevelEstimate D 0 z.1 z.2) =
          fun _ => 0 := by funext z; exact multilevelEstimate_zero D z.1 z.2
      rw [hzero]
      exact measurable_const
    | succ n =>
      have hbase (j : Fin (4 ^ (n + 1))) :
          Measurable (fun z : State × MultilevelNodeData Seed n => D.payoff z.1 (D.sample z.1 (z.2.1 j)) 0) := by
        have hs : Measurable (fun z : State × MultilevelNodeData Seed n =>
            D.sample z.1 (z.2.1 j)) :=
          hD.sample.comp (measurable_fst.prodMk (by fun_prop))
        exact hD.payoff.comp ((measurable_fst.prodMk hs).prodMk measurable_const)
      have hpair (l : Fin n) (j : Fin (4 ^ (n - l.val))) : Measurable
          (fun z : State × MultilevelNodeData Seed n =>
            let y := D.sample z.1 (z.2.2.1 l j)
            let child := D.child z.1 y
            D.payoff z.1 y (multilevelEstimate D (l.val + 1) child (z.2.2.2.1 l j)) -
              D.payoff z.1 y (multilevelEstimate D l.val child (z.2.2.2.2 l j))) := by
        have hy : Measurable (fun z : State × MultilevelNodeData Seed n => D.sample z.1 (z.2.2.1 l j)) :=
          hD.sample.comp (measurable_fst.prodMk (by fun_prop))
        have hchild : Measurable (fun z : State × MultilevelNodeData Seed n =>
            D.child z.1 (D.sample z.1 (z.2.2.1 l j))) :=
          hD.child.comp (measurable_fst.prodMk hy)
        have hu := (ih (l.val + 1) (by have := l.isLt; omega)).comp
          (hchild.prodMk (by fun_prop : Measurable (fun z : State × MultilevelNodeData Seed n => z.2.2.2.1 l j)))
        have hl := (ih l.val (by have := l.isLt; omega)).comp
          (hchild.prodMk (by fun_prop : Measurable (fun z : State × MultilevelNodeData Seed n => z.2.2.2.2 l j)))
        exact (hD.payoff.comp ((measurable_fst.prodMk hy).prodMk hu)).sub
          (hD.payoff.comp ((measurable_fst.prodMk hy).prodMk hl))
      have hbody : Measurable (fun z : State × MultilevelNodeData Seed n =>
          multilevelEstimate D (n + 1) z.1 ((multilevelNodeMeasurableEquiv Seed n).symm z.2)) := by
        change Measurable (fun z : State × MultilevelNodeData Seed n =>
          multilevelEstimate D (n + 1) z.1
            (.node z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2))
        simp only [multilevelEstimate]
        have hbaseSum := Finset.measurable_sum Finset.univ (fun j _ => hbase j)
        have hpairSum := Finset.measurable_sum Finset.univ (fun l _ =>
          (Finset.measurable_sum Finset.univ (fun j _ => hpair l j)).const_mul
            (1 / ((4 : ℝ) ^ (n - l.val))))
        have hraw := (hD.offset.comp measurable_fst).add
          ((hD.coefficient.comp measurable_fst).mul
            ((hbaseSum.const_mul (1 / ((4 : ℝ) ^ (n + 1)))).add hpairSum))
        have hclip : Measurable (fun z : State × MultilevelNodeData Seed n => clipFive
            (D.offset z.1 + D.coefficient z.1 *
              ((1 / ((4 : ℝ) ^ (n + 1))) *
                ∑ j : Fin (4 ^ (n + 1)), D.payoff z.1 (D.sample z.1 (z.2.1 j)) 0 +
                ∑ l : Fin n, (1 / ((4 : ℝ) ^ (n - l.val))) *
                  ∑ j : Fin (4 ^ (n - l.val)),
                    let y := D.sample z.1 (z.2.2.1 l j)
                    let child := D.child z.1 y
                    D.payoff z.1 y (multilevelEstimate D (l.val + 1) child (z.2.2.2.1 l j)) -
                      D.payoff z.1 y (multilevelEstimate D l.val child (z.2.2.2.2 l j))))) :=
          measurable_const.max (measurable_const.min hraw)
        exact Measurable.ite
          ((hD.isEmpty.comp measurable_fst) (measurableSet_singleton true))
          (hD.emptyValue.comp measurable_fst) hclip
      have he : Measurable (fun z : State × MultilevelTree Seed (n + 1) =>
          (z.1, multilevelNodeMeasurableEquiv Seed n z.2)) :=
        measurable_fst.prodMk
          ((multilevelNodeMeasurableEquiv Seed n).measurable.comp measurable_snd)
      simpa only [Function.comp_def, MeasurableEquiv.symm_apply_apply] using hbody.comp he

lemma integrable_multilevelEstimate {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (x : State) :
    Integrable (fun t => multilevelEstimate D r x t) (multilevelTreeLaw μ r) := by
  have hm : Measurable (fun t : MultilevelTree Seed r => multilevelEstimate D r x t) :=
    (measurable_multilevelEstimate D hD r).comp (measurable_const.prodMk measurable_id)
  apply Integrable.of_bound hm.aestronglyMeasurable 5
  exact ae_of_all _ (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (multilevelEstimate_bounds D hEmpty r x t).1]
    exact (multilevelEstimate_bounds D hEmpty r x t).2)

lemma multilevelEstimate_sq_error_le_twentyFive {State Seed Transition : Type*}
    (D : MultilevelRecursion State Seed Transition ℝ)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (r : ℕ) (x : State) (t : MultilevelTree Seed r) {v : ℝ}
    (hv0 : 0 ≤ v) (hv5 : v ≤ 5) : (multilevelEstimate D r x t - v) ^ 2 ≤ 25 := by
  have hb := multilevelEstimate_bounds D hEmpty r x t
  have ha : |multilevelEstimate D r x t - v| ≤ 5 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hs := (sq_le_sq₀ (abs_nonneg (multilevelEstimate D r x t - v))
    (by norm_num : (0 : ℝ) ≤ 5)).2 ha
  norm_num only [sq_abs, show (5 : ℝ) ^ 2 = 25 by norm_num] at hs
  exact hs

lemma integrable_multilevelEstimate_sq_error {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (x : State) {v : ℝ}
    (hv0 : 0 ≤ v) (hv5 : v ≤ 5) :
    Integrable (fun t => (multilevelEstimate D r x t - v) ^ 2) (multilevelTreeLaw μ r) := by
  have hm : Measurable (fun t : MultilevelTree Seed r => multilevelEstimate D r x t) :=
    (measurable_multilevelEstimate D hD r).comp (measurable_const.prodMk measurable_id)
  apply Integrable.of_bound ((hm.sub_const v).pow_const 2).aestronglyMeasurable 25
  exact ae_of_all _ (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact multilevelEstimate_sq_error_le_twentyFive D hEmpty r x t hv0 hv5)

lemma integral_multilevelEstimate_sq_error_le_twentyFive {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (x : State) {v : ℝ}
    (hv0 : 0 ≤ v) (hv5 : v ≤ 5) :
    (∫ t, (multilevelEstimate D r x t - v) ^ 2 ∂multilevelTreeLaw μ r) ≤ 25 := by
  calc
    _ ≤ ∫ _t : MultilevelTree Seed r, (25 : ℝ) ∂multilevelTreeLaw μ r :=
      integral_mono (integrable_multilevelEstimate_sq_error D hD hEmpty μ r x hv0 hv5)
        (integrable_const 25) (fun t =>
          multilevelEstimate_sq_error_le_twentyFive D hEmpty r x t hv0 hv5)
    _ = _ := by simp

end ProphetSecretary.Analysis
