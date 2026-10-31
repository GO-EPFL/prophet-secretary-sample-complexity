import ProphetSecretary.Limiting.HybridValuePolicy
import ProphetSecretary.Limiting.HybridRetainedMonotonicity

/-!
# Actual hybrid continuation and Bellman action losses

A retained arrival removes its identity; an anonymous arrival leaves the
retained unseen set unchanged. The potential uses the genuine hybrid scalar
supremum with the remaining Poisson intensity and duration horizon. The
complete vectors below only evaluate these analytical losses. The executed
callback still reads its specified past and current offer.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting
variable {n N : ℕ} {Seed : Type*}

noncomputable def FiniteIntensityHybridInstance.finiteContinuationAtArrival (B : FiniteIntensityHybridInstance n)
    (w c : ℝ) (x u : Fin (n+N) → ℝ) (k : Fin (n+N)) : ℝ :=
  w*finiteHybridThreshold (B.valueHybridThreshold w c) N ()
    (Model.unseen (Model.history Finset.univ x u (u k))) (u k) k

noncomputable def HybridRule.arrivalValueLoss (π : HybridRule n Seed) (B : FiniteIntensityHybridInstance n)
    (w c : ℝ) (v : HybridWorld n Seed) (k : Fin (n+v.1.1)) : ℝ :=
  let x := combinedValues v.2.1 v.1.2
  let u := combinedClocks v.2.2.1 v.1.2
  let V := B.finiteContinuationAtArrival w c x u k
  max (w*x k) V-(if (π.asFinitePolicy v.1.1).action v.2.2.2 Finset.univ x u k = true then w*x k else V)

noncomputable def HybridRule.reachedValueLoss (π : HybridRule n Seed) (B : FiniteIntensityHybridInstance n)
    (w c : ℝ) (v : HybridWorld n Seed) : ℝ :=
  ∑ k : Fin (n+v.1.1), if (π.asFinitePolicy v.1.1).Reaches v.2.2.2
    (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) k then π.arrivalValueLoss B w c v k else 0

lemma HybridRule.arrivalValueLoss_nonnegative (π : HybridRule n Seed) (B : FiniteIntensityHybridInstance n)
    (w c : ℝ) (v : HybridWorld n Seed) (k : Fin (n+v.1.1)) : 0 ≤ π.arrivalValueLoss B w c v k := by
  unfold HybridRule.arrivalValueLoss
  dsimp only
  split_ifs
  · exact sub_nonneg.mpr (le_max_left _ _)
  · exact sub_nonneg.mpr (le_max_right _ _)

lemma HybridRule.reachedValueLoss_nonnegative (π : HybridRule n Seed) (B : FiniteIntensityHybridInstance n)
    (w c : ℝ) (v : HybridWorld n Seed) : 0 ≤ π.reachedValueLoss B w c v :=
  Finset.sum_nonneg fun k _ => by
    split_ifs
    · exact π.arrivalValueLoss_nonnegative B w c v k
    · exact le_rfl

/-- Greedy actions have zero local loss in their defining actual potential.
Identifying the potential with policy performance is a separate identity. -/
lemma FiniteIntensityHybridInstance.valueRule_arrivalValueLoss_zero
    (B : FiniteIntensityHybridInstance n) {w : ℝ} (hw : 0 < w) (c : ℝ)
    (v : HybridWorld n Unit) (k : Fin (n+v.1.1)) : (B.valueRule w c).arrivalValueLoss B w c v k = 0 := by
  let x := combinedValues v.2.1 v.1.2
  let u := combinedClocks v.2.2.1 v.1.2
  let θ := finiteHybridThreshold (B.valueHybridThreshold w c) v.1.1 ()
    (Model.unseen (Model.history Finset.univ x u (u k))) (u k) k
  have hAction : ((B.valueRule w c).asFinitePolicy v.1.1).action v.2.2.2 Finset.univ x u k = true ↔ θ ≤ x k := by
    rw [FiniteIntensityHybridInstance.valueRule,hybridThresholdRule_asFinitePolicy]
    simp only [Model.Policy.action,Model.thresholdPolicy,decide_eq_true_eq]
    rfl
  change max (w*x k) (w*θ)-(if _ then w*x k else w*θ) = 0
  by_cases h : θ ≤ x k
  · rw [if_pos (hAction.mpr h),max_eq_left (mul_le_mul_of_nonneg_left h hw.le),sub_self]
  · rw [if_neg (fun ha => h (hAction.mp ha)),max_eq_right
      (mul_le_mul_of_nonneg_left (not_le.mp h).le hw.le),sub_self]

lemma FiniteIntensityHybridInstance.valueRule_reachedValueLoss_zero
    (B : FiniteIntensityHybridInstance n) {w : ℝ} (hw : 0 < w) (c : ℝ) (v : HybridWorld n Unit) :
    (B.valueRule w c).reachedValueLoss B w c v = 0 := by
  unfold HybridRule.reachedValueLoss
  apply Finset.sum_eq_zero
  intro k _
  split_ifs
  · exact B.valueRule_arrivalValueLoss_zero hw c v k
  · rfl

lemma FiniteIntensityHybridInstance.finiteValueThreshold_jointMeasurable
    (B : FiniteIntensityHybridInstance n) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (N : ℕ) :
    Measurable (fun z : Finset (Fin (n+N)) × (Fin (n+N) × ℝ) =>
      finiteHybridThreshold (B.valueHybridThreshold w c) N () z.1 z.2.2 z.2.1) := by
  apply measurable_from_prod_countable_right
  intro A
  apply measurable_from_prod_countable_right
  intro k
  exact (finiteHybridThreshold_continuous (B.valueHybridThreshold w c) N ()
    (fun S i => B.valueHybridThreshold_continuous hw hc S i) A k).measurable

lemma FiniteIntensityHybridInstance.measurable_finiteContinuationAtArrival
    (B : FiniteIntensityHybridInstance n) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    {Ω : Type*} [MeasurableSpace Ω] {x u : Ω → Fin (n+N) → ℝ}
    (hx : ∀ i, Measurable (fun ω => x ω i)) (hu : ∀ i, Measurable (fun ω => u ω i)) (k : Fin (n+N)) :
    Measurable (fun ω => B.finiteContinuationAtArrival w c (x ω) (u ω) k) := by
  have hState := Model.measurable_unseen.comp (Model.measurable_history Finset.univ hx hu (hu k))
  have hθ := (B.finiteValueThreshold_jointMeasurable hw hc N).comp
    (hState.prodMk ((measurable_const (a := k)).prodMk (hu k)))
  exact hθ.const_mul w

end ProphetSecretary.Limiting
