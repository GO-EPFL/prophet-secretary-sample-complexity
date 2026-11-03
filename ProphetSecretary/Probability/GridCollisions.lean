import ProphetSecretary.Probability.FairBitUniform
import ProphetSecretary.Model.Independence
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Fin

/-!
# Collisions of independent rounded uniforms

A pair of distinct coordinates collides with probability `1/N`. The union
is over unordered pairs, giving the factor `n(n-1)/2` for a vector of size
`n`. The same law is obtained by independent fair-bit decoding.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators

namespace ProphetSecretary.Probability
open ProphetSecretary.Model

noncomputable def gridIndexVectorLaw (n N : ℕ) (hN : 0 < N) : Measure (Fin n → Fin N) :=
  Measure.pi (fun _ => uniformGridIndexLaw N hN)

instance gridIndexVectorLaw_probability (n N : ℕ) (hN : 0 < N) :
    IsProbabilityMeasure (gridIndexVectorLaw n N hN) := by unfold gridIndexVectorLaw; infer_instance

lemma measurePreserving_gridIndexVector (n N : ℕ) (hN : 0 < N) :
    MeasurePreserving (fun u : Fin n → ℝ => fun i => uniformGridIndex N hN (u i))
      (Instance.clocksLaw n) (gridIndexVectorLaw n N hN) :=
  measurePreserving_pi _ _ (fun _ => ⟨measurable_uniformGridIndex N hN,map_uniformGridIndex N hN⟩)

lemma measurePreserving_fairIndexVector (n b : ℕ) :
    MeasurePreserving (fun u : Fin n → Fin b → Bool => fun i => fairBitsIndex b (u i))
      (Measure.pi (fun _ : Fin n => fairBitVectorLaw b)) (gridIndexVectorLaw n (2^b) (by positivity)) :=
  measurePreserving_pi _ _ (fun _ => ⟨measurable_of_countable _,map_fairBitsIndex b⟩)

lemma gridIndex_pair_collision {n N : ℕ} (hN : 0 < N) (i j : Fin n) (hij : i ≠ j) :
    (gridIndexVectorLaw n N hN).real {u | u i = u j} = 1/(N:ℝ) := by
  let μ := gridIndexVectorLaw n N hN
  let ν := uniformGridIndexLaw N hN
  let E := fun a : Fin N => {u : Fin n → Fin N | u i = a ∧ u j = a}
  have hI : iIndepFun (fun q : Fin n => fun u : Fin n → Fin N => u q) μ :=
    iIndepFun_pi (μ := fun _ : Fin n => ν) (X := fun _ => id) (fun _ => aemeasurable_id)
  have hp (q : Fin n) : MeasurePreserving (fun u : Fin n → Fin N => u q) μ ν :=
    measurePreserving_eval (fun _ : Fin n => ν) q
  have hE (a : Fin N) : μ.real (E a) = (1/(N:ℝ))*(1/(N:ℝ)) := by
    change (μ ((fun u : Fin n → Fin N => u i) ⁻¹' {a} ∩
      (fun u : Fin n → Fin N => u j) ⁻¹' {a})).toReal = _
    rw [(hI.indepFun hij).measure_inter_preimage_eq_mul _ _ (measurableSet_singleton a) (measurableSet_singleton a),
      (hp i).measure_preimage (measurableSet_singleton a).nullMeasurableSet,
      (hp j).measure_preimage (measurableSet_singleton a).nullMeasurableSet, ENNReal.toReal_mul]
    change ν.real {a} * ν.real {a} = _
    rw [uniformGridIndexLaw_real_singleton]
  have hdisj : Pairwise (fun a b => Disjoint (E a) (E b)) := by
    intro a b hab
    exact Set.disjoint_left.mpr (fun u hu hv => hab (hu.1.symm.trans hv.1))
  have hcover : {u : Fin n → Fin N | u i = u j} = ⋃ a, E a := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, E]
    exact ⟨fun h => ⟨u i,rfl,h.symm⟩, fun ⟨_,hi,hj⟩ => hi.trans hj.symm⟩
  rw [hcover, measureReal_iUnion_fintype (μ := μ) hdisj (fun _ => (Set.to_countable _).measurableSet)]
  simp_rw [hE]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp [show (N:ℝ) ≠ 0 by positivity]

theorem gridIndex_collision_probability (n N : ℕ) (hN : 0 < N) :
    (gridIndexVectorLaw n N hN).real {u | ¬Function.Injective u} ≤
      ((n:ℝ)*((n:ℝ)-1))/(2*(N:ℝ)) := by
  let μ := gridIndexVectorLaw n N hN
  let E := fun (j i : Fin n) => {u : Fin n → Fin N | u i = u j}
  have hC : {u : Fin n → Fin N | ¬Function.Injective u} =
      ⋃ j : Fin n, ⋃ i ∈ Finset.Iio j, E j i := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_Iio, E]
    constructor
    · intro h
      change ¬∀ a b, u a = u b → a = b at h
      simp only [not_forall] at h
      obtain ⟨a,b,he,hne⟩ := h
      rcases lt_or_gt_of_ne hne with hab | hba
      · exact ⟨b,a,hab,he⟩
      · exact ⟨a,b,hba,he.symm⟩
    · rintro ⟨j,i,hij,he⟩ hu
      exact hij.ne (hu he)
  rw [hC]
  calc
    _ ≤ ∑ j : Fin n, μ.real (⋃ i ∈ Finset.Iio j, E j i) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ j : Fin n, ∑ i ∈ Finset.Iio j, μ.real (E j i) :=
      Finset.sum_le_sum (fun j _ => measureReal_biUnion_finset_le _ _)
    _ = ∑ j : Fin n, (j.val:ℝ)*(1/(N:ℝ)) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_congr rfl (fun i hi => gridIndex_pair_collision hN i j (Finset.mem_Iio.mp hi).ne)]
      simp [Fin.card_Iio, nsmul_eq_mul]
    _ = _ := by
      rw [← Finset.sum_mul, ← Nat.cast_sum]
      have hc : (∑ j : Fin n, j.val)*2 = n*(n-1) := by
        rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i) n]
        exact Finset.sum_range_id_mul_two n
      cases n with
      | zero => simp
      | succ n =>
        have hc' : ((∑ j : Fin (n+1), j.val):ℝ)*2 = (n+1:ℝ)*n := by exact_mod_cast hc
        push_cast
        field_simp
        linarith

theorem roundedUniform_collision_probability (n N : ℕ) (hN : 0 < N) :
    (Instance.clocksLaw n).real {u | ¬Function.Injective (fun i => uniformGridIndex N hN (u i))} ≤
      ((n:ℝ)*((n:ℝ)-1))/(2*(N:ℝ)) := by
  let E := {u : Fin n → Fin N | ¬Function.Injective u}
  have h := (measurePreserving_gridIndexVector n N hN).measure_preimage
    (Set.to_countable E).measurableSet.nullMeasurableSet
  have he := congrArg ENNReal.toReal h
  change (Instance.clocksLaw n).real {u | ¬Function.Injective (fun i => uniformGridIndex N hN (u i))} =
      (gridIndexVectorLaw n N hN).real E at he
  exact he.le.trans (gridIndex_collision_probability n N hN)

end ProphetSecretary.Probability
