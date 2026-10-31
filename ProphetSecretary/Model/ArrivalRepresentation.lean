import ProphetSecretary.Model.Arrival

/-!
# Arrival orders and invariant clock information

For the uniform-clock model, any measurable event unchanged by relabeling clocks is
independent of the arrival order. In particular the sorted arrival times satisfy this
invariance. This is the event-level factorization underlying internal timestamp simulation.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators

namespace ProphetSecretary.Model.Instance

variable {n : ℕ}

/-- Every relabeling-invariant event factors from each strict arrival order. -/
lemma arrivalOrder_invariant_event (B : Set (Fin n → ℝ)) (hB : MeasurableSet B)
    (hInv : ∀ (p : Equiv.Perm (Fin n)) u, (fun k => u (p k)) ∈ B ↔ u ∈ B)
    (p : Equiv.Perm (Fin n)) :
    clocksLaw n (B ∩ {u | HasArrivalOrder u p}) =
      clocksLaw n B * (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞)⁻¹ := by
  have hequal (q : Equiv.Perm (Fin n)) :
      clocksLaw n (B ∩ {u | HasArrivalOrder u q}) =
        clocksLaw n (B ∩ {u | HasArrivalOrder u (Equiv.refl (Fin n))}) := by
    have h := (clock_reindex_measurePreserving q).measure_preimage
      (hB.inter (measurableSet_hasArrivalOrder (Equiv.refl (Fin n)))).nullMeasurableSet
    have he : (fun u : Fin n → ℝ => fun k => u (q k)) ⁻¹'
        (B ∩ {u | HasArrivalOrder u (Equiv.refl (Fin n))}) = B ∩ {u | HasArrivalOrder u q} := by
      ext u
      change ((fun k => u (q k)) ∈ B ∧ StrictMono (fun k => u (q k))) ↔
        (u ∈ B ∧ StrictMono (fun k => u (q k)))
      rw [hInv]
    rw [he] at h
    exact h
  have hd : Pairwise (fun p q : Equiv.Perm (Fin n) =>
      Disjoint (B ∩ {u | HasArrivalOrder u p}) (B ∩ {u | HasArrivalOrder u q})) := by
    intro p q hpq
    apply Set.disjoint_left.mpr
    intro u hp hq
    exact hpq (arrivalOrder_unique hp.2 hq.2)
  have hae : (⋃ q : Equiv.Perm (Fin n), B ∩ {u | HasArrivalOrder u q}) =ᵐ[clocksLaw n] B := by
    filter_upwards [clocks_pairwise_distinct (n := n)] with u hu
    apply propext
    constructor
    · intro h
      obtain ⟨q, hq⟩ := Set.mem_iUnion.mp h
      exact hq.1
    · intro h
      obtain ⟨q, hq⟩ := exists_arrivalOrder hu
      exact Set.mem_iUnion.mpr ⟨q, h, hq⟩
  have hm := measure_congr hae
  rw [measure_iUnion hd (fun q => hB.inter (measurableSet_hasArrivalOrder q)), tsum_fintype] at hm
  simp_rw [hequal] at hm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hm
  let c : ℝ≥0∞ := Fintype.card (Equiv.Perm (Fin n))
  have hc0 : c ≠ 0 := by simp [c, Fintype.card_ne_zero]
  have hctop : c ≠ ∞ := by simp [c]
  rw [hequal]
  calc
    clocksLaw n (B ∩ {u | HasArrivalOrder u (Equiv.refl (Fin n))}) =
        (clocksLaw n (B ∩ {u | HasArrivalOrder u (Equiv.refl (Fin n))}) * c) * c⁻¹ := by
      rw [mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, mul_one]
    _ = clocksLaw n B * c⁻¹ := by rw [mul_comm _ c, hm]

/-- The finite permutation space carries its discrete σ-algebra. -/
instance arrivalPermutationMeasurableSpace : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

instance arrivalPermutationMeasurableSingleton : MeasurableSingletonClass (Equiv.Perm (Fin n)) :=
  ⟨fun _ => trivial⟩

lemma measurableSet_injective_clocks : MeasurableSet {u : Fin n → ℝ | Function.Injective u} := by
  change MeasurableSet {u : Fin n → ℝ | ∀ i j, u i = u j → i = j}
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i = j
  · subst j; simp
  · have he : {u : Fin n → ℝ | u i = u j → i = j} = {u | u i ≠ u j} := by
      ext u
      simp [hij]
    rw [he]
    exact (measurableSet_eq_fun (f := fun u : Fin n → ℝ => u i)
      (g := fun u : Fin n → ℝ => u j) (by fun_prop) (by fun_prop)).compl

/-- The unique strict arrival order on tie-free vectors; arbitrary identity order on ties. -/
noncomputable def arrivalPermutation (u : Fin n → ℝ) : Equiv.Perm (Fin n) :=
  if hu : Function.Injective u then (exists_arrivalOrder hu).choose else Equiv.refl (Fin n)

lemma hasArrivalOrder_arrivalPermutation {u : Fin n → ℝ} (hu : Function.Injective u) :
    HasArrivalOrder u (arrivalPermutation u) := by
  simpa only [arrivalPermutation, dif_pos hu] using (exists_arrivalOrder hu).choose_spec

lemma arrivalPermutation_eq_iff {u : Fin n → ℝ} (hu : Function.Injective u)
    (p : Equiv.Perm (Fin n)) : arrivalPermutation u = p ↔ HasArrivalOrder u p := by
  constructor
  · intro hp; rw [← hp]; exact hasArrivalOrder_arrivalPermutation hu
  · exact fun hp => arrivalOrder_unique (hasArrivalOrder_arrivalPermutation hu) hp

lemma measurable_arrivalPermutation : Measurable (@arrivalPermutation n) := by
  classical
  apply measurable_to_countable'
  intro p
  have he : arrivalPermutation ⁻¹' {p} =
      ({u : Fin n → ℝ | Function.Injective u} ∩ {u | HasArrivalOrder u p}) ∪
      (if p = Equiv.refl (Fin n) then {u | ¬Function.Injective u} else ∅) := by
    ext u
    by_cases hu : Function.Injective u
    · simp [hu, arrivalPermutation_eq_iff hu]
    · simp [arrivalPermutation, hu, eq_comm]
  rw [he]
  apply MeasurableSet.union (measurableSet_injective_clocks.inter (measurableSet_hasArrivalOrder p))
  split_ifs
  · exact measurableSet_injective_clocks.compl
  · exact MeasurableSet.empty

/-- Sorted numerical clock vector. On the null tie event it is set to zero, ensuring
invariance under relabeling on every vector. -/
noncomputable def sortedClocks (u : Fin n → ℝ) : Fin n → ℝ :=
  if Function.Injective u then fun k => u (arrivalPermutation u k) else fun _ => 0

lemma measurable_sortedClocks : Measurable (@sortedClocks n) := by
  apply measurable_pi_lambda
  intro k
  simp only [sortedClocks, ite_apply]
  apply Measurable.ite measurableSet_injective_clocks _ measurable_const
  have h : Measurable (fun z : (Fin n → ℝ) × Equiv.Perm (Fin n) => z.1 (z.2 k)) := by
    apply measurable_from_prod_countable_left
    intro p
    exact measurable_pi_apply (p k)
  exact h.comp (measurable_id.prodMk measurable_arrivalPermutation)

lemma sortedClocks_reindex (p : Equiv.Perm (Fin n)) (u : Fin n → ℝ) :
    sortedClocks (fun k => u (p k)) = sortedClocks u := by
  have hi : Function.Injective (fun k => u (p k)) ↔ Function.Injective u :=
    ⟨fun h a b hab => p.symm.injective (h (by simpa using hab)), fun h => h.comp p.injective⟩
  by_cases hu : Function.Injective u
  · have hp := hasArrivalOrder_arrivalPermutation hu
    have hq := hasArrivalOrder_arrivalPermutation (hi.mpr hu)
    have he : Set.range (fun k => u (arrivalPermutation u k)) =
        Set.range (fun k => u (p (arrivalPermutation (fun j => u (p j)) k))) := by
      ext y
      constructor
      · rintro ⟨k, rfl⟩
        refine ⟨(arrivalPermutation (fun j => u (p j))).symm (p.symm (arrivalPermutation u k)), ?_⟩
        simp
      · rintro ⟨k, rfl⟩
        exact ⟨(arrivalPermutation u).symm (p (arrivalPermutation (fun j => u (p j)) k)), by simp⟩
    have heq := hp.range_inj hq |>.mp he
    simpa only [sortedClocks, if_pos hu, if_pos (hi.mpr hu)] using heq.symm
  · simp only [sortedClocks, if_neg hu, if_neg (fun h => hu (hi.mp h))]

/-- The sorted clock information factors from every arrival order. -/
lemma sortedClocks_arrivalOrder_event (s : Set (Fin n → ℝ)) (hs : MeasurableSet s)
    (p : Equiv.Perm (Fin n)) :
    clocksLaw n (sortedClocks ⁻¹' s ∩ {u | HasArrivalOrder u p}) =
      clocksLaw n (sortedClocks ⁻¹' s) * (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞)⁻¹ := by
  exact arrivalOrder_invariant_event _ (measurable_sortedClocks hs)
    (fun p u => by rw [mem_preimage, sortedClocks_reindex, mem_preimage]) p

lemma arrivalPermutation_fiber_ae (p : Equiv.Perm (Fin n)) :
    arrivalPermutation ⁻¹' {p} =ᵐ[clocksLaw n] {u | HasArrivalOrder u p} := by
  filter_upwards [clocks_pairwise_distinct (n := n)] with u hu
  apply propext
  exact arrivalPermutation_eq_iff hu p

lemma arrivalPermutation_singleton_probability (p : Equiv.Perm (Fin n)) :
    clocksLaw n (arrivalPermutation ⁻¹' {p}) = (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞)⁻¹ := by
  rw [measure_congr (arrivalPermutation_fiber_ae p)]
  exact arrivalOrder_probability p

private lemma indepFun_of_finite_fibers {Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B] [Fintype B] [MeasurableSingletonClass B]
    {μ : Measure Ω} {f : Ω → A} {g : Ω → B} (hf : Measurable f) (hg : Measurable g)
    (hatom : ∀ s, MeasurableSet s → ∀ b,
      μ (f ⁻¹' s ∩ g ⁻¹' {b}) = μ (f ⁻¹' s) * μ (g ⁻¹' {b})) : IndepFun f g μ := by
  classical
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs _
  let T : Finset B := t.toFinite.toFinset
  have he : g ⁻¹' t = ⋃ b ∈ T, g ⁻¹' {b} := by ext ω; simp [T]
  have hd : (↑T : Set B).PairwiseDisjoint (fun b => g ⁻¹' {b}) := by
    intro b _ c _ hbc
    apply Set.disjoint_left.mpr
    intro ω hb hc
    exact hbc (hb.symm.trans hc)
  have hdf : (↑T : Set B).PairwiseDisjoint (fun b => f ⁻¹' s ∩ g ⁻¹' {b}) := by
    intro b hb c hc hbc
    exact (hd hb hc hbc).mono inter_subset_right inter_subset_right
  calc
    μ (f ⁻¹' s ∩ g ⁻¹' t) = ∑ b ∈ T, μ (f ⁻¹' s ∩ g ⁻¹' {b}) := by
      rw [he]
      simp_rw [Set.inter_iUnion]
      exact measure_biUnion_finset hdf (fun b _ => (hf hs).inter (hg (measurableSet_singleton b)))
    _ = μ (f ⁻¹' s) * ∑ b ∈ T, μ (g ⁻¹' {b}) := by
      simp_rw [hatom s hs]
      rw [Finset.mul_sum]
    _ = μ (f ⁻¹' s) * μ (g ⁻¹' t) := by
      rw [he, measure_biUnion_finset hd (fun b _ => hg (measurableSet_singleton b))]

/-- The complete sorted vector is independent of the uniformly random identity order. -/
lemma sortedClocks_arrivalPermutation_independent :
    IndepFun (@sortedClocks n) arrivalPermutation (clocksLaw n) := by
  apply indepFun_of_finite_fibers measurable_sortedClocks measurable_arrivalPermutation
  intro s hs p
  have he := arrivalPermutation_fiber_ae (n := n) p
  have he' : (sortedClocks ⁻¹' s ∩ arrivalPermutation ⁻¹' {p} : Set (Fin n → ℝ)) =ᵐ[clocksLaw n]
      (sortedClocks ⁻¹' s ∩ {u | HasArrivalOrder u p} : Set (Fin n → ℝ)) := by
    filter_upwards [he] with u hu
    change (arrivalPermutation u = p) = HasArrivalOrder u p at hu
    change (sortedClocks u ∈ s ∧ arrivalPermutation u = p) =
      (sortedClocks u ∈ s ∧ HasArrivalOrder u p)
    rw [hu]
  rw [measure_congr he', arrivalPermutation_singleton_probability]
  exact sortedClocks_arrivalOrder_event s hs p

/-- Uniform law on identity orders, expressed as normalized counting measure. -/
noncomputable def uniformPermutationLaw (n : ℕ) : Measure (Equiv.Perm (Fin n)) :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℝ≥0∞)⁻¹ • Measure.count

lemma arrivalPermutation_map :
    (clocksLaw n).map arrivalPermutation = uniformPermutationLaw n := by
  apply Measure.ext_of_singleton
  intro p
  rw [Measure.map_apply measurable_arrivalPermutation (measurableSet_singleton p),
    arrivalPermutation_singleton_probability]
  simp [uniformPermutationLaw]

instance uniformPermutationLaw_probability : IsProbabilityMeasure (uniformPermutationLaw n) := by
  rw [← arrivalPermutation_map]
  exact Measure.isProbabilityMeasure_map measurable_arrivalPermutation.aemeasurable

/-- Assign sorted times successively to the identities specified by `p`. -/
def reconstructClocks (z : (Fin n → ℝ) × Equiv.Perm (Fin n)) : Fin n → ℝ :=
  fun i => z.1 (z.2.symm i)

lemma measurable_reconstructClocks : Measurable (@reconstructClocks n) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_from_prod_countable_left
  intro p
  exact measurable_pi_apply (p.symm i)

lemma reconstruct_sorted_arrivalPermutation {u : Fin n → ℝ} (hu : Function.Injective u) :
    reconstructClocks (sortedClocks u, arrivalPermutation u) = u := by
  funext i
  simp [reconstructClocks, sortedClocks, hu]

/-- The joint law is the product of the sorted-time law and the uniform identity order. -/
lemma sortedClocks_arrivalPermutation_jointLaw :
    (clocksLaw n).map (fun u => (sortedClocks u, arrivalPermutation u)) =
      ((clocksLaw n).map sortedClocks).prod (uniformPermutationLaw n) := by
  rw [← arrivalPermutation_map]
  exact sortedClocks_arrivalPermutation_independent.map_prod_eq_prod_map_map
    measurable_sortedClocks.aemeasurable measurable_arrivalPermutation.aemeasurable

/-- Sampling sorted times independently of a uniform identity order and assigning
those times successively reconstructs independent uniform clocks exactly in law. -/
lemma reconstructClocks_measurePreserving :
    MeasurePreserving (@reconstructClocks n)
      (((clocksLaw n).map sortedClocks).prod (uniformPermutationLaw n)) (clocksLaw n) := by
  refine ⟨measurable_reconstructClocks, ?_⟩
  rw [← sortedClocks_arrivalPermutation_jointLaw,
    Measure.map_map measurable_reconstructClocks (measurable_sortedClocks.prodMk measurable_arrivalPermutation)]
  have he : (reconstructClocks ∘ fun u : Fin n → ℝ => (sortedClocks u, arrivalPermutation u)) =ᵐ[clocksLaw n] id := by
    filter_upwards [clocks_pairwise_distinct (n := n)] with u hu
    exact reconstruct_sorted_arrivalPermutation hu
  rw [Measure.map_congr he, Measure.map_id]

end ProphetSecretary.Model.Instance
