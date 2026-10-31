import ProphetSecretary.Model.ValueTransform

/-!
# A measurable prophet winner and its response

The smallest identity attaining a positive maximum wins. At a zero maximum the
response is zero, including the empty instance. This is an analytical full-vector
selection, not information available to an online policy. It is the tie-break
and D(φ) used in `upmom:stationarity`.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

def ProphetWins (x : Fin n → ℝ) (i : Fin n) : Prop :=
  0 < x i ∧ x i = Instance.maximum x ∧ ∀ j, x j = Instance.maximum x → i ≤ j

lemma prophetWins_unique {x : Fin n → ℝ} {i j : Fin n} (hi : ProphetWins x i) (hj : ProphetWins x j) : i = j :=
  le_antisymm (hi.2.2 j hj.2.1) (hj.2.2 i hi.2.1)

lemma exists_prophetWins {x : Fin n → ℝ} (hx : 0 < Instance.maximum x) : ∃ i, ProphetWins x i := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (Option (Fin n)))) ⟨none, Finset.mem_univ _⟩ (fun j => j.elim 0 x)
  have hmax : Instance.maximum x = j.elim 0 x := hj
  have hex : ∃ i, x i = Instance.maximum x := by
    cases j with
    | none => simp only [Option.elim_none] at hmax; linarith
    | some i => exact ⟨i, hmax.symm⟩
  let A := Finset.univ.filter fun i => x i = Instance.maximum x
  have hA : A.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  have heq := (Finset.mem_filter.mp (Finset.min'_mem A hA)).2
  refine ⟨A.min' hA, ?_, heq, ?_⟩
  · rw [heq]
    exact hx
  · intro i hi
    exact Finset.min'_le A i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)

lemma measurableSet_prophetWins (i : Fin n) : MeasurableSet {x : Fin n → ℝ | ProphetWins x i} := by
  apply (measurableSet_lt measurable_const (measurable_pi_apply i)).inter
  apply (measurableSet_eq_fun (measurable_pi_apply i) Instance.measurable_maximum).inter
  change MeasurableSet {x : Fin n → ℝ | ∀ j, x j = Instance.maximum x → i ≤ j}
  rw [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i ≤ j
  · simp [hij]
  · simpa only [hij, imp_false, Set.compl_setOf] using
      (measurableSet_eq_fun (measurable_pi_apply j) Instance.measurable_maximum).compl

noncomputable def prophetResponse (ψ : Fin n → ℝ → ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, if ProphetWins x i then ψ i (x i) else 0

lemma prophetResponse_eq_of_winner (ψ : Fin n → ℝ → ℝ) {x : Fin n → ℝ} {i : Fin n}
    (hi : ProphetWins x i) : prophetResponse ψ x = ψ i (x i) := by
  unfold prophetResponse
  rw [Finset.sum_eq_single i]
  · simp only [if_pos hi]
  · intro j _ hji
    have hj : ¬ProphetWins x j := fun hj => hji (prophetWins_unique hj hi)
    simp only [if_neg hj]
  · simp

lemma prophetResponse_zero_of_maximum_zero (ψ : Fin n → ℝ → ℝ) {x : Fin n → ℝ}
    (hx : Instance.maximum x = 0) : prophetResponse ψ x = 0 := by
  have hnone : ∀ i, ¬ProphetWins x i := by
    intro i hi
    have hxi := hi.2.1.trans hx
    linarith [hi.1]
  simp only [prophetResponse, hnone, if_false, Finset.sum_const_zero]

lemma measurable_prophetResponse (ψ : Fin n → ℝ → ℝ) (hψ : ∀ i, Measurable (ψ i)) :
    Measurable (prophetResponse ψ) := by
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (measurableSet_prophetWins i) ((hψ i).comp (measurable_pi_apply i)) measurable_const

lemma prophetResponse_abs_le (ψ : Fin n → ℝ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hψ : ∀ i a, |ψ i a| ≤ B) (x : Fin n → ℝ) : |prophetResponse ψ x| ≤ B := by
  by_cases hx : 0 < Instance.maximum x
  · obtain ⟨i, hi⟩ := exists_prophetWins hx
    rw [prophetResponse_eq_of_winner ψ hi]
    exact hψ i (x i)
  · have hz := le_antisymm (not_lt.mp hx) (Instance.maximum_nonnegative x)
    rw [prophetResponse_zero_of_maximum_zero ψ hz, abs_zero]
    exact hB

lemma maximum_perturbation_lower (ψ : Fin n → ℝ → ℝ) (t : ℝ) (x : Fin n → ℝ) :
    Instance.maximum x + t * prophetResponse ψ x ≤ Instance.maximum (fun i => x i + t * ψ i (x i)) := by
  by_cases hx : 0 < Instance.maximum x
  · obtain ⟨i, hi⟩ := exists_prophetWins hx
    rw [prophetResponse_eq_of_winner ψ hi, ← hi.2.1]
    exact Instance.le_maximum (fun j => x j + t * ψ j (x j)) i
  · have hz := le_antisymm (not_lt.mp hx) (Instance.maximum_nonnegative x)
    rw [prophetResponse_zero_of_maximum_zero ψ hz, hz, mul_zero, zero_add]
    exact Instance.maximum_nonnegative _

noncomputable def Instance.expectedProphetResponse (P : Instance n) (ψ : Fin n → ℝ → ℝ) : ℝ :=
  ∫ x, prophetResponse ψ x ∂P.valuesLaw

lemma Instance.integrable_prophetResponse (P : Instance n) (ψ : Fin n → ℝ → ℝ)
    (hψ : ∀ i, Measurable (ψ i)) (hbound : ∀ i a, |ψ i a| ≤ 1) :
    Integrable (prophetResponse ψ) P.valuesLaw := by
  apply Integrable.of_bound (measurable_prophetResponse ψ hψ).aestronglyMeasurable 1
  exact Eventually.of_forall fun x => by
    simpa only [Real.norm_eq_abs] using prophetResponse_abs_le ψ zero_le_one hbound x

lemma prophetResponse_neg (ψ : Fin n → ℝ → ℝ) (x : Fin n → ℝ) :
    prophetResponse (fun i a => -ψ i a) x = -prophetResponse ψ x := by
  simp only [prophetResponse, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

lemma Instance.expectedProphetResponse_neg (P : Instance n) (ψ : Fin n → ℝ → ℝ) :
    P.expectedProphetResponse (fun i a => -ψ i a) = -P.expectedProphetResponse ψ := by
  simp only [expectedProphetResponse, prophetResponse_neg, integral_neg]

/-- The old winning identity supports the new maximum. The expectation uses the
actual coordinate pushforward; no online policy observes this winner. -/
theorem Instance.expectedMaximum_perturbation_lower (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (ψ : Fin n → ℝ → ℝ)
    (hψ : ∀ i, Measurable (ψ i)) (hbound : ∀ i a, |ψ i a| ≤ 1) (t : ℝ)
    (hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ x + t * ψ i x) :
    P.expectedMaximum + t * P.expectedProphetResponse ψ ≤
      (P.mapValues (fun i x => x + t * ψ i x)
        (fun i => measurable_id.add ((hψ i).const_mul t)) hnn).expectedMaximum := by
  let f : Fin n → ℝ → ℝ := fun i x => x + t * ψ i x
  have hf : ∀ i, Measurable (f i) := fun i => measurable_id.add ((hψ i).const_mul t)
  have hd : ∀ i, ∀ᵐ x ∂P.law i, |f i x - x| ≤ |t| := by
    intro i
    exact Eventually.of_forall fun x => by
      dsimp [f]
      rw [add_sub_cancel_left, abs_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (hbound i x) (abs_nonneg t)
  have hQ := P.mapValues_integrable_of_bounded_displacement hP f hf hnn hd
  have hmap := P.mapValues_measurePreserving f hf hnn
  have hF := hmap.integrable_comp_of_integrable hQ
  have hi := integral_mono (hP.add ((P.integrable_prophetResponse ψ hψ hbound).const_mul t)) hF
    (fun x => maximum_perturbation_lower ψ t x)
  change (∫ x, Instance.maximum x + t * prophetResponse ψ x ∂P.valuesLaw) ≤
    (∫ x, Instance.maximum (fun i => f i (x i)) ∂P.valuesLaw) at hi
  rw [integral_add hP ((P.integrable_prophetResponse ψ hψ hbound).const_mul t), integral_const_mul] at hi
  have heq := integral_map (μ := P.valuesLaw) hmap.measurable.aemeasurable
    Instance.measurable_maximum.aestronglyMeasurable
  rw [hmap.map_eq] at heq
  exact hi.trans_eq heq.symm

end ProphetSecretary.Model
