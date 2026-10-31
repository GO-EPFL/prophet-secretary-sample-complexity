import ProphetSecretary.Probability.DeterministicClockSplit
import ProphetSecretary.Probability.BlockIndependence
import ProphetSecretary.Reach.Pending

/-!
# Observable prefix survival

Whether an online execution survives to a fixed time depends only on the observations
before that time. Fresh coordinates whose clocks remain at or after the fixed time may
be erased without changing that event. This functional fact is proved before applying
product-law independence.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

lemma history_congr_before_fresh (A D : Finset (Fin n)) (x x' u u' : Fin n → ℝ) (t : ℝ)
    (hx : ∀ j ∉ A, x j = x' j) (hu : ∀ j ∉ A, u j = u' j)
    (hf : ∀ j ∈ A, t ≤ u j) (hf' : ∀ j ∈ A, t ≤ u' j) {s : ℝ} (hs : s ≤ t) :
    history D x u s = history D x' u' s := by
  funext j
  by_cases hj : j ∈ A
  · have hno : ¬u j < s := not_lt_of_ge (hs.trans (hf j hj))
    have hno' : ¬u' j < s := not_lt_of_ge (hs.trans (hf' j hj))
    simp [history, hno, hno']
  · simp only [history, hx j hj, hu j hj]

lemma Policy.le_stoppingTime_iff_no_earlier_acceptance (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) {t : ℝ} (ht : t ≤ 1) :
    t ≤ π.stoppingTime r D x u ↔ ∀ j ∈ D, u j < t → π.action r D x u j = false := by
  constructor
  · intro h j hj hju
    cases ha : π.action r D x u j with
    | false => rfl
    | true =>
      have hjacc := (π.mem_accepted r D x u j).mpr ⟨hj, ha⟩
      have htime := h.trans (π.stoppingTime_le_of_accepted r D x u j hjacc)
      exact False.elim ((not_le_of_gt hju) htime)
  · intro h
    apply (π.le_stoppingTime_iff r D x u t).mpr
    refine ⟨ht, ?_⟩
    intro j hj
    by_contra htime
    have hju : u j < t := lt_of_not_ge htime
    have hjD := ((π.mem_accepted r D x u j).mp hj).1
    have hfalse := h j hjD hju
    have htrue := ((π.mem_accepted r D x u j).mp hj).2
    have hbad : (false : Bool) = true := hfalse.symm.trans htrue
    cases hbad

lemma Policy.le_stoppingTime_of_fresh_congr (π : Policy Seed n) (r : Seed)
    (A D : Finset (Fin n)) (x x' u u' : Fin n → ℝ) {t : ℝ} (ht : t ≤ 1)
    (hx : ∀ j ∉ A, x j = x' j) (hu : ∀ j ∉ A, u j = u' j)
    (hf : ∀ j ∈ A, t ≤ u j) (hf' : ∀ j ∈ A, t ≤ u' j)
    (hsurvive : t ≤ π.stoppingTime r D x u) : t ≤ π.stoppingTime r D x' u' := by
  rw [π.le_stoppingTime_iff_no_earlier_acceptance r D x' u' ht]
  intro j hj hju
  by_cases hjA : j ∈ A
  · exact False.elim ((not_lt_of_ge (hf' j hjA)) hju)
  · have hju0 : u j < t := by rw [hu j hjA]; exact hju
    have hhistory := history_congr_before_fresh A D x x' u u' t hx hu hf hf' hju.le
    have haction : π.action r D x u j = π.action r D x' u' j := by
      unfold Policy.action
      rw [hu j hjA, hx j hjA, hhistory]
    rw [← haction]
    exact (π.le_stoppingTime_iff_no_earlier_acceptance r D x u ht).mp hsurvive j hj hju0

lemma Policy.le_stoppingTime_iff_fresh_congr (π : Policy Seed n) (r : Seed)
    (A D : Finset (Fin n)) (x x' u u' : Fin n → ℝ) {t : ℝ} (ht : t ≤ 1)
    (hx : ∀ j ∉ A, x j = x' j) (hu : ∀ j ∉ A, u j = u' j)
    (hf : ∀ j ∈ A, t ≤ u j) (hf' : ∀ j ∈ A, t ≤ u' j) :
    t ≤ π.stoppingTime r D x u ↔ t ≤ π.stoppingTime r D x' u' :=
  ⟨π.le_stoppingTime_of_fresh_congr r A D x x' u u' ht hx hu hf hf',
    π.le_stoppingTime_of_fresh_congr r A D x' x u' u ht (fun j hj => (hx j hj).symm)
      (fun j hj => (hu j hj).symm) hf' hf⟩

noncomputable def observedPrefix (i : Fin n) (t : ℝ) (ω : World n Seed) : History n :=
  history (Finset.univ.erase i) ω.1 ω.2.1 t

lemma splitClocks_fresh_ge (A : Finset (Fin n)) (i : Fin n) (hAi : i ∉ A) {t : ℝ} (ht : t ≤ 1)
    (v : Fin n → ℝ) (hv : ∀ j ∈ A, 0 ≤ v j) (j : Fin n) (hj : j ∈ A) : t ≤ splitClocks A i t v j := by
  have hji : j ≠ i := by rintro rfl; exact hAi hj
  simp only [splitClocks, splitClock, if_neg hji, if_pos hj, Instance.tailClock]
  exact le_add_of_nonneg_right (mul_nonneg (sub_nonneg.mpr ht) (hv j hj))

lemma splitClocks_erased_fresh (A : Finset (Fin n)) (i : Fin n) (hAi : i ∉ A) (t : ℝ)
    (v : Fin n → ℝ) (j : Fin n) (hj : j ∈ A) : splitClocks A i t (eraseCoordinates A 0 v) j = t := by
  have hji : j ≠ i := by rintro rfl; exact hAi hj
  simp only [splitClocks, splitClock, if_neg hji, if_pos hj, eraseCoordinates, Instance.tailClock, mul_zero, add_zero]

lemma splitClocks_erase_outside (A : Finset (Fin n)) (i : Fin n) (t : ℝ)
    (v : Fin n → ℝ) (j : Fin n) (hj : j ∉ A) :
    splitClocks A i t (eraseCoordinates A 0 v) j = splitClocks A i t v j := by
  simp only [splitClocks, eraseCoordinates, if_neg hj]

lemma observedPrefix_split_erase (A : Finset (Fin n)) (i : Fin n) (hAi : i ∉ A) {t : ℝ} (ht : t ≤ 1)
    (ω : World n Seed) (hv : ∀ j ∈ A, 0 ≤ ω.2.1 j) :
    observedPrefix i t (splitWorld A i t (eraseSetWorld A ω)) = observedPrefix i t (splitWorld A i t ω) := by
  apply history_congr_before_fresh A (Finset.univ.erase i)
    (eraseCoordinates A 0 ω.1) ω.1 (splitClocks A i t (eraseCoordinates A 0 ω.2.1)) (splitClocks A i t ω.2.1) t
    (fun j hj => by simp only [eraseCoordinates, if_neg hj])
    (fun j hj => splitClocks_erase_outside A i t ω.2.1 j hj)
    (fun j hj => by rw [splitClocks_erased_fresh A i hAi t ω.2.1 j hj])
    (fun j hj => splitClocks_fresh_ge A i hAi ht ω.2.1 hv j hj) le_rfl

lemma Policy.pending_survival_split_erase (π : Policy Seed n) (A : Finset (Fin n)) (i : Fin n)
    (hAi : i ∉ A) {t : ℝ} (ht : t ≤ 1) (ω : World n Seed) (hv : ∀ j ∈ A, 0 ≤ ω.2.1 j) :
    t ≤ π.pendingTime ω.2.2 (splitWorld A i t (eraseSetWorld A ω)).1 (splitWorld A i t (eraseSetWorld A ω)).2.1 i ↔
      t ≤ π.pendingTime ω.2.2 (splitWorld A i t ω).1 (splitWorld A i t ω).2.1 i := by
  apply π.le_stoppingTime_iff_fresh_congr ω.2.2 A (Finset.univ.erase i)
    (eraseCoordinates A 0 ω.1) ω.1 (splitClocks A i t (eraseCoordinates A 0 ω.2.1)) (splitClocks A i t ω.2.1) ht
    (fun j hj => by simp only [eraseCoordinates, if_neg hj])
    (fun j hj => splitClocks_erase_outside A i t ω.2.1 j hj)
    (fun j hj => by rw [splitClocks_erased_fresh A i hAi t ω.2.1 j hj])
    (fun j hj => splitClocks_fresh_ge A i hAi ht ω.2.1 hv j hj)

variable [MeasurableSpace Seed]

lemma measurable_observedPrefix (i : Fin n) (t : ℝ) : Measurable (@observedPrefix n Seed i t) :=
  measurable_history (Finset.univ.erase i) (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) measurable_const

noncomputable def survivingPrefixWeight (π : Policy Seed n) (W : Seed × History n → ℝ)
    (A : Finset (Fin n)) (i : Fin n) (t : ℝ) (ω : World n Seed) : ℝ :=
  W (ω.2.2, observedPrefix i t (splitWorld A i t ω)) *
    (if t ≤ π.pendingTime ω.2.2 (splitWorld A i t ω).1 (splitWorld A i t ω).2.1 i then 1 else 0)

lemma measurable_survivingPrefixWeight (π : Policy Seed n) (hπ : π.IsMeasurable)
    (W : Seed × History n → ℝ) (hW : Measurable W) (A : Finset (Fin n)) (i : Fin n) (t : ℝ) :
    Measurable (survivingPrefixWeight π W A i t) := by
  have hprefix := (measurable_observedPrefix (Seed := Seed) i t).comp (measurable_splitWorld A i t)
  have hweight := hW.comp ((measurable_snd.comp measurable_snd).prodMk hprefix)
  have htime := (π.measurable_pendingWorldTime hπ i).comp (measurable_splitWorld A i t)
  exact hweight.mul (Measurable.ite (measurableSet_le measurable_const htime) measurable_const measurable_const)

omit [MeasurableSpace Seed] in
lemma survivingPrefixWeight_erase (π : Policy Seed n) (W : Seed × History n → ℝ)
    (A : Finset (Fin n)) (i : Fin n) (hAi : i ∉ A) {t : ℝ} (ht : t ≤ 1)
    (ω : World n Seed) (hv : ∀ j ∈ A, 0 ≤ ω.2.1 j) :
    survivingPrefixWeight π W A i t (eraseSetWorld A ω) = survivingPrefixWeight π W A i t ω := by
  have hprefix := observedPrefix_split_erase A i hAi ht ω hv
  have hsurvive := π.pending_survival_split_erase A i hAi ht ω hv
  have hweight : W ((eraseSetWorld A ω).2.2, observedPrefix i t (splitWorld A i t (eraseSetWorld A ω))) =
      W (ω.2.2, observedPrefix i t (splitWorld A i t ω)) :=
    congrArg W (Prod.ext rfl hprefix)
  unfold survivingPrefixWeight
  rw [hweight]
  congr 1
  exact ite_congr (propext hsurvive) (fun _ => rfl) (fun _ => rfl)

/-- Observable prefix survival and its multiplier are independent of the fresh block.
The independence is derived from proved functional erasure invariance. -/
lemma Instance.survivingPrefixWeight_fresh_independent (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy Seed n) (hπ : π.IsMeasurable) (W : Seed × History n → ℝ) (hW : Measurable W)
    (A : Finset (Fin n)) (i : Fin n) (hAi : i ∉ A) {t : ℝ} (ht : t ≤ 1) :
    IndepFun (survivingPrefixWeight π W A i t) (freshWorld A) (P.worldLaw ν) := by
  have h := (P.erasedWorld_freshWorld_independent ν A).comp
    (measurable_survivingPrefixWeight π hπ W hW A i t) measurable_id
  apply h.congr _ (Filter.EventuallyEq.rfl)
  filter_upwards [P.world_clocks_mem_unitInterval ν] with ω hω
  exact survivingPrefixWeight_erase π W A i hAi ht ω (fun j _ => (hω j).1)

end ProphetSecretary.Model
