import ProphetSecretary.Model.Simulation

/-!
# Simulating appended deterministic zero offers

The zero clocks are supplied as auxiliary randomness. At a base offer the simulator
reconstructs the augmented past, including all zero identities. If the original policy
would already have selected a zero, it rejects every remaining base offer and waits to
terminal time. Testing an earlier zero uses only the base history before that zero.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model.ZeroSimulation

variable {Seed : Type*} {n m : ℕ}

/-- Append deterministic zeros, retaining separate observable identities. -/
def appendValues (x : Fin n → ℝ) : Fin (n + m) → ℝ :=
  Fin.addCases x (fun _ => 0)

def appendClocks (u : Fin n → ℝ) (z : Fin m → ℝ) : Fin (n + m) → ℝ :=
  Fin.addCases u z

noncomputable def truncateObservation : Option (ℝ × ℝ) → ℝ → Option (ℝ × ℝ)
  | none, _ => none
  | some p, t => if p.1 < t then some p else none

noncomputable def truncateHistory (h : History n) (t : ℝ) : History n :=
  fun i => truncateObservation (h i) t

noncomputable def augmentedHistory (h : History n) (z : Fin m → ℝ) (t : ℝ) :
    History (n + m) :=
  Fin.addCases (truncateHistory h t)
    (fun j => if z j < t then some (z j, 0) else none)

theorem truncateHistory_history (x u : Fin n → ℝ) {s t : ℝ} (hst : s ≤ t) :
    truncateHistory (history Finset.univ x u t) s = history Finset.univ x u s := by
  funext i
  by_cases hs : u i < s
  · have ht : u i < t := hs.trans_le hst
    simp [truncateHistory, truncateObservation, history, hs, ht]
  · by_cases ht : u i < t
    · simp [truncateHistory, truncateObservation, history, hs, ht]
    · simp [truncateHistory, truncateObservation, history, hs, ht]

theorem augmentedHistory_history (x u : Fin n → ℝ) (z : Fin m → ℝ)
    {s t : ℝ} (hst : s ≤ t) :
    augmentedHistory (history Finset.univ x u t) z s =
      history Finset.univ (appendValues (m := m) x) (appendClocks u z) s := by
  funext k
  induction k using Fin.addCases with
  | left i =>
    simp only [augmentedHistory, Fin.addCases_left, truncateHistory_history x u hst]
    simp [history, appendValues, appendClocks]
  | right j => simp [augmentedHistory, history, appendValues, appendClocks]

/-- `z` is sampled independently before the base execution. The simulator does not
expose these clocks to the online values; it uses them only as internal policy randomness. -/
noncomputable def simulate (π : Policy Seed (n + m)) : Policy (Seed × (Fin m → ℝ)) n where
  decide rz t i v h :=
    π.decide rz.1 t (Fin.castAdd m i) v (augmentedHistory h rz.2 t) &&
      Decidable.decide (¬∃ j : Fin m, rz.2 j < t ∧
        π.decide rz.1 (rz.2 j) (Fin.natAdd n j) 0 (augmentedHistory h rz.2 (rz.2 j)) = true)

/-- The complete-vector notation here is analytical. The preceding construction uses
only observations before the current candidate. -/
def noZeroBefore (π : Policy Seed (n + m)) (r : Seed) (x u : Fin n → ℝ)
    (z : Fin m → ℝ) (t : ℝ) : Prop :=
  ¬∃ j : Fin m, z j < t ∧
    π.action r Finset.univ (appendValues x) (appendClocks u z) (Fin.natAdd n j) = true

theorem simulate_action_iff (π : Policy Seed (n + m)) (r : Seed)
    (x u : Fin n → ℝ) (z : Fin m → ℝ) (i : Fin n) :
    (simulate π).action (r, z) Finset.univ x u i = true ↔
      π.action r Finset.univ (appendValues x) (appendClocks u z) (Fin.castAdd m i) = true ∧
        noZeroBefore π r x u z (u i) := by
  simp only [Policy.action, simulate, Bool.and_eq_true, decide_eq_true_eq,
    appendValues, appendClocks, Fin.addCases_left]
  rw [augmentedHistory_history x u z (le_refl (u i))]
  refine and_congr_right fun _ => ?_
  unfold noZeroBefore Policy.action
  simp only [appendValues, appendClocks, Fin.addCases_right]
  apply not_congr
  constructor
  · rintro ⟨j, hj, ha⟩
    refine ⟨j, hj, ?_⟩
    rwa [augmentedHistory_history x u z hj.le] at ha
  · rintro ⟨j, hj, ha⟩
    refine ⟨j, hj, ?_⟩
    rwa [augmentedHistory_history x u z hj.le]

theorem noZeroBefore_mono (π : Policy Seed (n + m)) (r : Seed)
    (x u : Fin n → ℝ) (z : Fin m → ℝ) {s t : ℝ} (hst : s ≤ t)
    (ht : noZeroBefore π r x u z t) : noZeroBefore π r x u z s := by
  rintro ⟨j, hj, ha⟩
  exact ht ⟨j, hj.trans_le hst, ha⟩

/-- The simulator only deletes possible acceptances, and hence never stops earlier. -/
theorem stoppingTime_le_simulated (π : Policy Seed (n + m)) (r : Seed)
    (x u : Fin n → ℝ) (z : Fin m → ℝ) :
    π.stoppingTime r Finset.univ (appendValues x) (appendClocks u z) ≤
      (simulate π).stoppingTime (r, z) Finset.univ x u := by
  apply ((simulate π).le_stoppingTime_iff (r, z) Finset.univ x u _).mpr
  refine ⟨π.stoppingTime_le_one r _ _ _, ?_⟩
  intro i hi
  have ha := (simulate_action_iff π r x u z i).mp
    (((simulate π).mem_accepted (r, z) _ x u i).mp hi).2
  have hm := (π.mem_accepted r _ (appendValues x) (appendClocks u z) (Fin.castAdd m i)).mpr
    ⟨Finset.mem_univ _, ha.1⟩
  simpa [appendClocks] using π.stoppingTime_le_of_accepted r _ _ _ _ hm

/-- A selected base offer has exactly the same selection event in both executions. -/
theorem selects_base_iff (π : Policy Seed (n + m)) (r : Seed)
    (x u : Fin n → ℝ) (z : Fin m → ℝ) (hu : ∀ i, u i ≤ 1) (i : Fin n) :
    (simulate π).Selects (r, z) Finset.univ x u i ↔
      π.Selects r Finset.univ (appendValues x) (appendClocks u z) (Fin.castAdd m i) := by
  constructor
  · intro hi
    have ha := (simulate_action_iff π r x u z i).mp
      (((simulate π).mem_accepted (r, z) _ x u i).mp hi.1).2
    refine ⟨(π.mem_accepted r _ _ _ _).mpr ⟨Finset.mem_univ _, ha.1⟩, ?_⟩
    simp only [appendClocks, Fin.addCases_left]
    apply le_antisymm
    · apply (π.le_stoppingTime_iff r _ _ _ _).mpr
      refine ⟨hu i, ?_⟩
      intro k hk
      induction k using Fin.addCases with
      | left j =>
        simp only [appendClocks, Fin.addCases_left]
        by_contra hji
        have ht : u j < u i := lt_of_not_ge hji
        have hjaction := (π.mem_accepted r _ _ _ _).mp hk |>.2
        have hjsim := (simulate_action_iff π r x u z j).mpr
          ⟨hjaction, noZeroBefore_mono π r x u z ht.le ha.2⟩
        have hjsel := ((simulate π).mem_accepted (r, z) _ x u j).mpr
          ⟨Finset.mem_univ _, hjsim⟩
        have htime := (simulate π).stoppingTime_le_of_accepted (r, z) _ x u j hjsel
        rw [← hi.2] at htime
        exact (not_le_of_gt ht) htime
      | right j =>
        simp only [appendClocks, Fin.addCases_right]
        by_contra hj
        exact ha.2 ⟨j, lt_of_not_ge hj, ((π.mem_accepted r _ _ _ _).mp hk).2⟩
    · have hm := (π.mem_accepted r _ _ _ _).mpr ⟨Finset.mem_univ _, ha.1⟩
      simpa [appendClocks] using π.stoppingTime_le_of_accepted r _ _ _ _ hm
  · intro hi
    have htime : u i = π.stoppingTime r Finset.univ (appendValues x) (appendClocks u z) := by
      simpa [appendClocks] using hi.2
    have hn : noZeroBefore π r x u z (u i) := by
      rintro ⟨j, hj, hja⟩
      have hjm := (π.mem_accepted r _ _ _ _).mpr ⟨Finset.mem_univ _, hja⟩
      have hle := π.stoppingTime_le_of_accepted r _ _ _ _ hjm
      rw [← htime] at hle
      exact (not_le_of_gt hj) (by simpa [appendClocks] using hle)
    have ham := ((simulate π).mem_accepted (r, z) _ x u i).mpr
      ⟨Finset.mem_univ _, (simulate_action_iff π r x u z i).mpr
        ⟨((π.mem_accepted r _ _ _ _).mp hi.1).2, hn⟩⟩
    refine ⟨ham, le_antisymm ?_ ((simulate π).stoppingTime_le_of_accepted (r, z) _ x u i ham)⟩
    rw [htime]
    exact stoppingTime_le_simulated π r x u z

theorem actualSelects_base_iff (π : Policy Seed (n + m)) (r : Seed)
    (x u : Fin n → ℝ) (z : Fin m → ℝ) (hu : ∀ i, u i ≤ 1) (i : Fin n) :
    (simulate π).ActualSelects (r, z) Finset.univ x u i ↔
      π.ActualSelects r Finset.univ (appendValues x) (appendClocks u z) (Fin.castAdd m i) := by
  constructor
  · intro hi
    refine ⟨(selects_base_iff π r x u z hu i).mp hi.1, ?_⟩
    intro k hk
    induction k using Fin.addCases with
    | left j => exact hi.2 j ((selects_base_iff π r x u z hu j).mpr hk)
    | right j =>
      change i.val ≤ n + j.val
      exact i.isLt.le.trans (Nat.le_add_right n j.val)
  · intro hi
    refine ⟨(selects_base_iff π r x u z hu i).mpr hi.1, ?_⟩
    intro j hj
    exact hi.2 (Fin.castAdd m j) ((selects_base_iff π r x u z hu j).mp hj)

/-- Selecting an appended zero becomes waiting until terminal time. -/
theorem no_simulated_selection_of_zero (π : Policy Seed (n + m)) (r : Seed)
    (x u : Fin n → ℝ) (z : Fin m → ℝ) (hu : ∀ i, u i ≤ 1) (j : Fin m)
    (hj : π.ActualSelects r Finset.univ (appendValues x) (appendClocks u z) (Fin.natAdd n j)) :
    ∀ i, ¬(simulate π).ActualSelects (r, z) Finset.univ x u i := by
  intro i hi
  have hbase := (actualSelects_base_iff π r x u z hu i).mp hi
  have he := π.actualSelects_unique r Finset.univ (appendValues x) (appendClocks u z) hbase hj
  have hlt : Fin.castAdd m i < Fin.natAdd n j := by
    change i.val < n + j.val
    exact i.isLt.trans_le (Nat.le_add_right n j.val)
  exact (ne_of_lt hlt) he

theorem simulated_stoppingTime_eq_one_of_zero (π : Policy Seed (n + m)) (r : Seed)
    (x u : Fin n → ℝ) (z : Fin m → ℝ) (hu : ∀ i, u i ≤ 1) (j : Fin m)
    (hj : π.ActualSelects r Finset.univ (appendValues x) (appendClocks u z) (Fin.natAdd n j)) :
    (simulate π).stoppingTime (r, z) Finset.univ x u = 1 :=
  (simulate π).stoppingTime_eq_one_of_no_actualSelection (r, z) Finset.univ x u
    (no_simulated_selection_of_zero π r x u z hu j hj)

/-- Exact reward preservation holds on every outcome with base clocks in `[0,1]`.
No injectivity assumption is needed: the deterministic identity tie-break is preserved. -/
theorem reward_eq (π : Policy Seed (n + m)) (r : Seed)
    (x u : Fin n → ℝ) (z : Fin m → ℝ) (hu : ∀ i, u i ≤ 1) :
    (simulate π).reward (r, z) Finset.univ x u =
      π.reward r Finset.univ (appendValues x) (appendClocks u z) := by
  by_cases h : ∃ k, π.ActualSelects r Finset.univ (appendValues x) (appendClocks u z) k
  · obtain ⟨k, hk⟩ := h
    induction k using Fin.addCases with
    | left i =>
      rw [(simulate π).reward_eq_of_actualSelects (r, z) Finset.univ x u
        ((actualSelects_base_iff π r x u z hu i).mpr hk),
        π.reward_eq_of_actualSelects r Finset.univ (appendValues x) (appendClocks u z) hk]
      simp [appendValues]
    | right j =>
      rw [(simulate π).reward_eq_zero_of_no_actualSelection (r, z) Finset.univ x u
        (no_simulated_selection_of_zero π r x u z hu j hk),
        π.reward_eq_of_actualSelects r Finset.univ (appendValues x) (appendClocks u z) hk]
      simp [appendValues]
  · have hs : ∀ i, ¬(simulate π).ActualSelects (r, z) Finset.univ x u i := by
      intro i hi
      exact h ⟨Fin.castAdd m i, (actualSelects_base_iff π r x u z hu i).mp hi⟩
    rw [(simulate π).reward_eq_zero_of_no_actualSelection (r, z) Finset.univ x u hs,
      π.reward_eq_zero_of_no_actualSelection r Finset.univ (appendValues x) (appendClocks u z)
        (fun k hk => h ⟨k, hk⟩)]

private def observationEncode : Option (ℝ × ℝ) → Unit ⊕ (ℝ × ℝ)
  | none => Sum.inl ()
  | some p => Sum.inr p

private theorem measurable_observationEncode : Measurable observationEncode := by
  exact Measurable.of_comap_le le_rfl

private def observationTime : Option (ℝ × ℝ) → ℝ
  | none => 0
  | some p => p.1

private theorem measurable_observationTime : Measurable observationTime := by
  have h : Measurable (fun o => Sum.elim (fun _ : Unit => (0 : ℝ)) Prod.fst
      (observationEncode o)) :=
    ((measurable_const : Measurable (fun _ : Unit => (0 : ℝ))).sumElim
      measurable_fst).comp measurable_observationEncode
  convert h using 1
  funext o
  cases o <;> rfl

private theorem measurable_observationSome : Measurable (@some (ℝ × ℝ)) := by
  rw [measurable_comap_iff]
  exact measurable_inr

private theorem truncateObservation_eq (o : Option (ℝ × ℝ)) (t : ℝ) :
    truncateObservation o t = if o ≠ none ∧ observationTime o < t then o else none := by
  cases o <;> simp [truncateObservation, observationTime]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Truncating a previously observed past to an earlier time preserves measurability. -/
theorem measurable_truncateObservation {o : Ω → Option (ℝ × ℝ)} {t : Ω → ℝ}
    (ho : Measurable o) (ht : Measurable t) :
    Measurable fun ω => truncateObservation (o ω) (t ω) := by
  have hn : MeasurableSet {ω | o ω = none} := by
    have hs : MeasurableSet (Set.range (Sum.inl : Unit → Unit ⊕ (ℝ × ℝ))) :=
      measurableSet_range_inl
    have h := hs.preimage (measurable_observationEncode.comp ho)
    convert h using 1
    ext ω
    cases hω : o ω <;> simp [observationEncode, hω]
  have hc : MeasurableSet {ω | o ω ≠ none ∧ observationTime (o ω) < t ω} :=
    hn.compl.inter (measurableSet_lt (measurable_observationTime.comp ho) ht)
  convert Measurable.ite hc ho (measurable_const : Measurable fun _ : Ω =>
    (none : Option (ℝ × ℝ))) using 1
  funext ω
  exact truncateObservation_eq (o ω) (t ω)

theorem measurable_augmentedHistory {h : Ω → History n} {z : Ω → Fin m → ℝ} {t : Ω → ℝ}
    (hh : ∀ i, Measurable fun ω => h ω i) (hz : ∀ j, Measurable fun ω => z ω j)
    (ht : Measurable t) : Measurable fun ω => augmentedHistory (h ω) (z ω) (t ω) := by
  apply measurable_pi_lambda
  intro k
  induction k using Fin.addCases with
  | left i =>
    simpa only [augmentedHistory, Fin.addCases_left, truncateHistory] using
      measurable_truncateObservation (hh i) ht
  | right j =>
    have hs : Measurable (fun ω => some (z ω j, (0 : ℝ))) :=
      measurable_observationSome.comp ((hz j).prodMk measurable_const)
    convert measurable_truncateObservation hs ht using 1
    funext ω
    simp [augmentedHistory, truncateObservation]

variable [MeasurableSpace Seed]

/-- Adding independent zero clocks to the seed yields an admissible randomized base
policy. This regularity follows from the explicit history reconstruction above. -/
theorem simulate_isMeasurable (π : Policy Seed (n + m)) (hπ : π.IsMeasurable) :
    (simulate π).IsMeasurable := by
  let W := (Seed × (Fin m → ℝ)) × (ℝ × (Fin n × (ℝ × History n)))
  have hr : Measurable (fun w : W => w.1.1) := measurable_fst.fst
  have hz : ∀ j, Measurable (fun w : W => w.1.2 j) :=
    fun j => (measurable_pi_apply j).comp measurable_fst.snd
  have ht : Measurable (fun w : W => w.2.1) := measurable_snd.fst
  have hv : Measurable (fun w : W => w.2.2.2.1) := measurable_snd.snd.snd.fst
  have hh : ∀ i, Measurable (fun w : W => w.2.2.2.2 i) :=
    fun i => (measurable_pi_apply i).comp measurable_snd.snd.snd.snd
  have hid : Measurable (fun w : W => Fin.castAdd m w.2.2.1) :=
    (measurable_of_finite (Fin.castAdd m)).comp measurable_snd.snd.fst
  have hb : Measurable (fun w : W => π.decide w.1.1 w.2.1 (Fin.castAdd m w.2.2.1)
      w.2.2.2.1 (augmentedHistory w.2.2.2.2 w.1.2 w.2.1)) :=
    hπ.comp (hr.prodMk (ht.prodMk (hid.prodMk
      (hv.prodMk (measurable_augmentedHistory hh hz ht)))))
  have hj : ∀ j : Fin m, Measurable (fun w : W => π.decide w.1.1 (w.1.2 j)
      (Fin.natAdd n j) 0 (augmentedHistory w.2.2.2.2 w.1.2 (w.1.2 j))) := by
    intro j
    exact hπ.comp (hr.prodMk ((hz j).prodMk (measurable_const.prodMk
      (measurable_const.prodMk (measurable_augmentedHistory hh hz (hz j))))))
  have he : MeasurableSet {w : W | ∃ j : Fin m, w.1.2 j < w.2.1 ∧
      π.decide w.1.1 (w.1.2 j) (Fin.natAdd n j) 0
        (augmentedHistory w.2.2.2.2 w.1.2 (w.1.2 j)) = true} := by
    rw [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro j
    exact (measurableSet_lt (hz j) ht).inter ((hj j) (measurableSet_singleton true))
  apply measurable_to_bool
  convert (hb (measurableSet_singleton true)).inter he.compl using 1
  ext w
  simp only [simulate, Bool.and_eq_true, decide_eq_true_eq, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff]
  rfl

end ProphetSecretary.Model.ZeroSimulation
