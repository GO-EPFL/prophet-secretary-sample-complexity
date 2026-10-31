import ProphetSecretary.Model.Bellman
import ProphetSecretary.Model.CandidateSplit
import ProphetSecretary.Model.FirstArrivalChild

/-!
# The first online decision

The first candidate sees an empty history. On rejection, its observed identity, value,
and timestamp form a fixed rejected prefix, and the remaining execution is the causal
continuation from `ContinuationTransport`. The result is pathwise and assumes no policy
optimality. The child's identities retain their increasing original-label enumeration.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

noncomputable def firstPrefix {m : ℕ} (i : Fin m) (t x : ℝ) : History m :=
  Function.update (fun _ => none) i (some (t, x))

@[simp] lemma firstPrefix_same {m : ℕ} (i : Fin m) (t x : ℝ) :
    firstPrefix i t x i = some (t, x) := by simp [firstPrefix]

@[simp] lemma firstPrefix_ne {m : ℕ} (i j : Fin m) (t x : ℝ) (hji : j ≠ i) :
    firstPrefix i t x j = none := by simp [firstPrefix, hji]

variable {n : ℕ} {Seed : Type*}

def Policy.firstAction (π : Policy Seed (n + 1)) (r : Seed) (i : Fin (n + 1)) (t x : ℝ) : Bool :=
  π.decide r t i x (fun _ => none)

lemma validPrefix_firstPrefix (i : Fin (n + 1)) (t x : ℝ) :
    ValidPrefix (remainingSet i) t (firstPrefix i t x) := by
  constructor
  · intro j hj
    exact firstPrefix_ne i j t x (Finset.mem_erase.mp hj).1
  · intro j hj
    have hji : j = i := by simpa [remainingSet] using hj
    subst j
    exact ⟨t, x, firstPrefix_same i t x, le_rfl⟩

lemma extendValues_firstPrefix (i : Fin (n + 1)) (t x : ℝ)
    (y : Fin (remainingSet i).card → ℝ) :
    extendValues (remainingSet i) (firstPrefix i t x) y = insertCandidate i (x, y) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [extendValues, remainingSet, insertCandidate, observationValue]
  · simp [extendValues, remainingSet, insertCandidate, hji]

lemma extendClocks_firstPrefix (i : Fin (n + 1)) (t x : ℝ)
    (v : Fin (remainingSet i).card → ℝ) :
    extendClocks (remainingSet i) t (firstPrefix i t x) v = Instance.firstChildClocks i (t, v) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [extendClocks, remainingSet, Instance.firstChildClocks, insertCandidate, observationTime]
  · simp [extendClocks, remainingSet, Instance.firstChildClocks, insertCandidate, hji,
      Instance.tailClocks, Instance.tailClock]

@[simp] lemma firstChildClocks_same (i : Fin (n + 1)) (t : ℝ)
    (v : Fin (remainingSet i).card → ℝ) : Instance.firstChildClocks i (t, v) i = t := by
  simp [Instance.firstChildClocks]

lemma firstChildClocks_gt_of_ne (i j : Fin (n + 1)) {t : ℝ} (ht : t < 1)
    (v : Fin (remainingSet i).card → ℝ) (hv : ∀ k, 0 < v k) (hji : j ≠ i) :
    t < Instance.firstChildClocks i (t, v) j := by
  simp only [Instance.firstChildClocks, insertCandidate, dif_neg hji, Instance.tailClocks, Instance.tailClock]
  have hp := mul_pos (sub_pos.mpr ht) (hv (stateIndex (remainingSet i) j (by simp [remainingSet, hji])))
  linarith

lemma history_firstChildClocks (i : Fin (n + 1)) {t : ℝ} (ht : t < 1)
    (x : ℝ) (y v : Fin (remainingSet i).card → ℝ) (hv : ∀ k, 0 < v k) :
    history Finset.univ (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) t =
      (fun _ => none) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [history]
  · have hn := not_lt_of_ge (firstChildClocks_gt_of_ne i j ht v hv hji).le
    simp only [history, Finset.mem_univ, true_and, if_neg hn]

lemma Policy.action_firstChild (π : Policy Seed (n + 1)) (r : Seed) (i : Fin (n + 1))
    {t : ℝ} (ht : t < 1) (x : ℝ) (y v : Fin (remainingSet i).card → ℝ) (hv : ∀ k, 0 < v k) :
    π.action r Finset.univ (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) i =
      π.firstAction r i t x := by
  unfold Policy.action Policy.firstAction
  rw [firstChildClocks_same, insertCandidate_same, history_firstChildClocks i ht x y v hv]

lemma Policy.stoppingTime_first_accept (π : Policy Seed (n + 1)) (r : Seed) (i : Fin (n + 1))
    {t : ℝ} (ht : t < 1) (x : ℝ) (y v : Fin (remainingSet i).card → ℝ) (hv : ∀ k, 0 < v k)
    (ha : π.firstAction r i t x = true) :
    π.stoppingTime r Finset.univ (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) = t := by
  have hmem : i ∈ π.accepted r Finset.univ (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) := by
    apply (π.mem_accepted _ _ _ _ i).mpr
    exact ⟨Finset.mem_univ _, (π.action_firstChild r i ht x y v hv).trans ha⟩
  apply le_antisymm
  · simpa only [firstChildClocks_same] using π.stoppingTime_le_of_accepted r _ _ _ i hmem
  · apply (π.le_stoppingTime_iff r _ _ _ t).mpr
    refine ⟨ht.le, ?_⟩
    intro j _
    by_cases hji : j = i
    · subst j
      exact (firstChildClocks_same i t v).ge
    · exact (firstChildClocks_gt_of_ne i j ht v hv hji).le

lemma Policy.actualSelects_first_accept (π : Policy Seed (n + 1)) (r : Seed) (i : Fin (n + 1))
    {t : ℝ} (ht : t < 1) (x : ℝ) (y v : Fin (remainingSet i).card → ℝ) (hv : ∀ k, 0 < v k)
    (ha : π.firstAction r i t x = true) :
    π.ActualSelects r Finset.univ (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) i := by
  have hτ := π.stoppingTime_first_accept r i ht x y v hv ha
  refine ⟨⟨(π.mem_accepted _ _ _ _ i).mpr ⟨Finset.mem_univ _, (π.action_firstChild r i ht x y v hv).trans ha⟩,
    (firstChildClocks_same i t v).trans hτ.symm⟩, ?_⟩
  intro j hj
  by_cases hji : j = i
  · subst j
    exact le_rfl
  · have hg := firstChildClocks_gt_of_ne i j ht v hv hji
    rw [hj.2, hτ] at hg
    exact False.elim ((lt_irrefl t) hg)

lemma Policy.reward_first_accept (π : Policy Seed (n + 1)) (r : Seed) (i : Fin (n + 1))
    {t : ℝ} (ht : t < 1) (x : ℝ) (y v : Fin (remainingSet i).card → ℝ) (hv : ∀ k, 0 < v k)
    (ha : π.firstAction r i t x = true) :
    π.reward r Finset.univ (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) = x := by
  have h := π.reward_eq_of_actualSelects r Finset.univ (insertCandidate i (x, y))
    (Instance.firstChildClocks i (t, v)) (π.actualSelects_first_accept r i ht x y v hv ha)
  simpa only [insertCandidate_same] using h

lemma prefixBefore_firstPrefix (i : Fin (n + 1)) (t x : ℝ) :
    prefixBefore (firstPrefix i t x) t = (fun _ => none) := by
  funext j
  by_cases hji : j = i
  · subst j
    simp [prefixBefore, observationTime]
  · simp [prefixBefore, firstPrefix_ne i j t x hji, observationTime]

lemma Policy.prefixRejected_first_reject (π : Policy Seed (n + 1)) (r : Seed) (i : Fin (n + 1))
    (t x : ℝ) (ha : π.firstAction r i t x = false) :
    PrefixRejected π r (remainingSet i) (firstPrefix i t x) := by
  intro j hj
  have hji : j = i := by simpa [remainingSet] using hj
  subst j
  simpa only [firstPrefix_same, observationTime, observationValue, Option.elim_some,
    prefixBefore_firstPrefix, Policy.firstAction] using ha

/-- The exact scalar payoff decomposition at the first observed offer. No optimizer,
Markov restriction, or tie-free assumption on future clocks appears in this identity. -/
lemma Policy.firstDecision_scalarPayoff (π : Policy Seed (n + 1)) (r : Seed) (i : Fin (n + 1))
    {t : ℝ} (ht : t < 1) (x : ℝ) (y v : Fin (remainingSet i).card → ℝ) (hv : ∀ k, 0 < v k)
    (w c : ℝ) :
    w * π.reward r Finset.univ (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) +
      c * π.stoppingTime r Finset.univ (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) =
    c * t + if π.firstAction r i t x = true then w * x else
      (w * (π.fixedContinuation (remainingSet i) r t (firstPrefix i t x)).reward () Finset.univ y v +
        (c * (1 - t)) * (π.fixedContinuation (remainingSet i) r t (firstPrefix i t x)).stoppingTime
          () Finset.univ y v) := by
  by_cases ha : π.firstAction r i t x = true
  · rw [if_pos ha, π.reward_first_accept r i ht x y v hv ha,
      π.stoppingTime_first_accept r i ht x y v hv ha]
    ring
  · have hf : π.firstAction r i t x = false := by cases h : π.firstAction r i t x <;> simp_all
    rw [if_neg ha]
    have hs := π.scalarPayoff_extend (remainingSet i) ht (firstPrefix i t x)
      (validPrefix_firstPrefix i t x) r y v hv (π.prefixRejected_first_reject r i t x hf) w c
    rw [extendValues_firstPrefix, extendClocks_firstPrefix] at hs
    have hs' : w * π.reward r Finset.univ (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) +
        c * (π.stoppingTime r Finset.univ (insertCandidate i (x, y)) (Instance.firstChildClocks i (t, v)) - t) =
        w * (π.fixedContinuation (remainingSet i) r t (firstPrefix i t x)).reward () Finset.univ y v +
          (c * (1 - t)) * (π.fixedContinuation (remainingSet i) r t (firstPrefix i t x)).stoppingTime
            () Finset.univ y v := hs
    linarith

/-- The complete future vectors are integration variables, not observations passed to
the first decision. The displayed decision depends only on seed, identity, time and value. -/
abbrev FirstDecisionData (S : Type*) (i : Fin (n + 1)) :=
  S × (ℝ × (ℝ × ((Fin (remainingSet i).card → ℝ) × (Fin (remainingSet i).card → ℝ))))

noncomputable def Policy.firstChildPayoff (π : Policy Seed (n + 1)) (i : Fin (n + 1))
    (w c : ℝ) (z : FirstDecisionData Seed i) : ℝ :=
  w * π.reward z.1 Finset.univ (insertCandidate i (z.2.2.1, z.2.2.2.1))
      (Instance.firstChildClocks i (z.2.1, z.2.2.2.2)) +
    c * π.stoppingTime z.1 Finset.univ (insertCandidate i (z.2.2.1, z.2.2.2.1))
      (Instance.firstChildClocks i (z.2.1, z.2.2.2.2))

noncomputable def Policy.firstRemainingPayoff (π : Policy Seed (n + 1)) (i : Fin (n + 1))
    (w c : ℝ) (z : FirstDecisionData Seed i) : ℝ :=
  w * (π.fixedContinuation (remainingSet i) z.1 z.2.1 (firstPrefix i z.2.1 z.2.2.1)).reward
      () Finset.univ z.2.2.2.1 z.2.2.2.2 +
    (c * (1 - z.2.1)) *
      (π.fixedContinuation (remainingSet i) z.1 z.2.1 (firstPrefix i z.2.1 z.2.2.1)).stoppingTime
        () Finset.univ z.2.2.2.1 z.2.2.2.2

section Measurability

variable [MeasurableSpace Seed]

lemma measurable_firstPrefix (i : Fin (n + 1)) :
    Measurable (fun z : ℝ × ℝ => firstPrefix i z.1 z.2) := by
  apply measurable_pi_lambda
  intro j
  by_cases hji : j = i
  · subst j
    simp only [firstPrefix_same]
    rw [measurable_comap_iff]
    exact measurable_inr
  · simp only [firstPrefix_ne i j _ _ hji]
    exact measurable_const

lemma Policy.measurable_firstAction (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (i : Fin (n + 1)) : Measurable (fun z : Seed × (ℝ × ℝ) => π.firstAction z.1 i z.2.1 z.2.2) :=
  hπ.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk
    (measurable_const.prodMk (measurable_snd.snd.prodMk measurable_const))))

lemma Policy.measurable_firstChildPayoff (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (i : Fin (n + 1)) (w c : ℝ) : Measurable (π.firstChildPayoff i w c) := by
  let W := FirstDecisionData Seed i
  have hr : Measurable (fun z : W => z.1) := measurable_fst
  have ht : Measurable (fun z : W => z.2.1) := measurable_snd.fst
  have hx : Measurable (fun z : W => z.2.2.1) := measurable_snd.snd.fst
  have hy : Measurable (fun z : W => z.2.2.2.1) := measurable_snd.snd.snd.fst
  have hv : Measurable (fun z : W => z.2.2.2.2) := measurable_snd.snd.snd.snd
  have hvalues := (measurable_insertCandidate i).comp (hx.prodMk hy)
  have hclocks := (Instance.measurable_firstChildClocks i).comp (ht.prodMk hv)
  exact ((π.measurable_reward hπ hr (fun j => (measurable_pi_apply j).comp hvalues)
    (fun j => (measurable_pi_apply j).comp hclocks) Finset.univ).const_mul w).add
      ((π.measurable_stoppingTime hπ hr (fun j => (measurable_pi_apply j).comp hvalues)
        (fun j => (measurable_pi_apply j).comp hclocks) Finset.univ).const_mul c)

lemma Policy.measurable_firstRemainingPayoff (π : Policy Seed (n + 1)) (hπ : π.IsMeasurable)
    (i : Fin (n + 1)) (w c : ℝ) : Measurable (π.firstRemainingPayoff i w c) := by
  let W := FirstDecisionData Seed i
  have hr : Measurable (fun z : W => z.1) := measurable_fst
  have ht : Measurable (fun z : W => z.2.1) := measurable_snd.fst
  have hx : Measurable (fun z : W => z.2.2.1) := measurable_snd.snd.fst
  have hy : Measurable (fun z : W => z.2.2.2.1) := measurable_snd.snd.snd.fst
  have hv : Measurable (fun z : W => z.2.2.2.2) := measurable_snd.snd.snd.snd
  have hp := (measurable_firstPrefix i).comp (ht.prodMk hx)
  have hseed := hr.prodMk (ht.prodMk hp)
  have hcπ := π.continuationRule_isMeasurable hπ (remainingSet i)
  have hR := (π.continuationRule (remainingSet i)).measurable_reward hcπ hseed
    (fun j => (measurable_pi_apply j).comp hy) (fun j => (measurable_pi_apply j).comp hv) Finset.univ
  have hT := (π.continuationRule (remainingSet i)).measurable_stoppingTime hcπ hseed
    (fun j => (measurable_pi_apply j).comp hy) (fun j => (measurable_pi_apply j).comp hv) Finset.univ
  exact (hR.const_mul w).add ((measurable_const.mul (measurable_const.sub ht)).mul hT)

end Measurability
end ProphetSecretary.Model

