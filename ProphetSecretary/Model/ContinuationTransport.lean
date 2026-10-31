import ProphetSecretary.Model.Continuation
import ProphetSecretary.Reach.ReachHorizonRescaling

/-!
# Transporting an observed continuation state

The continuation rule retains all observed identities, values, and timestamps,
including zero observations, as a fixed prefix. Future timestamps are rescaled
from the remaining physical interval to `[0,1]`. Only the future past is supplied
at each decision; the completed future vector is used only to compare executions.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

def observationTime (o : Option (ℝ × ℝ)) : ℝ := o.elim 0 Prod.fst

def observationValue (o : Option (ℝ × ℝ)) : ℝ := o.elim 0 Prod.snd

/-- Restore physical elapsed time to a normalized future observation. -/
def continuationObservation (s : ℝ) : Option (ℝ × ℝ) → Option (ℝ × ℝ) :=
  Option.map (fun p ↦ (s + (1 - s) * p.1, p.2))

/-- The index of an original unseen identity in the state's increasing enumeration. -/
noncomputable def stateIndex (A : Finset (Fin n)) (i : Fin n) (hi : i ∈ A) : Fin A.card :=
  (A.orderIsoOfFin rfl).symm ⟨i, hi⟩

@[simp] lemma stateIndex_stateEmbedding (A : Finset (Fin n)) (j : Fin A.card) :
    stateIndex A (stateEmbedding A j) (A.orderEmbOfFin_mem rfl j) = j := by
  change (A.orderIsoOfFin rfl).symm ((A.orderIsoOfFin rfl) j) = j
  exact OrderIso.symm_apply_apply _ _

@[simp] lemma stateEmbedding_stateIndex (A : Finset (Fin n)) (i : Fin n) (hi : i ∈ A) :
    stateEmbedding A (stateIndex A i hi) = i := by
  change ((A.orderIsoOfFin rfl) ((A.orderIsoOfFin rfl).symm ⟨i, hi⟩) : Fin n) = i
  simp only [OrderIso.apply_symm_apply]

/-- An observed prefix has no observation at unseen identities. Every other
identity has a recorded time and value, with timestamp at most `s`. -/
def ValidPrefix (A : Finset (Fin n)) (s : ℝ) (H : History n) : Prop :=
  (∀ i ∈ A, H i = none) ∧
  (∀ i ∉ A, ∃ t x, H i = some (t, x) ∧ t ≤ s)

/-- Merge the fixed observed prefix with the past of future offers. -/
noncomputable def continuationHistory (A : Finset (Fin n)) (s : ℝ)
    (H : History n) (K : History A.card) : History n :=
  fun i ↦ if hi : i ∈ A then continuationObservation s (K (stateIndex A i hi)) else H i

noncomputable def extendValues (A : Finset (Fin n)) (H : History n)
    (y : Fin A.card → ℝ) : Fin n → ℝ :=
  fun i ↦ if hi : i ∈ A then y (stateIndex A i hi) else observationValue (H i)

noncomputable def extendClocks (A : Finset (Fin n)) (s : ℝ) (H : History n)
    (v : Fin A.card → ℝ) : Fin n → ℝ :=
  fun i ↦ if hi : i ∈ A then s + (1 - s) * v (stateIndex A i hi) else observationTime (H i)

lemma stateEmbedding_mem (A : Finset (Fin n)) (j : Fin A.card) : stateEmbedding A j ∈ A :=
  A.orderEmbOfFin_mem rfl j

@[simp] lemma extendValues_stateEmbedding (A : Finset (Fin n)) (H : History n)
    (y : Fin A.card → ℝ) (j : Fin A.card) :
    extendValues A H y (stateEmbedding A j) = y j := by
  simp only [extendValues, dif_pos (stateEmbedding_mem A j), stateIndex_stateEmbedding]

@[simp] lemma extendClocks_stateEmbedding (A : Finset (Fin n)) (s : ℝ) (H : History n)
    (v : Fin A.card → ℝ) (j : Fin A.card) :
    extendClocks A s H v (stateEmbedding A j) = s + (1 - s) * v j := by
  simp only [extendClocks, dif_pos (stateEmbedding_mem A j), stateIndex_stateEmbedding]

/-- The new seed retains the original seed, elapsed time, and observed prefix.
No future observations are encoded in this seed. -/
noncomputable def Policy.continuationRule (π : Policy Seed n) (A : Finset (Fin n)) :
    Policy (Seed × (ℝ × History n)) A.card where
  decide z t j x K := π.decide z.1 (z.2.1 + (1 - z.2.1) * t)
    (stateEmbedding A j) x (continuationHistory A z.2.1 z.2.2 K)

lemma continuationHistory_history (A : Finset (Fin n)) {s : ℝ} (hs : s < 1)
    (H : History n) (hH : ValidPrefix A s H) (y v : Fin A.card → ℝ)
    {t : ℝ} (ht : 0 < t) :
    continuationHistory A s H (history Finset.univ y v t) =
      history Finset.univ (extendValues A H y) (extendClocks A s H v)
        (s + (1 - s) * t) := by
  funext i
  have hpos : 0 < 1 - s := sub_pos.mpr hs
  by_cases hi : i ∈ A
  · simp only [continuationHistory, extendValues, extendClocks, dif_pos hi,
      history, Finset.mem_univ, true_and, add_lt_add_iff_left,
      mul_lt_mul_iff_right₀ hpos, continuationObservation]
    split_ifs <;> rfl
  · obtain ⟨u, x, hobs, hu⟩ := hH.2 i hi
    have hbefore : u < s + (1 - s) * t := by nlinarith
    simp only [continuationHistory, extendValues, extendClocks, dif_neg hi,
      hobs, observationValue, observationTime, Option.elim_some,
      history, Finset.mem_univ, true_and, if_pos hbefore]

lemma Policy.continuationRule_action (π : Policy Seed n) (A : Finset (Fin n))
    {s : ℝ} (hs : s < 1) (H : History n) (hH : ValidPrefix A s H)
    (r : Seed) (y v : Fin A.card → ℝ) (j : Fin A.card) (hv : 0 < v j) :
    (π.continuationRule A).action (r, s, H) Finset.univ y v j =
      π.action r Finset.univ (extendValues A H y) (extendClocks A s H v) (stateEmbedding A j) := by
  simp only [Policy.action, Policy.continuationRule, extendValues_stateEmbedding,
    extendClocks_stateEmbedding, continuationHistory_history A hs H hH y v hv]

/-- The strict past of an already observed prefix. -/
noncomputable def prefixBefore (H : History n) (t : ℝ) : History n :=
  fun i ↦ if observationTime (H i) < t then H i else none

/-- The observed decisions in a continuation state have all rejected. This is
an assertion about the observable prefix, with no dependence on future offers. -/
def PrefixRejected (π : Policy Seed n) (r : Seed) (A : Finset (Fin n)) (H : History n) : Prop :=
  ∀ i ∉ A, π.decide r (observationTime (H i)) i (observationValue (H i))
    (prefixBefore H (observationTime (H i))) = false

lemma history_extend_before_prefix (A : Finset (Fin n)) {s : ℝ} (hs : s < 1)
    (H : History n) (hH : ValidPrefix A s H) (y v : Fin A.card → ℝ)
    (hv : ∀ j, 0 < v j) {t : ℝ} (ht : t ≤ s) :
    history Finset.univ (extendValues A H y) (extendClocks A s H v) t = prefixBefore H t := by
  funext i
  by_cases hi : i ∈ A
  · have hfuture : ¬s + (1 - s) * v (stateIndex A i hi) < t := by
      have hh := hv (stateIndex A i hi)
      nlinarith
    simp only [history, Finset.mem_univ, true_and, extendClocks, dif_pos hi,
      if_neg hfuture, prefixBefore, hH.1 i hi, observationTime, Option.elim_none]
    split_ifs <;> rfl
  · obtain ⟨u, x, ho, _hu⟩ := hH.2 i hi
    simp only [history, Finset.mem_univ, true_and, extendClocks, extendValues,
      dif_neg hi, prefixBefore, ho, observationTime, observationValue, Option.elim_some]

lemma Policy.action_extend_observed (π : Policy Seed n) (A : Finset (Fin n))
    {s : ℝ} (hs : s < 1) (H : History n) (hH : ValidPrefix A s H)
    (r : Seed) (y v : Fin A.card → ℝ) (hv : ∀ j, 0 < v j)
    (i : Fin n) (hi : i ∉ A) :
    π.action r Finset.univ (extendValues A H y) (extendClocks A s H v) i =
      π.decide r (observationTime (H i)) i (observationValue (H i))
        (prefixBefore H (observationTime (H i))) := by
  obtain ⟨u, x, ho, hu⟩ := hH.2 i hi
  simp only [Policy.action, extendClocks, extendValues, dif_neg hi]
  rw [history_extend_before_prefix A hs H hH y v hv (by simpa only [ho, observationTime, Option.elim_some] using hu)]

lemma Policy.accepted_extend (π : Policy Seed n) (A : Finset (Fin n))
    {s : ℝ} (hs : s < 1) (H : History n) (hH : ValidPrefix A s H)
    (r : Seed) (y v : Fin A.card → ℝ) (hv : ∀ j, 0 < v j)
    (hReject : PrefixRejected π r A H) :
    π.accepted r Finset.univ (extendValues A H y) (extendClocks A s H v) =
      ((π.continuationRule A).accepted (r, s, H) Finset.univ y v).image (stateEmbedding A) := by
  ext i
  constructor
  · intro hi
    have hiA : i ∈ A := by
      by_contra hn
      have hf := (π.action_extend_observed A hs H hH r y v hv i hn).trans (hReject i hn)
      have ht := (π.mem_accepted _ _ _ _ i).mp hi |>.2
      rw [hf] at ht
      cases ht
    let j := stateIndex A i hiA
    have hej : stateEmbedding A j = i := stateEmbedding_stateIndex A i hiA
    apply Finset.mem_image.mpr
    refine ⟨j, ?_, hej⟩
    apply ((π.continuationRule A).mem_accepted _ _ _ _ j).mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [π.continuationRule_action A hs H hH r y v j (hv j), hej]
    exact ((π.mem_accepted _ _ _ _ i).mp hi).2
  · intro hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    apply (π.mem_accepted _ _ _ _ _).mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← π.continuationRule_action A hs H hH r y v j (hv j)]
    exact (((π.continuationRule A).mem_accepted _ _ _ _ j).mp hj).2

/-- Restarting after a rejected prefix gives physical stopping time
`s+(1-s)τ`; if no future offer is accepted this is exactly one. -/
lemma Policy.stoppingTime_extend (π : Policy Seed n) (A : Finset (Fin n))
    {s : ℝ} (hs : s < 1) (H : History n) (hH : ValidPrefix A s H)
    (r : Seed) (y v : Fin A.card → ℝ) (hv : ∀ j, 0 < v j)
    (hReject : PrefixRejected π r A H) :
    π.stoppingTime r Finset.univ (extendValues A H y) (extendClocks A s H v) =
      s + (1 - s) * (π.continuationRule A).stoppingTime (r, s, H) Finset.univ y v := by
  have ht : s + (1 - s) * 1 = 1 := by ring
  have hset : π.stopTimes r Finset.univ (extendValues A H y) (extendClocks A s H v) =
      ((π.continuationRule A).stopTimes (r, s, H) Finset.univ y v).image
        (fun t ↦ s + (1 - s) * t) := by
    simp only [Policy.stopTimes, π.accepted_extend A hs H hH r y v hv hReject,
      Finset.image_insert, Finset.image_image, Function.comp_def, extendClocks_stateEmbedding, ht]
  unfold Policy.stoppingTime
  simp only [hset]
  have hf : Monotone (fun t : ℝ ↦ s + (1 - s) * t) := by
    intro a b hab
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hab (sub_nonneg.mpr hs.le))
  exact Finset.min'_image hf _ _

/-- Additional stopping time measured from the beginning of the remaining
horizon; its default is `1-s` when no future offer is selected. -/
lemma Policy.additionalDuration_extend (π : Policy Seed n) (A : Finset (Fin n))
    {s : ℝ} (hs : s < 1) (H : History n) (hH : ValidPrefix A s H)
    (r : Seed) (y v : Fin A.card → ℝ) (hv : ∀ j, 0 < v j)
    (hReject : PrefixRejected π r A H) :
    π.stoppingTime r Finset.univ (extendValues A H y) (extendClocks A s H v) - s =
      (1 - s) * (π.continuationRule A).stoppingTime (r, s, H) Finset.univ y v := by
  rw [π.stoppingTime_extend A hs H hH r y v hv hReject]
  ring

lemma Policy.selects_extend (π : Policy Seed n) (A : Finset (Fin n))
    {s : ℝ} (hs : s < 1) (H : History n) (hH : ValidPrefix A s H)
    (r : Seed) (y v : Fin A.card → ℝ) (hv : ∀ j, 0 < v j)
    (hReject : PrefixRejected π r A H) (j : Fin A.card) :
    π.Selects r Finset.univ (extendValues A H y) (extendClocks A s H v) (stateEmbedding A j) ↔
      (π.continuationRule A).Selects (r, s, H) Finset.univ y v j := by
  simp only [Policy.Selects, Policy.mem_accepted, Finset.mem_univ, true_and,
    ← π.continuationRule_action A hs H hH r y v j (hv j), extendClocks_stateEmbedding,
    π.stoppingTime_extend A hs H hH r y v hv hReject, add_right_inj,
    mul_right_inj' (ne_of_gt (sub_pos.mpr hs))]

lemma Policy.actualSelects_extend (π : Policy Seed n) (A : Finset (Fin n))
    {s : ℝ} (hs : s < 1) (H : History n) (hH : ValidPrefix A s H)
    (r : Seed) (y v : Fin A.card → ℝ) (hv : ∀ j, 0 < v j)
    (hReject : PrefixRejected π r A H) (j : Fin A.card) :
    π.ActualSelects r Finset.univ (extendValues A H y) (extendClocks A s H v) (stateEmbedding A j) ↔
      (π.continuationRule A).ActualSelects (r, s, H) Finset.univ y v j := by
  constructor
  · rintro ⟨hj, hmin⟩
    refine ⟨(π.selects_extend A hs H hH r y v hv hReject j).mp hj, ?_⟩
    intro k hk
    have h := hmin (stateEmbedding A k) ((π.selects_extend A hs H hH r y v hv hReject k).mpr hk)
    exact (A.orderEmbOfFin rfl).le_iff_le.mp h
  · rintro ⟨hj, hmin⟩
    refine ⟨(π.selects_extend A hs H hH r y v hv hReject j).mpr hj, ?_⟩
    intro i hi
    have hiA : i ∈ A := by
      by_contra hn
      have hf := (π.action_extend_observed A hs H hH r y v hv i hn).trans (hReject i hn)
      have ht := (π.mem_accepted _ _ _ _ i).mp hi.1 |>.2
      rw [hf] at ht
      cases ht
    let k := stateIndex A i hiA
    have hek : stateEmbedding A k = i := stateEmbedding_stateIndex A i hiA
    have hk := (π.selects_extend A hs H hH r y v hv hReject k).mp (by simpa only [hek] using hi)
    have h := (A.orderEmbOfFin rfl).monotone (hmin k hk)
    change stateEmbedding A j ≤ stateEmbedding A k at h
    simpa only [hek] using h

/-- The selected reward is preserved by continuation transport. The increasing
identity embedding also preserves tie breaking, so no tie-free hypothesis is needed. -/
lemma Policy.reward_extend (π : Policy Seed n) (A : Finset (Fin n))
    {s : ℝ} (hs : s < 1) (H : History n) (hH : ValidPrefix A s H)
    (r : Seed) (y v : Fin A.card → ℝ) (hv : ∀ j, 0 < v j)
    (hReject : PrefixRejected π r A H) :
    π.reward r Finset.univ (extendValues A H y) (extendClocks A s H v) =
      (π.continuationRule A).reward (r, s, H) Finset.univ y v := by
  unfold Policy.reward
  have hzero : ∀ i ∉ A, ¬π.ActualSelects r Finset.univ
      (extendValues A H y) (extendClocks A s H v) i := by
    intro i hi hsel
    have hf := (π.action_extend_observed A hs H hH r y v hv i hi).trans (hReject i hi)
    have ht := (π.mem_accepted _ _ _ _ i).mp hsel.1.1 |>.2
    rw [hf] at ht
    cases ht
  rw [← Finset.sum_subset (Finset.subset_univ A) (by intro i _hi hn; simp only [if_neg (hzero i hn)])]
  have hA : Finset.univ.image (stateEmbedding A) = A := A.image_orderEmbOfFin_univ rfl
  rw (occs := .pos [1]) [← hA]
  rw [Finset.sum_image (by intro i _hi j _hj hij; exact (stateEmbedding A).injective hij)]
  apply Finset.sum_congr rfl
  intro j _hj
  simp only [π.actualSelects_extend A hs H hH r y v hv hReject j, extendValues_stateEmbedding]

/-- The continuation's duration coefficient becomes `c(1-s)` after rescaling;
the accrued duration payoff `cs` is excluded from the additional value. -/
lemma Policy.scalarPayoff_extend (π : Policy Seed n) (A : Finset (Fin n))
    {s : ℝ} (hs : s < 1) (H : History n) (hH : ValidPrefix A s H)
    (r : Seed) (y v : Fin A.card → ℝ) (hv : ∀ j, 0 < v j)
    (hReject : PrefixRejected π r A H) (w c : ℝ) :
    w * π.reward r Finset.univ (extendValues A H y) (extendClocks A s H v) +
      c * (π.stoppingTime r Finset.univ (extendValues A H y) (extendClocks A s H v) - s) =
      w * (π.continuationRule A).reward (r, s, H) Finset.univ y v +
        (c * (1 - s)) * (π.continuationRule A).stoppingTime (r, s, H) Finset.univ y v := by
  rw [π.reward_extend A hs H hH r y v hv hReject,
    π.additionalDuration_extend A hs H hH r y v hv hReject]
  ring

section Measurability

variable [MeasurableSpace Seed]

private def observationEncoding : Option (ℝ × ℝ) → Unit ⊕ (ℝ × ℝ) :=
  fun o ↦ match o with | none => Sum.inl () | some p => Sum.inr p

private lemma measurable_observationEncoding : Measurable observationEncoding :=
  Measurable.of_comap_le le_rfl

lemma measurable_observationTime : Measurable observationTime := by
  have hm : Measurable (Sum.elim (fun _ : Unit ↦ (0 : ℝ)) (Prod.fst : ℝ × ℝ → ℝ)) :=
    measurable_const.sumElim measurable_fst
  convert hm.comp measurable_observationEncoding using 1
  funext o
  cases o <;> rfl

lemma measurable_observationValue : Measurable observationValue := by
  have hm : Measurable (Sum.elim (fun _ : Unit ↦ (0 : ℝ)) (Prod.snd : ℝ × ℝ → ℝ)) :=
    measurable_const.sumElim measurable_snd
  convert hm.comp measurable_observationEncoding using 1
  funext o
  cases o <;> rfl

lemma measurableSet_observation_none : MeasurableSet {o : Option (ℝ × ℝ) | o = none} := by
  convert measurable_observationEncoding
    (measurableSet_range_inl (α := Unit) (β := ℝ × ℝ)) using 1
  ext o
  cases o <;> simp [observationEncoding]

lemma measurable_continuationObservation :
    Measurable (fun z : ℝ × Option (ℝ × ℝ) ↦ continuationObservation z.1 z.2) := by
  rw [measurable_comap_iff]
  have ht : Measurable (fun z : ℝ × Option (ℝ × ℝ) ↦ observationTime z.2) :=
    measurable_observationTime.comp measurable_snd
  have hx : Measurable (fun z : ℝ × Option (ℝ × ℝ) ↦ observationValue z.2) :=
    measurable_observationValue.comp measurable_snd
  have htime : Measurable (fun z : ℝ × Option (ℝ × ℝ) ↦ z.1 + (1 - z.1) * observationTime z.2) :=
    measurable_fst.add ((measurable_const.sub measurable_fst).mul ht)
  have hcond : MeasurableSet {z : ℝ × Option (ℝ × ℝ) | z.2 = none} :=
    measurableSet_observation_none.preimage measurable_snd
  have hIf : Measurable (fun z : ℝ × Option (ℝ × ℝ) ↦
      if z.2 = none then (Sum.inl () : Unit ⊕ (ℝ × ℝ)) else
        Sum.inr (z.1 + (1 - z.1) * observationTime z.2, observationValue z.2)) :=
    Measurable.ite hcond measurable_const (measurable_inr.comp (htime.prodMk hx))
  convert hIf using 1
  funext z
  rcases z with ⟨s, o⟩
  cases o <;> simp <;> rfl

lemma measurable_continuationHistory (A : Finset (Fin n)) :
    Measurable (fun z : ℝ × (History n × History A.card) ↦
      continuationHistory A z.1 z.2.1 z.2.2) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i ∈ A
  · simp only [continuationHistory, dif_pos hi]
    exact measurable_continuationObservation.comp
      (measurable_fst.prodMk ((measurable_pi_apply (stateIndex A i hi)).comp
        (measurable_snd.comp measurable_snd)))
  · simp only [continuationHistory, dif_neg hi]
    exact (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)

lemma measurable_prefixBefore : Measurable (fun z : History n × ℝ ↦ prefixBefore z.1 z.2) := by
  apply measurable_pi_lambda
  intro i
  have hobs : Measurable (fun z : History n × ℝ ↦ z.1 i) :=
    (measurable_pi_apply i).comp measurable_fst
  have hcond := measurableSet_lt (measurable_observationTime.comp hobs) measurable_snd
  exact Measurable.ite hcond hobs measurable_const

/-- Whether a fixed finite observed prefix has survived is itself observable
and measurable; this test cannot inspect any unseen coordinate. -/
lemma Policy.measurableSet_prefixRejected (π : Policy Seed n) (hπ : π.IsMeasurable)
    (A : Finset (Fin n)) :
    MeasurableSet {z : Seed × (ℝ × History n) | PrefixRejected π z.1 A z.2.2} := by
  classical
  change MeasurableSet {z : Seed × (ℝ × History n) | ∀ i, i ∉ A → _}
  rw [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  by_cases hi : i ∈ A
  · simp [hi]
  have hobs : Measurable (fun z : Seed × (ℝ × History n) ↦ z.2.2 i) :=
    (measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)
  have ht := measurable_observationTime.comp hobs
  have hx := measurable_observationValue.comp hobs
  have hH : Measurable (fun z : Seed × (ℝ × History n) ↦ z.2.2) :=
    measurable_snd.comp measurable_snd
  have hbefore := measurable_prefixBefore.comp (hH.prodMk ht)
  have hm : Measurable (fun z : Seed × (ℝ × History n) ↦
      π.decide z.1 (observationTime (z.2.2 i)) i (observationValue (z.2.2 i))
        (prefixBefore z.2.2 (observationTime (z.2.2 i)))) :=
    hπ.comp (measurable_fst.prodMk (ht.prodMk ((measurable_const (a := i)).prodMk (hx.prodMk hbefore))))
  have hfalse : MeasurableSet {z : Seed × (ℝ × History n) |
      π.decide z.1 (observationTime (z.2.2 i)) i (observationValue (z.2.2 i))
        (prefixBefore z.2.2 (observationTime (z.2.2 i))) = false} := by
    convert hm (measurableSet_singleton false) using 1
    ext z
    simp
  simpa only [hi, not_false_eq_true, true_implies] using hfalse

lemma measurable_extendValues (A : Finset (Fin n)) :
    Measurable (fun z : History n × (Fin A.card → ℝ) ↦ extendValues A z.1 z.2) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i ∈ A
  · simp only [extendValues, dif_pos hi]
    exact (measurable_pi_apply (stateIndex A i hi)).comp measurable_snd
  · simp only [extendValues, dif_neg hi]
    exact measurable_observationValue.comp ((measurable_pi_apply i).comp measurable_fst)

lemma measurable_extendClocks (A : Finset (Fin n)) :
    Measurable (fun z : ℝ × (History n × (Fin A.card → ℝ)) ↦ extendClocks A z.1 z.2.1 z.2.2) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i ∈ A
  · simp only [extendClocks, dif_pos hi]
    exact measurable_fst.add ((measurable_const.sub measurable_fst).mul
      ((measurable_pi_apply (stateIndex A i hi)).comp (measurable_snd.comp measurable_snd)))
  · simp only [extendClocks, dif_neg hi]
    exact measurable_observationTime.comp
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))

lemma validPrefix_iff (A : Finset (Fin n)) (s : ℝ) (H : History n) :
    ValidPrefix A s H ↔
      (∀ i ∈ A, H i = none) ∧ (∀ i ∉ A, H i ≠ none ∧ observationTime (H i) ≤ s) := by
  constructor
  · rintro ⟨hu, hs⟩
    refine ⟨hu, ?_⟩
    intro i hi
    obtain ⟨t, x, he, ht⟩ := hs i hi
    simp only [he, ne_eq, Option.some_ne_none, not_false_eq_true, observationTime,
      Option.elim_some, true_and]
    exact ht
  · rintro ⟨hu, hs⟩
    refine ⟨hu, ?_⟩
    intro i hi
    obtain ⟨hne, ht⟩ := hs i hi
    cases he : H i with
    | none => exact False.elim (hne he)
    | some p =>
      exact ⟨p.1, p.2, rfl, by simpa only [he, observationTime, Option.elim_some] using ht⟩

lemma measurableSet_validPrefix (A : Finset (Fin n)) :
    MeasurableSet {z : ℝ × History n | ValidPrefix A z.1 z.2} := by
  simp_rw [validPrefix_iff]
  apply MeasurableSet.inter
  · change MeasurableSet {z : ℝ × History n | ∀ i, i ∈ A → z.2 i = none}
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i ∈ A
    · simpa only [hi, true_implies, Set.preimage_setOf_eq] using measurableSet_observation_none.preimage
        ((measurable_pi_apply i).comp measurable_snd)
    · simp only [hi, false_implies, setOf_true]
      exact MeasurableSet.univ
  · change MeasurableSet {z : ℝ × History n | ∀ i, i ∉ A →
        z.2 i ≠ none ∧ observationTime (z.2 i) ≤ z.1}
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro i
    by_cases hi : i ∈ A
    · simp only [hi, not_true_eq_false, false_implies, setOf_true]
      exact MeasurableSet.univ
    have hobs : Measurable (fun z : ℝ × History n ↦ z.2 i) :=
      (measurable_pi_apply i).comp measurable_snd
    have hnone := measurableSet_observation_none.preimage hobs
    have htime := measurableSet_le (measurable_observationTime.comp hobs) measurable_fst
    simpa only [hi, not_false_eq_true, true_implies, Set.preimage_setOf_eq,
      Set.compl_setOf, Set.setOf_and, Function.comp_apply] using hnone.compl.inter htime

lemma Policy.continuationRule_isMeasurable (π : Policy Seed n) (hπ : π.IsMeasurable)
    (A : Finset (Fin n)) : (π.continuationRule A).IsMeasurable := by
  let T := (Seed × (ℝ × History n)) × (ℝ × (Fin A.card × (ℝ × History A.card)))
  have hr : Measurable (fun z : T ↦ z.1.1) := measurable_fst.comp measurable_fst
  have hs : Measurable (fun z : T ↦ z.1.2.1) := measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hH : Measurable (fun z : T ↦ z.1.2.2) := measurable_snd.comp (measurable_snd.comp measurable_fst)
  have ht : Measurable (fun z : T ↦ z.2.1) := measurable_fst.comp measurable_snd
  have hj : Measurable (fun z : T ↦ z.2.2.1) := measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hx : Measurable (fun z : T ↦ z.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hK : Measurable (fun z : T ↦ z.2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have htime : Measurable (fun z : T ↦ z.1.2.1 + (1 - z.1.2.1) * z.2.1) :=
    hs.add ((measurable_const.sub hs).mul ht)
  have hid := (measurable_of_finite (stateEmbedding A)).comp hj
  have hhist := (measurable_continuationHistory A).comp (hs.prodMk (hH.prodMk hK))
  exact hπ.comp (hr.prodMk (htime.prodMk (hid.prodMk (hx.prodMk hhist))))

end Measurability
end ProphetSecretary.Model
