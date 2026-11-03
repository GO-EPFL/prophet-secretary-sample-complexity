import ProphetSecretary.Model.RankToClockMeasurability
import ProphetSecretary.Model.ExecutionAgreement
import ProphetSecretary.Model.ContinuationTransport

/-!
# Clock annotations preserve the arrival ranks

Replacing each numerical timestamp does not remove identities from the
observed history. A rank policy with assigned timestamps may therefore
process tied times in the exogenous order and still use the usual causal
clock callback. The continuous timestamps in the comparison below are
analytical variables.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

/-- Apply a numerical timestamp map to each observation that has already arrived. -/
def annotateClockHistory (f : ℝ → ℝ) (H : History n) : History n :=
  fun j => (H j).map (fun z => (f z.1,z.2))

@[simp] lemma annotateClockHistory_eq_none (f : ℝ → ℝ) (H : History n) (j : Fin n) :
    annotateClockHistory f H j=none ↔ H j=none := by
  cases h : H j <;> simp [annotateClockHistory,h]

@[simp] lemma unseen_annotateClockHistory (f : ℝ → ℝ) (H : History n) :
    unseen (annotateClockHistory f H)=unseen H := by
  ext j
  simp [unseen]

@[simp] lemma currentRankFromClock_annotateClockHistory (f : ℝ → ℝ) (H : History n) (i : Fin n) :
    currentRankFromClock i (annotateClockHistory f H)=currentRankFromClock i H := by
  have h : clockHistoryPresent (annotateClockHistory f H)=clockHistoryPresent H := by
    ext j
    simp [clockHistoryPresent]
  rw [currentRankFromClock,currentRankFromClock,h]

lemma measurable_annotateClockHistory {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (annotateClockHistory (n := n) f) := by
  have hm : Measurable (fun o : Option (ℝ × ℝ) => o.map (fun z => (f z.1,z.2))) := by
    rw [measurable_comap_iff]
    have hT := hf.comp measurable_observationTime
    have hV := measurable_observationValue
    have h : Measurable (fun o : Option (ℝ × ℝ) => if o=none then
        (Sum.inl () : Unit ⊕ (ℝ × ℝ)) else Sum.inr (f (observationTime o),observationValue o)) :=
      Measurable.ite measurableSet_observation_none measurable_const (measurable_inr.comp (hT.prodMk hV))
    convert h using 1
    funext o
    cases o <;> rfl
  apply measurable_pi_lambda
  intro j
  have hEval : Measurable (fun H : History n => H j) := measurable_pi_apply j
  have h := hm.comp hEval
  simpa only [Function.comp_def,annotateClockHistory] using h

/-- An analytical clock execution retaining the original arrival history. -/
def Policy.withClockAnnotations (π : Policy Seed n) (f : ℝ → ℝ) : Policy Seed n where
  decide r t i x H := π.decide r (f t) i x (annotateClockHistory f H)

lemma Policy.withClockAnnotations_isMeasurable [MeasurableSpace Seed] (π : Policy Seed n)
    (hπ : π.IsMeasurable) {f : ℝ → ℝ} (hf : Measurable f) :
    (π.withClockAnnotations f).IsMeasurable := by
  let Ω := Seed × (ℝ × (Fin n × (ℝ × History n)))
  have h : Measurable (fun p : Ω =>
      (p.1,f p.2.1,p.2.2.1,p.2.2.2.1,annotateClockHistory f p.2.2.2.2)) :=
    measurable_fst.prodMk ((hf.comp (by fun_prop)).prodMk
      ((by fun_prop : Measurable (fun p : Ω => p.2.2.1)).prodMk
        ((by fun_prop : Measurable (fun p : Ω => p.2.2.2.1)).prodMk
          ((measurable_annotateClockHistory hf).comp (by fun_prop)))))
  exact hπ.comp h

lemma Policy.withClockAnnotations_action (π : Policy Seed n) (f : ℝ → ℝ) (r : Seed)
    (s : Fin n → ℝ) (hs : StrictMono s) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ)
    (i : Fin n) :
    (π.withClockAnnotations f).action r Finset.univ x (Instance.reconstructClocks (s,p)) i =
      π.clockToRank.action (f ∘ s,r) p x i := by
  change π.decide r (f (s (p.symm i))) i (x i)
      (annotateClockHistory f (history Finset.univ x (Instance.reconstructClocks (s,p)) (s (p.symm i))))=
    π.decide r (f (s (p.symm i))) i (x i)
      (fun j => (rankHistory p x (p.symm i) j).map (fun a => (f (s a.1),a.2)))
  congr 1
  rw [← rankHistory_to_time s hs p x (p.symm i)]
  funext j
  unfold annotateClockHistory
  rw [Option.map_map]
  rfl

lemma Policy.withClockAnnotations_outcomes (π : Policy Seed n) (f : ℝ → ℝ) (r : Seed)
    (s : Fin n → ℝ) (hs : StrictMono s) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    (π.withClockAnnotations f).reward r Finset.univ x (Instance.reconstructClocks (s,p)) =
      π.clockToRank.rankToClock.reward (f ∘ s,r) Finset.univ x (Instance.reconstructClocks (s,p)) ∧
    (π.withClockAnnotations f).stoppingTime r Finset.univ x (Instance.reconstructClocks (s,p)) =
      π.clockToRank.rankToClock.stoppingTime (f ∘ s,r) Finset.univ x (Instance.reconstructClocks (s,p)) :=
  Policy.outcomes_eq_of_actions_eq _ _ _ _ _ _ _ (fun i =>
    (π.withClockAnnotations_action f r s hs p x i).trans
      (π.clockToRank.rankToClock_action (f ∘ s,r) s hs p x i).symm)

lemma Policy.withClockAnnotations_reward_eq_rank (π : Policy Seed n) (f : ℝ → ℝ) (r : Seed)
    (s : Fin n → ℝ) (hs : StrictMono s) (hU : ∀ k,s k≤1) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    (π.withClockAnnotations f).reward r Finset.univ x (Instance.reconstructClocks (s,p)) =
      π.clockToRank.reward (f ∘ s,r) p x :=
  (π.withClockAnnotations_outcomes f r s hs p x).1.trans (π.clockToRank.rankToClock_reward _ s hs hU p x)

lemma Policy.withClockAnnotations_reaches_iff_rank (π : Policy Seed n) (f : ℝ → ℝ) (r : Seed)
    (s : Fin n → ℝ) (hs : StrictMono s) (hU : ∀ k,s k≤1) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ)
    (i : Fin n) :
    (π.withClockAnnotations f).Reaches r x (Instance.reconstructClocks (s,p)) i ↔
      π.clockToRank.Reaches (f ∘ s,r) p x i := by
  have h := (π.withClockAnnotations_outcomes f r s hs p x).2
  rw [Policy.Reaches,h,← Policy.Reaches]
  exact π.clockToRank.rankToClock_reaches _ s hs hU p x i

/-- The reported timestamp of the first selected rank, or one if no rank was selected. -/
noncomputable def RankPolicy.reportedDuration (π : RankPolicy Seed n) (r : Seed)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (s : Fin n → ℝ) : ℝ :=
  1-∑ i : Fin n, if π.Selects r p x i then 1-s (p.symm i) else 0

lemma RankPolicy.reportedDuration_eq_of_selects (π : RankPolicy Seed n) (r : Seed)
    (p : Equiv.Perm (Fin n)) (x s : Fin n → ℝ) {i : Fin n} (hi : π.Selects r p x i) :
    π.reportedDuration r p x s=s (p.symm i) := by
  unfold RankPolicy.reportedDuration
  rw [Finset.sum_eq_single i]
  · simp only [if_pos hi]
    ring
  · intro j _ hji
    exact if_neg (fun hj => hji (π.selects_unique r p x hj hi))
  · simp

lemma RankPolicy.reportedDuration_eq_one_of_no_selection (π : RankPolicy Seed n) (r : Seed)
    (p : Equiv.Perm (Fin n)) (x s : Fin n → ℝ) (h : ∀ i, ¬π.Selects r p x i) :
    π.reportedDuration r p x s=1 := by simp [RankPolicy.reportedDuration,h]

/-- Preserve the terminal-time convention while rounding a selected timestamp. -/
noncomputable def terminalClockReport (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  if t=1 then 1 else f t

@[simp] lemma terminalClockReport_one (f : ℝ → ℝ) : terminalClockReport f 1=1 := by
  simp [terminalClockReport]

lemma measurable_terminalClockReport {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (terminalClockReport f) :=
  Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const hf

lemma terminalClockReport_range {f : ℝ → ℝ} {δ t : ℝ} (ht : t∈Icc (0 : ℝ) 1)
    (hδ : 0≤δ) (hf : ∀ u∈Icc (0 : ℝ) 1, 0≤f u ∧ f u≤u ∧ u-f u≤δ) :
    terminalClockReport f t∈Icc (0 : ℝ) t ∧ t-terminalClockReport f t≤δ := by
  by_cases he : t=1
  · subst t
    simp [hδ]
  · simpa only [terminalClockReport,if_neg he] using
      (show f t∈Icc (0 : ℝ) t ∧ t-f t≤δ from ⟨⟨(hf t ht).1,(hf t ht).2.1⟩,(hf t ht).2.2⟩)

lemma terminalClockReport_monotoneOn {f : ℝ → ℝ}
    (hf : MonotoneOn f (Icc (0 : ℝ) 1)) (h1 : ∀ t∈Icc (0 : ℝ) 1, f t≤1) :
    MonotoneOn (terminalClockReport f) (Icc (0 : ℝ) 1) := by
  intro a ha b hb hab
  by_cases hb1 : b=1
  · subst b
    rw [terminalClockReport_one]
    by_cases ha1 : a=1
    · simp [ha1]
    · simpa only [terminalClockReport,if_neg ha1] using h1 a ha
  · have ha1 : a≠1 := fun he => hb1 (le_antisymm hb.2 (he ▸ hab))
    simp only [terminalClockReport,if_neg ha1,if_neg hb1]
    exact hf ha hb hab

lemma Policy.withClockAnnotations_report_eq_rank (π : Policy Seed n) (f : ℝ → ℝ) (r : Seed)
    (s : Fin n → ℝ) (hs : StrictMono s) (hU : ∀ k,s k<1) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    terminalClockReport f ((π.withClockAnnotations f).stoppingTime r Finset.univ x
      (Instance.reconstructClocks (s,p))) =
      π.clockToRank.reportedDuration (f ∘ s,r) p x (f ∘ s) := by
  let u := Instance.reconstructClocks (s,p)
  let Q := π.clockToRank
  let r' := (f ∘ s,r)
  have hTime := (π.withClockAnnotations_outcomes f r s hs p x).2
  rw [hTime]
  rcases Q.rankToClock.stoppingTime_eq_one_or_selects r' Finset.univ x u with h | ⟨i,hi⟩
  · rw [h,terminalClockReport_one]
    apply Eq.symm
    apply Q.reportedDuration_eq_one_of_no_selection
    intro i hi
    have h' := (Q.rankToClock_selects r' s hs (fun j => (hU j).le) p x i).mpr hi
    have he := h'.2
    change u i=Q.rankToClock.stoppingTime r' Finset.univ x u at he
    rw [h] at he
    exact (hU (p.symm i)).ne he
  · have h' := (Q.rankToClock_selects r' s hs (fun j => (hU j).le) p x i).mp hi
    rw [Q.reportedDuration_eq_of_selects r' p x _ h',← hi.2]
    exact if_neg (hU (p.symm i)).ne

end ProphetSecretary.Model
