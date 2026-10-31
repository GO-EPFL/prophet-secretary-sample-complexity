import ProphetSecretary.Limiting.CountableFiniteContinuation
import ProphetSecretary.Limiting.CountableTruncationLower
import ProphetSecretary.Limiting.HybridBellmanIdentity
import ProphetSecretary.Limiting.CountableValuePolicy

/-!
# Actual finite-hybrid value rules on the common countable world

The extension observes the first N individual identities, including zeros,
and anonymous marks above b. Exact zero-variable value comparisons identify
its child continuation with the projected full unseen mask.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal Classical

namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def truncatedValueRule (B : CountableInstance) (N : ℕ) (b : ℝ)
    (hb : (B.terminal : ℝ) < b) (w c : ℝ) : CountableRule Unit :=
  extendTruncatedRule ((B.truncation N b hb).valueRule w c) b

noncomputable def truncatedValuePolicy (B : CountableInstance) (N : ℕ) (b : ℝ)
    (hb : (B.terminal : ℝ) < b) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) : RandomizedCountablePolicy B :=
  ((B.truncation N b hb).valueThresholdPolicy hw hc).extendToCountable B hb

lemma truncatedValuePolicy_rule (B : CountableInstance) (N : ℕ) (b : ℝ)
    (hb : (B.terminal : ℝ) < b) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (B.truncatedValuePolicy N b hb hw hc).rule = B.truncatedValueRule N b hb w c := rfl

lemma truncatedContinuationValue_individual_eq (B : CountableInstance) (N : ℕ) (b : ℝ)
    (hb : (B.terminal : ℝ) < b) (H : IndividualHistory) (i : Fin N) {w c : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (t : ℝ) :
    B.truncatedContinuationValue N b hb (eraseMask (unseenMask H) i.val) w c (remainingTime t) =
      ((B.truncation N b hb).restrictIndividuals ((Model.unseen (prefixHistory N H)).erase i)).continuationValue
        w c (remainingTime t) := by
  have hSet := finiteMaskSet_restrict_eraseMask N (unseenMask H) i
  rw [finiteMaskSet_restrict_unseenMask] at hSet
  exact (B.truncatedContinuationValue_eq_restrict N b hb (eraseMask (unseenMask H) i.val) hw hc (remainingTime t)).trans
    (congrArg (fun A : Finset (Fin N) => ((B.truncation N b hb).restrictIndividuals A).continuationValue w c (remainingTime t)) hSet)

lemma truncatedContinuationValue_poisson_eq (B : CountableInstance) (N : ℕ) (b : ℝ)
    (hb : (B.terminal : ℝ) < b) (H : IndividualHistory) {w c : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (t : ℝ) :
    B.truncatedContinuationValue N b hb (unseenMask H) w c (remainingTime t) =
      ((B.truncation N b hb).restrictIndividuals (Model.unseen (prefixHistory N H))).continuationValue
        w c (remainingTime t) :=
  (B.truncatedContinuationValue_eq_restrict N b hb (unseenMask H) hw hc (remainingTime t)).trans
    (congrArg (fun A : Finset (Fin N) => ((B.truncation N b hb).restrictIndividuals A).continuationValue w c (remainingTime t))
      (finiteMaskSet_restrict_unseenMask N H))

lemma truncatedValueRule_individual_iff (B : CountableInstance) (N : ℕ) (b : ℝ)
    (hb : (B.terminal : ℝ) < b) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (r : Unit) (t : ℝ) (i : ℕ) (hi : i < N) (x : ℝ) (H : IndividualHistory) (M : Measure Point) :
    (B.truncatedValueRule N b hb w c).individual r t i x H M = true ↔
      B.truncatedContinuationValue N b hb (eraseMask (unseenMask H) i) w c (remainingTime t) ≤ w*x := by
  have hCont := B.truncatedContinuationValue_individual_eq N b hb H ⟨i,hi⟩ hw.le hc t
  simp only [truncatedValueRule,extendTruncatedRule,dif_pos hi,FiniteIntensityHybridInstance.valueRule,
    hybridThresholdRule,FiniteIntensityHybridInstance.valueHybridThreshold,Option.elim_some,decide_eq_true_eq]
  rw [hCont]
  simpa only [mul_comm x w] using (div_le_iff₀ hw :
    ((B.truncation N b hb).restrictIndividuals ((Model.unseen (prefixHistory N H)).erase ⟨i,hi⟩)).continuationValue w c (remainingTime t)/w ≤ x ↔ _)

lemma truncatedValueRule_individual_false (B : CountableInstance) (N : ℕ) (b : ℝ)
    (hb : (B.terminal : ℝ) < b) (r : Unit) (w c t : ℝ) (i : ℕ) (hi : ¬i < N)
    (x : ℝ) (H : IndividualHistory) (M : Measure Point) :
    (B.truncatedValueRule N b hb w c).individual r t i x H M = false := dif_neg hi

lemma truncatedValueRule_poisson_iff (B : CountableInstance) (N : ℕ) (b : ℝ)
    (hb : (B.terminal : ℝ) < b) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (r : Unit) (t x : ℝ) (H : IndividualHistory) (M : Measure Point) :
    (B.truncatedValueRule N b hb w c).poisson r t x H M = true ↔ b < x ∧
      B.truncatedContinuationValue N b hb (unseenMask H) w c (remainingTime t) ≤ w*x := by
  have hCont := B.truncatedContinuationValue_poisson_eq N b hb H hw.le hc t
  by_cases hx : b < x
  · simp only [truncatedValueRule,extendTruncatedRule,if_pos hx]
    simp only [FiniteIntensityHybridInstance.valueRule,hybridThresholdRule,
      FiniteIntensityHybridInstance.valueHybridThreshold,Option.elim_none,decide_eq_true_eq,hx,true_and]
    rw [hCont]
    simpa only [mul_comm x w] using (div_le_iff₀ hw :
      ((B.truncation N b hb).restrictIndividuals (Model.unseen (prefixHistory N H))).continuationValue w c (remainingTime t)/w ≤ x ↔ _)
  · simp only [truncatedValueRule,extendTruncatedRule,if_neg hx]
    simp only [reduceCtorEq,hx,false_and]

lemma truncatedContinuationValue_waiting_le (B : CountableInstance) (N : ℕ) (b : ℝ)
    (hb : (B.terminal : ℝ) < b) (keep : IndividualMask) (w c : ℝ) (u : ℝ≥0) :
    w*(B.terminal : ℝ)+c*(u : ℝ) ≤ B.truncatedContinuationValue N b hb keep w c u :=
  ((B.remainingState keep u).truncation N b hb).terminalScalar_le_optimalScalarValue w (c*(u : ℝ))

lemma truncated_acceptance_floor (B : CountableInstance) (N : ℕ) (b : ℝ)
    (hb : (B.terminal : ℝ) < b) (keep : IndividualMask) {w c t x : ℝ} (hw : 0 < w) (ht : t ≤ 1)
    (hAccept : B.truncatedContinuationValue N b hb keep w c (remainingTime t) ≤ w*x) :
    (B.terminal : ℝ)+(c/w)*(1-t) ≤ x := by
  have hWait := B.truncatedContinuationValue_waiting_le N b hb keep w c (remainingTime t)
  rw [coe_remainingTime ht] at hWait
  have hBound := hWait.trans hAccept
  apply (mul_le_mul_iff_right₀ hw).mp
  have he : w*((B.terminal : ℝ)+(c/w)*(1-t)) = w*(B.terminal : ℝ)+c*(1-t) := by
    calc
      _ = w*(B.terminal : ℝ)+((c/w)*w)*(1-t) := by ring
      _ = _ := by rw [div_mul_cancel₀ c hw.ne']
  rw [he]
  exact hBound

lemma truncatedValueRule_candidate_floor (B : CountableInstance) (N : ℕ) (b : ℝ)
    (hb : (B.terminal : ℝ) < b) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (v : CompleteWorld Unit) (j : Candidate) (ht : (candidatePoint v j).1 ≤ 1)
    (hAction : (B.truncatedValueRule N b hb w c).candidateAction v j = true) :
    (B.terminal : ℝ)+(c/w)*(1-(candidatePoint v j).1) ≤ (candidatePoint v j).2 := by
  cases j with
  | inl i =>
    by_cases hi : i < N
    · have hAccept := (B.truncatedValueRule_individual_iff N b hb hw hc v.2.2.2 (v.2.2.1 i) i hi (v.2.1 i)
        (individualHistory v.2.1 v.2.2.1 (v.2.2.1 i)) (anonymousHistory v.1 (v.2.2.1 i))).mp hAction
      exact B.truncated_acceptance_floor N b hb _ hw ht hAccept
    · have hAct : (B.truncatedValueRule N b hb w c).individual v.2.2.2 (v.2.2.1 i) i (v.2.1 i)
          (individualHistory v.2.1 v.2.2.1 (v.2.2.1 i)) (anonymousHistory v.1 (v.2.2.1 i)) = true := hAction
      rw [B.truncatedValueRule_individual_false N b hb v.2.2.2 w c (v.2.2.1 i) i hi (v.2.1 i)
        (individualHistory v.2.1 v.2.2.1 (v.2.2.1 i)) (anonymousHistory v.1 (v.2.2.1 i))] at hAct
      exact Bool.noConfusion hAct
  | inr kj =>
    let p := configurationPoint kj.2 (v.1 kj.1)
    have hAccept := (B.truncatedValueRule_poisson_iff N b hb hw hc v.2.2.2 p.1 p.2
      (individualHistory v.2.1 v.2.2.1 p.1) (anonymousHistory v.1 p.1)).mp hAction
    exact B.truncated_acceptance_floor N b hb _ hw ht hAccept.2

lemma truncatedValueRule_code_floor (B : CountableInstance) (N : ℕ) (b : ℝ)
    (hb : (B.terminal : ℝ) < b) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (v : CompleteWorld Unit) (i : ℕ) (hi : (B.truncatedValueRule N b hb w c).codeAccepted v i) :
    (B.terminal : ℝ)+(c/w)*(1-codeTime v i) ≤ codeValue v i :=
  B.truncatedValueRule_candidate_floor N b hb hw hc v (candidateEnumeration.symm i) hi.2.1.2 hi.2.2

lemma truncatedValuePolicy_scalarObjective (B : CountableInstance) (hZero : B.terminal = 0)
    (N : ℕ) (b : ℝ) (hb : (B.terminal : ℝ) < b) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (B.truncatedValuePolicy N b hb hw.le hc).scalarObjective w c = (B.truncation N b hb).optimalScalarValue w c :=
  (((B.truncation N b hb).valueThresholdPolicy hw.le hc).extendToCountable_scalarObjective B hb w c).trans
    ((B.truncation N b hb).valueThresholdPolicy_optimal hZero hw hc)

end ProphetSecretary.Limiting.CountableInstance
