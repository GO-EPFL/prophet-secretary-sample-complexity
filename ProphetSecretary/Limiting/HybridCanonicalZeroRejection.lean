import ProphetSecretary.Limiting.HybridFiniteCutoffEvaluation
import ProphetSecretary.Limiting.HybridValuePolicy
import ProphetSecretary.Model.Restriction
import ProphetSecretary.Model.ZeroSimulationExactDuration

/-!
# Canonical coarse rules reject zero at every preterminal time

Strictly positive duration weight makes every continuation threshold positive
before time one. The statement holds for every observation history and is
preserved when extra identities are ignored. Actual padded-zero clocks are
preterminal almost surely, so their causal simulation preserves duration.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n N m q : ℕ}

lemma FiniteIntensityHybridInstance.cutoff_valueRule_zero_decide
    (B : FiniteIntensityHybridInstance n) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (N : ℕ) (d t : ℝ) (ht : t<1) (k : Fin (n+N)) (H : Model.History (n+N)) :
    (((B.valueRule w c).above d).asFinitePolicy N).decide () t k 0 H=false := by
  induction k using Fin.addCases with
  | left i =>
    simp only [HybridRule.asFinitePolicy,Fin.addCases_left,HybridRule.above,
      FiniteIntensityHybridInstance.valueRule,hybridThresholdRule,decide_eq_false_iff_not]
    exact not_le.mpr (B.valueHybridThreshold_pos hw hc _ _ ht)
  | right j =>
    simp only [HybridRule.asFinitePolicy,Fin.addCases_right,HybridRule.above,
      FiniteIntensityHybridInstance.valueRule,hybridThresholdRule]
    have hn := not_le.mpr (B.valueHybridThreshold_pos hw hc (Model.unseen (retainedHistory H)) none ht)
    simp [hn]

lemma FiniteIntensityHybridInstance.cutoff_valueRule_ignoreExtras_zero_decide
    (B : FiniteIntensityHybridInstance n) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (N : ℕ) (d t : ℝ) (ht : t<1) (e : Fin (n+N) ↪ Fin q) (k : Fin q) (H : Model.History q) :
    ((((B.valueRule w c).above d).asFinitePolicy N).ignoreExtras e).decide () t k 0 H=false := by
  change decide (∃ i, e i=k ∧ (((B.valueRule w c).above d).asFinitePolicy N).decide () t i 0
    (Model.projectHistory e H)=true)=false
  rw [decide_eq_false_iff_not]
  rintro ⟨i,_hi,hiAct⟩
  rw [B.cutoff_valueRule_zero_decide hw hc N d t ht i (Model.projectHistory e H)] at hiAct
  cases hiAct

lemma FiniteIntensityHybridInstance.coarse_no_zero_actions
    (B : FiniteIntensityHybridInstance n) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (N : ℕ) (d : ℝ) (e : Fin (n+N) ↪ Fin (q+m)) (P : Model.Instance q) :
    let π := ((B.valueThresholdPolicy hw.le hc.le).finiteCutoffEvaluation N d).ignoreExtras e
    ∀ᵐ ω ∂(P.appendZeros m).worldLaw π.seedLaw, ∀ j : Fin m,
      π.rule.action ω.2.2 Finset.univ ω.1 ω.2.1 (j.natAdd q) ≠ true := by
  let π := ((B.valueThresholdPolicy hw.le hc.le).finiteCutoffEvaluation N d).ignoreExtras e
  have hTimes : ∀ᵐ ω ∂(P.appendZeros m).worldLaw π.seedLaw, ∀ k, ω.2.1 k<1 := by
    rw [ae_all_iff]
    intro k
    exact ((P.appendZeros m).world_clock_measurePreserving π.seedLaw k).quasiMeasurePreserving.ae
      (uniformClock_mem_Ioo.mono (fun _ h => h.2))
  have hZeros : ∀ᵐ ω ∂(P.appendZeros m).worldLaw π.seedLaw, ∀ j : Fin m, ω.1 (j.natAdd q)=0 := by
    rw [ae_all_iff]
    intro j
    have hz : ∀ᵐ x ∂(P.appendZeros m).law (j.natAdd q), x=0 := by simp [Model.Instance.appendZeros]
    exact ((measurePreserving_eval (P.appendZeros m).law (j.natAdd q)).comp
      (measurePreserving_fst (μ := (P.appendZeros m).valuesLaw)
        (ν := (Model.Instance.clocksLaw (q+m)).prod π.seedLaw))).quasiMeasurePreserving.ae hz
  haveI : Subsingleton π.Seed := by
    change Subsingleton Unit
    infer_instance
  filter_upwards [hTimes,hZeros] with ω hTimes hZeros
  intro j
  have hSeed : ω.2.2=() := Subsingleton.elim _ _
  rw [hSeed]
  change (((((B.valueRule w c).above d).asFinitePolicy N).ignoreExtras e).decide () (ω.2.1 (j.natAdd q))
    (j.natAdd q) (ω.1 (j.natAdd q)) (Model.history Finset.univ ω.1 ω.2.1 (ω.2.1 (j.natAdd q)))) ≠ true
  rw [hZeros j,B.cutoff_valueRule_ignoreExtras_zero_decide hw hc N d _ (hTimes _) e]
  simp

lemma FiniteIntensityHybridInstance.coarse_zero_simulation_expectedDuration
    (B : FiniteIntensityHybridInstance n) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (N : ℕ) (d : ℝ) (e : Fin (n+N) ↪ Fin (q+m)) (P : Model.Instance q) :
    let π := ((B.valueThresholdPolicy hw.le hc.le).finiteCutoffEvaluation N d).ignoreExtras e
    π.simulateZeros.expectedDuration P=π.expectedDuration (P.appendZeros m) := by
  let π := ((B.valueThresholdPolicy hw.le hc.le).finiteCutoffEvaluation N d).ignoreExtras e
  exact Model.RandomizedPolicy.simulateZeros_expectedDuration_eq_of_no_zero_action π P
    (B.coarse_no_zero_actions hw hc N d e P)

end ProphetSecretary.Limiting
