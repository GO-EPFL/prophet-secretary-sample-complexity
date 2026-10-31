import ProphetSecretary.Limiting.HybridPolicy
import ProphetSecretary.Probability.FiniteClockCompensator

/-!
# Resampling a retained clock in the hybrid model

Only the chosen retained clock is replaced. The anonymous configuration is
analytical data and the original common history rule is preserved. Pending
survival is derived from that rule's finite-array execution on each branch.
-/

open MeasureTheory Set
open scoped Classical ENNReal

namespace ProphetSecretary.Limiting

variable {n N : ℕ} {Seed : Type*}

lemma combinedClocks_update (u : Fin n → ℝ) (v : Fin N → Point) (i : Fin n) (s : ℝ) :
    combinedClocks (Function.update u i s) v = Function.update (combinedClocks u v) (i.castAdd N) s := by
  funext k
  induction k using Fin.addCases with
  | left j =>
    by_cases hji : j = i
    · subst j
      simp [combinedClocks]
    · have hne : j.castAdd N ≠ i.castAdd N := by simpa only [ne_eq, Fin.castAdd_inj] using hji
      simp only [combinedClocks, Fin.addCases_left, Function.update_of_ne hji, Function.update_of_ne hne]
  | right j =>
    have hne : j.natAdd n ≠ i.castAdd N := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd, Fin.val_castAdd] at hv
      omega
    simp only [combinedClocks, Fin.addCases_right, Function.update_of_ne hne]

def replaceIndividualClock (i : Fin n) (z : HybridWorld n Seed × ℝ) : HybridWorld n Seed :=
  (z.1.1, Model.Instance.replaceClock i (z.1.2, z.2))

def eraseIndividualClock (i : Fin n) (v : HybridWorld n Seed) : HybridWorld n Seed :=
  (v.1, Model.Instance.eraseClock i v.2)

lemma eraseIndividualClock_replace (i : Fin n) (z : HybridWorld n Seed × ℝ) :
    eraseIndividualClock i (replaceIndividualClock i z) = eraseIndividualClock i z.1 := by
  simp only [eraseIndividualClock, replaceIndividualClock, Model.Instance.eraseClock_replaceClock]

noncomputable def HybridRule.pendingIndividualTime (π : HybridRule n Seed) (i : Fin n) (v : HybridWorld n Seed) : ℝ :=
  (π.asFinitePolicy v.1.1).pendingTime v.2.2.2 (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) (i.castAdd v.1.1)

lemma HybridRule.pendingIndividualTime_replace (π : HybridRule n Seed) (i : Fin n) (z : HybridWorld n Seed × ℝ) :
    π.pendingIndividualTime i (replaceIndividualClock i z) = π.pendingIndividualTime i z.1 := by
  dsimp only [HybridRule.pendingIndividualTime, replaceIndividualClock, Model.Instance.replaceClock]
  rw [combinedClocks_update]
  have h := (π.asFinitePolicy z.1.1.1).pendingTime_update z.1.2.2.2
    (combinedValues z.1.2.1 z.1.1.2) (combinedClocks z.1.2.2.1 z.1.1.2)
    (i.castAdd z.1.1.1) (combinedValues z.1.2.1 z.1.1.2 (i.castAdd z.1.1.1)) z.2
  simpa only [Function.update_eq_self] using h

lemma HybridRule.reach_replaceIndividualClock (π : HybridRule n Seed) (i : Fin n)
    (z : HybridWorld n Seed × ℝ) (hu : z.2 ≤ 1) :
    z.2 ≤ π.realizedDuration (replaceIndividualClock i z) ↔ z.2 ≤ π.pendingIndividualTime i z.1 := by
  have he := (π.asFinitePolicy z.1.1.1).reaches_iff_le_pendingTime z.1.2.2.2
    (combinedValues z.1.2.1 z.1.1.2) (combinedClocks (Function.update z.1.2.2.1 i z.2) z.1.1.2)
    (i.castAdd z.1.1.1) (by simpa only [combinedClocks, Fin.addCases_left, Function.update_self] using hu)
  change z.2 ≤ π.realizedDuration (replaceIndividualClock i z) ↔ _
  have hσ := π.pendingIndividualTime_replace i z
  dsimp only [HybridRule.pendingIndividualTime, replaceIndividualClock, Model.Instance.replaceClock] at hσ
  rw [hσ] at he
  simp only [Model.Policy.Reaches, combinedClocks, Fin.addCases_left, Function.update_self] at he
  dsimp only [HybridRule.realizedDuration, HybridRule.stoppingTime, HybridRule.pendingIndividualTime,
    replaceIndividualClock, Model.Instance.replaceClock]
  convert! he using 1

lemma HybridRule.survival_replaceIndividualClock (π : HybridRule n Seed) (i : Fin n)
    (z : HybridWorld n Seed × ℝ) (t : ℝ) (ht : t ≤ 1) (hu : t ≤ z.2) :
    t ≤ π.realizedDuration (replaceIndividualClock i z) ↔ t ≤ π.pendingIndividualTime i z.1 := by
  have he := (π.asFinitePolicy z.1.1.1).survival_iff_pending_of_not_arrived z.1.2.2.2
    (combinedValues z.1.2.1 z.1.1.2) (combinedClocks (Function.update z.1.2.2.1 i z.2) z.1.1.2)
    (i.castAdd z.1.1.1) ht (by simpa only [combinedClocks, Fin.addCases_left, Function.update_self] using hu)
  have hσ := π.pendingIndividualTime_replace i z
  dsimp only [HybridRule.pendingIndividualTime, replaceIndividualClock, Model.Instance.replaceClock] at hσ
  rw [hσ] at he
  exact he

variable [MeasurableSpace Seed]

lemma measurable_eraseIndividualClock (i : Fin n) : Measurable (@eraseIndividualClock n Seed i) :=
  measurable_fst.prodMk ((Model.Instance.measurable_eraseClock i).comp measurable_snd)

lemma replaceIndividualClock_measurePreserving (P : Model.Instance n) (μ : FiniteMeasure ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    MeasurePreserving (replaceIndividualClock i) ((hybridWorldLaw P μ ν).prod Model.Instance.uniformClock)
      (hybridWorldLaw P μ ν) := by
  have h₁ := measurePreserving_prodAssoc (configurationLaw μ) (P.worldLaw ν) Model.Instance.uniformClock
  have h₂ := (MeasurePreserving.id (configurationLaw μ)).prod (P.replaceClock_measurePreserving ν i)
  exact h₂.comp h₁

end ProphetSecretary.Limiting
