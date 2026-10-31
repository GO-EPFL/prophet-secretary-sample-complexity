import ProphetSecretary.Model.TerminalReward
import ProphetSecretary.Model.PositiveValuePolicy

/-!
# A causal lower transfer from excess offers to a fixed terminal reward

A policy that accepts only positive excess values is pulled back along the
observed value map. It retains identities and every zero excess observation.
On selection x=a+(x−a)₊; on no selection the original terminal reward is a.
The actual product-law map proves the expected scalar-payoff identity.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma RandomizedPolicy.terminalReward_excessPullback (π : RandomizedPolicy n) {a : ℝ} (ha : 0 ≤ a)
    (hpos : ∀ (r : π.Seed) (x u : Fin n → ℝ) (i : Fin n),
      π.rule.ActualSelects r Finset.univ x u i → 0 < x i) (ω : π.World) :
    let f : Fin n → ℝ → ℝ := fun _ => excessValueMap a
    let πP := π.pullbackValuesIndexed f (fun _ => measurable_excessValueMap a)
    πP.realizedTerminalReward a ω = a + π.realizedReward (transformWorld f ω) := by
  let f : Fin n → ℝ → ℝ := fun _ => excessValueMap a
  let πP := π.pullbackValuesIndexed f (fun _ => measurable_excessValueMap a)
  have hsel (i : Fin n) : πP.rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i ↔
      π.rule.ActualSelects ω.2.2 Finset.univ (fun j => f j (ω.1 j)) ω.2.1 i :=
    π.rule.pullbackValuesBy_actualSelects_iff (id : π.Seed → π.Seed) (fun _ => f) ω.2.2 Finset.univ ω.1 ω.2.1 i
  by_cases hs : ∃ i, πP.rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i
  · obtain ⟨i,hi⟩ := hs
    have hm := (hsel i).mp hi
    have hp := hpos ω.2.2 (fun j => f j (ω.1 j)) ω.2.1 i hm
    change (if ∃ j, πP.rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 j then πP.realizedReward ω else a) = _
    rw [if_pos ⟨i,hi⟩]
    change πP.rule.reward ω.2.2 Finset.univ ω.1 ω.2.1 =
      a + π.rule.reward ω.2.2 Finset.univ (fun j => f j (ω.1 j)) ω.2.1
    rw [πP.rule.reward_eq_of_actualSelects _ _ _ _ hi,π.rule.reward_eq_of_actualSelects _ _ _ _ hm]
    exact positive_excess_reconstructs_value ha hp
  · have hn : ∀ i, ¬π.rule.ActualSelects ω.2.2 Finset.univ (fun j => f j (ω.1 j)) ω.2.1 i :=
      fun i hi => hs ⟨i,(hsel i).mpr hi⟩
    change (if ∃ j, πP.rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 j then πP.realizedReward ω else a) = _
    rw [if_neg hs]
    change a = a + π.rule.reward ω.2.2 Finset.univ (fun j => f j (ω.1 j)) ω.2.1
    rw [π.rule.reward_eq_zero_of_no_actualSelection _ _ _ _ hn,add_zero]

lemma RandomizedPolicy.duration_excessPullback (π : RandomizedPolicy n) (a : ℝ) (ω : π.World) :
    let f : Fin n → ℝ → ℝ := fun _ => excessValueMap a
    let πP := π.pullbackValuesIndexed f (fun _ => measurable_excessValueMap a)
    πP.realizedDuration ω = π.realizedDuration (transformWorld f ω) :=
  π.rule.pullbackValuesBy_stoppingTime (id : π.Seed → π.Seed) (fun _ => fun _ => excessValueMap a)
    ω.2.2 Finset.univ ω.1 ω.2.1

/-- All expectations use the actual independent original/transformed laws.
The pullback uses only each value when that identity arrives. -/
theorem RandomizedPolicy.terminalScalarObjective_excessPullback (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {a : ℝ} (ha : 0 ≤ a)
    (hpos : ∀ (r : π.Seed) (x u : Fin n → ℝ) (i : Fin n),
      π.rule.ActualSelects r Finset.univ x u i → 0 < x i) (w c : ℝ) :
    let f : Fin n → ℝ → ℝ := fun _ => excessValueMap a
    let πP := π.pullbackValuesIndexed f (fun _ => measurable_excessValueMap a)
    πP.terminalScalarObjective P a w c = w * a + π.scalarObjective (P.excessOffers a) w c := by
  let f : Fin n → ℝ → ℝ := fun _ => excessValueMap a
  let hf : ∀ i, Measurable (f i) := fun _ => measurable_excessValueMap a
  let hnn : ∀ i, ∀ᵐ x ∂P.law i, 0 ≤ f i x := fun i => (P.nonnegative i).mono fun _ hx => excessValueMap_nonnegative hx
  let πP := π.pullbackValuesIndexed f hf
  have hQ := P.excessOffers_integrable_maximum hP ha
  have hmp := P.transformWorld_measurePreserving f hf hnn π.seedLaw
  have hJ : Integrable (fun ω : π.World => w * π.realizedReward ω + c * π.realizedDuration ω)
      ((P.excessOffers a).worldLaw π.seedLaw) :=
    ((π.integrable_realizedReward (P.excessOffers a) hQ).const_mul w).add
      ((π.integrable_realizedDuration (P.excessOffers a)).const_mul c)
  have hJm : Measurable (fun ω : π.World => w * π.realizedReward ω + c * π.realizedDuration ω) :=
    (π.measurable_realizedReward.const_mul w).add (π.measurable_realizedDuration.const_mul c)
  have hI : Integrable (fun ω : π.World => w * π.realizedReward (transformWorld f ω) +
      c * π.realizedDuration (transformWorld f ω)) (P.worldLaw π.seedLaw) :=
    hmp.integrable_comp_of_integrable hJ
  have he := integral_map (μ := P.worldLaw π.seedLaw) hmp.measurable.aemeasurable hJm.aestronglyMeasurable
  rw [hmp.map_eq] at he
  change (∫ ω : π.World, w * πP.realizedTerminalReward a ω + c * πP.realizedDuration ω ∂P.worldLaw π.seedLaw) = _
  have hpoint : (fun ω : π.World => w * πP.realizedTerminalReward a ω + c * πP.realizedDuration ω) =
      (fun ω => w * a + (w * π.realizedReward (transformWorld f ω) + c * π.realizedDuration (transformWorld f ω))) := by
    funext ω
    rw [π.terminalReward_excessPullback ha hpos ω,π.duration_excessPullback a ω]
    ring
  rw [hpoint, integral_add (integrable_const (w * a)) hI, integral_const]
  simp only [probReal_univ,one_smul]
  exact congrArg (fun t : ℝ => w * a + t) he.symm

end ProphetSecretary.Model
