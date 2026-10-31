import ProphetSecretary.Model.ScalarObjectiveBounds

/-!
# Waiting for one identity

Accepting a prescribed identity is admissible regardless of all earlier values, including
zeros. Its expected reward is exactly that marginal's first moment. This supplies the
coordinate lower bound used in the unstopped-premium moment estimates.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def RandomizedPolicy.chooseIdentity (i : Fin n) : RandomizedPolicy n where
  Seed := Unit
  seedLaw := Measure.dirac ()
  rule := ⟨fun _ _ j _ _ => decide (j = i)⟩
  measurable_rule := by
    let T := Unit × (ℝ × (Fin n × (ℝ × History n)))
    have hj : Measurable (fun z : T => z.2.2.1) :=
      measurable_fst.comp (measurable_snd.comp measurable_snd)
    exact (measurable_of_finite (fun j : Fin n => decide (j = i))).comp hj

lemma RandomizedPolicy.chooseIdentity_reward (i : Fin n) (r : Unit) (x u : Fin n → ℝ)
    (hui : u i ≤ 1) : (chooseIdentity i).rule.reward r Finset.univ x u = x i := by
  let π := (chooseIdentity i).rule
  have ha : π.accepted r Finset.univ x u = {i} := by
    ext j
    simp [π, chooseIdentity, Policy.accepted, Policy.action]
  have hs : π.stoppingTime r Finset.univ x u = u i := by
    apply le_antisymm
    · apply π.stoppingTime_le_of_accepted r Finset.univ x u i
      rw [ha]
      exact Finset.mem_singleton_self i
    · apply (π.le_stoppingTime_iff r Finset.univ x u (u i)).mpr
      refine ⟨hui, ?_⟩
      intro j hj
      rw [ha, Finset.mem_singleton] at hj
      subst j
      exact le_rfl
  have hsel : π.Selects r Finset.univ x u i := ⟨by rw [ha]; simp, hs.symm⟩
  have hactual : π.ActualSelects r Finset.univ x u i := by
    refine ⟨hsel, ?_⟩
    intro j hj
    have hji : j = i := by simpa only [ha, Finset.mem_singleton] using hj.1
    subst j
    exact le_rfl
  exact π.reward_eq_of_actualSelects r Finset.univ x u hactual

lemma RandomizedPolicy.chooseIdentity_expectedReward (P : Instance n) (i : Fin n) :
    (chooseIdentity i).expectedReward P = ∫ x, x ∂P.law i := by
  let π := chooseIdentity i
  have hp : MeasurePreserving (fun ω : π.World => ω.1 i) (P.worldLaw π.seedLaw) (P.law i) :=
    (measurePreserving_eval P.law i).comp measurePreserving_fst
  have hmap := integral_map (μ := P.worldLaw π.seedLaw) hp.measurable.aemeasurable
    (measurable_id : Measurable (id : ℝ → ℝ)).aestronglyMeasurable
  rw [hp.map_eq] at hmap
  calc
    _ = ∫ ω : π.World, ω.1 i ∂P.worldLaw π.seedLaw := by
      apply integral_congr_ae
      filter_upwards [P.world_clocks_mem_unitInterval π.seedLaw] with ω hω
      exact chooseIdentity_reward i ω.2.2 ω.1 ω.2.1 (hω i).2
    _ = _ := hmap.symm

/-- Each individual first moment is available by a causal feasible policy. -/
theorem optimalScalarValue_ge_coordinateMean (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (i : Fin n) :
    w * (∫ x, x ∂P.law i) ≤ optimalScalarValue P w c := by
  let π := RandomizedPolicy.chooseIdentity i
  have hV := scalarObjective_le_optimal π P hP hw hc
  have hJ := π.scalarObjective_eq P hP w c
  rw [RandomizedPolicy.chooseIdentity_expectedReward P i] at hJ
  have hT := π.expectedDuration_nonnegative P
  nlinarith [mul_nonneg hc hT]

end ProphetSecretary.Model
