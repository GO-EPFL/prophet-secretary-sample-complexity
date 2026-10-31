import ProphetSecretary.Limiting.IndividualGapIndex

/-!
# Ignoring added individual identities

An existing shared hybrid rule can reject additional individual candidates and
project their identities out of its retained history. Anonymous observations are
unchanged. The callback construction is uniform in the realized Poisson count.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

variable {n m : ℕ} {Seed : Type*}

noncomputable def HybridRule.ignoreIndividualExtras (π : HybridRule n Seed) (e : Fin n ↪ Fin m) : HybridRule m Seed where
  individual r t j x H Ξ := decide (∃ i, e i = j ∧ π.individual r t i x (Model.projectHistory e H) Ξ = true)
  poisson r t x H Ξ := π.poisson r t x (Model.projectHistory e H) Ξ

variable [MeasurableSpace Seed]

lemma HybridRule.ignoreIndividualExtras_isMeasurable (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (e : Fin n ↪ Fin m) : (π.ignoreIndividualExtras e).IsMeasurable := by
  constructor
  · apply measurable_to_bool
    let Ω := Seed × (ℝ × (Fin m × (ℝ × (Model.History m × Measure Point))))
    change MeasurableSet {z : Ω | decide (∃ i, e i = z.2.2.1 ∧
      π.individual z.1 z.2.1 i z.2.2.2.1 (Model.projectHistory e z.2.2.2.2.1) z.2.2.2.2.2 = true) = true}
    simp only [decide_eq_true_eq]
    rw [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    apply (measurableSet_eq_fun measurable_const (by fun_prop)).inter
    have hm : Measurable (fun z : Ω => π.individual z.1 z.2.1 i z.2.2.2.1
      (Model.projectHistory e z.2.2.2.2.1) z.2.2.2.2.2) := by
      have hp : Measurable (fun z : Ω => (z.1,(z.2.1,(i,(z.2.2.2.1,
          (Model.projectHistory e z.2.2.2.2.1,z.2.2.2.2.2)))))) := by
        unfold Model.projectHistory
        fun_prop
      exact hπ.1.comp hp
    exact hm (measurableSet_singleton true)
  · let Ω := Seed × (Point × (Model.History m × Measure Point))
    have hm : Measurable (fun z : Ω => (z.1,(z.2.1,(Model.projectHistory e z.2.2.1,z.2.2.2)))) := by
      unfold Model.projectHistory
      fun_prop
    exact hπ.2.comp hm

omit [MeasurableSpace Seed] in
lemma retainedHistory_individualGap_project (k N : ℕ) (H : Model.History (n + k + N)) :
    retainedHistory (Model.projectHistory (HybridZeroSimulation.keepEmbedding n k N).toEmbedding H) =
      Model.projectHistory (Fin.castAddEmb k) (retainedHistory H) := by
  funext i
  change H (HybridZeroSimulation.keepEmbedding n k N (i.castAdd N)) = H ((i.castAdd k).castAdd N)
  rw [HybridZeroSimulation.keepEmbedding_left]

omit [MeasurableSpace Seed] in
lemma poissonHistory_individualGap_project (k N : ℕ) (H : Model.History (n + k + N)) :
    poissonHistory (Model.projectHistory (HybridZeroSimulation.keepEmbedding n k N).toEmbedding H) = poissonHistory H := by
  unfold poissonHistory
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  change H (HybridZeroSimulation.keepEmbedding n k N (j.natAdd n)) = H (j.natAdd (n + k))
  rw [HybridZeroSimulation.keepEmbedding_right]

omit [MeasurableSpace Seed] in
lemma HybridRule.ignoreIndividualExtras_adapter (π : HybridRule n Seed) (k N : ℕ) :
    (π.ignoreIndividualExtras (Fin.castAddEmb k)).asFinitePolicy N =
      (π.asFinitePolicy N).ignoreExtras (HybridZeroSimulation.keepEmbedding n k N).toEmbedding := by
  change Model.Policy.mk _ = Model.Policy.mk _
  congr 1
  funext r t j x H
  have hret := retainedHistory_individualGap_project k N H
  have hpoi := poissonHistory_individualGap_project k N H
  induction j using Fin.addCases with
  | left j =>
    simp only [Fin.addCases_left, HybridRule.ignoreIndividualExtras, Fin.castAddEmb_apply]
    induction j using Fin.addCases with
    | left i =>
      change decide (∃ l : Fin n, l.castAdd k = i.castAdd k ∧
        π.individual r t l x (Model.projectHistory (Fin.castAddEmb k) (retainedHistory H)) (poissonHistory H) = true) =
        decide (∃ l : Fin (n + N), HybridZeroSimulation.keepEmbedding n k N l = (i.castAdd k).castAdd N ∧
          (π.asFinitePolicy N).decide r t l x (Model.projectHistory (HybridZeroSimulation.keepEmbedding n k N).toEmbedding H) = true)
      rw [← HybridZeroSimulation.keepEmbedding_left (n := n) (k := k) (N := N) i]
      simp only [Fin.castAdd_inj, (HybridZeroSimulation.keepEmbedding n k N).injective.eq_iff, exists_eq_left,
        HybridRule.asFinitePolicy, Fin.addCases_left, hret, hpoi]
    | right j =>
      have hcast : ∀ l : Fin n, l.castAdd k ≠ j.natAdd n := by
        intro l heq
        have hv := congrArg Fin.val heq
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      change decide (∃ l : Fin n, l.castAdd k = j.natAdd n ∧ _) =
        decide (∃ l : Fin (n + N), HybridZeroSimulation.keepEmbedding n k N l = (j.natAdd n).castAdd N ∧ _)
      simp only [hcast, HybridZeroSimulation.keepEmbedding_ne_inserted, false_and]
      simp
  | right j =>
    simp only [Fin.addCases_right, HybridRule.ignoreIndividualExtras]
    change π.poisson r t x (Model.projectHistory (Fin.castAddEmb k) (retainedHistory H)) (poissonHistory H) =
      decide (∃ l : Fin (n + N), HybridZeroSimulation.keepEmbedding n k N l = j.natAdd (n + k) ∧
        (π.asFinitePolicy N).decide r t l x (Model.projectHistory (HybridZeroSimulation.keepEmbedding n k N).toEmbedding H) = true)
    rw [← HybridZeroSimulation.keepEmbedding_right (n := n) (k := k) (N := N) j]
    simp only [(HybridZeroSimulation.keepEmbedding n k N).injective.eq_iff, exists_eq_left,
      HybridRule.asFinitePolicy, Fin.addCases_right, hret, hpoi]
    cases π.poisson r t x (Model.projectHistory (Fin.castAddEmb k) (retainedHistory H)) (poissonHistory H) <;> rfl

omit [MeasurableSpace Seed] in
lemma HybridRule.ignoreIndividualExtras_stoppingTime (π : HybridRule n Seed) (k : ℕ) (r : Seed)
    (x u : Fin n → ℝ) (z : Fin k → ℝ) (ω : Configuration) :
    (π.ignoreIndividualExtras (Fin.castAddEmb k)).stoppingTime r
      (Model.ZeroSimulation.appendValues x) (Model.ZeroSimulation.appendClocks u z) ω =
        π.stoppingTime r x u ω := by
  change ((π.ignoreIndividualExtras (Fin.castAddEmb k)).asFinitePolicy ω.1).stoppingTime r Finset.univ
    (combinedValues (Model.ZeroSimulation.appendValues x) ω.2) (combinedClocks (Model.ZeroSimulation.appendClocks u z) ω.2) = _
  rw [π.ignoreIndividualExtras_adapter k ω.1, Model.Policy.ignoreExtras_stoppingTime]
  have hx : combinedValues (Model.ZeroSimulation.appendValues (m := k) x) ω.2 ∘
      (HybridZeroSimulation.keepEmbedding n k ω.1).toEmbedding = combinedValues x ω.2 := by
    funext i
    exact HybridZeroSimulation.combinedValues_keep x ω.2 i
  have hu : combinedClocks (Model.ZeroSimulation.appendClocks u z) ω.2 ∘
      (HybridZeroSimulation.keepEmbedding n k ω.1).toEmbedding = combinedClocks u ω.2 := by
    funext i
    exact HybridZeroSimulation.combinedClocks_keep u z ω.2 i
  rw [hx,hu]
  rfl

omit [MeasurableSpace Seed] in
lemma HybridRule.ignoreIndividualExtras_reward_zero (π : HybridRule n Seed) (k : ℕ) (r : Seed)
    (x u : Fin n → ℝ) (z : Fin k → ℝ) (ω : Configuration) :
    (π.ignoreIndividualExtras (Fin.castAddEmb k)).reward 0 r
      (Model.ZeroSimulation.appendValues x) (Model.ZeroSimulation.appendClocks u z) ω =
        π.reward 0 r x u ω := by
  rw [HybridZeroSimulation.reward_zero_eq_finite, HybridZeroSimulation.reward_zero_eq_finite,
    π.ignoreIndividualExtras_adapter k ω.1, Model.Policy.ignoreExtras_reward_orderEmbedding]
  have hx : combinedValues (Model.ZeroSimulation.appendValues (m := k) x) ω.2 ∘
      (HybridZeroSimulation.keepEmbedding n k ω.1).toEmbedding = combinedValues x ω.2 := by
    funext i
    exact HybridZeroSimulation.combinedValues_keep x ω.2 i
  have hu : combinedClocks (Model.ZeroSimulation.appendClocks u z) ω.2 ∘
      (HybridZeroSimulation.keepEmbedding n k ω.1).toEmbedding = combinedClocks u ω.2 := by
    funext i
    exact HybridZeroSimulation.combinedClocks_keep u z ω.2 i
  change (π.asFinitePolicy ω.1).reward r Finset.univ
    (combinedValues (Model.ZeroSimulation.appendValues x) ω.2 ∘ (HybridZeroSimulation.keepEmbedding n k ω.1).toEmbedding)
    (combinedClocks (Model.ZeroSimulation.appendClocks u z) ω.2 ∘ (HybridZeroSimulation.keepEmbedding n k ω.1).toEmbedding) = _
  rw [hx,hu]

end ProphetSecretary.Limiting
