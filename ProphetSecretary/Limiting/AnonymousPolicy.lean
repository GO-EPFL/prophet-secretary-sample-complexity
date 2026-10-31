import ProphetSecretary.Limiting.ConfigurationMeasurability
import ProphetSecretary.Limiting.Support
import ProphetSecretary.Limiting.Mecke
import ProphetSecretary.Reach.Pending

/-!
# Executing one anonymous rule across all Poisson counts

The finite policy family below is an analytical adapter for a single anonymous
history rule. Its decisions receive neither the array length nor generation
labels. The adapter is not an independently optimized policy for each length.
Deleting one candidate constructs its actual pending execution.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal NNReal

namespace ProphetSecretary.Limiting

private def observationEncoding : Option Point → Unit ⊕ Point
  | none => Sum.inl ()
  | some p => Sum.inr p

noncomputable def observationMeasure : Option Point → Measure Point
  | none => 0
  | some p => Measure.dirac p

lemma measurable_observationMeasure : Measurable observationMeasure := by
  have hc : Measurable observationEncoding := Measurable.of_comap_le le_rfl
  have hm : Measurable (Sum.elim (fun _ : Unit => (0 : Measure Point)) Measure.dirac) :=
    measurable_const.sumElim Measure.measurable_dirac
  convert hm.comp hc using 1
  funext o
  cases o <;> rfl

noncomputable def historyMeasure {N : ℕ} (H : ProphetSecretary.Model.History N) : Measure Point :=
  ∑ j, observationMeasure (H j)

lemma measurable_historyMeasure (N : ℕ) : Measurable (@historyMeasure N) :=
  Finset.measurable_fun_sum _ (fun j _ => measurable_observationMeasure.comp (measurable_pi_apply j))

/-- A derived analytical finite-array adapter. Every member uses exactly the same
anonymous decision function and aggregates only actually observed points. -/
noncomputable def AnonymousRule.asFinitePolicy {Seed : Type*} (π : AnonymousRule Seed) (N : ℕ) :
    ProphetSecretary.Model.Policy Seed N where
  decide r t _j x H := π.decide r t x (historyMeasure H)

lemma AnonymousRule.asFinitePolicy_isMeasurable {Seed : Type*} [MeasurableSpace Seed]
    (π : AnonymousRule Seed) (hπ : π.IsMeasurable) (N : ℕ) : (π.asFinitePolicy N).IsMeasurable := by
  let Z := Seed × (ℝ × (Fin N × (ℝ × ProphetSecretary.Model.History N)))
  have hr : Measurable (fun z : Z => z.1) := measurable_fst
  have ht : Measurable (fun z : Z => z.2.1) := measurable_fst.comp measurable_snd
  have hx : Measurable (fun z : Z => z.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hH : Measurable (fun z : Z => z.2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  exact hπ.comp (hr.prodMk ((ht.prodMk hx).prodMk ((measurable_historyMeasure N).comp hH)))

lemma historyMeasure_history {N : ℕ} (v : Fin N → Point) (t : ℝ) :
    historyMeasure (ProphetSecretary.Model.history Finset.univ (fun j => (v j).2) (fun j => (v j).1) t) =
      observedHistory ⟨N, v⟩ t := by
  unfold historyMeasure observedHistory
  apply Finset.sum_congr rfl
  intro j _
  simp only [ProphetSecretary.Model.history, Finset.mem_univ, true_and]
  split_ifs <;> rfl

lemma historyMeasure_history_erase {m : ℕ} (v : Fin (m + 1) → Point) (j : Fin (m + 1)) (t : ℝ) :
    historyMeasure (ProphetSecretary.Model.history (Finset.univ.erase j) (fun k => (v k).2) (fun k => (v k).1) t) =
      observedHistory (configurationMk m (fun k => v (j.succAbove k))) t := by
  unfold historyMeasure
  rw [Fin.sum_univ_succAbove _ j]
  have hj : observationMeasure (ProphetSecretary.Model.history (Finset.univ.erase j)
      (fun k => (v k).2) (fun k => (v k).1) t j) = 0 := by simp [ProphetSecretary.Model.history, observationMeasure]
  rw [hj, zero_add]
  change (∑ k : Fin m, observationMeasure (ProphetSecretary.Model.history (Finset.univ.erase j)
      (fun k => (v k).2) (fun k => (v k).1) t (j.succAbove k))) = _
  unfold observedHistory
  apply Finset.sum_congr rfl
  intro k _
  have hkne : j.succAbove k ≠ j := Fin.succAbove_ne j k
  simp only [ProphetSecretary.Model.history, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, hkne, not_false_eq_true, true_and, configurationMk]
  split_ifs <;> rfl

lemma AnonymousRule.asFinitePolicy_action {Seed : Type*} (π : AnonymousRule Seed) (r : Seed)
    {N : ℕ} (v : Fin N → Point) (j : Fin N) :
    (π.asFinitePolicy N).action r Finset.univ (fun k => (v k).2) (fun k => (v k).1) j = π.action r v j := by
  unfold ProphetSecretary.Model.Policy.action AnonymousRule.asFinitePolicy
  dsimp only
  rw [historyMeasure_history]
  rfl

lemma AnonymousRule.asFinitePolicy_pending_action {Seed : Type*} (π : AnonymousRule Seed) (r : Seed)
    {m : ℕ} (v : Fin (m + 1) → Point) (j : Fin (m + 1)) (k : Fin m) :
    (π.asFinitePolicy (m + 1)).action r (Finset.univ.erase j) (fun l => (v l).2) (fun l => (v l).1)
      (j.succAbove k) = π.action r (fun l => v (j.succAbove l)) k := by
  unfold ProphetSecretary.Model.Policy.action AnonymousRule.asFinitePolicy
  dsimp only
  rw [historyMeasure_history_erase]
  rfl

noncomputable def AnonymousRule.stoppingTime {Seed : Type*} (π : AnonymousRule Seed) (r : Seed)
    (ω : Configuration) : ℝ :=
  (π.asFinitePolicy ω.1).stoppingTime r Finset.univ (fun j => (ω.2 j).2) (fun j => (ω.2 j).1)

def AnonymousRule.Reaches {Seed : Type*} (π : AnonymousRule Seed) (r : Seed)
    (ω : Configuration) (j : Fin ω.1) : Prop :=
  (π.asFinitePolicy ω.1).Reaches r (fun k => (ω.2 k).2) (fun k => (ω.2 k).1) j

lemma AnonymousRule.pendingTime_eq_deleted {Seed : Type*} (π : AnonymousRule Seed) (r : Seed)
    {m : ℕ} (v : Fin (m + 1) → Point) (j : Fin (m + 1)) :
    (π.asFinitePolicy (m + 1)).pendingTime r (fun k => (v k).2) (fun k => (v k).1) j =
      π.stoppingTime r (configurationMk m (fun k => v (j.succAbove k))) := by
  let ψ := π.asFinitePolicy (m + 1)
  let χ := π.asFinitePolicy m
  let x := fun k => (v k).2
  let u := fun k => (v k).1
  let y := fun k : Fin m => (v (j.succAbove k)).2
  let w := fun k : Fin m => (v (j.succAbove k)).1
  have hact (k : Fin m) : ψ.action r (Finset.univ.erase j) x u (j.succAbove k) = χ.action r Finset.univ y w k :=
    (π.asFinitePolicy_pending_action r v j k).trans (π.asFinitePolicy_action r (fun l => v (j.succAbove l)) k).symm
  have hac (k : Fin m) : j.succAbove k ∈ ψ.accepted r (Finset.univ.erase j) x u ↔ k ∈ χ.accepted r Finset.univ y w := by
    rw [ψ.mem_accepted, χ.mem_accepted]
    have hkne : j.succAbove k ≠ j := Fin.succAbove_ne j k
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, ne_eq, hkne, not_false_eq_true, true_and, hact]
  change ψ.stoppingTime r (Finset.univ.erase j) x u = χ.stoppingTime r Finset.univ y w
  apply le_antisymm
  · apply (χ.le_stoppingTime_iff _ _ _ _ _).mpr
    refine ⟨ψ.stoppingTime_le_one _ _ _ _, ?_⟩
    intro k hk
    exact ψ.stoppingTime_le_of_accepted r (Finset.univ.erase j) x u (j.succAbove k) ((hac k).mpr hk)
  · apply (ψ.le_stoppingTime_iff _ _ _ _ _).mpr
    refine ⟨χ.stoppingTime_le_one _ _ _ _, ?_⟩
    intro k hk
    have hkj : k ≠ j := (Finset.mem_erase.mp ((ψ.mem_accepted _ _ _ _ _).mp hk).1).1
    obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hkj
    have hk' : j.succAbove l ∈ ψ.accepted r (Finset.univ.erase j) x u := by rw [hl]; exact hk
    have he := χ.stoppingTime_le_of_accepted r Finset.univ y w l ((hac l).mp hk')
    simpa only [w, hl, u] using he

/-- Reaching a candidate is equivalent to its arrival preceding the stopping time
of the actual deleted execution of the same anonymous rule. -/
lemma AnonymousRule.reaches_iff_le_deleted {Seed : Type*} (π : AnonymousRule Seed) (r : Seed)
    (ω : Configuration) (j : Fin ω.1) (ht : (ω.2 j).1 ≤ 1) :
    π.Reaches r ω j ↔ (ω.2 j).1 ≤ π.stoppingTime r (erasePoint ω j) := by
  rcases ω with ⟨N, v⟩
  cases N with
  | zero => exact Fin.elim0 j
  | succ m =>
    rw [AnonymousRule.Reaches, (π.asFinitePolicy (m + 1)).reaches_iff_le_pendingTime r _ _ j ht,
      π.pendingTime_eq_deleted r v j]
    rfl

lemma AnonymousRule.measurable_stoppingTime {Seed : Type*} [MeasurableSpace Seed]
    (π : AnonymousRule Seed) (hπ : π.IsMeasurable) :
    Measurable (fun v : World Seed => π.stoppingTime v.2 v.1) := by
  apply measurable_of_configuration_prod_branches
  intro N
  change Measurable (fun v : (Fin N → Point) × Seed => (π.asFinitePolicy N).stoppingTime v.2 Finset.univ
    (fun j => (v.1 j).2) (fun j => (v.1 j).1))
  exact (π.asFinitePolicy N).measurable_stoppingTime (π.asFinitePolicy_isMeasurable hπ N) measurable_snd
    (fun j => measurable_snd.comp ((measurable_pi_apply j).comp measurable_fst))
    (fun j => measurable_fst.comp ((measurable_pi_apply j).comp measurable_fst)) Finset.univ

lemma AnonymousRule.stoppingTime_le_one {Seed : Type*} (π : AnonymousRule Seed) (r : Seed) (ω : Configuration) :
    π.stoppingTime r ω ≤ 1 := (π.asFinitePolicy ω.1).stoppingTime_le_one _ _ _ _

lemma AnonymousRule.stoppingTime_mem_unitInterval {Seed : Type*} [MeasurableSpace Seed]
    (π : AnonymousRule Seed) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ v : World Seed ∂worldLaw μ ν, π.stoppingTime v.2 v.1 ∈ Icc (0 : ℝ) 1 := by
  have hc := (Measure.quasiMeasurePreserving_fst (μ := configurationLaw μ) (ν := ν)).ae
    (configuration_times_mem_Ioo μ)
  filter_upwards [hc] with v hv
  exact ⟨(π.asFinitePolicy v.1.1).stoppingTime_nonneg _ _ _ _ (fun j => (hv j).1.le), π.stoppingTime_le_one _ _⟩

lemma AnonymousRule.integrable_stoppingTime {Seed : Type*} [MeasurableSpace Seed]
    (π : AnonymousRule Seed) (hπ : π.IsMeasurable) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    Integrable (fun v : World Seed => π.stoppingTime v.2 v.1) (worldLaw μ ν) := by
  apply Integrable.of_bound (π.measurable_stoppingTime hπ).aestronglyMeasurable 1
  filter_upwards [π.stoppingTime_mem_unitInterval μ ν] with v hv
  simpa only [Real.norm_eq_abs, abs_of_nonneg hv.1] using hv.2

end ProphetSecretary.Limiting
