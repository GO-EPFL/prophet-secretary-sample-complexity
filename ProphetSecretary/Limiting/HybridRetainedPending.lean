import ProphetSecretary.Limiting.HybridIndividualClock
import ProphetSecretary.Reach.FiniteReach

/-!
# Retained-candidate pending execution in a finite-intensity hybrid instance

The same count-hidden hybrid rule is executed while one retained identity
remains pending. Both its value and clock are erased only in the analytical
auxiliary variable. Actual product-law independence from that value-clock pair
is derived from this erasure and the independent anonymous configuration.
-/
open MeasureTheory ProbabilityTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n N : ℕ} {Seed : Type*}

lemma combinedValues_update_retained (x : Fin n → ℝ) (v : Fin N → Point) (i : Fin n) (a : ℝ) :
    combinedValues (Function.update x i a) v = Function.update (combinedValues x v) (i.castAdd N) a := by
  funext k
  induction k using Fin.addCases with
  | left j =>
    by_cases hji : j = i
    · subst j
      simp [combinedValues]
    · have hne : j.castAdd N ≠ i.castAdd N := by simpa only [ne_eq,Fin.castAdd_inj] using hji
      simp only [combinedValues,Fin.addCases_left,Function.update_of_ne hji,Function.update_of_ne hne]
  | right j =>
    have hne : j.natAdd n ≠ i.castAdd N := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
      omega
    simp only [combinedValues,Fin.addCases_right,Function.update_of_ne hne]

lemma HybridRule.pendingIndividualTime_eraseCandidate (π : HybridRule n Seed) (i : Fin n)
    (v : HybridWorld n Seed) :
    π.pendingIndividualTime i (v.1,Model.Instance.eraseWorld i v.2) = π.pendingIndividualTime i v := by
  dsimp only [HybridRule.pendingIndividualTime,Model.Instance.eraseWorld,Model.eraseCoordinate]
  rw [combinedValues_update_retained,combinedClocks_update,Model.Policy.pendingTime_update]

variable [MeasurableSpace Seed]

lemma HybridRule.measurable_pendingIndividualTime (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (i : Fin n) : Measurable (π.pendingIndividualTime i) := by
  apply measurable_of_configuration_prod_branches
  intro N
  let Ω := (Fin N → Point) × Model.World n Seed
  have hr : Measurable (fun v : Ω => v.2.2.2) := measurable_snd.comp (measurable_snd.comp measurable_snd)
  have hx (j : Fin n) : Measurable (fun v : Ω => v.2.1 j) :=
    (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)
  have hu (j : Fin n) : Measurable (fun v : Ω => v.2.2.1 j) :=
    (measurable_pi_apply j).comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
  have hv (j : Fin N) : Measurable (fun v : Ω => v.1 j) := (measurable_pi_apply j).comp measurable_fst
  exact (π.asFinitePolicy N).measurable_stoppingTime (π.asFinitePolicy_isMeasurable hπ N) hr
    (fun k => measurable_combinedValues_family _ hx _ hv k)
    (fun k => measurable_combinedClocks_family _ hu _ hv k) (Finset.univ.erase (i.castAdd N))

lemma HybridRule.pendingIndividualTime_mem_unit (π : HybridRule n Seed) (P : Model.Instance n)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    ∀ᵐ v : HybridWorld n Seed ∂hybridWorldLaw P μ ν, π.pendingIndividualTime i v ∈ Icc (0 : ℝ) 1 := by
  have hc := (Measure.quasiMeasurePreserving_fst (μ := configurationLaw μ) (ν := P.worldLaw ν)).ae
    (configuration_times_mem_Ioo μ)
  have hi := (Measure.quasiMeasurePreserving_snd (μ := configurationLaw μ) (ν := P.worldLaw ν)).ae
    (P.world_clocks_mem_unitInterval ν)
  filter_upwards [hc,hi] with v hv hvi
  have htime : ∀ k : Fin (n+v.1.1), 0 ≤ combinedClocks v.2.2.1 v.1.2 k := by
    intro k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) k
    · simpa only [combinedClocks,Fin.addCases_left] using (hvi j).1
    · simpa only [combinedClocks,Fin.addCases_right] using (hv j).1.le
  exact ⟨(π.asFinitePolicy v.1.1).stoppingTime_nonneg _ _ _ _ htime,
    (π.asFinitePolicy v.1.1).stoppingTime_le_one _ _ _ _⟩

lemma HybridRule.integrable_pendingIndividualTime (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    Integrable (π.pendingIndividualTime i) (hybridWorldLaw P μ ν) := by
  apply Integrable.of_bound (π.measurable_pendingIndividualTime hπ i).aestronglyMeasurable 1
  filter_upwards [π.pendingIndividualTime_mem_unit P μ ν i] with v hv
  simpa only [Real.norm_eq_abs,abs_of_nonneg hv.1] using hv.2

/-- Joint independence from both omitted coordinates is a consequence of the
actual auxiliary execution and product laws, not an assumption on the rule. -/
theorem HybridRule.pendingIndividualTime_candidate_independent (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    IndepFun (π.pendingIndividualTime i) (fun v : HybridWorld n Seed => (v.2.1 i,v.2.2.1 i))
      (hybridWorldLaw P μ ν) := by
  have hpair : Measurable (fun ω : Model.World n Seed => (ω.1 i,ω.2.1 i)) :=
    ((measurable_pi_apply i).comp measurable_fst).prodMk ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))
  have hseed := Model.indepFun_with_seed (Model.Instance.measurable_eraseWorld (Seed := Seed) i) hpair
    (P.erasedWorld_candidate_independent ν i) (ν := configurationLaw μ)
  have hswap := Measure.measurePreserving_swap (μ := configurationLaw μ) (ν := P.worldLaw ν)
  have hleft : Measurable (fun z : Model.World n Seed × Configuration => (Model.Instance.eraseWorld i z.1,z.2)) :=
    ((Model.Instance.measurable_eraseWorld (Seed := Seed) i).comp measurable_fst).prodMk measurable_snd
  have hright : Measurable (fun z : Model.World n Seed × Configuration => (z.1.1 i,z.1.2.1 i)) := hpair.comp measurable_fst
  have hpull := Model.indepFun_pullback hswap hleft hright hseed
  have hf : Measurable (fun z : Model.World n Seed × Configuration => π.pendingIndividualTime i (z.2,z.1)) :=
    (π.measurable_pendingIndividualTime hπ i).comp measurable_swap
  have hfinal := hpull.comp hf measurable_id
  convert hfinal using 1
  · funext v
    exact (π.pendingIndividualTime_eraseCandidate i v).symm
  · rfl
  · rfl

lemma HybridRule.pendingIndividualTime_clock_independent (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    IndepFun (π.pendingIndividualTime i) (fun v : HybridWorld n Seed => v.2.2.1 i) (hybridWorldLaw P μ ν) := by
  have h := π.pendingIndividualTime_candidate_independent hπ P μ ν i
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  exact h.measure_inter_preimage_eq_mul s (Prod.snd ⁻¹' t) hs (measurable_snd ht)

end ProphetSecretary.Limiting
