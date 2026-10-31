import ProphetSecretary.Limiting.ConfigurationCapExcess

/-!
# Actual finite-prefix sums of countable cap excess

Each prefix retains the first N individual identities and the first N actual
Poisson generation bands. These are analytical benchmark prefixes, not policy
observations. Their excess sums dominate the prefix maximum excess, and their
expectations are bounded by the actual total cap excess.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal Topology
namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def capExcessPrefix (K : ℝ≥0) (N : ℕ) (v : ValueWorld) : ℝ :=
  ∑ i : Fin N, (Model.tailValue K (v.2 i.val)+configurationCapExcess K (v.1 i.val))

lemma capExcessPrefix_nonnegative (K : ℝ≥0) (N : ℕ) (v : ValueWorld) : 0 ≤ capExcessPrefix K N v :=
  Finset.sum_nonneg (fun i _ => add_nonneg (Model.tailValue_nonnegative K (v.2 i.val)) (configurationCapExcess_nonnegative K (v.1 i.val)))

lemma le_cutoff_add_tailValue (K : ℝ≥0) (x : ℝ) : x ≤ (K : ℝ)+Model.tailValue K x := by
  have h : x-(K : ℝ) ≤ Model.tailValue K x := le_max_left _ _
  simpa only [add_comm] using (sub_le_iff_le_add).mp h

lemma candidateMaxima_le_cutoff_add_excess (K : ℝ≥0) (v : ValueWorld) (i : ℕ) :
    candidateMaxima v i ≤ (K : ℝ)+(Model.tailValue K (v.2 i)+configurationCapExcess K (v.1 i)) := by
  have hX := le_cutoff_add_tailValue K (v.2 i)
  have hM := (le_cutoff_add_tailValue K (bandMaximum (v.1 i))).trans
    (add_le_add le_rfl (tail_bandMaximum_le_configurationCapExcess K (v.1 i)))
  apply max_le
  · exact hX.trans (add_le_add le_rfl (le_add_of_nonneg_right (configurationCapExcess_nonnegative K _)))
  · exact hM.trans (add_le_add le_rfl (le_add_of_nonneg_left (Model.tailValue_nonnegative K _)))

lemma maximumPrefix_capExcess_le (B : CountableInstance) (K : ℝ≥0) (hK : (B.terminal : ℝ) ≤ K)
    (N : ℕ) (v : ValueWorld) : Model.tailValue K (B.maximumPrefix N v) ≤ capExcessPrefix K N v := by
  have hS := capExcessPrefix_nonnegative K N v
  have hMax : B.maximumPrefix N v ≤ (K : ℝ)+capExcessPrefix K N v := by
    apply max_le (hK.trans (le_add_of_nonneg_right hS))
    apply Model.Instance.maximum_le _ (add_nonneg K.property hS)
    intro i
    have hTerm : Model.tailValue K (v.2 i.val)+configurationCapExcess K (v.1 i.val) ≤ capExcessPrefix K N v :=
      Finset.single_le_sum (f := fun j : Fin N => Model.tailValue K (v.2 j.val)+configurationCapExcess K (v.1 j.val))
        (fun j _ => add_nonneg (Model.tailValue_nonnegative K (v.2 j.val)) (configurationCapExcess_nonnegative K (v.1 j.val)))
        (Finset.mem_univ i)
    exact (candidateMaxima_le_cutoff_add_excess K v i.val).trans (add_le_add le_rfl hTerm)
  apply max_le _ hS
  exact (sub_le_iff_le_add).mpr (by simpa only [add_comm] using hMax)

lemma individualCapExcess_valueWorld_measurePreserving (B : CountableInstance) (i : ℕ) :
    MeasurePreserving (fun v : ValueWorld => v.2 i) B.valueLaw (B.individuals i : Measure ℝ) :=
  (B.individualValue_measurePreserving i).comp measurePreserving_snd

lemma bandCapExcess_valueWorld_measurePreserving (B : CountableInstance) (i : ℕ) :
    MeasurePreserving (fun v : ValueWorld => v.1 i) B.valueLaw (configurationLaw (B.bandIntensity i)) :=
  (B.bandConfiguration_measurePreserving i).comp measurePreserving_fst

lemma integrable_individualCapExcess_valueWorld (B : CountableInstance) (K : ℝ≥0) (i : ℕ) :
    Integrable (fun v : ValueWorld => Model.tailValue K (v.2 i)) B.valueLaw :=
  (B.individualCapExcess_valueWorld_measurePreserving i).integrable_comp_of_integrable (B.individualCapExcess_integrable K i)

lemma integral_individualCapExcess_valueWorld (B : CountableInstance) (K : ℝ≥0) (i : ℕ) :
    (∫ v : ValueWorld, Model.tailValue K (v.2 i) ∂B.valueLaw)=B.individualCapExcess K i :=
  (B.individualCapExcess_valueWorld_measurePreserving i).hasLaw.integral_comp
    (B.individualCapExcess_integrable K i).aestronglyMeasurable

lemma integrable_bandCapExcess_valueWorld (B : CountableInstance) (K : ℝ≥0) (i : ℕ) :
    Integrable (fun v : ValueWorld => configurationCapExcess K (v.1 i)) B.valueLaw :=
  (B.bandCapExcess_valueWorld_measurePreserving i).integrable_comp_of_integrable
    (integrable_configurationCapExcess _ B.cap K (B.bandIntensity_supported i))

lemma integral_bandCapExcess_valueWorld (B : CountableInstance) (K : ℝ≥0) (i : ℕ) :
    (∫ v : ValueWorld, configurationCapExcess K (v.1 i) ∂B.valueLaw)=
      ∫ x, Model.tailValue K x ∂(B.bandIntensity i : Measure ℝ) :=
  ((B.bandCapExcess_valueWorld_measurePreserving i).hasLaw.integral_comp
    (integrable_configurationCapExcess _ B.cap K (B.bandIntensity_supported i)).aestronglyMeasurable).trans
      (integral_configurationCapExcess _ B.cap K (B.bandIntensity_supported i))

lemma integrable_capExcessPrefix (B : CountableInstance) (K : ℝ≥0) (N : ℕ) :
    Integrable (capExcessPrefix K N) B.valueLaw :=
  integrable_finsetSum Finset.univ (fun i _ => (B.integrable_individualCapExcess_valueWorld K i.val).add
    (B.integrable_bandCapExcess_valueWorld K i.val))

lemma integral_capExcessPrefix (B : CountableInstance) (K : ℝ≥0) (N : ℕ) :
    (∫ v, capExcessPrefix K N v ∂B.valueLaw)=
      (∑ i : Fin N, B.individualCapExcess K i.val)+
      ∑ i : Fin N, ∫ x, Model.tailValue K x ∂(B.bandIntensity i.val : Measure ℝ) := by
  unfold capExcessPrefix
  rw [integral_finsetSum Finset.univ (fun i _ => (B.integrable_individualCapExcess_valueWorld K i.val).add
    (B.integrable_bandCapExcess_valueWorld K i.val))]
  simp only [integral_add (B.integrable_individualCapExcess_valueWorld K _) (B.integrable_bandCapExcess_valueWorld K _),
    B.integral_individualCapExcess_valueWorld,B.integral_bandCapExcess_valueWorld,Finset.sum_add_distrib]

lemma integral_capExcessPrefix_le_total (B : CountableInstance) (K : ℝ≥0) (hK : (B.terminal : ℝ) < K) (N : ℕ) :
    (∫ v, capExcessPrefix K N v ∂B.valueLaw) ≤ B.totalCapExcess K := by
  rw [B.integral_capExcessPrefix K N]
  apply add_le_add
  · rw [Fin.sum_univ_eq_sum_range]
    exact (B.summable_individualCapExcess K hK).sum_le_tsum (Finset.range N)
      (fun i _ => B.individualCapExcess_nonnegative K i)
  · rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ∫ x, Model.tailValue K x ∂(B.bandIntensity i : Measure ℝ)) N]
    have h := (B.hasSum_bandCapExcess K hK).summable.sum_le_tsum (Finset.range N)
      (fun i _ => integral_nonneg (Model.tailValue_nonnegative K))
    rwa [(B.hasSum_bandCapExcess K hK).tsum_eq] at h

lemma integrable_maximumPrefix_capExcess (B : CountableInstance) (K : ℝ≥0) (N : ℕ) :
    Integrable (fun v => Model.tailValue K (B.maximumPrefix N v)) B.valueLaw := by
  apply Integrable.of_bound ((Model.measurable_tailValue K).comp (B.measurable_maximumPrefix N)).aestronglyMeasurable (B.cap : ℝ)
  filter_upwards [B.candidateMaxima_bounded] with v hv
  have hZero : 0 ≤ B.maximumPrefix N v := B.terminal.property.trans (le_max_left _ _)
  have hMax : B.maximumPrefix N v ≤ (B.cap : ℝ) :=
    prefixMaximum_le (by exact_mod_cast B.terminal_le_cap) B.cap.property _ hv N
  change |Model.tailValue K (B.maximumPrefix N v)| ≤ (B.cap : ℝ)
  rw [abs_of_nonneg (Model.tailValue_nonnegative K _)]
  exact (Model.tailValue_le_abs K _).trans ((abs_of_nonneg hZero).le.trans hMax)

lemma integrable_maximum_capExcess (B : CountableInstance) (K : ℝ≥0) :
    Integrable (fun v => Model.tailValue K (B.maximum v)) B.valueLaw := by
  apply B.integrable_maximum.abs.mono' ((Model.measurable_tailValue K).comp B.measurable_maximum).aestronglyMeasurable
  exact Eventually.of_forall (fun v => by
    change |Model.tailValue K (B.maximum v)| ≤ |B.maximum v|
    rw [abs_of_nonneg (Model.tailValue_nonnegative K _)]
    exact Model.tailValue_le_abs K _)

lemma integral_maximumPrefix_capExcess_tendsto (B : CountableInstance) (K : ℝ≥0) :
    Tendsto (fun N => ∫ v, Model.tailValue K (B.maximumPrefix N v) ∂B.valueLaw) atTop
      (𝓝 (∫ v, Model.tailValue K (B.maximum v) ∂B.valueLaw)) := by
  have hMono : Monotone (Model.tailValue K) := fun x y hxy => max_le_max (sub_le_sub_right hxy _) le_rfl
  have hCont : Continuous (Model.tailValue K) := (continuous_id.sub continuous_const).max continuous_const
  apply integral_tendsto_of_tendsto_of_monotone (B.integrable_maximumPrefix_capExcess K) (B.integrable_maximum_capExcess K)
  · exact Eventually.of_forall (fun v => hMono.comp (prefixMaximum_monotone B.terminal (candidateMaxima v)))
  · filter_upwards [B.candidateMaxima_bounded] with v hv
    exact (hCont.tendsto _).comp (prefixMaximum_tendsto
      (show (B.terminal : ℝ) ≤ B.cap by exact_mod_cast B.terminal_le_cap) B.cap.property _ hv)

/-- The actual prophet excess is bounded by the sum of individual and Poisson
excess first moments, with no bound on unrestricted first moments near reserve. -/
theorem expectedMaximum_capExcess_le_total (B : CountableInstance) (K : ℝ≥0)
    (hK : (B.terminal : ℝ) < K) :
    (∫ v, Model.tailValue K (B.maximum v) ∂B.valueLaw) ≤ B.totalCapExcess K := by
  apply le_of_tendsto (B.integral_maximumPrefix_capExcess_tendsto K)
  exact Eventually.of_forall (fun N =>
    (integral_mono (B.integrable_maximumPrefix_capExcess K N) (B.integrable_capExcessPrefix K N)
      (B.maximumPrefix_capExcess_le K hK.le N)).trans (B.integral_capExcessPrefix_le_total K hK N))

end ProphetSecretary.Limiting.CountableInstance
