import ProphetSecretary.Limiting.CountableCapExcess
import ProphetSecretary.Limiting.Campbell
import ProphetSecretary.Limiting.PoissonCounts

/-!
# Cap excess and overlap within an actual Poisson configuration

The excess sum has the Campbell first moment. Its difference from the excess
of the largest mark is nonnegative, and vanishes only when at most one mark
exceeds the cap. Poisson first and second count moments then force a zero
upper tail if the expected overlap is zero.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal
namespace ProphetSecretary.Limiting

noncomputable def configurationCapExcess (K : ℝ≥0) (ω : Configuration) : ℝ :=
  ∑ j : Fin ω.1, Model.tailValue K (ω.2 j).2

noncomputable def configurationCapOverlap (K : ℝ≥0) (ω : Configuration) : ℝ :=
  configurationCapExcess K ω-Model.tailValue K (CountableInstance.bandMaximum ω)

lemma configurationCapExcess_nonnegative (K : ℝ≥0) (ω : Configuration) : 0 ≤ configurationCapExcess K ω :=
  Finset.sum_nonneg (fun j _ => Model.tailValue_nonnegative K (ω.2 j).2)

lemma tail_bandMaximum_le_configurationCapExcess (K : ℝ≥0) (ω : Configuration) :
    Model.tailValue K (CountableInstance.bandMaximum ω) ≤ configurationCapExcess K ω := by
  have hSum := configurationCapExcess_nonnegative K ω
  have hMax : CountableInstance.bandMaximum ω ≤ (K : ℝ)+configurationCapExcess K ω := by
    apply Model.Instance.maximum_le _ (add_nonneg K.property hSum)
    intro j
    have hTerm : Model.tailValue K (ω.2 j).2 ≤ configurationCapExcess K ω :=
      Finset.single_le_sum (fun l _ => Model.tailValue_nonnegative K (ω.2 l).2) (Finset.mem_univ j)
    have hRaw : (ω.2 j).2-(K : ℝ) ≤ Model.tailValue K (ω.2 j).2 := le_max_left _ _
    change (ω.2 j).2 ≤ (K : ℝ)+configurationCapExcess K ω
    simpa only [add_comm] using (sub_le_iff_le_add).mp (hRaw.trans hTerm)
  exact max_le (by linarith) hSum

lemma configurationCapOverlap_nonnegative (K : ℝ≥0) (ω : Configuration) : 0 ≤ configurationCapOverlap K ω :=
  sub_nonneg.mpr (tail_bandMaximum_le_configurationCapExcess K ω)

lemma measurable_configurationCapExcess (K : ℝ≥0) : Measurable (configurationCapExcess K) := by
  apply measurable_of_configuration_branches
  intro N
  change Measurable (fun pts : Fin N → Point => ∑ j : Fin N, Model.tailValue K (pts j).2)
  exact Finset.measurable_fun_sum _ (fun j _ =>
    (Model.measurable_tailValue K).comp (measurable_snd.comp (measurable_pi_apply j)))

lemma measurable_configurationCapOverlap (K : ℝ≥0) : Measurable (configurationCapOverlap K) :=
  (measurable_configurationCapExcess K).sub ((Model.measurable_tailValue K).comp CountableInstance.measurable_bandMaximum)

lemma integrable_configurationCapExcess (μ : FiniteMeasure ℝ) (H K : ℝ≥0)
    (hSupp : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) H) :
    Integrable (configurationCapExcess K) (configurationLaw μ) := by
  have hCount := (configuration_count_integrable μ).mul_const (H : ℝ)
  apply hCount.mono' (measurable_configurationCapExcess K).aestronglyMeasurable
  filter_upwards [configuration_points_mem_band μ H hSupp] with ω hω
  rw [Real.norm_eq_abs,abs_of_nonneg (configurationCapExcess_nonnegative K ω)]
  calc
    _ ≤ ∑ _j : Fin ω.1, (H : ℝ) := Finset.sum_le_sum (fun j _ =>
      (Model.tailValue_le_abs K (ω.2 j).2).trans ((abs_of_pos (hω j).2.1).le.trans (hω j).2.2))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]

lemma integral_configurationCapExcess (μ : FiniteMeasure ℝ) (H K : ℝ≥0)
    (hSupp : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) H) :
    (∫ ω, configurationCapExcess K ω ∂configurationLaw μ)=∫ x, Model.tailValue K x ∂(μ : Measure ℝ) := by
  let f : Point → ℝ≥0∞ := fun p => ENNReal.ofReal (Model.tailValue K p.2)
  have hf : Measurable f := ((Model.measurable_tailValue K).comp measurable_snd).ennreal_ofReal
  have hI := integrable_configurationCapExcess μ H K hSupp
  have hμI := Model.integrable_tailValue (μ : Measure ℝ)
    (finiteIntensity_integrable_mark μ H (hSupp.mono fun _ hx => ⟨hx.1.le,hx.2⟩)) K
  have hE : ENNReal.ofReal (∫ ω, configurationCapExcess K ω ∂configurationLaw μ)=
      ENNReal.ofReal (∫ x, Model.tailValue K x ∂(μ : Measure ℝ)) := by
    calc
      _ = ∫⁻ ω, ENNReal.ofReal (configurationCapExcess K ω) ∂configurationLaw μ :=
        ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall (configurationCapExcess_nonnegative K))
      _ = ∫⁻ ω, pointSum f ω ∂configurationLaw μ := by
        apply lintegral_congr
        intro ω
        exact ENNReal.ofReal_sum_of_nonneg (fun j _ => Model.tailValue_nonnegative K (ω.2 j).2)
      _ = ∫⁻ p, f p ∂intensity μ := lintegral_pointSum μ f hf
      _ = ∫⁻ x, ENNReal.ofReal (Model.tailValue K x) ∂(μ : Measure ℝ) := by
        unfold intensity
        rw [lintegral_prod _ hf.aemeasurable]
        simp only [f,lintegral_const,measure_univ,mul_one]
      _ = _ := (ofReal_integral_eq_lintegral_ofReal hμI (Eventually.of_forall (Model.tailValue_nonnegative K))).symm
  have h := congrArg ENNReal.toReal hE
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (configurationCapExcess_nonnegative K)),
    ENNReal.toReal_ofReal (integral_nonneg (Model.tailValue_nonnegative K))] using h

lemma integrable_configurationCapOverlap (μ : FiniteMeasure ℝ) (H K : ℝ≥0)
    (hSupp : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) H) :
    Integrable (configurationCapOverlap K) (configurationLaw μ) := by
  have hSum := integrable_configurationCapExcess μ H K hSupp
  have hMax : Integrable (fun ω => Model.tailValue K (CountableInstance.bandMaximum ω)) (configurationLaw μ) := by
    apply hSum.mono' ((Model.measurable_tailValue K).comp CountableInstance.measurable_bandMaximum).aestronglyMeasurable
    exact Eventually.of_forall (fun ω => by
      change |Model.tailValue K (CountableInstance.bandMaximum ω)| ≤ configurationCapExcess K ω
      rw [abs_of_nonneg (Model.tailValue_nonnegative K _)]
      exact tail_bandMaximum_le_configurationCapExcess K ω)
  exact hSum.sub hMax

private lemma maximum_lt_of_all {n : ℕ} (x : Fin n → ℝ) {b : ℝ} (hb : 0 < b) (hx : ∀ i, x i < b) :
    Model.Instance.maximum x < b := by
  unfold Model.Instance.maximum
  apply (Finset.sup'_lt_iff _).mpr
  intro j _
  cases j with
  | none => exact hb
  | some i => exact hx i

lemma configurationCapOverlap_pos_of_two (K : ℝ≥0) (ω : Configuration) (i j : Fin ω.1) (hij : i ≠ j)
    (hi : (K : ℝ) < (ω.2 i).2) (hj : (K : ℝ) < (ω.2 j).2) : 0 < configurationCapOverlap K ω := by
  let f : Fin ω.1 → ℝ := fun k => Model.tailValue K (ω.2 k).2
  have hf (k : Fin ω.1) : 0 ≤ f k := Model.tailValue_nonnegative K _
  have hfi : 0 < f i := (sub_pos.mpr hi).trans_le (le_max_left _ _)
  have hfj : 0 < f j := (sub_pos.mpr hj).trans_le (le_max_left _ _)
  have hPair (a b : Fin ω.1) (hab : a ≠ b) : f a+f b ≤ ∑ k : Fin ω.1, f k := by
    have hSub : ({a,b} : Finset (Fin ω.1)) ⊆ Finset.univ := Finset.subset_univ _
    have h := Finset.sum_le_sum_of_subset_of_nonneg hSub (fun k _ _ => hf k)
    simpa only [Finset.sum_pair hab] using h
  have hLt (k : Fin ω.1) : f k < ∑ l : Fin ω.1, f l := by
    by_cases hki : k=i
    · subst k
      linarith only [hPair i j hij,hfj]
    · linarith only [hPair k i hki,hfi]
  have hSumPos : 0 < configurationCapExcess K ω := (hf i).trans_lt (hLt i)
  have hMax : CountableInstance.bandMaximum ω < (K : ℝ)+configurationCapExcess K ω := by
    apply maximum_lt_of_all _ (add_pos_of_nonneg_of_pos K.property hSumPos)
    intro k
    have hRaw : (ω.2 k).2-(K : ℝ) ≤ f k := le_max_left _ _
    have hL := hLt k
    change f k < configurationCapExcess K ω at hL
    change (ω.2 k).2 < (K : ℝ)+configurationCapExcess K ω
    simpa only [add_comm] using (sub_lt_iff_lt_add).mp (hRaw.trans_lt hL)
  have hTail : Model.tailValue K (CountableInstance.bandMaximum ω) < configurationCapExcess K ω :=
    max_lt (by linarith only [hMax]) hSumPos
  exact sub_pos.mpr hTail

lemma pointCount_le_one_of_capOverlap_zero (K : ℝ≥0) (ω : Configuration)
    (hZero : configurationCapOverlap K ω=0) : pointCount (univ ×ˢ Ioi (K : ℝ)) ω ≤ 1 := by
  let S : Finset (Fin ω.1) := Finset.univ.filter (fun j => (K : ℝ) < (ω.2 j).2)
  have hCard : S.card ≤ 1 := by
    by_contra h
    obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp (lt_of_not_ge h)
    have hPos := configurationCapOverlap_pos_of_two K ω i j hij
      (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2
    exact (ne_of_gt hPos) hZero
  simpa only [S,Finset.card_filter,pointCount,mem_prod,mem_univ,true_and,mem_Ioi] using hCard

lemma poisson_tail_zero_of_integral_capOverlap_zero (μ : FiniteMeasure ℝ) (H K : ℝ≥0)
    (hSupp : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) H)
    (hZero : (∫ ω, configurationCapOverlap K ω ∂configurationLaw μ)=0) :
    (μ : Measure ℝ) (Ioi (K : ℝ))=0 := by
  have hAE := (integral_eq_zero_iff_of_nonneg (configurationCapOverlap_nonnegative K)
    (integrable_configurationCapOverlap μ H K hSupp)).mp hZero
  have hSq : (fun ω : Configuration => (pointCount (univ ×ˢ Ioi (K : ℝ)) ω : ℝ)^2) =ᵐ[configurationLaw μ]
      (fun ω => (pointCount (univ ×ˢ Ioi (K : ℝ)) ω : ℝ)) := by
    filter_upwards [hAE] with ω hω
    have hCount := pointCount_le_one_of_capOverlap_zero K ω hω
    interval_cases hC : pointCount (univ ×ˢ Ioi (K : ℝ)) ω <;> norm_num
  have hMean := integral_congr_ae hSq
  rw [integral_pointCount_second μ (MeasurableSet.univ.prod measurableSet_Ioi),
    integral_pointCount μ (MeasurableSet.univ.prod measurableSet_Ioi)] at hMean
  have hRate : (intensity μ).real (univ ×ˢ Ioi (K : ℝ))=(μ : Measure ℝ).real (Ioi (K : ℝ)) := by
    rw [intensity,measureReal_prod_prod,probReal_univ,one_mul]
  rw [hRate] at hMean
  have hReal : (μ : Measure ℝ).real (Ioi (K : ℝ))=0 := by nlinarith only [hMean]
  exact ((ENNReal.toReal_eq_zero_iff _).mp hReal).resolve_right (measure_ne_top _ _)

end ProphetSecretary.Limiting
