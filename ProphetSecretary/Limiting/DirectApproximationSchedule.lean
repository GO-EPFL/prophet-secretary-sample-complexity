import ProphetSecretary.Analysis.DirectPoissonSize
import ProphetSecretary.Limiting.FinitePoissonBenchmarkLimit
import ProphetSecretary.Limiting.CountableBenchmarkLimit
import ProphetSecretary.Limiting.CountableValueLimit
import ProphetSecretary.Limiting.CountableTruncationTail

/-!
# A concrete direct finite approximation schedule

Retain the first m individuals and the cloud above markCutoff m. Choose
one finite Poisson refinement whose benchmark error is below 1/(m+1)
and whose virtual count dominates the explicit base-intensity bound.
The resulting count is fixed before any likelihood parameter is varied;
perturbed laws must reuse it rather than recomputing the refinement.
Paper correspondence: `con:direct-approx`.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal Topology
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Analysis

noncomputable def directTruncation (B : CountableInstance) (m : ℕ) : FiniteIntensityHybridInstance m :=
  B.truncation m (B.markCutoff m) (B.terminal_lt_markCutoff m)

lemma exists_directRefinement (B : CountableInstance) (hZero : B.terminal=0) (m : ℕ) :
    ∃ j : ℕ, directPoissonMultiplicity (B.directTruncation m).intensity.mass m≤j ∧
      |((B.directTruncation m).finitePoissonApproximation j).expectedMaximum-
        (B.directTruncation m).expectedMaximum|<1/((m : ℝ)+1) := by
  have hM := (B.directTruncation m).finitePoissonApproximation_expectedMaximum_tendsto hZero
  have hEvent := (eventually_ge_atTop (directPoissonMultiplicity (B.directTruncation m).intensity.mass m)).and
    (hM.eventually (Metric.ball_mem_nhds _ (by positivity : (0 : ℝ)<1/((m : ℝ)+1))))
  obtain ⟨j,hLarge,hClose⟩ := hEvent.exists
  exact ⟨j,hLarge,by simpa only [Metric.mem_ball,Real.dist_eq] using hClose⟩

noncomputable def directRefinementIndex (B : CountableInstance) (hZero : B.terminal=0) (m : ℕ) : ℕ :=
  Classical.choose (B.exists_directRefinement hZero m)

lemma directRefinementIndex_spec (B : CountableInstance) (hZero : B.terminal=0) (m : ℕ) :
    directPoissonMultiplicity (B.directTruncation m).intensity.mass m≤B.directRefinementIndex hZero m ∧
      |((B.directTruncation m).finitePoissonApproximation (B.directRefinementIndex hZero m)).expectedMaximum-
        (B.directTruncation m).expectedMaximum|<1/((m : ℝ)+1) :=
  Classical.choose_spec (B.exists_directRefinement hZero m)

noncomputable def directVirtualCount (B : CountableInstance) (hZero : B.terminal=0) (m : ℕ) : ℕ :=
  bernoulliMultiplicity (((B.directTruncation m).intensity : Measure ℝ).real univ) (B.directRefinementIndex hZero m)

noncomputable def directFiniteApproximation (B : CountableInstance) (hZero : B.terminal=0) (m : ℕ) :
    Model.Instance (m+B.directVirtualCount hZero m) :=
  (B.directTruncation m).finitePoissonApproximation (B.directRefinementIndex hZero m)

lemma directVirtualCount_ge_explicit (B : CountableInstance) (hZero : B.terminal=0) (m : ℕ) :
    directPoissonMultiplicity (B.directTruncation m).intensity.mass m≤B.directVirtualCount hZero m := by
  have h := (B.directRefinementIndex_spec hZero m).1
  dsimp only [directVirtualCount,bernoulliMultiplicity]
  omega

lemma directVirtualCount_positive (B : CountableInstance) (hZero : B.terminal=0) (m : ℕ) :
    0<B.directVirtualCount hZero m :=
  (directPoissonMultiplicity_positive (B.directTruncation m).intensity.mass m).trans_le
    (B.directVirtualCount_ge_explicit hZero m)

lemma directVirtualCount_rate_le (B : CountableInstance) (hZero : B.terminal=0) (m : ℕ) :
    (B.directTruncation m).intensity.mass≤(B.directVirtualCount hZero m : ℝ≥0) :=
  (rate_le_directPoissonMultiplicity (B.directTruncation m).intensity.mass m).trans
    (by exact_mod_cast B.directVirtualCount_ge_explicit hZero m)

lemma directVirtualCount_probability_le_half (B : CountableInstance) (hZero : B.terminal=0) (m : ℕ) :
    ((B.directTruncation m).intensity.mass : ℝ)/(B.directVirtualCount hZero m : ℝ)≤1/2 := by
  have hCount : (directPoissonMultiplicity (B.directTruncation m).intensity.mass m : ℝ)≤B.directVirtualCount hZero m :=
    by exact_mod_cast B.directVirtualCount_ge_explicit hZero m
  exact (div_le_div_of_nonneg_left (B.directTruncation m).intensity.mass.coe_nonneg
    (Nat.cast_pos.mpr (directPoissonMultiplicity_positive _ _)) hCount).trans
      (directPoissonProbability_le_half _ _)

lemma directVirtualCount_square_error_le (B : CountableInstance) (hZero : B.terminal=0) (m : ℕ) :
    ((B.directTruncation m).intensity.mass : ℝ)^2/(B.directVirtualCount hZero m : ℝ)≤1/((m : ℝ)+1)^2 := by
  have hCount : (directPoissonMultiplicity (B.directTruncation m).intensity.mass m : ℝ)≤B.directVirtualCount hZero m :=
    by exact_mod_cast B.directVirtualCount_ge_explicit hZero m
  exact (div_le_div_of_nonneg_left (sq_nonneg _)
    (Nat.cast_pos.mpr (directPoissonMultiplicity_positive _ _)) hCount).trans (directPoisson_square_error_le _ _)

lemma directVirtualCount_tendsto (B : CountableInstance) (hZero : B.terminal=0) :
    Tendsto (B.directVirtualCount hZero) atTop atTop := by
  apply tendsto_atTop_mono _ (directPoissonMultiplicity_tendsto (fun m => (B.directTruncation m).intensity.mass))
  exact fun m => B.directVirtualCount_ge_explicit hZero m

lemma directVirtualCount_square_error_tendsto (B : CountableInstance) (hZero : B.terminal=0) :
    Tendsto (fun m => ((B.directTruncation m).intensity.mass : ℝ)^2/(B.directVirtualCount hZero m : ℝ))
      atTop (𝓝 (0 : ℝ)) := by
  have hUpper : Tendsto (fun m : ℕ => 1/((m : ℝ)+1)^2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [div_pow,one_pow,zero_pow (by norm_num : (2 : ℕ)≠0)] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).pow 2
  exact squeeze_zero (fun m => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    (fun m => B.directVirtualCount_square_error_le hZero m) hUpper

lemma directFiniteApproximation_bounded (B : CountableInstance) (hZero : B.terminal=0) (m : ℕ) :
    ∀ i, ∀ᵐ x ∂(B.directFiniteApproximation hZero m).law i, x≤(B.cap : ℝ) := by
  unfold directFiniteApproximation
  rw [←(B.directTruncation m).rareDesign_eq_finitePoissonApproximation]
  exact rareDesign_bounded _ _ _ (B.directTruncation m).individual_bounded _ _ _ _

/-- The prophet limit concerns the actual product instances, not merely their
scalar values. Its per-truncation approximation error was chosen explicitly. -/
theorem directFiniteApproximation_expectedMaximum_tendsto (B : CountableInstance) (hZero : B.terminal=0) :
    Tendsto (fun m => (B.directFiniteApproximation hZero m).expectedMaximum) atTop (𝓝 B.expectedMaximum) := by
  have hM := B.truncation_expectedMaximum_tendsto id B.markCutoff B.terminal_lt_markCutoff tendsto_id B.markCutoff_tendsto
  have hTailError : Tendsto (fun m => |(B.directTruncation m).expectedMaximum-B.expectedMaximum|) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,abs_zero,directTruncation,id_eq] using (hM.sub_const B.expectedMaximum).abs
  have hUpper := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).add hTailError
  rw [zero_add] at hUpper
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hUpper
  intro m
  rw [Real.norm_eq_abs]
  exact (abs_sub_le _ _ _).trans (add_le_add (B.directRefinementIndex_spec hZero m).2.le le_rfl)

/-- The same actual approximants converge in scalar value for every pair of
nonnegative coefficients, without a total first-moment bound. -/
theorem directFiniteApproximation_value_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0≤w) (hc : 0≤c) :
    Tendsto (fun m => Model.optimalScalarValue (B.directFiniteApproximation hZero m) w c)
      atTop (𝓝 (B.optimalScalarValue w c)) := by
  let e := fun m => ((B.directTruncation m).intensity.mass : ℝ)^2/(B.directVirtualCount hZero m : ℝ)
  have hError : Tendsto e atTop (𝓝 (0 : ℝ)) := B.directVirtualCount_square_error_tendsto hZero
  have hSqrt : Tendsto (fun m => Real.sqrt (e m)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using (Real.continuous_sqrt.tendsto 0).comp hError
  have hSmall : Tendsto (fun m => w*(B.cap : ℝ)*(e m+(Real.pi/2)*Real.sqrt (e m))) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero,add_zero] using (hError.add (hSqrt.const_mul (Real.pi/2))).const_mul (w*(B.cap : ℝ))
  have hApprox (m : ℕ) :
      |Model.optimalScalarValue (B.directFiniteApproximation hZero m) w c-(B.directTruncation m).optimalScalarValue w c|≤
        w*(B.cap : ℝ)*(e m+(Real.pi/2)*Real.sqrt (e m)) := by
    have h := (B.directTruncation m).rareDesign_value_uniform_error hZero ⟨w,hw⟩
      (B.directTruncation m).intensity.mass le_rfl
      (bernoulliMultiplicity (((B.directTruncation m).intensity : Measure ℝ).real univ) (B.directRefinementIndex hZero m))
      (bernoulliMultiplicity_positive _ _) ((B.directTruncation m).mass_le_finitePoissonMultiplicity _)
      hw le_rfl hc
    rw [(B.directTruncation m).rareDesign_eq_finitePoissonApproximation (B.directRefinementIndex hZero m)] at h
    exact h
  have hT := B.truncation_value_tendsto id B.markCutoff B.terminal_lt_markCutoff tendsto_id B.markCutoff_tendsto hw hc
  have hTailError : Tendsto (fun m => |(B.directTruncation m).optimalScalarValue w c-B.optimalScalarValue w c|)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self,abs_zero,directTruncation,id_eq] using (hT.sub_const (B.optimalScalarValue w c)).abs
  have hUpper := hSmall.add hTailError
  rw [zero_add] at hUpper
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hUpper
  intro m
  rw [Real.norm_eq_abs]
  exact (abs_sub_le _ _ _).trans (add_le_add (hApprox m) le_rfl)

lemma directFiniteApproximation_tailCount_eq (B : CountableInstance) (hZero : B.terminal=0)
    (m : ℕ) {b : ℝ} (hb : 0≤b) :
    (B.directFiniteApproximation hZero m).tailCount b=(B.directTruncation m).tailCount b := by
  let T := B.directTruncation m
  let k := B.directVirtualCount hZero m
  have hk : 0<k := B.directVirtualCount_positive hZero m
  have hm : T.intensity.mass≤(k : ℝ≥0) := B.directVirtualCount_rate_le hZero m
  have hEq : B.directFiniteApproximation hZero m=rareDesign T.individuals T.intensity T.cap
      (T.intensity_supported.mono (fun _ hx => ⟨hx.1.le,hx.2⟩)) k hk hm :=
    (T.rareDesign_eq_finitePoissonApproximation (B.directRefinementIndex hZero m)).symm
  rw [hEq]
  unfold Model.Instance.tailCount
  rw [Fin.sum_univ_add]
  dsimp only [k]
  simp only [rareDesign,appendIID,Fin.addCases_left,Fin.addCases_right]
  change T.individuals.tailCount b+(∑ _ : Fin k,
    (rareProbabilityLaw T.intensity (k : ℝ≥0) (by exact_mod_cast hk) hm : Measure ℝ).real (Ioi b))=
      T.individuals.tailCount b+(T.intensity : Measure ℝ).real (Ioi b)
  simp only [rareProbabilityLaw_real_Ioi _ _ _ _ hb,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,NNReal.coe_natCast]
  rw [←mul_assoc,mul_inv_cancel₀ (ne_of_gt (Nat.cast_pos.mpr hk) : (k : ℝ)≠0),one_mul]

/-- An explicit finite common tail-count profile, uniform in the full
approximation index and independent of the growing number of offers. -/
theorem directFiniteApproximation_tailCount_le (B : CountableInstance) (hZero : B.terminal=0)
    (m : ℕ) {b : ℝ} (hb : 0<b) :
    (B.directFiniteApproximation hZero m).tailCount b≤(B.totalTailMass b).toReal := by
  rw [B.directFiniteApproximation_tailCount_eq hZero m hb.le]
  exact B.truncation_tailCount_le m (B.terminal_lt_markCutoff m) b
    (by simpa only [hZero,NNReal.coe_zero] using hb)

end ProphetSecretary.Limiting.CountableInstance
