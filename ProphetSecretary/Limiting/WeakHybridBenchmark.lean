import ProphetSecretary.Limiting.HybridMaximumDistribution
import ProphetSecretary.Limiting.HybridScalarObjectives
import ProphetSecretary.Model.WeakValueContinuity
import ProphetSecretary.Probability.WeakCDF
import ProphetSecretary.Probability.BoundedCDFMean

/-!
# Weak continuity of bounded finite-hybrid prophet benchmarks

The exact Poisson void CDF and the retained product CDF converge at common
continuity levels. Bounded layer cake transfers this to the expected maximum.
There is no policy or optimizing-policy convergence assertion.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n : ℕ}

lemma hybridMaximum_real_Iic (P : Model.Instance n) (μ : FiniteMeasure ℝ)
    {a t : ℝ} (ht : 0 ≤ t) (hat : a ≤ t) :
    (hybridValueLaw P μ).real {v | hybridMaximum a v ≤ t} =
      Real.exp (-(μ : Measure ℝ).real (Ioi t)) * ∏ i, (P.law i).real (Iic t) := by
  rw [Measure.real,hybridMaximum_probability_Iic P μ ht hat,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,ENNReal.toReal_prod]
  rfl

lemma hybridMaximum_real_Iic_below (P : Model.Instance n) (μ : FiniteMeasure ℝ)
    {a t : ℝ} (ht : t < a) : (hybridValueLaw P μ).real {v | hybridMaximum a v ≤ t} = 0 := by
  have he : {v : Configuration × (Fin n → ℝ) | hybridMaximum a v ≤ t} = ∅ := by
    ext v
    simp only [mem_setOf_eq,mem_empty_iff_false,iff_false]
    exact not_le_of_gt (ht.trans_le (le_max_left _ _))
  rw [he,measureReal_empty]

/-- Fixed finite retained dimension and a common terminal reward: weak laws
imply convergence of the actual capped prophet expectations. Atoms and zero
intensity are allowed. -/
theorem expectedMaximum_tendsto_of_weak {Γ : Type*} {l : Filter Γ} [l.IsCountablyGenerated]
    (Bs : Γ → FiniteIntensityHybridInstance n) (B : FiniteIntensityHybridInstance n)
    (H : ℝ≥0) (hCaps : ∀ m, (Bs m).cap ≤ H) (hCap : B.cap ≤ H)
    (hTerm : ∀ m, (Bs m).terminal = B.terminal)
    (hIndividual : ∀ i, Tendsto (fun m => (Bs m).individuals.marginalProbabilityLaw i) l
      (𝓝 (B.individuals.marginalProbabilityLaw i)))
    (hIntensity : Tendsto (fun m => (Bs m).intensity) l (𝓝 B.intensity)) :
    Tendsto (fun m => (Bs m).expectedMaximum) l (𝓝 B.expectedMaximum) := by
  have hsRange (m : Γ) : ∀ᵐ v ∂hybridValueLaw (Bs m).individuals (Bs m).intensity,
      hybridMaximum (B.terminal : ℝ) v ∈ Icc (0 : ℝ) H := by
    filter_upwards [hybridValueLaw_values_bounds (Bs m).individuals (Bs m).intensity
      (Bs m).individual_bounded (Bs m).intensity_supported] with v hv
    refine ⟨hybridMaximum_nonnegative _ _,?_⟩
    apply hybridMaximum_le H.property
      (show (B.terminal : ℝ) ≤ (H : ℝ) by rw [← hTerm m]; exact_mod_cast (Bs m).terminal_le_cap.trans (hCaps m))
    intro k
    exact (hv k).2.trans (by exact_mod_cast hCaps m)
  have hRange : ∀ᵐ v ∂hybridValueLaw B.individuals B.intensity,
      hybridMaximum (B.terminal : ℝ) v ∈ Icc (0 : ℝ) H := by
    filter_upwards [hybridValueLaw_values_bounds B.individuals B.intensity B.individual_bounded B.intensity_supported] with v hv
    refine ⟨hybridMaximum_nonnegative _ _,?_⟩
    exact hybridMaximum_le H.property (by exact_mod_cast B.terminal_le_cap.trans hCap) v
      (fun k => (hv k).2.trans (by exact_mod_cast hCap))
  have hCDF : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) H),
      Tendsto (fun m => (hybridValueLaw (Bs m).individuals (Bs m).intensity).real
        {v | hybridMaximum (B.terminal : ℝ) v ≤ t}) l
        (𝓝 ((hybridValueLaw B.individuals B.intensity).real {v | hybridMaximum (B.terminal : ℝ) v ≤ t})) := by
    have hAi : ∀ᵐ t ∂volume, ∀ i : Fin n, (B.individuals.law i) {t} = 0 :=
      ae_all_iff.mpr (fun i => atom_zero_volume_ae (B.individuals.marginalProbabilityLaw i).toFiniteMeasure)
    filter_upwards [ae_restrict_of_ae (atom_zero_volume_ae B.intensity),ae_restrict_of_ae hAi,
      ae_restrict_mem measurableSet_Ioc] with t htμ hti ht
    by_cases hta : (B.terminal : ℝ) ≤ t
    · simp_rw [hybridMaximum_real_Iic _ _ ht.1.le hta]
      have hP (i : Fin n) : Tendsto (fun m => ((Bs m).individuals.law i).real (Iic t)) l
          (𝓝 ((B.individuals.law i).real (Iic t))) := by
        have he := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' (hIndividual i)
          (show (B.individuals.marginalProbabilityLaw i : Measure ℝ) (frontier (Iic t)) = 0 by
            change (B.individuals.law i) (frontier (Iic t)) = 0
            simpa only [frontier_Iic] using hti i)
        exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp he
      exact ((Real.continuous_exp.tendsto _).comp (finiteMeasure_real_Ioi_tendsto hIntensity htμ).neg).mul
        (tendsto_finsetProd Finset.univ (fun i _ => hP i))
    · simp_rw [hybridMaximum_real_Iic_below _ _ (not_le.mp hta)]
      exact tendsto_const_nhds
  have h := tendsto_integrals_of_bounded_cdf
    (fun m => hybridValueLaw (Bs m).individuals (Bs m).intensity)
    (hybridValueLaw B.individuals B.intensity)
    (fun _ => hybridMaximum (B.terminal : ℝ)) (hybridMaximum (B.terminal : ℝ))
    (fun _ => measurable_hybridMaximum _) (measurable_hybridMaximum _) H hsRange hRange hCDF
  convert h using 1
  · funext m
    simp only [FiniteIntensityHybridInstance.expectedMaximum,hybridExpectedMaximum,hTerm m]
  · rfl

end ProphetSecretary.Limiting
