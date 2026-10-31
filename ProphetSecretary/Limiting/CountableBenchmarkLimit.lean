import ProphetSecretary.Limiting.CountableMaximumDistribution
import ProphetSecretary.Limiting.WeakHybridBenchmark

/-!
# Cofinal truncation limits of the actual countable prophet benchmark

The finite retained CDF products converge to the actual infinite-product CDF.
At a level above reserve, the cloud tail is eventually exactly unchanged by
the cutoff. Bounded layer cake then yields convergence of expected maxima.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal Classical BigOperators
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Probability
variable (B : CountableInstance)

lemma maximum_probability_below_reserve {t : ℝ} (ht : t < (B.terminal : ℝ)) :
    B.valueLaw {v | B.maximum v ≤ t} = 0 := by
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [B.maximum_bounded] with v hv
  exact not_le_of_gt (ht.trans_le hv.1)

/-- Both truncation parameters may approach their targets jointly. The
retained prefix tends to infinity, while every cutoff remains above reserve. -/
theorem truncation_expectedMaximum_tendsto (Ns : ℕ → ℕ) (bs : ℕ → ℝ)
    (hbs : ∀ m, (B.terminal : ℝ) < bs m) (hN : Tendsto Ns atTop atTop)
    (hb : Tendsto bs atTop (𝓝 (B.terminal : ℝ))) :
    Tendsto (fun m => (B.truncation (Ns m) (bs m) (hbs m)).expectedMaximum) atTop (𝓝 B.expectedMaximum) := by
  let Cs := fun m => B.truncation (Ns m) (bs m) (hbs m)
  have hsRange (m : ℕ) : ∀ᵐ v ∂hybridValueLaw (Cs m).individuals (Cs m).intensity,
      hybridMaximum (B.terminal : ℝ) v ∈ Icc (0 : ℝ) B.cap := by
    filter_upwards [hybridValueLaw_values_bounds (Cs m).individuals (Cs m).intensity
      (Cs m).individual_bounded (Cs m).intensity_supported] with v hv
    exact ⟨hybridMaximum_nonnegative _ _,hybridMaximum_le B.cap.property
      (by exact_mod_cast B.terminal_le_cap) v (fun k => (hv k).2)⟩
  have hCDF : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) B.cap),
      Tendsto (fun m => (hybridValueLaw (Cs m).individuals (Cs m).intensity).real
        {v | hybridMaximum (B.terminal : ℝ) v ≤ t}) atTop
        (𝓝 (B.valueLaw.real {v | B.maximum v ≤ t})) := by
    filter_upwards [ae_restrict_of_ae (show ∀ᵐ t : ℝ ∂volume, t ≠ (B.terminal : ℝ) from volume.ae_ne _),
      ae_restrict_mem measurableSet_Ioc] with t hta ht
    rcases lt_or_gt_of_ne hta with hlow | hhigh
    · have he (m : ℕ) : (hybridValueLaw (Cs m).individuals (Cs m).intensity).real
          {v | hybridMaximum (B.terminal : ℝ) v ≤ t} = 0 := hybridMaximum_real_Iic_below _ _ hlow
      simp_rw [he,Measure.real,B.maximum_probability_below_reserve hlow]
      exact tendsto_const_nhds
    · have hProd := (ENNReal.multipliable_of_le_one (fun i : ℕ =>
        (prob_le_one : (B.individuals i : Measure ℝ) (Iic t) ≤ 1))).hasProd.tendsto_prod_nat.comp hN
      have hENN : Tendsto (fun m => hybridValueLaw (Cs m).individuals (Cs m).intensity
          {v | hybridMaximum (B.terminal : ℝ) v ≤ t}) atTop
          (𝓝 (B.valueLaw {v | B.maximum v ≤ t})) := by
        rw [B.maximum_probability_Iic hhigh]
        have hevent : ∀ᶠ m in atTop, bs m < t := (tendsto_order.mp hb).2 t hhigh
        have hEq : (fun m => ENNReal.ofReal (Real.exp (-B.intensity.real (Ioi t))) *
            ∏ i ∈ Finset.range (Ns m), (B.individuals i : Measure ℝ) (Iic t)) =ᶠ[atTop]
            (fun m => hybridValueLaw (Cs m).individuals (Cs m).intensity
              {v | hybridMaximum (B.terminal : ℝ) v ≤ t}) := by
          filter_upwards [hevent] with m hm
          rw [hybridMaximum_probability_Iic _ _ ht.1.le hhigh.le]
          have hTail : ((Cs m).intensity : Measure ℝ).real (Ioi t) = B.intensity.real (Ioi t) := by
            change (B.intensity.restrict (Ioi (bs m))).real (Ioi t) = _
            rw [Measure.real,Measure.restrict_apply measurableSet_Ioi,
              inter_eq_left.mpr (show Ioi t ⊆ Ioi (bs m) from fun _ hx => hm.trans hx)]
            rfl
          rw [hTail]
          congr 1
          change (∏ i ∈ Finset.range (Ns m), (B.individuals i : Measure ℝ) (Iic t)) =
            ∏ i : Fin (Ns m), (B.individuals i.val : Measure ℝ) (Iic t)
          exact (Fin.prod_univ_eq_prod_range _ _).symm
        exact Tendsto.congr' hEq (ENNReal.Tendsto.const_mul hProd (Or.inr ENNReal.ofReal_ne_top))
      exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hENN
  have hRange : ∀ᵐ v ∂B.valueLaw, B.maximum v ∈ Icc (0 : ℝ) B.cap :=
    B.maximum_bounded.mono fun _ hv => ⟨B.terminal.property.trans hv.1,hv.2⟩
  exact tendsto_integrals_of_bounded_cdf
    (fun m => hybridValueLaw (Cs m).individuals (Cs m).intensity) B.valueLaw
    (fun _ => hybridMaximum (B.terminal : ℝ)) B.maximum (fun _ => measurable_hybridMaximum _)
    B.measurable_maximum B.cap hsRange hRange hCDF

end ProphetSecretary.Limiting.CountableInstance
