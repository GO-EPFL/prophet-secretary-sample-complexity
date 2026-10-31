import ProphetSecretary.Limiting.CountableBandMecke

/-!
# Integrable real Mecke identity for bounded nonnegative kernels

Unit-bounded kernels give sums dominated by the actual finite Poisson band
count. Both sides are therefore integrable, and the nonnegative full-world
Mecke identity converts to the ordinary real integral.
-/
open MeasureTheory Set Filter
open scoped Classical ENNReal
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

noncomputable def realBandMeckeSum (k : ℕ) (F : Point × CompleteWorld Seed → ℝ)
    (v : CompleteWorld Seed) : ℝ :=
  ∑ j : Fin (v.1 k).1, F ((v.1 k).2 j,eraseAnonymousPoint k v j)

omit [MeasurableSpace Seed] in
lemma ofReal_realBandMeckeSum (k : ℕ) (F : Point × CompleteWorld Seed → ℝ)
    (hF : ∀ z, 0 ≤ F z) (v : CompleteWorld Seed) :
    ENNReal.ofReal (realBandMeckeSum k F v)=
      bandMeckeSum k (fun z => ENNReal.ofReal (F z)) v :=
  ENNReal.ofReal_sum_of_nonneg (fun j _ => hF ((v.1 k).2 j,eraseAnonymousPoint k v j))

omit [MeasurableSpace Seed] in
lemma realBandMeckeSum_nonnegative (k : ℕ) (F : Point × CompleteWorld Seed → ℝ)
    (hF : ∀ z, 0 ≤ F z) (v : CompleteWorld Seed) : 0 ≤ realBandMeckeSum k F v :=
  Finset.sum_nonneg (fun j _ => hF ((v.1 k).2 j,eraseAnonymousPoint k v j))

lemma measurable_realBandMeckeSum (k : ℕ) (F : Point × CompleteWorld Seed → ℝ)
    (hF : Measurable F) (hNonnegative : ∀ z, 0 ≤ F z) :
    Measurable (realBandMeckeSum k F) := by
  have hMeas := ENNReal.measurable_toReal.comp
    (measurable_bandMeckeSum k _ (ENNReal.measurable_ofReal.comp hF))
  have hEq : (fun v : CompleteWorld Seed =>
      (bandMeckeSum k (fun z => ENNReal.ofReal (F z)) v).toReal)=realBandMeckeSum k F := by
    funext v
    rw [← ofReal_realBandMeckeSum k F hNonnegative v,ENNReal.toReal_ofReal (realBandMeckeSum_nonnegative k F hNonnegative v)]
  exact hEq ▸ hMeas

lemma integrable_bandConfiguration_count (B : CountableInstance) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (k : ℕ) :
    Integrable (fun v : CompleteWorld Seed => ((v.1 k).1 : ℝ)) (B.completeWorldLaw ν) := by
  have hMP := (B.bandConfiguration_measurePreserving k).comp
    (measurePreserving_fst : MeasurePreserving (Prod.fst : CompleteWorld Seed → BandConfigurations)
      (B.completeWorldLaw ν) B.bandConfigurationsLaw)
  exact hMP.integrable_comp_of_integrable (configuration_count_integrable (B.bandIntensity k))

theorem band_mecke_real_bounded (B : CountableInstance) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (k : ℕ) (F : Point × CompleteWorld Seed → ℝ)
    (hF : Measurable F) (hBound : ∀ z, F z ∈ Icc (0 : ℝ) 1) :
    Integrable (realBandMeckeSum k F) (B.completeWorldLaw ν) ∧
      Integrable F ((ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν)) ∧
      (∫ v, realBandMeckeSum k F v ∂B.completeWorldLaw ν)=
        ∫ z, F z ∂(ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν) := by
  have hNonnegative := fun z => (hBound z).1
  have hSumMeas := measurable_realBandMeckeSum k F hF hNonnegative
  have hSumInt : Integrable (realBandMeckeSum k F) (B.completeWorldLaw ν) := by
    apply (B.integrable_bandConfiguration_count ν k).mono' hSumMeas.aestronglyMeasurable
    exact Eventually.of_forall (fun v => by
      rw [Real.norm_eq_abs,abs_of_nonneg (realBandMeckeSum_nonnegative k F hNonnegative v)]
      have hLe := Finset.sum_le_sum (s := Finset.univ) (f := fun j : Fin (v.1 k).1 => F ((v.1 k).2 j,eraseAnonymousPoint k v j))
        (g := fun _ => (1 : ℝ)) (fun j _ => (hBound _).2)
      simpa only [realBandMeckeSum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] using hLe)
  have hInt : Integrable F ((ProphetSecretary.Limiting.intensity (B.bandIntensity k)).prod (B.completeWorldLaw ν)) := by
    apply Integrable.of_bound hF.aestronglyMeasurable 1
    exact Eventually.of_forall (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (hBound z).1]; exact (hBound z).2)
  refine ⟨hSumInt,hInt,?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall (realBandMeckeSum_nonnegative k F hNonnegative)) hSumMeas.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hNonnegative) hF.aestronglyMeasurable]
  congr 1
  simp_rw [ofReal_realBandMeckeSum k F hNonnegative]
  exact B.band_mecke ν k _ (ENNReal.measurable_ofReal.comp hF)

end ProphetSecretary.Limiting.CountableInstance
