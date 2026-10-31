import ProphetSecretary.Probability.UniformHazard
import Mathlib.Probability.CDF

/-!
# A probability-integral transform from attained CDF levels

On a measurable linear order, if the lower CDF attains every interior probability
level, its value at a random observation is uniform. The proof uses ordered
threshold inclusions and a midpoint argument, requiring no order topology on the
observation space. Tagged atom jumps will supply the attained-level hypothesis.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Probability
variable {α : Type*} [LinearOrder α] [MeasurableSpace α]

noncomputable def orderCDF (μ : Measure α) (x : α) : ℝ := μ.real (Iic x)

lemma orderCDF_mem_unit (μ : Measure α) [IsProbabilityMeasure μ] (x : α) : orderCDF μ x∈Icc (0:ℝ) 1 :=
  ⟨measureReal_nonneg,measureReal_le_one⟩

lemma orderCDF_monotone (μ : Measure α) [IsProbabilityMeasure μ] : Monotone (orderCDF μ) :=
  fun _ _ h => measureReal_mono (μ:=μ) (Set.Iic_subset_Iic.mpr h) (measure_ne_top _ _)

lemma measurable_orderCDF (μ : Measure α) [IsProbabilityMeasure μ]
    (hLE : MeasurableSet {p : α × α | p.1≤p.2}) : Measurable (orderCDF μ) := by
  have hIic (x : α) : MeasurableSet (Iic x) := hLE.preimage (measurable_id.prodMk measurable_const)
  have hSwap : MeasurableSet {p : α × α | p.2≤p.1} := hLE.preimage measurable_swap
  have hF : Measurable (fun p : α × α => if p.2≤p.1 then (1:ℝ) else 0) :=
    measurable_const.ite hSwap measurable_const
  have hEq : orderCDF μ=(fun x => ∫ y, (if y≤x then (1:ℝ) else 0) ∂μ) := by
    funext x
    have h := integral_indicator_const (μ:=μ) (1:ℝ) (hIic x)
    simpa only [orderCDF,Set.indicator_apply,Set.mem_Iic,smul_eq_mul,mul_one] using h.symm
  rw [hEq]
  exact (hF.stronglyMeasurable.integral_prod_right').measurable

lemma uniformClock_lowerCDF (s : ℝ) :
    Model.Instance.uniformClock.real (Iic s)=max (min s 1) 0 := by
  have hSet : Iic s∩Icc (0:ℝ) 1=Icc 0 (min s 1) := by
    ext x
    simp only [Set.mem_inter_iff,Set.mem_Iic,Set.mem_Icc,le_min_iff]
    tauto
  rw [Model.Instance.uniformClock,Measure.real,Measure.restrict_apply measurableSet_Iic,hSet,Real.volume_Icc]
  simp only [sub_zero,ENNReal.toReal_ofReal']

/-- Uniform law of the lower CDF when every interior probability level is attained. -/
theorem orderCDF_measurePreserving_uniform (μ : Measure α) [IsProbabilityMeasure μ]
    (hLE : MeasurableSet {p : α × α | p.1≤p.2})
    (hRange : ∀ q∈Ioo (0:ℝ) 1, ∃ x : α, orderCDF μ x=q) :
    MeasurePreserving (orderCDF μ) μ Model.Instance.uniformClock := by
  have hMeas := measurable_orderCDF μ hLE
  refine ⟨hMeas,?_⟩
  haveI : IsProbabilityMeasure (μ.map (orderCDF μ)) := Measure.isProbabilityMeasure_map hMeas.aemeasurable
  have hCDF (s : ℝ) : (μ.map (orderCDF μ)).real (Iic s)=Model.Instance.uniformClock.real (Iic s) := by
    rw [map_measureReal_apply hMeas measurableSet_Iic,uniformClock_lowerCDF]
    by_cases hs0 : s<0
    · have hE : (orderCDF μ) ⁻¹' Iic s=∅ := by
        ext x
        simp only [Set.mem_preimage,Set.mem_Iic,Set.mem_empty_iff_false,iff_false,not_le]
        exact hs0.trans_le (orderCDF_mem_unit μ x).1
      rw [hE,measureReal_empty,min_eq_left (show s≤1 by linarith only [hs0]),max_eq_right hs0.le]
    · have hsNonneg : 0≤s := le_of_not_gt hs0
      by_cases hs1 : s<1
      · have hUpper : μ.real ((orderCDF μ) ⁻¹' Iic s)≤s := by
          by_contra hNot
          have hBad : s<μ.real ((orderCDF μ) ⁻¹' Iic s) := lt_of_not_ge hNot
          let r := (s+μ.real ((orderCDF μ) ⁻¹' Iic s))/2
          have hR : r∈Ioo (0:ℝ) 1 := by
            have hProb : μ.real ((orderCDF μ) ⁻¹' Iic s)≤1 := measureReal_le_one
            dsimp [r]
            constructor <;> linarith only [hBad,hsNonneg,hs1,hProb]
          obtain ⟨x,hx⟩ := hRange r hR
          have hSub : (orderCDF μ) ⁻¹' Iic s⊆Iic x := by
            intro z hz
            change orderCDF μ z≤s at hz
            by_contra hzx
            have hMono := orderCDF_monotone μ (le_of_not_ge hzx)
            dsimp [r] at hx
            linarith only [hMono,hx,hz,hBad]
          have hMass := measureReal_mono (μ:=μ) hSub (measure_ne_top _ _)
          change μ.real ((orderCDF μ) ⁻¹' Iic s)≤orderCDF μ x at hMass
          rw [hx] at hMass
          dsimp [r] at hMass
          linarith only [hMass,hBad]
        have hLower : s≤μ.real ((orderCDF μ) ⁻¹' Iic s) := by
          by_cases hsPos : 0<s
          · obtain ⟨x,hx⟩ := hRange s ⟨hsPos,hs1⟩
            have hSub : Iic x⊆(orderCDF μ) ⁻¹' Iic s := by
              intro z hz
              change orderCDF μ z≤s
              rw [←hx]
              exact orderCDF_monotone μ hz
            have hMass := measureReal_mono (μ:=μ) hSub (measure_ne_top _ _)
            change orderCDF μ x≤_ at hMass
            rwa [hx] at hMass
          · have hsZero : s=0 := by linarith only [hsNonneg,hsPos]
            rw [hsZero]
            exact measureReal_nonneg
        rw [le_antisymm hUpper hLower,min_eq_left hs1.le,max_eq_left hsNonneg]
      · have hsOne : 1≤s := le_of_not_gt hs1
        have hE : (orderCDF μ) ⁻¹' Iic s=Set.univ := by
          ext x
          simp only [Set.mem_preimage,Set.mem_Iic,Set.mem_univ,iff_true]
          exact (orderCDF_mem_unit μ x).2.trans hsOne
        rw [hE,probReal_univ,min_eq_right hsOne,max_eq_left (by norm_num : (0:ℝ)≤1)]
  apply Measure.eq_of_cdf
  ext s
  rw [cdf_eq_real,cdf_eq_real]
  exact hCDF s

end ProphetSecretary.Probability
