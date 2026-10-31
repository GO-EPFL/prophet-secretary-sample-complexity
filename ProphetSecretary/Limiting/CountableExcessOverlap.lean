import ProphetSecretary.Limiting.CountableCapExcessGaps

/-!
# Equality in the countable prophet excess bound eliminates overlap

The deterministic prefix deficits are integrated before taking the actual
maximum limit. Equality of total expected excess and expected maximum excess
forces every individual-pair minimum and every Poisson-band overlap to have
zero expectation. Actual Poisson count moments then eliminate the intensity
strictly above the cap.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal Topology
namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def individualCapOverlap (K : ℝ≥0) (i j : ℕ) (v : ValueWorld) : ℝ :=
  min (Model.tailValue K (v.2 i)) (Model.tailValue K (v.2 j))

lemma individualCapOverlap_nonnegative (K : ℝ≥0) (i j : ℕ) (v : ValueWorld) :
    0 ≤ individualCapOverlap K i j v := le_min (Model.tailValue_nonnegative K _) (Model.tailValue_nonnegative K _)

lemma integrable_individualCapOverlap (B : CountableInstance) (K : ℝ≥0) (i j : ℕ) :
    Integrable (individualCapOverlap K i j) B.valueLaw :=
  (B.integrable_individualCapExcess_valueWorld K i).inf (B.integrable_individualCapExcess_valueWorld K j)

lemma integrable_bandCapOverlap_valueWorld (B : CountableInstance) (K : ℝ≥0) (i : ℕ) :
    Integrable (fun v : ValueWorld => configurationCapOverlap K (v.1 i)) B.valueLaw :=
  (B.bandCapExcess_valueWorld_measurePreserving i).integrable_comp_of_integrable
    (integrable_configurationCapOverlap _ B.cap K (B.bandIntensity_supported i))

lemma integral_bandCapOverlap_valueWorld (B : CountableInstance) (K : ℝ≥0) (i : ℕ) :
    (∫ v : ValueWorld, configurationCapOverlap K (v.1 i) ∂B.valueLaw)=
      ∫ ω, configurationCapOverlap K ω ∂configurationLaw (B.bandIntensity i) :=
  (B.bandCapExcess_valueWorld_measurePreserving i).hasLaw.integral_comp
    (integrable_configurationCapOverlap _ B.cap K (B.bandIntensity_supported i)).aestronglyMeasurable

lemma individualCapOverlap_integral_zero_of_prophet_equality (B : CountableInstance) (K : ℝ≥0)
    (hK : (B.terminal : ℝ) < K)
    (hEq : B.totalCapExcess K=∫ v, Model.tailValue K (B.maximum v) ∂B.valueLaw)
    (i j : ℕ) (hij : i ≠ j) : (∫ v, individualCapOverlap K i j v ∂B.valueLaw)=0 := by
  have hUpper : (∫ v, Model.tailValue K (B.maximum v) ∂B.valueLaw)+
      (∫ v, individualCapOverlap K i j v ∂B.valueLaw) ≤ B.totalCapExcess K := by
    apply le_of_tendsto ((B.integral_maximumPrefix_capExcess_tendsto K).add tendsto_const_nhds)
    filter_upwards [eventually_ge_atTop (max i j+1)] with N hN
    have hiN : i < N := by omega
    have hjN : j < N := by omega
    let ii : Fin N := ⟨i,hiN⟩
    let jj : Fin N := ⟨j,hjN⟩
    have hne : ii ≠ jj := fun h => hij (congrArg Fin.val h)
    have hP := integral_mono ((B.integrable_maximumPrefix_capExcess K N).add (B.integrable_individualCapOverlap K i j))
      (B.integrable_capExcessPrefix K N) (fun v =>
        B.maximumPrefix_capExcess_add_individualOverlap_le K hK.le N v ii jj hne)
    change (∫ v, Model.tailValue K (B.maximumPrefix N v)+individualCapOverlap K i j v ∂B.valueLaw) ≤
      ∫ v, capExcessPrefix K N v ∂B.valueLaw at hP
    rw [integral_add (B.integrable_maximumPrefix_capExcess K N) (B.integrable_individualCapOverlap K i j)] at hP
    exact hP.trans (B.integral_capExcessPrefix_le_total K hK N)
  rw [hEq] at hUpper
  exact le_antisymm (by linarith only [hUpper]) (integral_nonneg (individualCapOverlap_nonnegative K i j))

lemma bandCapOverlap_integral_zero_of_prophet_equality (B : CountableInstance) (K : ℝ≥0)
    (hK : (B.terminal : ℝ) < K)
    (hEq : B.totalCapExcess K=∫ v, Model.tailValue K (B.maximum v) ∂B.valueLaw) (i : ℕ) :
    (∫ ω, configurationCapOverlap K ω ∂configurationLaw (B.bandIntensity i))=0 := by
  have hUpper : (∫ v, Model.tailValue K (B.maximum v) ∂B.valueLaw)+
      (∫ v : ValueWorld, configurationCapOverlap K (v.1 i) ∂B.valueLaw) ≤ B.totalCapExcess K := by
    apply le_of_tendsto ((B.integral_maximumPrefix_capExcess_tendsto K).add tendsto_const_nhds)
    filter_upwards [eventually_ge_atTop (i+1)] with N hN
    have hiN : i < N := by omega
    let ii : Fin N := ⟨i,hiN⟩
    have hP := integral_mono ((B.integrable_maximumPrefix_capExcess K N).add (B.integrable_bandCapOverlap_valueWorld K i))
      (B.integrable_capExcessPrefix K N) (fun v => B.maximumPrefix_capExcess_add_bandOverlap_le K hK.le N v ii)
    change (∫ v : ValueWorld, Model.tailValue K (B.maximumPrefix N v)+configurationCapOverlap K (v.1 i) ∂B.valueLaw) ≤
      ∫ v, capExcessPrefix K N v ∂B.valueLaw at hP
    rw [integral_add (B.integrable_maximumPrefix_capExcess K N) (B.integrable_bandCapOverlap_valueWorld K i)] at hP
    exact hP.trans (B.integral_capExcessPrefix_le_total K hK N)
  rw [hEq] at hUpper
  have hWorld : (∫ v : ValueWorld, configurationCapOverlap K (v.1 i) ∂B.valueLaw)=0 :=
    le_antisymm (by linarith only [hUpper]) (integral_nonneg (fun v => configurationCapOverlap_nonnegative K (v.1 i)))
  rw [B.integral_bandCapOverlap_valueWorld K i] at hWorld
  exact hWorld

theorem intensity_tail_zero_of_prophet_excess_equality (B : CountableInstance) (K : ℝ≥0)
    (hK : (B.terminal : ℝ) < K)
    (hEq : B.totalCapExcess K=∫ v, Model.tailValue K (B.maximum v) ∂B.valueLaw) :
    B.intensity (Ioi (K : ℝ))=0 := by
  have hBand (i : ℕ) : (B.bandIntensity i : Measure ℝ) (Ioi (K : ℝ))=0 :=
    poisson_tail_zero_of_integral_capOverlap_zero _ B.cap K (B.bandIntensity_supported i)
      (B.bandCapOverlap_integral_zero_of_prophet_equality K hK hEq i)
  rw [← B.sum_bandIntensity,Measure.sum_apply _ measurableSet_Ioi]
  simp only [hBand,tsum_zero]

end ProphetSecretary.Limiting.CountableInstance
