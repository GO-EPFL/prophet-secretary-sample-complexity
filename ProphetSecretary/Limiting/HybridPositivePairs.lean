import ProphetSecretary.Limiting.HybridPositivePairBranch
import ProphetSecretary.Limiting.HybridPairCountMoment
import ProphetSecretary.Limiting.ZeroIntensity
import ProphetSecretary.Limiting.HybridRewardTail

/-!
# Unconditional positive close-pair probability in hybrid instances

The count-conditioned finite bound is averaged using the actual Poisson count
second moment. The resulting bound involves only the positive-level tail
count, including retained and anonymous offers. All clocks are counted even
after a policy stops. This is the pair estimate in `cor:selected-occurrence`.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma mass_mul_normalize_measureReal (μ : FiniteMeasure ℝ) (S : Set ℝ) :
    (μ.mass : ℝ)*(μ.normalize : Measure ℝ).real S=(μ : Measure ℝ).real S := by
  have hm : (μ : Measure ℝ)=(μ.mass : ℝ≥0∞) • (μ.normalize : Measure ℝ) :=
    congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ)) μ.self_eq_mass_smul_normalize
  rw [hm,measureReal_ennreal_smul_apply,ENNReal.coe_toReal]

lemma FiniteIntensityHybridInstance.closePositivePair_probability_zero_intensity
    (B : FiniteIntensityHybridInstance n) (hμ : B.intensity=0)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (b : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    (B.law ν).real (hybridClosePositivePair b η) ≤
      2*η*((B.tailCount b)^2+B.tailCount b) := by
  have hE := measurableSet_hybridClosePositivePair (n := n) (Seed := Seed) b η
  have hMP : MeasurePreserving (fun z : Model.World n Seed => (emptyConfiguration,z))
      (B.individuals.worldLaw ν) (B.law ν) := by
    simpa only [FiniteIntensityHybridInstance.law,hμ] using zeroIntensityWorld_measurePreserving B.individuals ν
  have hPre : (fun z : Model.World n Seed => (emptyConfiguration,z)) ⁻¹' hybridClosePositivePair b η =
      {z | Model.closePositivePair b η z.1 z.2.1} := by
    ext z
    have hx : combinedValues z.1 (fun j : Fin 0 => (Fin.elim0 j : Point))=z.1 := by
      funext i
      induction i using Fin.addCases with
      | left i => simp only [combinedValues,Fin.addCases_left]; congr 1
      | right j => exact Fin.elim0 j
    have hu : combinedClocks z.2.1 (fun j : Fin 0 => (Fin.elim0 j : Point))=z.2.1 := by
      funext i
      induction i using Fin.addCases with
      | left i => simp only [combinedClocks,Fin.addCases_left]; congr 1
      | right j => exact Fin.elim0 j
    change Model.closePositivePair b η
      (combinedValues z.1 (fun j : Fin 0 => (Fin.elim0 j : Point)))
      (combinedClocks z.2.1 (fun j : Fin 0 => (Fin.elim0 j : Point))) ↔ _
    rw [hx,hu]
    rfl
  have hEq := congrArg ENNReal.toReal (hMP.measure_preimage hE.nullMeasurableSet)
  rw [hPre] at hEq
  have hTail : B.tailCount b=B.individuals.tailCount b := by simp [FiniteIntensityHybridInstance.tailCount,hμ]
  calc
    _ = (B.individuals.worldLaw ν).real {z | Model.closePositivePair b η z.1 z.2.1} := hEq.symm
    _ ≤ 2*η*(B.individuals.tailCount b)^2 := B.individuals.closePositivePair_probability ν b hη
    _ ≤ _ := by
      rw [hTail]
      have hS := B.individuals.tailCount_nonnegative b
      nlinarith only [mul_nonneg hη hS]

theorem FiniteIntensityHybridInstance.closePositivePair_probability
    (B : FiniteIntensityHybridInstance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (b : ℝ) {η : ℝ} (hη : 0 ≤ η) :
    (B.law ν).real (hybridClosePositivePair b η) ≤
      2*η*((B.tailCount b)^2+B.tailCount b) := by
  by_cases hμ : B.intensity=0
  · exact B.closePositivePair_probability_zero_intensity hμ ν b hη
  let s := B.individuals.tailCount b
  let p := (B.intensity.normalize : Measure ℝ).real (Ioi b)
  let rate := (B.intensity.mass : ℝ)
  let E : Set (HybridWorld n Seed) := hybridClosePositivePair b η
  let I : HybridWorld n Seed → ℝ := E.indicator (fun _ => 1)
  let G : HybridWorld n Seed → ℝ := fun v => 2*η*(s+(v.1.1 : ℝ)*p)^2
  have hE : MeasurableSet E := measurableSet_hybridClosePositivePair b η
  have hI : Integrable I (B.law ν) := (integrable_const (1 : ℝ)).indicator hE
  have hIm : Measurable I := measurable_const.indicator hE
  have hIeq : (∫ v, I v ∂B.law ν)=(B.law ν).real E := integral_indicator_one hE
  have hN : Measurable (fun v : HybridWorld n Seed => (v.1.1 : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (measurable_configuration_count.comp measurable_fst)
  have hGm : Measurable G := ((measurable_const.add (hN.mul_const p)).pow_const 2).const_mul (2*η)
  have hG : Integrable G (B.law ν) :=
    (world_affineCountSquare_integrable B.intensity (B.individuals.worldLaw ν) s p).const_mul (2*η)
  have hSI := hasSum_worldLaw_fibers B.intensity (B.individuals.worldLaw ν) I hIm hI
  have hSG := hasSum_worldLaw_fibers B.intensity (B.individuals.worldLaw ν) G hGm hG
  have hTerm (N : ℕ) :
      poissonWeight B.intensity.mass N*(∫ z, I (configurationMk N z.1,z.2)
        ∂(arrayLaw B.intensity N).prod (B.individuals.worldLaw ν)) ≤
      poissonWeight B.intensity.mass N*(∫ z, G (configurationMk N z.1,z.2)
        ∂(arrayLaw B.intensity N).prod (B.individuals.worldLaw ν)) := by
    let EN : Set ((Fin N → Point) × Model.World n Seed) :=
      (fun z => (configurationMk N z.1,z.2)) ⁻¹' E
    have hEN : MeasurableSet EN := hE.preimage ((measurable_configuration_mk N).prodMap measurable_id)
    have hIN : (∫ z, I (configurationMk N z.1,z.2)
        ∂(arrayLaw B.intensity N).prod (B.individuals.worldLaw ν)) =
        ((arrayLaw B.intensity N).prod (B.individuals.worldLaw ν)).real EN :=
      integral_indicator_one hEN
    have hGN : (∫ z, G (configurationMk N z.1,z.2)
        ∂(arrayLaw B.intensity N).prod (B.individuals.worldLaw ν))=2*η*(s+(N : ℝ)*p)^2 := by
      change (∫ _z, (2*η*(s+(N : ℝ)*p)^2) ∂(arrayLaw B.intensity N).prod (B.individuals.worldLaw ν)) = _
      simp only [integral_const,probReal_univ,one_smul]
    rw [hIN,hGN]
    apply mul_le_mul_of_nonneg_left (B.closePositivePair_branch_probability hμ ν N b hη)
    unfold poissonWeight
    positivity
  have hSum := Summable.tsum_le_tsum hTerm hSI.summable hSG.summable
  rw [hSI.tsum_eq,hSG.tsum_eq] at hSum
  change (∫ v, I v ∂B.law ν) ≤ ∫ v, G v ∂B.law ν at hSum
  rw [hIeq] at hSum
  have hMean : (∫ v, G v ∂B.law ν)=2*η*(s^2+2*s*p*rate+p^2*(rate^2+rate)) := by
    change (∫ v : World (Model.World n Seed), 2*η*(s+(v.1.1 : ℝ)*p)^2
      ∂worldLaw B.intensity (B.individuals.worldLaw ν)) = _
    rw [integral_const_mul,integral_world_affineCountSquare]
  have hp0 : 0 ≤ p := measureReal_nonneg
  have hp1 : p ≤ 1 := measureReal_le_one
  have hrate : 0 ≤ rate := B.intensity.mass.property
  have hs : 0 ≤ s := B.individuals.tailCount_nonnegative b
  have hpSq : p^2 ≤ p := by nlinarith only [mul_nonpos_of_nonneg_of_nonpos hp0 (sub_nonpos.mpr hp1)]
  have hExtra := mul_le_mul_of_nonneg_left hpSq hrate
  have hTail : B.tailCount b=s+rate*p := by
    unfold FiniteIntensityHybridInstance.tailCount
    rw [← mass_mul_normalize_measureReal B.intensity (Ioi b)]
  have hPol : s^2+2*s*p*rate+p^2*(rate^2+rate) ≤ (B.tailCount b)^2+B.tailCount b := by
    have hEq : s^2+2*s*p*rate+p^2*(rate^2+rate)=(s+rate*p)^2+rate*p^2 := by ring
    rw [hEq,hTail]
    exact add_le_add le_rfl (hExtra.trans (le_add_of_nonneg_left hs))
  calc
    _ ≤ ∫ v, G v ∂B.law ν := hSum
    _ = _ := hMean
    _ ≤ _ := mul_le_mul_of_nonneg_left hPol (mul_nonneg (by norm_num) hη)

end ProphetSecretary.Limiting
