import ProphetSecretary.Limiting.HybridAnonymousBand
import ProphetSecretary.Limiting.CampbellUnionBound
import ProphetSecretary.Limiting.ConfigurationSetMeasurability

/-!
# Anonymous boundary probability with independent retained clocks

The actual anonymous configuration is independent of the retained world and
policy seed. Conditioning here is only an analytical product-integral step;
it does not disclose the anonymous count or future retained clocks online.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Aux : Type*} [MeasurableSpace Aux]

noncomputable def FiniteIntensityHybridInstance.anonymousBandEvent (B : FiniteIntensityHybridInstance n)
    (w c b e : ℝ) (clocks : Aux → Fin n → ℝ) : Set (World Aux) :=
  {v | ∃ j : Fin v.1.1, v.1.2 j ∈ B.anonymousPositiveBand w c b e (clocks v.2)}

lemma FiniteIntensityHybridInstance.measurableSet_anonymousBandEvent (B : FiniteIntensityHybridInstance n)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (b e : ℝ)
    {clocks : Aux → Fin n → ℝ} (hclocks : Measurable clocks) :
    MeasurableSet (B.anonymousBandEvent w c b e clocks) := by
  apply measurableSet_of_configuration_prod_branches
  intro N
  change MeasurableSet {v : (Fin N → Point) × Aux | ∃ j : Fin N,
    b ≤ (v.1 j).2 ∧ |B.candidateGap w c none (v.1 j).2 (clocks v.2) (v.1 j).1| ≤ e}
  rw [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro j
  have hp : Measurable (fun v : (Fin N → Point) × Aux => v.1 j) :=
    (measurable_pi_apply j).comp measurable_fst
  have hu := hclocks.comp (measurable_snd : Measurable (fun v : (Fin N → Point) × Aux => v.2))
  have hg := (B.measurable_candidateGap_joint hw hc none).comp (hp.snd.prodMk (hu.prodMk hp.fst))
  exact (measurableSet_le measurable_const hp.snd).inter
    (measurableSet_le (continuous_abs.measurable.comp hg) measurable_const)

theorem FiniteIntensityHybridInstance.anonymousBandEvent_probability
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    (ν : Measure Aux) [IsProbabilityMeasure ν] {clocks : Aux → Fin n → ℝ} (hclocks : Measurable clocks)
    {H w c b L e : ℝ} (hH : 0 ≤ H) (hCap : (B.cap : ℝ) ≤ H)
    (hw : 0 < w) (hc : 0 < c) (hb : 0 < b)
    (hL : B.tailCount (b/4) ≤ L) (he0 : 0 ≤ e) (he : e ≤ w*b/4) :
    ((configurationLaw B.intensity).prod ν).real (B.anonymousBandEvent w c b e clocks) ≤
      (2*e/(c*Model.positiveBandDuration H w c b L)) * (B.intensity : Measure ℝ).real (Ici b) := by
  let K := 2*e/(c*Model.positiveBandDuration H w c b L)
  have hK : 0 ≤ K := by
    have := Model.positiveBandDuration_pos hH hw hc hb ((B.tailCount_nonnegative _).trans hL)
    dsimp only [K]
    positivity
  have hE := B.measurableSet_anonymousBandEvent hw.le hc.le b e hclocks
  have hProb : ((configurationLaw B.intensity).prod ν) (B.anonymousBandEvent w c b e clocks) ≤
      ENNReal.ofReal K*(B.intensity : Measure ℝ) (Ici b) := by
    rw [Measure.prod_apply_symm hE]
    calc
      _ ≤ ∫⁻ _z, ENNReal.ofReal K*(B.intensity : Measure ℝ) (Ici b) ∂ν := by
        apply lintegral_mono
        intro z
        exact (probability_exists_configuration_point_le_intensity B.intensity
          (B.measurableSet_anonymousPositiveBand hw.le hc.le b e (clocks z))).trans
            (B.anonymousPositiveBand_intensity ha hH hCap hw hc hb hL he0 he (clocks z))
      _ = _ := by simp
  have hReal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hProb
  simpa only [measureReal_def,ENNReal.toReal_mul,ENNReal.toReal_ofReal hK] using hReal

end ProphetSecretary.Limiting
