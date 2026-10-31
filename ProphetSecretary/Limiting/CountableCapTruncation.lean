import ProphetSecretary.Limiting.CountableCapping
import ProphetSecretary.Limiting.HybridCapping
import ProphetSecretary.Limiting.CountableValueLimit
import ProphetSecretary.Limiting.ExcessPoissonization

/-!
# Capping commutes with positive-band truncation below the cap

Retained identities, including zero observations, are unchanged. On anonymous
marks, min(x,K)>b is equivalent to x>b when b<K. This exact data identity gives
full-policy value convergence for capped countable truncations.
-/

open MeasureTheory Set Filter
open scoped NNReal Topology Classical
namespace ProphetSecretary.Limiting

namespace CountableInstance

lemma capAt_intensityAbove (B : CountableInstance) (hZero : B.terminal=0) (K : ℝ≥0) (hK : 0<K)
    {b : ℝ} (hb : (B.terminal:ℝ)<b) (hbK : b<(K:ℝ)) :
    (B.capAt hZero K hK).intensityAbove b (by simpa only [hZero,capAt_terminal,NNReal.coe_zero] using hb)=
      (B.intensityAbove b hb).map (Model.capValue K) := by
  apply FiniteMeasure.toMeasure_injective
  change (B.intensity.map (Model.capValue K)).restrict (Ioi b)=
    (B.intensity.restrict (Ioi b)).map (Model.capValue K)
  have hPre : Model.capValue K ⁻¹' Ioi b=Ioi b := by
    ext x
    change b<min x (K:ℝ) ↔ b<x
    simp only [lt_min_iff,hbK,and_true]
  rw [Measure.restrict_map (Model.measurable_capValue K) measurableSet_Ioi,hPre]

lemma capAt_truncation (B : CountableInstance) (hZero : B.terminal=0) (K : ℝ≥0) (hK : 0<K)
    (N : ℕ) {b : ℝ} (hb : (B.terminal:ℝ)<b) (hbK : b<(K:ℝ)) :
    (B.capAt hZero K hK).truncation N b (by simpa only [hZero,capAt_terminal,NNReal.coe_zero] using hb)=
      (B.truncation N b hb).capAt K hK := by
  apply FiniteIntensityHybridInstance.ext_data
  · rfl
  · exact hZero.symm
  · apply Model.Instance.eq_of_law_eq
    funext i
    rfl
  · exact B.capAt_intensityAbove hZero K hK hb hbK

lemma capped_truncation_value_tendsto (B : CountableInstance) (hZero : B.terminal=0) (K : ℝ≥0) (hK : 0<K)
    (Ns : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ m, (B.terminal:ℝ)<bs m)
    (hN : Tendsto Ns atTop atTop) (hb : Tendsto bs atTop (𝓝 (B.terminal:ℝ)))
    {w c : ℝ} (hw : 0≤w) (hc : 0≤c) :
    Tendsto (fun m => ((B.truncation (Ns m) (bs m) (hbs m)).capAt K hK).optimalScalarValue w c) atTop
      (𝓝 ((B.capAt hZero K hK).optimalScalarValue w c)) := by
  have hbs' (m : ℕ) : ((B.capAt hZero K hK).terminal:ℝ)<bs m := by
    simpa only [hZero,capAt_terminal,NNReal.coe_zero] using hbs m
  have hb' : Tendsto bs atTop (𝓝 (((B.capAt hZero K hK).terminal:ℝ))) := by
    simpa only [hZero,capAt_terminal,NNReal.coe_zero] using hb
  have hCore := (B.capAt hZero K hK).truncation_value_tendsto Ns bs hbs' hN hb' hw hc
  apply hCore.congr'
  have hKOld : (B.terminal:ℝ)<(K:ℝ) := by
    rw [hZero,NNReal.coe_zero]
    exact_mod_cast hK
  have hBelow : ∀ᶠ m in atTop, bs m<(K:ℝ) := hb.eventually (Iio_mem_nhds hKOld)
  filter_upwards [hBelow] with m hm
  exact congrArg (fun D : FiniteIntensityHybridInstance (Ns m) => D.optimalScalarValue w c)
    (B.capAt_truncation hZero K hK (Ns m) (hbs m) hm)

end CountableInstance
end ProphetSecretary.Limiting
