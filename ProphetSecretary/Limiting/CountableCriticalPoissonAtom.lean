import ProphetSecretary.Limiting.CountableAtomBenchmarkGain
import ProphetSecretary.Limiting.NoReserve
import ProphetSecretary.Model.HalfGuarantee
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# A positive Poisson atom cannot be a critical maximum

The symmetric atom displacement has scalar change o(h), whereas the actual
prophet gain has a positive linear coefficient if the atom can be maximal.
The unconditional countable scalar inequality excludes that possibility.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

lemma intensity_atom_le_cap (B : CountableInstance) {x : ℝ} (hAtom : 0<B.intensity {x}) :
    x≤(B.cap : ℝ) := by
  by_contra hn
  have hx : (B.cap : ℝ)<x := not_le.mp hn
  have hTail : B.intensity (Ioi (B.cap : ℝ))=0 :=
    measure_eq_zero_iff_ae_notMem.mpr (B.intensity_supported.mono (fun _ hz => not_lt.mpr hz.2))
  have hSub : ({x} : Set ℝ)⊆Ioi (B.cap : ℝ) := by
    intro y hy
    rwa [mem_singleton_iff.mp hy]
  have hBound := (measure_mono hSub).trans_eq hTail
  exact (not_lt_of_ge hBound) hAtom

theorem critical_poisson_atom_cdf_zero (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c)
    (x : ℝ) (hx : 0<x) (hAtom : 0<B.intensity {x}) : B.maximumCdf x=0 := by
  have hZero := B.terminal_eq_zero_of_critical hw hc.le hCritical
  have hxCap := B.intensity_atom_le_cap hAtom
  let family := B.symmetricAtomPath hZero x hx
  let q := (B.scaleBand {x} 0).maximumCdf x
  let m := B.intensity.real {x}
  let p := q*(1-Real.exp (-m/2))^2
  have hLittleO := B.symmetricAtomPath_scalar_change_isLittleO hZero hw hc x hx
  have hLimit : Tendsto (fun h : ℝ => ((family h).optimalScalarValue w c-B.optimalScalarValue w c)/h)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    hLittleO.tendsto_div_nhds_zero.mono_left nhdsWithin_le_nhds
  have hRadius := individualValueRadius_pos (by norm_num : (0 : ℝ)≤1) (half_pos hx)
  have hC : 0<optimalCompetitiveRatio := lt_of_lt_of_le (by norm_num : (0 : ℝ)<1/2) half_le_optimalCompetitiveRatio
  have hCw : 0<optimalCompetitiveRatio*w := mul_pos hC hw
  have hBase : B.optimalScalarValue w c=optimalCompetitiveRatio*(w*B.expectedMaximum+c) :=
    sub_eq_zero.mp hCritical.2
  have hLower : ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ),
      optimalCompetitiveRatio*w*p≤((family h).optimalScalarValue w c-B.optimalScalarValue w c)/h := by
    filter_upwards [(self_mem_nhdsWithin : Ioi (0 : ℝ)∈𝓝[>] (0 : ℝ)),
      nhdsWithin_le_nhds (Iio_mem_nhds hRadius),nhdsWithin_le_nhds (Iio_mem_nhds hx),
      nhdsWithin_le_nhds (Iio_mem_nhds zero_lt_one)] with h hh hNear hX h1
    have hh0 : 0<h := hh
    have hNearAbs : |h|≤ individualValueRadius 1 (x/2) := by
      rw [abs_of_pos hh0]
      exact hNear.le
    have hGain := B.symmetricAtomPath_expectedMaximum_gain hZero hx hxCap hh0 hX h1.le hNearAbs
    have hRobust := (family h).globalScalar_inequality hw.le hc.le
    have hValue : optimalCompetitiveRatio*w*((family h).expectedMaximum-B.expectedMaximum)≤
        (family h).optimalScalarValue w c-B.optimalScalarValue w c := by
      nlinarith only [hRobust,hBase]
    have hMax : h*p≤(family h).expectedMaximum-B.expectedMaximum := by
      dsimp only [p,q,m]
      nlinarith only [hGain]
    have hScaled := (mul_le_mul_of_nonneg_left hMax hCw.le).trans hValue
    apply (le_div_iff₀ hh).mpr
    convert hScaled using 1
    ring
  have hBound : optimalCompetitiveRatio*w*p≤0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hLimit hLower
  have hm : 0<m := ENNReal.toReal_pos (ne_of_gt hAtom) (B.intensity_atom_finite hZero hx).ne
  have hE : 0<1-Real.exp (-m/2) := sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have hq0 : 0≤q := (B.scaleBand {x} 0).maximumCdf_mem_unit x |>.1
  have hq : q=0 := by
    by_contra hq
    have hp : 0<p := mul_pos (lt_of_le_of_ne hq0 (Ne.symm hq)) (sq_pos_of_pos hE)
    exact (not_lt_of_ge hBound) (mul_pos hCw hp)
  have hFactor := B.maximumCdf_atom_factor hZero x x hx
  calc
    B.maximumCdf x=q := by
      simpa only [lt_self_iff_false,if_false,mul_zero,neg_zero,Real.exp_zero,mul_one] using hFactor
    _ = 0 := hq

end ProphetSecretary.Limiting.CountableInstance
