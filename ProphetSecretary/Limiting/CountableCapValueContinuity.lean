import ProphetSecretary.Limiting.CountableCapTruncation
import ProphetSecretary.Limiting.HybridCapHeightValue

/-!
# Cap-height continuity for full countable optimized values

The finite-hybrid displacement bound is uniform in the retained dimension and
omitted-band cutoff. Actual truncation value limits therefore preserve it.
The same bound permits moving positive caps and duration coefficients before
the countable truncation limit, without any uniform first-moment assumption.
-/

open MeasureTheory Set Filter
open scoped NNReal Topology Classical
namespace ProphetSecretary.Limiting.CountableInstance

lemma capAt_value_abs_sub_le (B : CountableInstance) (hZero : B.terminal=0)
    (K H : ℝ≥0) (hK : 0<K) (hH : 0<H) {w c : ℝ} (hw : 0<w) (hc : 0≤c) :
    |(B.capAt hZero K hK).optimalScalarValue w c-(B.capAt hZero H hH).optimalScalarValue w c|≤w*|(K:ℝ)-(H:ℝ)| := by
  have hKL := B.capped_truncation_value_tendsto hZero K hK id B.markCutoff B.terminal_lt_markCutoff
    tendsto_id B.markCutoff_tendsto hw.le hc
  have hHL := B.capped_truncation_value_tendsto hZero H hH id B.markCutoff B.terminal_lt_markCutoff
    tendsto_id B.markCutoff_tendsto hw.le hc
  apply le_of_tendsto_of_tendsto (hKL.sub hHL).abs tendsto_const_nhds
  exact Eventually.of_forall fun m => (B.truncation m (B.markCutoff m) (B.terminal_lt_markCutoff m)).capAt_value_abs_sub_le
    hZero K H hK hH hw hc

lemma capped_truncation_value_tendsto_moving (B : CountableInstance) (hZero : B.terminal=0)
    (Ns : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ m, (B.terminal:ℝ)<bs m)
    (hN : Tendsto Ns atTop atTop) (hb : Tendsto bs atTop (𝓝 (B.terminal:ℝ)))
    {Ks : ℕ → ℝ≥0} {K : ℝ≥0} (hKs : ∀ m, 0<Ks m) (hK : 0<K)
    (hKLimit : Tendsto Ks atTop (𝓝 K)) {cs : ℕ → ℝ} {c w : ℝ}
    (hcs : ∀ m, 0≤cs m) (hc : 0≤c) (hw : 0<w) (hcLimit : Tendsto cs atTop (𝓝 c)) :
    Tendsto (fun m => ((B.truncation (Ns m) (bs m) (hbs m)).capAt (Ks m) (hKs m)).optimalScalarValue w (cs m)) atTop
      (𝓝 ((B.capAt hZero K hK).optimalScalarValue w c)) := by
  let T := fun m => B.truncation (Ns m) (bs m) (hbs m)
  have hBound (m : ℕ) :
      |((T m).capAt (Ks m) (hKs m)).optimalScalarValue w (cs m)-((T m).capAt K hK).optimalScalarValue w c|≤
        w*|(Ks m:ℝ)-(K:ℝ)|+|cs m-c| := by
    exact (abs_sub_le _ (((T m).capAt K hK).optimalScalarValue w (cs m)) _).trans
      (add_le_add ((T m).capAt_value_abs_sub_le hZero (Ks m) K (hKs m) hK hw (hcs m))
        (((T m).capAt K hK).optimalScalarValue_duration_abs_sub_le w (cs m) c))
  have hErr : Tendsto (fun m => w*|(Ks m:ℝ)-(K:ℝ)|+|cs m-c|) atTop (𝓝 (0:ℝ)) := by
    have hCaps := ((NNReal.tendsto_coe.2 hKLimit).sub_const (K:ℝ)).abs.const_mul w
    have hCoeffs := (hcLimit.sub_const c).abs
    simpa only [sub_self,abs_zero,mul_zero,add_zero] using hCaps.add hCoeffs
  have hDiff : Tendsto (fun m => ((T m).capAt (Ks m) (hKs m)).optimalScalarValue w (cs m)-
      ((T m).capAt K hK).optimalScalarValue w c) atTop (𝓝 (0:ℝ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hErr
    intro m
    simpa only [sub_zero,Real.norm_eq_abs] using hBound m
  have hFixed : Tendsto (fun m => ((T m).capAt K hK).optimalScalarValue w c) atTop
      (𝓝 ((B.capAt hZero K hK).optimalScalarValue w c)) :=
    B.capped_truncation_value_tendsto hZero K hK Ns bs hbs hN hb hw.le hc
  simpa only [sub_add_cancel,zero_add] using hDiff.add hFixed

end ProphetSecretary.Limiting.CountableInstance
