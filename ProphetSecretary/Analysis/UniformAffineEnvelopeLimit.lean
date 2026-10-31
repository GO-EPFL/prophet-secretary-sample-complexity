import ProphetSecretary.Analysis.StableEnvelope
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Passing a uniform affine envelope through pointwise limits

Values and fixed-base coefficients converge separately. A common remainder
modulus then controls the limiting derivative, without convergence of the
optimizing policies.
-/
open Filter Set
open scoped Topology
namespace ProphetSecretary.Analysis

lemma affine_envelope_limit {f : ℕ → ℝ → ℝ} {F : ℝ → ℝ} {d : ℕ → ℝ} {D R θ : ℝ}
    (hfθ : Tendsto (fun n => f n θ) atTop (𝓝 (F θ)))
    (hf0 : Tendsto (fun n => f n 0) atTop (𝓝 (F 0)))
    (hd : Tendsto d atTop (𝓝 D))
    (hBound : ∀ n, |f n θ-f n 0-θ*d n|≤R) :
    |F θ-F 0-θ*D|≤R := by
  exact le_of_tendsto' (((hfθ.sub hf0).sub (hd.const_mul θ)).abs) hBound

theorem hasDerivAt_of_monotone_envelope {F : ℝ → ℝ} {D ρ K w : ℝ} {ψ : ℝ → ℝ}
    (hρ : 0<ρ) (hK : 0≤K) (hw : 0≤w) (hMono : Monotone ψ)
    (hLim : Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hBound : ∀ θ, |θ|≤ρ → |F θ-F 0-θ*D|≤w*ψ (K*|θ|)*|θ|) :
    HasDerivAt F D 0 := by
  apply hasDerivAt_iff_isLittleO.mpr
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  have hLimW : Tendsto (fun r => w*ψ r) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using hLim.const_mul w
  obtain ⟨η,hηSmall,hη⟩ := ((hLimW.eventually (gt_mem_nhds hε)).and self_mem_nhdsWithin).exists
  let δ := min ρ (η/(K+1))
  have hδ : 0<δ := lt_min hρ (div_pos hη (by positivity))
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hδ) hδ] with θ hθ
  have hAbs : |θ|≤δ := (abs_lt.mpr hθ).le
  have hRad : |θ|≤ρ := hAbs.trans (min_le_left _ _)
  have hArg : K*|θ|≤η := by
    have hx := (le_div_iff₀ (by positivity : 0<K+1)).mp (hAbs.trans (min_le_right _ _))
    nlinarith [abs_nonneg θ]
  have hScale : w*ψ (K*|θ|)≤ε :=
    (mul_le_mul_of_nonneg_left (hMono hArg) hw).trans hηSmall.le
  rw [Real.norm_eq_abs,Real.norm_eq_abs,sub_zero,smul_eq_mul]
  exact (hBound θ hRad).trans (mul_le_mul_of_nonneg_right hScale (abs_nonneg θ))

end ProphetSecretary.Analysis
