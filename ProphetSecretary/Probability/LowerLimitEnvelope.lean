import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Lower limits of bounded nonnegative envelopes

The lower limit is first taken in the complete nonnegative extended reals.
The supplied finite bound proves finiteness before conversion to a real.
Consequently eventual domination and weighted lower-limit inequalities retain
their meaning even if arbitrary null outcomes are not bounded.
-/

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace ProphetSecretary.Probability

noncomputable def lowerLimitEnvelope {Ω : Type*} (E : ℕ → Ω → ℝ) (ω : Ω) : ℝ :=
  (liminf (fun m => ENNReal.ofReal (E m ω)) atTop).toReal

lemma lowerLimitEnvelope_nonnegative {Ω : Type*} (E : ℕ → Ω → ℝ) (ω : Ω) : 0 ≤ lowerLimitEnvelope E ω :=
  ENNReal.toReal_nonneg

lemma measurable_lowerLimitEnvelope {Ω : Type*} [MeasurableSpace Ω] {E : ℕ → Ω → ℝ}
    (hE : ∀ m, Measurable (E m)) : Measurable (lowerLimitEnvelope E) :=
  (Measurable.liminf (fun m => ENNReal.continuous_ofReal.measurable.comp (hE m))).ennreal_toReal

lemma lowerLimitEnvelope_liminf_ne_top {e : ℕ → ℝ} {D : ℝ} (hBound : ∀ m, e m ≤ D) :
    liminf (fun m => ENNReal.ofReal (e m)) atTop ≠ ⊤ := by
  have hle : liminf (fun m => ENNReal.ofReal (e m)) atTop ≤ ENNReal.ofReal D :=
    liminf_le_of_frequently_le' (Frequently.of_forall fun m => ENNReal.ofReal_le_ofReal (hBound m))
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

lemma lowerLimitEnvelope_le {Ω : Type*} (E : ℕ → Ω → ℝ) (ω : Ω) {D : ℝ}
    (hD : 0 ≤ D) (hBound : ∀ m, E m ω ≤ D) : lowerLimitEnvelope E ω ≤ D := by
  have hle : liminf (fun m => ENNReal.ofReal (E m ω)) atTop ≤ ENNReal.ofReal D :=
    liminf_le_of_frequently_le' (Frequently.of_forall fun m => ENNReal.ofReal_le_ofReal (hBound m))
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  simpa only [lowerLimitEnvelope,ENNReal.toReal_ofReal hD] using h

lemma le_lowerLimitEnvelope_of_eventual {Ω : Type*} (E : ℕ → Ω → ℝ) (ω : Ω) {x D : ℝ}
    (hx : 0 ≤ x) (hBound : ∀ m, E m ω ≤ D) (hEvent : ∀ᶠ m in atTop, x ≤ E m ω) :
    x ≤ lowerLimitEnvelope E ω := by
  have hle : ENNReal.ofReal x ≤ liminf (fun m => ENNReal.ofReal (E m ω)) atTop :=
    le_liminf_of_le (h := hEvent.mono fun _ h => ENNReal.ofReal_le_ofReal h)
  have h := ENNReal.toReal_mono (lowerLimitEnvelope_liminf_ne_top hBound) hle
  simpa only [ENNReal.toReal_ofReal hx,lowerLimitEnvelope] using h

/-- Positive natural powers preserve this complete-lattice lower limit. -/
lemma ennreal_liminf_natPow (e : ℕ → ℝ≥0∞) {p : ℕ} (hp : 0<p) :
    liminf (fun m => e m ^ p) atTop = (liminf e atTop)^p := by
  have hpr : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hpow : liminf (fun m => e m ^ (p : ℝ)) atTop = (liminf e atTop)^(p : ℝ) := by
    change liminf (fun m => ENNReal.orderIsoRpow (p : ℝ) hpr (e m)) atTop =
      ENNReal.orderIsoRpow (p : ℝ) hpr (liminf e atTop)
    refine (OrderIso.liminf_apply (ENNReal.orderIsoRpow (p : ℝ) hpr) ?_ ?_ ?_ ?_).symm <;> isBoundedDefault
  simpa only [ENNReal.rpow_natCast] using hpow

/-- A convergent nonnegative multiplier may multiply the limiting envelope.
This is the pointwise inequality needed before the actual integral Fatou step. -/
lemma weighted_lowerLimitEnvelope_le {E : ℕ → ℝ} {W : ℕ → ℝ} {w D : ℝ}
    (hE0 : ∀ m, 0 ≤ E m) (hW0 : ∀ m, 0 ≤ W m) (hw0 : 0 ≤ w)
    (hBound : ∀ m, E m ≤ D) (hWlim : Tendsto W atTop (𝓝 w)) {p : ℕ} (hp : 0<p) :
    ENNReal.ofReal (w * lowerLimitEnvelope (fun m (_ : Unit) => E m) () ^ p) ≤
      liminf (fun m => ENNReal.ofReal (W m * E m ^ p)) atTop := by
  let η := liminf (fun m => ENNReal.ofReal (E m)) atTop
  have hη : η ≠ ⊤ := lowerLimitEnvelope_liminf_ne_top hBound
  have hWENN : Tendsto (fun m => ENNReal.ofReal (W m)) atTop (𝓝 (ENNReal.ofReal w)) :=
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hWlim
  have hmul := ENNReal.le_liminf_mul (u := fun m => ENNReal.ofReal (W m))
    (v := fun m => ENNReal.ofReal (E m)^p) (f := atTop)
  rw [hWENN.liminf_eq,ennreal_liminf_natPow _ hp] at hmul
  calc
    _ = ENNReal.ofReal w * η^p := by
      rw [ENNReal.ofReal_mul hw0,ENNReal.ofReal_pow (lowerLimitEnvelope_nonnegative _ _) p]
      change ENNReal.ofReal w * ENNReal.ofReal η.toReal ^ p = _
      rw [ENNReal.ofReal_toReal hη]
    _ ≤ liminf (fun m => ENNReal.ofReal (W m) * ENNReal.ofReal (E m)^p) atTop := hmul
    _ = _ := by
      apply congrArg (fun f : ℕ → ℝ≥0∞ => liminf f atTop)
      funext m
      rw [ENNReal.ofReal_mul (hW0 m),ENNReal.ofReal_pow (hE0 m) p]

end ProphetSecretary.Probability
