import ProphetSecretary.Limiting.CountablePoissonPayloadTruncation
import ProphetSecretary.Limiting.HybridPoissonPayloadEnvelope
import ProphetSecretary.Limiting.CountableTruncationTail
import ProphetSecretary.Limiting.CountableValueLimit
import ProphetSecretary.Analysis.UniformAffineEnvelopeLimit

/-!
# Passing Poisson payload envelopes to the actual countable policy value

Exact truncation commutation and the proved all-policy value limits transfer
the uniform finite envelope. The fixed canonical coefficient is passed
separately; its convergence is an explicit hypothesis of this transfer lemma.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
variable {T : Type} [MeasurableSpace T] [StandardBorelSpace T]

lemma hasDerivAt_poissonPayloadValuePath_of_coefficient_limit (B : CountableInstance)
    (hZero : B.terminal=0) {w c D b : ℝ} (hw : 0<w) (hc : 0<c) (hD : 0≤D) (hb : 0<b)
    (κ : Measure T) [IsProbabilityMeasure κ] (t0 : T) (A : ℝ × T → ℝ) (hA : Measurable A)
    (hBound : ∀ z, |A z|≤D) (hVanish : ∀ z, z.1<b → A z=0)
    (Ns : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ m, 0<bs m) (hbsSmall : ∀ m, bs m<b/2)
    (hNs : Tendsto Ns atTop atTop) (hbsLim : Tendsto bs atTop (𝓝 (0 : ℝ)))
    (a : ℝ) (hCoefficient : Tendsto (fun m =>
      canonicalChronologicalAmplitudeMean (B.truncation (Ns m) (bs m)
        (by simpa only [hZero,NNReal.coe_zero] using hbs m)) κ A w c) atTop (𝓝 a)) :
    HasDerivAt (fun θ => (B.poissonPayloadValuePath hZero κ A hA D b hD hb hBound hVanish θ).optimalScalarValue w c)
      (w*a) 0 := by
  let hCut : ∀ m, (B.terminal : ℝ)<bs m := fun m => by simpa only [hZero,NNReal.coe_zero] using hbs m
  let P := fun m => B.truncation (Ns m) (bs m) (hCut m)
  let L := fun d : ℝ => if hd : 0<d then B.positiveTailCount d (by simpa only [hZero,NNReal.coe_zero] using hd) else 0
  have hL : ∀ d, 0<d → 0≤L d := by
    intro d hd
    dsimp only [L]
    rw [dif_pos hd]
    exact B.positiveTailCount_nonnegative d _
  have hTail : ∀ m d, 0<d → (P m).tailCount d≤L d := by
    intro m d hd
    dsimp only [L]
    rw [dif_pos hd]
    exact B.truncation_tailCount_le (Ns m) (hCut m) d _
  obtain ⟨ψ,_hψ,hMono,_hψZero,hLim,hFinite⟩ :=
    finite_hybrid_poisson_payload_envelope (T := T) Ns P B.cap.property hw hc hD hb
      (fun _ => hZero) (fun _ => le_rfl) L hL hTail
  let F := fun θ => (B.poissonPayloadValuePath hZero κ A hA D b hD hb hBound hVanish θ).optimalScalarValue w c
  let f := fun m θ => ((P m).poissonPayloadValuePath κ A hA D b hD hb hBound hVanish θ).optimalScalarValue w c
  have hf (θ : ℝ) : Tendsto (fun m => f m θ) atTop (𝓝 (F θ)) := by
    have h := (B.poissonPayloadValuePath hZero κ A hA D b hD hb hBound hVanish θ).truncation_value_tendsto
      Ns bs hbs hNs hbsLim hw.le hc.le
    have hEq (m : ℕ) := B.poissonPayloadValuePath_truncation hZero κ A hA hD hb hBound hVanish θ
      (Ns m) (bs m) (hbs m) (hbsSmall m)
    simpa only [hEq] using h
  have hError (θ : ℝ) (hθ : |θ|≤ individualValueRadius D b) :
      |F θ-F 0-θ*(w*a)|≤w*ψ (2*(w*D)*|θ|)*|θ| := by
    apply ProphetSecretary.Analysis.affine_envelope_limit (hf θ) (hf 0) (hCoefficient.const_mul w)
    intro m
    have h := hFinite κ t0 A hA hBound hVanish m θ hθ
    simpa only [f,(P m).poissonPayloadValuePath_value_zero κ A hA hD hb hBound hVanish w c] using h
  exact ProphetSecretary.Analysis.hasDerivAt_of_monotone_envelope (individualValueRadius_pos hD hb)
    (mul_nonneg (by norm_num) (mul_nonneg hw.le hD)) hw.le hMono hLim hError

end ProphetSecretary.Limiting.CountableInstance
