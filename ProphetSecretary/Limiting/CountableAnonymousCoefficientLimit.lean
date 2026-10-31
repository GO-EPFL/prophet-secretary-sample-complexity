import ProphetSecretary.Limiting.TruncatedAnonymousSelectedTag

/-!
# Finite hybrid anonymous coefficients converge to the full coefficient

The exact observer-law identity identifies each finite coefficient with the
same full-world selected tag. Actual canonical outcome and selected-tag
convergence then pass its expectation along every cofinal truncation path.
This is the anonymous selected-mark coefficient in paper `lem:envelopes`.
-/

open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting.CountableInstance

lemma truncatedValueRule_anonymousCoefficient_eq (B : CountableInstance) (hZero : B.terminal=0)
    (N : ℕ) {d w c : ℝ} (hd : (B.terminal : ℝ)<d) (hw : 0≤w) (hc : 0≤c)
    (φ : ℝ → ℝ) (hφ : Measurable φ) (hφ0 : φ 0=0) :
    (∫ v, (((B.truncation N d hd).valueRule w c).asFinitePolicy v.1.1).selectedTag ()
      (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2)
      (Fin.addCases (fun _ : Fin N => 0) (fun j : Fin v.1.1 => φ ((v.1.2 j).2)))
      ∂(B.truncation N d hd).law (Measure.dirac ())) =
    ∫ v, (B.truncatedValueRule N d hd w c).selectedTag (anonymousPerturbationTag φ) v
      ∂B.completeWorldLaw (Measure.dirac ()) := by
  have hSeed (v : HybridWorld N Unit) : v.2.2.2=() := Subsingleton.elim _ _
  have h := ((B.truncation N d hd).valueRule w c).integral_anonymousSelectedTag_eq_extended
    ((B.truncation N d hd).valueRule_isMeasurable hw hc) B hZero (Measure.dirac ()) hd φ hφ hφ0
  simp only [hSeed] at h
  unfold truncatedValueRule
  convert h using 1

/-- The finite hybrid coefficient uses the actual count-hidden canonical rule;
the limiting coefficient uses the full countable canonical rule. -/
theorem finiteHybrid_anonymousCoefficient_tendsto (B : CountableInstance)
    (hZero : B.terminal=0) {w c D b : ℝ} (hw : 0<w) (hc : 0<c) (hD : 0≤D) (hb : 0<b)
    (Ns : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ m, (B.terminal : ℝ)<bs m)
    (hNs : Tendsto Ns atTop atTop) (hbsLim : Tendsto bs atTop (𝓝 (B.terminal : ℝ)))
    (φ : ℝ → ℝ) (hφ : Measurable φ) (hBound : ∀ x, |φ x|≤D)
    (hVanish : ∀ x, x<b → φ x=0) :
    Tendsto (fun m => ∫ v,
      (((B.truncation (Ns m) (bs m) (hbs m)).valueRule w c).asFinitePolicy v.1.1).selectedTag ()
        (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2)
        (Fin.addCases (fun _ : Fin (Ns m) => 0) (fun j : Fin v.1.1 => φ ((v.1.2 j).2)))
      ∂(B.truncation (Ns m) (bs m) (hbs m)).law (Measure.dirac ())) atTop
      (𝓝 (∫ v, (B.valueRule w c).selectedTag (anonymousPerturbationTag φ) v
        ∂B.completeWorldLaw (Measure.dirac ()))) := by
  have hEq (m : ℕ) := B.truncatedValueRule_anonymousCoefficient_eq hZero (Ns m) (hbs m)
    hw.le hc.le φ hφ (hVanish 0 hb)
  simp_rw [hEq]
  exact B.truncatedValueRule_anonymousPerturbationMean_tendsto hZero hw hc hD hb
    Ns bs hbs hNs hbsLim φ hφ hBound hVanish

end ProphetSecretary.Limiting.CountableInstance
