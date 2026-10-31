import ProphetSecretary.Limiting.ExcessIntensity
import ProphetSecretary.Limiting.FiniteMeasureSubsequence

/-!
# Fixed-multiplicity rare-offer laws without normalization discontinuities

A finite intensity μ and q≥μ(total) determine the finite offer law
(1−μ(total)/q)δ₀+μ/q. This is an ordinary nonnegative offer distribution,
not a Poisson intensity with added zero marks. Its weak continuity includes
zero limiting intensity, without asserting convergence of normalized marks.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting

noncomputable def diracZeroFiniteMeasure : FiniteMeasure ℝ := ⟨Measure.dirac 0,inferInstance⟩
noncomputable def rareFiniteLaw (μ : FiniteMeasure ℝ) (q : ℝ≥0) : FiniteMeasure ℝ :=
  (1-q⁻¹*μ.mass) • diracZeroFiniteMeasure + q⁻¹ • μ

lemma diracZeroFiniteMeasure_univ : diracZeroFiniteMeasure univ = 1 := by
  change (Measure.dirac (0 : ℝ) univ).toNNReal = 1
  simp

lemma rareFiniteLaw_mass (μ : FiniteMeasure ℝ) {q : ℝ≥0} (hq : 0 < q) (hm : μ.mass ≤ q) :
    (rareFiniteLaw μ q).mass = 1 := by
  have hfrac : q⁻¹*μ.mass ≤ 1 := by
    simpa only [div_eq_mul_inv,mul_comm] using (div_le_one hq).mpr hm
  change ((1-q⁻¹*μ.mass) • diracZeroFiniteMeasure + q⁻¹ • μ) univ = 1
  simp only [FiniteMeasure.coeFn_add,Pi.add_apply,FiniteMeasure.smul_apply,smul_eq_mul,diracZeroFiniteMeasure_univ,mul_one]
  exact tsub_add_cancel_of_le hfrac

noncomputable def rareProbabilityLaw (μ : FiniteMeasure ℝ) (q : ℝ≥0) (hq : 0 < q) (hm : μ.mass ≤ q) :
    ProbabilityMeasure ℝ := by
  refine ⟨(rareFiniteLaw μ q : Measure ℝ),⟨?_⟩⟩
  rw [← FiniteMeasure.ennreal_mass,rareFiniteLaw_mass μ hq hm]
  rfl

lemma rareProbabilityLaw_toFiniteMeasure (μ : FiniteMeasure ℝ) (q : ℝ≥0) (hq : 0 < q) (hm : μ.mass ≤ q) :
    (rareProbabilityLaw μ q hq hm).toFiniteMeasure = rareFiniteLaw μ q := by
  apply FiniteMeasure.toMeasure_injective
  rfl

/-- Weak continuity of the unnormalized finite mixture, even at μ=0. -/
theorem rareFiniteLaw_tendsto {Γ : Type*} {l : Filter Γ} {μs : Γ → FiniteMeasure ℝ}
    {μ : FiniteMeasure ℝ} (hμ : Tendsto μs l (𝓝 μ)) (q : ℝ≥0) :
    Tendsto (fun m => rareFiniteLaw (μs m) q) l (𝓝 (rareFiniteLaw μ q)) := by
  have hc : Tendsto (fun m => (1-q⁻¹*(μs m).mass : ℝ≥0)) l (𝓝 (1-q⁻¹*μ.mass)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hμ.mass)
  exact (hc.smul tendsto_const_nhds).add (tendsto_const_nhds.smul hμ)

/-- The actual probability-law version, with one fixed multiplicity bound
before every member of the converging sequence. -/
theorem rareProbabilityLaw_tendsto {Γ : Type*} {l : Filter Γ} {μs : Γ → FiniteMeasure ℝ}
    {μ : FiniteMeasure ℝ} (hμ : Tendsto μs l (𝓝 μ)) (q : ℝ≥0) (hq : 0 < q)
    (hs : ∀ m, (μs m).mass ≤ q) (hm : μ.mass ≤ q) :
    Tendsto (fun m => rareProbabilityLaw (μs m) q hq (hs m)) l (𝓝 (rareProbabilityLaw μ q hq hm)) := by
  apply (ProbabilityMeasure.tendsto_nhds_iff_toFiniteMeasure_tendsto_nhds l).mpr
  change Tendsto (fun m => (rareProbabilityLaw (μs m) q hq (hs m)).toFiniteMeasure) l
    (𝓝 ((rareProbabilityLaw μ q hq hm).toFiniteMeasure))
  simp_rw [rareProbabilityLaw_toFiniteMeasure]
  exact rareFiniteLaw_tendsto hμ q

end ProphetSecretary.Limiting
