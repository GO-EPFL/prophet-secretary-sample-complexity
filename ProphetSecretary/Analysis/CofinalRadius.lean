import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# A uniform radius from joint cofinal sequence convergence

The discrete retained index and the cutoff above a reserve are independent
parameters. Testing every joint cofinal sequence yields a single rectangular
neighborhood, without assuming monotonicity of either approximating function.
-/

open Filter
open scoped Topology Classical

namespace ProphetSecretary.Analysis

lemma exists_uniform_cofinal_radius (f : ℕ → ℝ → ℝ) (a r : ℝ)
    (h : ∀ (Ns : ℕ → ℕ) (bs : ℕ → ℝ), (∀ m, a < bs m) →
      Tendsto Ns atTop atTop → Tendsto bs atTop (𝓝 a) →
      Tendsto (fun m => f (Ns m) (bs m)) atTop (𝓝 r)) :
    ∀ ε > (0 : ℝ), ∃ N0 : ℕ, ∃ δ > (0 : ℝ), ∀ N b,
      N0 ≤ N → a < b → b < a+δ → |f N b-r| < ε := by
  intro ε hε
  by_contra hbad
  push Not at hbad
  have hchoices (m : ℕ) := hbad m (1/((m : ℝ)+1)) (by positivity)
  choose Ns bs hN hba hbr hFail using hchoices
  have hNs : Tendsto Ns atTop atTop := tendsto_atTop_mono hN tendsto_id
  have hsub : Tendsto (fun m => bs m-a) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun m => (sub_pos.mpr (hba m)).le)
      (fun m => by linarith only [hbr m]) tendsto_one_div_add_atTop_nhds_zero_nat
  have hbs : Tendsto bs atTop (𝓝 a) := by
    have hs := hsub.const_add a
    simp only [add_zero] at hs
    convert hs using 1
    funext m
    ring
  have hf := Metric.tendsto_nhds.mp (h Ns bs hba hNs hbs) ε hε
  obtain ⟨m,hm⟩ := hf.exists
  have hm' : |f (Ns m) (bs m)-r| < ε := by simpa only [Real.dist_eq] using hm
  exact (not_lt_of_ge (hFail m)) hm'

end ProphetSecretary.Analysis
