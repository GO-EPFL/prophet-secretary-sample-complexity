import ProphetSecretary.Limiting.CountableBenchmarkLimit
import ProphetSecretary.Analysis.CofinalRadius

/-!
# A single uniform truncation neighborhood for the actual countable benchmark

This follows from the proved arbitrary joint cofinal sequence limit; neither
monotone cutoff sequences nor a policy-convergence hypothesis are required.
-/

open Filter
open scoped Topology

namespace ProphetSecretary.Limiting.CountableInstance

lemma truncation_expectedMaximum_uniform (B : CountableInstance) :
    ∀ ε > (0 : ℝ), ∃ N0 : ℕ, ∃ δ > (0 : ℝ), ∀ N b (hb : (B.terminal : ℝ) < b),
      N0 ≤ N → b < (B.terminal : ℝ)+δ →
        |(B.truncation N b hb).expectedMaximum-B.expectedMaximum| < ε := by
  let f : ℕ → ℝ → ℝ := fun N b =>
    if hb : (B.terminal : ℝ) < b then (B.truncation N b hb).expectedMaximum else B.expectedMaximum
  have hf : ∀ (Ns : ℕ → ℕ) (bs : ℕ → ℝ), (∀ m, (B.terminal : ℝ) < bs m) →
      Tendsto Ns atTop atTop → Tendsto bs atTop (𝓝 (B.terminal : ℝ)) →
      Tendsto (fun m => f (Ns m) (bs m)) atTop (𝓝 B.expectedMaximum) := by
    intro Ns bs hbs hN hb
    have h := B.truncation_expectedMaximum_tendsto Ns bs hbs hN hb
    have he : (fun m => f (Ns m) (bs m)) =
        (fun m => (B.truncation (Ns m) (bs m) (hbs m)).expectedMaximum) := by
      funext m
      exact dif_pos (hbs m)
    rwa [he]
  intro ε hε
  obtain ⟨N0,δ,hδ,hNear⟩ := ProphetSecretary.Analysis.exists_uniform_cofinal_radius f B.terminal B.expectedMaximum hf ε hε
  refine ⟨N0,δ,hδ,?_⟩
  intro N b hb hN hbd
  have h := hNear N b hN hb hbd
  simpa only [f,dif_pos hb] using h

end ProphetSecretary.Limiting.CountableInstance
