import ProphetSecretary.Probability.FiniteConditionalGrid

/-!
# Maxima on an arbitrary enumeration of observation times

Finite prefixes are sorted only for applying Doob's inequality. This yields the
same universal moments for any enumeration, so rational-time enumeration need
not be monotone and no observation is added to a sigma algebra.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Probability

lemma runningMaximum_le_of_initialBound {x : ℕ → ℝ} {D : ℝ} (N : ℕ)
    (hb : ∀ j ≤ N, x j ≤ D) : runningMaximum x N ≤ D := by
  induction N with
  | zero => exact hb 0 le_rfl
  | succ N ih => exact max_le (ih fun j hj => hb j (hj.trans (Nat.le_succ N))) (hb _ le_rfl)

lemma measurable_runningMaximum {Ω : Type*} [MeasurableSpace Ω] (X : ℕ → Ω → ℝ)
    (hm : ∀ j, Measurable (X j)) (N : ℕ) : Measurable (fun ω => runningMaximum (fun j => X j ω) N) := by
  induction N with
  | zero => exact hm 0
  | succ N ih => exact ih.max (hm (N+1))

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℝ mΩ) (f : Ω → ℝ) (τ : ℕ → ℝ)

lemma integrable_enumerated_condExpMaximum_pow {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ D) (p N : ℕ) :
    Integrable (fun ω => runningMaximum (fun j => |μ[f | ℱ (τ j)] ω|) N ^ p) μ := by
  have hm (j : ℕ) : Measurable (fun ω => |μ[f | ℱ (τ j)] ω|) := by
    have hc : StronglyMeasurable[ℱ (τ j)] (μ[f | ℱ (τ j)]) := stronglyMeasurable_condExp
    exact (continuous_abs.comp_stronglyMeasurable (hc.mono (ℱ.le (τ j)))).measurable
  apply Integrable.of_bound ((measurable_runningMaximum _ hm N).pow_const p).aestronglyMeasurable (D^p)
  have hall : ∀ᵐ ω ∂μ, ∀ j, |μ[f | ℱ (τ j)] ω| ≤ D :=
    ae_all_iff.mpr fun j => condExp_abs_bounded μ hD hbound
  filter_upwards [hall] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (runningMaximum_nonnegative (fun _ => abs_nonneg _) N) p)]
  exact pow_le_pow_left₀ (runningMaximum_nonnegative (fun _ => abs_nonneg _) N) (runningMaximum_le hω N) p

omit [IsProbabilityMeasure μ] in
lemma enumeratedMaximum_le_sortedGrid (N : ℕ) (ω : Ω) :
    let s := (Finset.range (N+1)).image τ
    let hs : s.Nonempty := ⟨τ 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩
    runningMaximum (fun j => |μ[f | ℱ (τ j)] ω|) N ≤
      runningMaximum (fun j => |μ[f | ℱ (finiteTimeGrid s hs j)] ω|) (s.card-1) := by
  let s := (Finset.range (N+1)).image τ
  have hs : s.Nonempty := ⟨τ 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩
  change runningMaximum (fun j => |μ[f | ℱ (τ j)] ω|) N ≤
    runningMaximum (fun j => |μ[f | ℱ (finiteTimeGrid s hs j)] ω|) (s.card-1)
  apply runningMaximum_le_of_initialBound
  intro j hj
  have hmem : τ j ∈ (Finset.range (N+1)).image τ :=
    Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
  obtain ⟨l, hl, heq⟩ := finiteTimeGrid_covers s hs hmem
  have he : |μ[f | ℱ (τ j)] ω| = |μ[f | ℱ (finiteTimeGrid s hs l)] ω| := by rw [heq]
  exact he.trans_le (le_runningMaximum (fun j => |μ[f | ℱ (finiteTimeGrid s hs j)] ω|) hl)

/-- Countable-time finite-prefix moments with the same Doob constants. -/
theorem enumeratedConditionalMaximum_moment {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ D) {p : ℕ} (hp : p=2 ∨ p=6)
    (hf : Integrable (fun ω => ‖f ω‖ ^ p) μ) (N : ℕ) :
    (∫ ω, runningMaximum (fun j => |μ[f | ℱ (τ j)] ω|) N ^ p ∂μ) ≤
      (if p=2 then 4 else 13) * ∫ ω, ‖f ω‖ ^ p ∂μ := by
  let s := (Finset.range (N+1)).image τ
  have hs : s.Nonempty := ⟨τ 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩
  have hI := integrable_enumerated_condExpMaximum_pow μ ℱ f τ hD hbound p N
  have hJ := integrable_enumerated_condExpMaximum_pow μ ℱ f (finiteTimeGrid s hs) hD hbound p (s.card-1)
  have hm := integral_mono hI hJ (fun ω => pow_le_pow_left₀
    (runningMaximum_nonnegative (fun _ => abs_nonneg _) N) (enumeratedMaximum_le_sortedGrid μ ℱ f τ N ω) p)
  apply hm.trans
  rcases hp with rfl | rfl
  · simpa using finiteConditionalGrid_secondMoment μ ℱ f hD hbound hf s hs
  · simpa using finiteConditionalGrid_sixthMoment μ ℱ f hD hbound hf s hs

end ProphetSecretary.Probability
