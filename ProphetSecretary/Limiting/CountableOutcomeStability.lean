import ProphetSecretary.Limiting.CountableOutcomeTriangle
import ProphetSecretary.Limiting.CountableTruncationTail
import ProphetSecretary.Limiting.HybridFixedWeightStability
import ProphetSecretary.Analysis.OutcomeTruncationLimit

/-!
# Full countable outcome stability

Causal omission, the same-input canonical comparison and absolute outcome
convergence transfer the finite-hybrid modulus to all admissible policies.
The modulus is uniform in retained dimension, cloud mass near zero, and the
competitor's independent auxiliary randomness.
-/

open MeasureTheory Set Filter
open scoped Topology Classical

namespace ProphetSecretary.Limiting
open CountableInstance

lemma RandomizedCountablePolicy.outcome_error_le_of_truncation_modulus {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (hZero : B.terminal=0)
    {δ w c : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c)
    (ω : ℝ → ℝ) (hMono : Monotone ω) (hωZero : ω 0=0)
    (hωLimit : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)))
    (hFinite : ∀ N (σ : RandomizedHybridPolicy N),
      let C := B.truncation N (B.markCutoff N) (B.terminal_lt_markCutoff N)
      σ.expectedValueOutcomeError C w c ≤ ω (C.optimalScalarValue w c-σ.scalarObjective C w c)) :
    π.expectedValueOutcomeError w c ≤
      2*(B.optimalScalarValue w c-π.scalarObjective w c)/δ+
        ω (2*(B.optimalScalarValue w c-π.scalarObjective w c)) := by
  have hw := hδ.trans_le hwδ
  have hc := hδ.trans_le hcδ
  let r := B.optimalScalarValue w c-π.scalarObjective w c
  let m := fun N => w*B.omissionError N (B.markCutoff N)
  let e := fun N => ∫ v, B.canonicalTruncationOutcomeError N w c v
    ∂B.completeWorldLaw (Measure.dirac ())
  have hr : 0 ≤ r := sub_nonneg.mpr (B.scalarObjective_le_value π w c)
  have hm : Tendsto m atTop (𝓝 (0 : ℝ)) := by
    have hCut : Tendsto (fun N => B.markCutoff N-(B.terminal : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      simpa only [sub_self] using B.markCutoff_tendsto.sub_const (B.terminal : ℝ)
    simpa only [m,CountableInstance.omissionError,zero_add,mul_zero] using
      (B.expectedIndividualTailExcessMaximum_tendsto.add hCut).const_mul w
  have he : Tendsto e atTop (𝓝 (0 : ℝ)) := B.canonicalTruncationOutcomeError_tendsto_zero hZero hw hc
  apply ProphetSecretary.Analysis.outcome_error_le_of_truncations (w := 1) hr hMono hωZero hωLimit hm he
  intro N
  let C := B.truncation N (B.markCutoff N) (B.terminal_lt_markCutoff N)
  let σ := π.simulateOmissions N (B.markCutoff N)
  have hTri := π.omission_outcome_triangle hZero N hδ hwδ hcδ (le_refl r)
  have hRegret := (π.omission_regret_mean_bounds N (B.terminal_lt_markCutoff N) hw.le hc.le (le_refl r)).1
  have hError := (hFinite N σ).trans (hMono hRegret)
  have h := hTri.trans (add_le_add (add_le_add le_rfl hError) le_rfl)
  change π.expectedValueOutcomeError w c ≤ (2*r+3*m N)/δ+ω (r+1*m N)+e N
  simpa only [m,one_mul,mul_assoc] using h

/-- One modulus works across a family of full countable instances with a
common cap and positive-level tail bounds, at all normalized interior weights. -/
theorem countable_outcome_stability_with_profile {α : Type*} (B : α → CountableInstance)
    {H δ : ℝ} (hH : 0 ≤ H) (hδ : 0 < δ)
    (ha : ∀ a, (B a).terminal=0) (hCap : ∀ a, ((B a).cap : ℝ) ≤ H)
    (L : ℝ → ℝ) (hL : ∀ d, 0 < d → 0 ≤ L d)
    (hTail : ∀ a d, 0 < d → ((B a).totalTailMass d).toReal ≤ L d) :
    ∃ Ω : ℝ → ℝ, (∀ r, 0 ≤ Ω r ∧ Ω r ≤ H+1) ∧ Monotone Ω ∧ Ω 0=0 ∧
      Tendsto Ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
      ∀ a w c, δ ≤ w → δ ≤ c → w+c=1 → ∀ π : RandomizedCountablePolicy (B a),
        π.expectedValueOutcomeError w c ≤ Ω ((B a).optimalScalarValue w c-π.scalarObjective w c) := by
  let C := fun q : α × ℕ => (B q.1).truncation q.2 ((B q.1).markCutoff q.2) ((B q.1).terminal_lt_markCutoff q.2)
  have hCTail (q : α × ℕ) (d : ℝ) (hd : 0 < d) : (C q).tailCount d ≤ L d := by
    have hdB : ((B q.1).terminal : ℝ) < d := by simpa only [ha q.1,NNReal.coe_zero] using hd
    exact ((B q.1).truncation_tailCount_le q.2 ((B q.1).terminal_lt_markCutoff q.2) d hdB).trans (hTail q.1 d hd)
  obtain ⟨ω,hω,hMono,hZero,hLimit,hError,_⟩ := finite_hybrid_outcome_stability_with_profile
    (fun q : α × ℕ => q.2) C hH hδ (fun q => ha q.1) (fun q => hCap q.1) L hL hCTail
  let Ω := fun r : ℝ => min (H+1) (2*max r 0/δ+ω (2*r))
  obtain ⟨hΩ,hΩMono,hΩZero,hΩLimit⟩ := ProphetSecretary.Analysis.enlarged_outcome_modulus
    hH hδ (fun r => (hω r).1) hMono hZero hLimit
  refine ⟨Ω,hΩ,hΩMono,hΩZero,hΩLimit,?_⟩
  intro a w c hw hc hSum π
  let r := (B a).optimalScalarValue w c-π.scalarObjective w c
  have hr : 0 ≤ r := sub_nonneg.mpr ((B a).scalarObjective_le_value π w c)
  have hBound := π.outcome_error_le_of_truncation_modulus (ha a) hδ hw hc ω hMono hZero hLimit
    (fun N σ => hError (a,N) w c hw hc hSum σ)
  have hCapError := π.expectedValueOutcomeError_le_bound (hCap a) (hδ.le.trans hw) (hδ.le.trans hc)
  apply le_min hCapError
  change π.expectedValueOutcomeError w c ≤ 2*max r 0/δ+ω (2*r)
  rw [max_eq_left hr]
  exact hBound

/-- Fixed positive weights also admit a common raw-regret modulus, without
normalizing the weights in the policy statement. -/
theorem countable_outcome_stability_fixed_weights {α : Type*} (B : α → CountableInstance)
    {H w c : ℝ} (hH : 0 ≤ H) (hw : 0 < w) (hc : 0 < c)
    (ha : ∀ a, (B a).terminal=0) (hCap : ∀ a, ((B a).cap : ℝ) ≤ H)
    (L : ℝ → ℝ) (hL : ∀ d, 0 < d → 0 ≤ L d)
    (hTail : ∀ a d, 0 < d → ((B a).totalTailMass d).toReal ≤ L d) :
    ∃ Ω : ℝ → ℝ, (∀ r, 0 ≤ Ω r ∧ Ω r ≤ H+1) ∧ Monotone Ω ∧ Ω 0=0 ∧
      Tendsto Ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
      ∀ a (π : RandomizedCountablePolicy (B a)),
        π.expectedValueOutcomeError w c ≤ Ω ((B a).optimalScalarValue w c-π.scalarObjective w c) := by
  let δ := min w c
  have hδ : 0 < δ := lt_min hw hc
  let C := fun q : α × ℕ => (B q.1).truncation q.2 ((B q.1).markCutoff q.2) ((B q.1).terminal_lt_markCutoff q.2)
  have hCTail (q : α × ℕ) (d : ℝ) (hd : 0 < d) : (C q).tailCount d ≤ L d := by
    have hdB : ((B q.1).terminal : ℝ) < d := by simpa only [ha q.1,NNReal.coe_zero] using hd
    exact ((B q.1).truncation_tailCount_le q.2 ((B q.1).terminal_lt_markCutoff q.2) d hdB).trans (hTail q.1 d hd)
  obtain ⟨ω,hω,hMono,hZero,hLimit,hError,_⟩ := finite_hybrid_outcome_stability_fixed_weights
    (fun q : α × ℕ => q.2) C hH hw hc (fun q => ha q.1) (fun q => hCap q.1) L hL hCTail
  let Ω := fun r : ℝ => min (H+1) (2*max r 0/δ+ω (2*r))
  obtain ⟨hΩ,hΩMono,hΩZero,hΩLimit⟩ := ProphetSecretary.Analysis.enlarged_outcome_modulus
    hH hδ (fun r => (hω r).1) hMono hZero hLimit
  refine ⟨Ω,hΩ,hΩMono,hΩZero,hΩLimit,?_⟩
  intro a π
  let r := (B a).optimalScalarValue w c-π.scalarObjective w c
  have hr : 0 ≤ r := sub_nonneg.mpr ((B a).scalarObjective_le_value π w c)
  have hBound := π.outcome_error_le_of_truncation_modulus (ha a) hδ (min_le_left w c) (min_le_right w c)
    ω hMono hZero hLimit (fun N σ => hError (a,N) σ)
  apply le_min (π.expectedValueOutcomeError_le_bound (hCap a) hw.le hc.le)
  change π.expectedValueOutcomeError w c ≤ 2*max r 0/δ+ω (2*r)
  rw [max_eq_left hr]
  exact hBound

end ProphetSecretary.Limiting
