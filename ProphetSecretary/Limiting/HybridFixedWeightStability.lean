import ProphetSecretary.Limiting.HybridWeightScaling
import ProphetSecretary.Limiting.HybridOutcomeStability

/-!
# Uniform hybrid stability at fixed positive scalar weights

Positive homogeneity normalizes arbitrary fixed reward and duration weights.
The resulting modulus is expressed in the original scalar regret, while the
canonical callback and all actual coupled outcomes remain unchanged.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*}

lemma HybridRule.coupledValueOutcomeError_smul (π : HybridRule n Seed)
    (B : FiniteIntensityHybridInstance n) {a w c : ℝ} (ha : 0 < a) (v : HybridWorld n Seed) :
    π.coupledValueOutcomeError B (a*w) (a*c) v = π.coupledValueOutcomeError B w c v := by
  unfold HybridRule.coupledValueOutcomeError
  simp only [B.valueRule_smul ha]

lemma RandomizedHybridPolicy.expectedValueOutcomeError_smul (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) {a w c : ℝ} (ha : 0 < a) :
    π.expectedValueOutcomeError B (a*w) (a*c) = π.expectedValueOutcomeError B w c := by
  unfold RandomizedHybridPolicy.expectedValueOutcomeError
  simp only [π.rule.coupledValueOutcomeError_smul B ha]

/-- Fixed positive weights require no normalization premise. The cap and
positive-tail profile are uniform across every retained dimension and cloud. -/
theorem finite_hybrid_outcome_stability_fixed_weights {α : Type*} (n : α → ℕ)
    (B : ∀ a, FiniteIntensityHybridInstance (n a)) {H w c : ℝ}
    (hH : 0 ≤ H) (hw : 0 < w) (hc : 0 < c)
    (ha : ∀ a, (B a).terminal=0) (hCap : ∀ a, ((B a).cap : ℝ) ≤ H)
    (L : ℝ → ℝ) (hL : ∀ d, 0 < d → 0 ≤ L d)
    (hTail : ∀ a d, 0 < d → (B a).tailCount d ≤ L d) :
    ∃ ω : ℝ → ℝ, (∀ t, 0 ≤ ω t ∧ ω t ≤ H+1) ∧ Monotone ω ∧ ω 0=0 ∧
      Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
      (∀ a (π : RandomizedHybridPolicy (n a)), π.expectedValueOutcomeError (B a) w c ≤
        ω ((B a).optimalScalarValue w c-π.scalarObjective (B a) w c)) ∧
      (∀ t < 0, ω t=0) := by
  let s := w+c
  let wn := w/s
  let cn := c/s
  let δ := min wn cn
  have hs : 0 < s := add_pos hw hc
  have hwn : 0 < wn := div_pos hw hs
  have hcn : 0 < cn := div_pos hc hs
  have hδ : 0 < δ := lt_min hwn hcn
  have hSum : wn+cn=1 := by
    dsimp only [wn,cn]
    rw [← add_div]
    exact div_self hs.ne'
  have hW : s*wn=w := by dsimp only [wn]; exact mul_div_cancel₀ w hs.ne'
  have hC : s*cn=c := by dsimp only [cn]; exact mul_div_cancel₀ c hs.ne'
  obtain ⟨ω,hω,hMono,hZero,hLim,hError,hNeg⟩ :=
    finite_hybrid_outcome_stability_with_profile n B hH hδ ha hCap L hL hTail
  let ν : ℝ → ℝ := fun r => ω (r/s)
  have hDiv : Tendsto (fun r : ℝ => r/s) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [id_eq,zero_div] using ((continuous_id.div_const s).tendsto (0 : ℝ)).mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact div_pos hr hs
  refine ⟨ν,(fun r => hω (r/s)),?_,?_,hLim.comp hDiv,?_,?_⟩
  · intro x y hxy
    exact hMono (div_le_div_of_nonneg_right hxy hs.le)
  · simpa only [ν,zero_div] using hZero
  · intro a π
    have hE := hError a wn cn (min_le_left _ _) (min_le_right _ _) hSum π
    have hOutcome := π.expectedValueOutcomeError_smul (B a) (a := s) (w := wn) (c := cn) hs
    rw [hW,hC] at hOutcome
    have hV := (B a).optimalScalarValue_smul (a := s) (w := wn) (c := cn) hs.le
    have hJ := π.scalarObjective_smul (B a) s wn cn
    rw [hW,hC] at hV hJ
    have hGap : ((B a).optimalScalarValue w c-π.scalarObjective (B a) w c)/s =
        (B a).optimalScalarValue wn cn-π.scalarObjective (B a) wn cn := by
      rw [hV,hJ,← mul_sub]
      exact mul_div_cancel_left₀ _ hs.ne'
    change π.expectedValueOutcomeError (B a) w c ≤ ω (((B a).optimalScalarValue w c-π.scalarObjective (B a) w c)/s)
    rw [hOutcome,hGap]
    exact hE
  · intro r hr
    exact hNeg (r/s) (div_neg_of_neg_of_pos hr hs)

end ProphetSecretary.Limiting
