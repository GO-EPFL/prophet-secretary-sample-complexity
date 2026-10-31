import ProphetSecretary.Limiting.OrderedPaddedLaws
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Extended rational tail limits for general cap-bounded sequences

Tail counts may diverge without a uniform first-moment bound. Compactness of
[0,∞] and its countable product extracts one actual subsequence on all rational
levels. This is the first step of the full H-only reserve extraction, distinct
from the bounded-total-first-moment subcase.
-/
open MeasureTheory Set Filter
open scoped Topology Classical BigOperators
namespace ProphetSecretary.Limiting

noncomputable def extendedTailCount {n : ℕ} (P : Model.Instance n) (x : ℝ) : ENNReal :=
  ∑ i, P.law i (Ioi x)

lemma extendedTailCount_finite {n : ℕ} (P : Model.Instance n) (x : ℝ) : extendedTailCount P x < ⊤ := by
  apply ENNReal.sum_lt_top.mpr
  intro i _
  exact measure_lt_top _ _

lemma extendedTailCount_antitone {n : ℕ} (P : Model.Instance n) : Antitone (extendedTailCount P) := by
  intro x y hxy
  apply Finset.sum_le_sum
  intro i _
  exact measure_mono (Ioi_subset_Ioi hxy)

lemma extendedTailCount_toReal {n : ℕ} (P : Model.Instance n) (x : ℝ) :
    (extendedTailCount P x).toReal = P.tailCount x :=
  ENNReal.toReal_sum (fun i _ => measure_ne_top (P.law i) (Ioi x))

lemma extendedTailCount_eq_zero_above_cap {n : ℕ} (P : Model.Instance n) {H : ℝ}
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) {x : ℝ} (hx : H ≤ x) : extendedTailCount P x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hcap i] with y hy
  exact not_lt_of_ge (hy.trans hx)

/-- The rational-level extended limits are extracted, not included as an
unproved hypothesis on the input sequence. -/
theorem exists_rational_extended_tail_subsequence (L : ℕ → ℝ → ENNReal) :
    ∃ (l : ℚ → ENNReal) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ q : ℚ, Tendsto (fun m => L (φ m) (q : ℝ)) atTop (𝓝 (l q)) := by
  obtain ⟨l,φ,hφ,hconv⟩ := SeqCompactSpace.tendsto_subseq (fun (m : ℕ) (q : ℚ) => L m (q : ℝ))
  exact ⟨l,φ,hφ,fun q => ((continuous_apply q).tendsto l).comp hconv⟩

/-- Actual finite independent input data, with each extended tail finite and
all rational cap levels having limiting tail count zero. -/
theorem exists_finite_instance_rational_tail_limits {H : ℝ} (sizes : ℕ → ℕ)
    (P : ∀ m, Model.Instance (sizes m)) (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ H) :
    ∃ (l : ℚ → ENNReal) (φ : ℕ → ℕ), StrictMono φ ∧ Antitone l ∧
      (∀ q : ℚ, H ≤ (q : ℝ) → l q = 0) ∧
      ∀ q : ℚ, Tendsto (fun m => extendedTailCount (P (φ m)) (q : ℝ)) atTop (𝓝 (l q)) := by
  obtain ⟨l,φ,hφ,hconv⟩ := exists_rational_extended_tail_subsequence (fun m => extendedTailCount (P m))
  have hanti : Antitone l := by
    intro q r hqr
    apply le_of_tendsto_of_tendsto (hconv r) (hconv q)
    exact Eventually.of_forall fun m => extendedTailCount_antitone (P (φ m)) (by exact_mod_cast hqr)
  have hzero (q : ℚ) (hq : H ≤ (q : ℝ)) : l q = 0 := by
    have heq : (fun m => extendedTailCount (P (φ m)) (q : ℝ)) = fun _ : ℕ => 0 :=
      funext fun m => extendedTailCount_eq_zero_above_cap (P (φ m)) (hcap (φ m)) hq
    apply tendsto_nhds_unique (hconv q)
    rw [heq]
    exact tendsto_const_nhds
  exact ⟨l,φ,hφ,hanti,hzero,hconv⟩

end ProphetSecretary.Limiting
