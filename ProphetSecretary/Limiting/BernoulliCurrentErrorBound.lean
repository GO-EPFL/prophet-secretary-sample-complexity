import ProphetSecretary.Limiting.BernoulliGeneratorSplit
import ProphetSecretary.Limiting.HybridClockMarginal
import ProphetSecretary.Limiting.SharpHazardMarginal

/-!
# The virtual Bernoulli current-state hazard error

The current premium is bounded by its first-moment budget. The actual virtual
clock projection is measure preserving, so the sharp uniform-clock hazard bound
applies even though the shared policy and continuation use the other observations.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma HybridRule.measurable_bernoulliCurrentError (π : HybridRule (n + k) Seed) (hπ : π.IsMeasurable)
    (Q : Model.Instance (n + k)) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (κ : Measure ℝ) [IsProbabilityMeasure κ] (hI : Integrable id κ) (p : unitInterval)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Measurable (π.bernoulliCurrentError Q κ p w c) := by
  have hs : MeasurableSet {q : HybridWorld (n + k) Seed × ℝ | q.2 ≤ π.realizedDuration q.1} :=
    measurableSet_le measurable_snd ((π.measurable_realizedDuration hπ).comp measurable_fst)
  have hmap : Measurable (fun q : HybridWorld (n + k) Seed × ℝ =>
      (q.2,fun j : Fin k => q.1.2.2.1 (j.natAdd n))) := by fun_prop
  have hH := (measurable_tailHazardError (fun _ : Fin k => (p : ℝ))).comp hmap
  have hpair : Measurable (fun q : HybridWorld (n + k) Seed × ℝ => ((q.2,(0 : ℝ)),q.1.2)) := by fun_prop
  have hcur := (measurable_designPoissonPremium Q hQ κ hI hw hc).comp hpair
  exact Measurable.ite hs (hH.mul hcur) measurable_const

omit [MeasurableSpace Seed] in
lemma HybridRule.bernoulliCurrentError_abs_le (π : HybridRule (n + k) Seed)
    (Q : Model.Instance (n + k)) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (κ : Measure ℝ) [IsProbabilityMeasure κ] (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (hI : Integrable id κ) (p : unitInterval)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (q : HybridWorld (n + k) Seed × ℝ) :
    |π.bernoulliCurrentError Q κ p w c q| ≤
      (w * ∫ x, x ∂κ) * |tailHazardError (fun _ : Fin k => (p : ℝ)) q.2 (fun j => q.1.2.2.1 (j.natAdd n))| := by
  have hb := Model.positivePremium_le_firstMoment κ hI hκ hw (poissonContinuation_nonnegative Q hQ hw hc q.1.2.2.1 q.2)
  unfold HybridRule.bernoulliCurrentError
  split_ifs
  · rw [abs_mul, abs_of_nonneg (Model.positivePremium_nonnegative _ _ _)]
    exact (mul_le_mul_of_nonneg_left hb (abs_nonneg _)).trans_eq (mul_comm _ _)
  · rw [abs_zero]
    exact mul_nonneg (mul_nonneg hw (integral_nonneg_of_ae hκ)) (abs_nonneg _)

/-- Explicit virtual error rate before p=λ/k is chosen. -/
theorem HybridRule.bernoulliCurrentError_integral_bound (π : HybridRule (n + k) Seed) (hπ : π.IsMeasurable)
    (Q R : Model.Instance (n + k)) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (κ : Measure ℝ) [IsProbabilityMeasure κ] (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (hI : Integrable id κ) (p : unitInterval)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Integrable (π.bernoulliCurrentError Q κ p w c)
      ((hybridWorldLaw R μ ν).prod Model.Instance.uniformClock) ∧
      |∫ q, π.bernoulliCurrentError Q κ p w c q
        ∂(hybridWorldLaw R μ ν).prod Model.Instance.uniformClock| ≤
          (Real.pi / 2) * w * (∫ x, x ∂κ) * Real.sqrt ((k : ℝ) * (p : ℝ) ^ 2) := by
  have hp := hybridTimeRestrictedClocks_measurePreserving R μ ν (Fin.natAddEmb n : Fin k ↪ Fin (n + k))
  have h := hazard_marginal_domination ((hybridWorldLaw R μ ν).prod Model.Instance.uniformClock)
    (fun q : HybridWorld (n + k) Seed × ℝ => q.2)
    (fun q => fun j : Fin k => q.1.2.2.1 (j.natAdd n)) hp (fun _ : Fin k => (p : ℝ))
    (mul_nonneg hw.le (integral_nonneg_of_ae hκ)) (π.bernoulliCurrentError Q κ p w c)
    (π.measurable_bernoulliCurrentError hπ Q hQ κ hI p hw hc)
    (π.bernoulliCurrentError_abs_le Q hQ κ hκ hI p hw.le hc)
  refine ⟨h.1, ?_⟩
  have hb := h.2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hb
  exact hb.trans_eq (by ring)

end ProphetSecretary.Limiting
