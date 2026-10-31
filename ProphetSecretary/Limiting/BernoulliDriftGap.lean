import ProphetSecretary.Limiting.BernoulliClockPremium

/-!
# Integrated quadratic Bernoulli child-state error

The per-arrival p² premium error is divided by the remaining horizon in the
clock generator. Its integral is nevertheless bounded by w p² Eκ: actual
individual-clock compensation cancels the future-arrival probability. No
uniform pointwise bound on the singular hazard itself is assumed.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Limiting

variable {n k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def HybridRule.bernoulliPremiumGap (π : HybridRule (n + k) Seed)
    (Q : Model.Instance (n + k)) (κ : Measure ℝ) (p : unitInterval) (w c : ℝ)
    (j : Fin k) (q : HybridWorld (n + k) Seed × ℝ) : ℝ :=
  if q.2 ≤ π.realizedDuration q.1 ∧ q.2 < q.1.2.2.1 (j.natAdd n) then
    (p : ℝ) * (individualDesignPremium Q κ w c (j.natAdd n) (q.2,q.1) -
      Model.positivePremium κ w (poissonContinuation Q w c q.1.2.2.1 q.2)) / (1 - q.2) else 0

lemma HybridRule.measurable_bernoulliPremiumGap (π : HybridRule (n + k) Seed) (hπ : π.IsMeasurable)
    (Q : Model.Instance (n + k)) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (κ : Measure ℝ) [IsProbabilityMeasure κ] (hI : Integrable id κ) (p : unitInterval)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (j : Fin k) :
    Measurable (π.bernoulliPremiumGap Q κ p w c j) := by
  have ha : MeasurableSet {q : HybridWorld (n + k) Seed × ℝ |
      q.2 ≤ π.realizedDuration q.1 ∧ q.2 < q.1.2.2.1 (j.natAdd n)} :=
    (measurableSet_le measurable_snd ((π.measurable_realizedDuration hπ).comp measurable_fst)).inter
      (measurableSet_lt measurable_snd (by fun_prop))
  have hswap : Measurable (fun q : HybridWorld (n + k) Seed × ℝ => (q.2,q.1)) := measurable_swap
  have hchild := (measurable_individualDesignPremium Q hQ κ hI hw hc (j.natAdd n)).comp hswap
  have hpair : Measurable (fun q : HybridWorld (n + k) Seed × ℝ => ((q.2,(0 : ℝ)),q.1.2)) := by fun_prop
  have hcur := (measurable_designPoissonPremium Q hQ κ hI hw hc).comp hpair
  exact Measurable.ite ha (((hchild.sub hcur).const_mul (p : ℝ)).div (measurable_const.sub measurable_snd)) measurable_const

/-- Integrability and the dimension-independent quadratic expectation bound. -/
theorem HybridRule.bernoulliPremiumGap_integral_bound (π : HybridRule (n + k) Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (R : Model.Instance (n + k)) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (p : unitInterval)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (hI : Integrable id κ)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (j : Fin k) :
    let Q := finitePoissonDesign P κ hκ p k
    let gap := π.bernoulliPremiumGap Q κ p w c j
    Integrable gap ((hybridWorldLaw R μ ν).prod Model.Instance.uniformClock) ∧
      0 ≤ (∫ q, gap q ∂(hybridWorldLaw R μ ν).prod Model.Instance.uniformClock) ∧
      (∫ q, gap q ∂(hybridWorldLaw R μ ν).prod Model.Instance.uniformClock) ≤
        w * (p : ℝ) ^ 2 * ∫ x, x ∂κ := by
  let Q := finitePoissonDesign P κ hκ p k
  let δ := w * (p : ℝ) ^ 2 * ∫ x, x ∂κ
  have hδ : 0 ≤ δ := mul_nonneg (mul_nonneg hw.le (sq_nonneg _)) (integral_nonneg_of_ae hκ)
  have hQ := finitePoissonDesign_integrable_maximum P κ hκ p k hP hI
  let G : ℝ × HybridWorld (n + k) Seed → ℝ := fun _ => δ
  have hcomp := π.individual_compensator_real hπ (j.natAdd n) R μ ν G measurable_const (fun _ => hδ) (fun _ => le_rfl)
  have hb (q : HybridWorld (n + k) Seed × ℝ) :
      0 ≤ π.bernoulliPremiumGap Q κ p w c j q ∧
        π.bernoulliPremiumGap Q κ p w c j q ≤ π.realIndividualStoppedHazard (j.natAdd n) G q := by
    have h := bernoulli_clock_weighted_child_premium_gap P κ hκ p k hP hI hw hc q.1.2.2.1 q.2 j
    dsimp only at h
    unfold HybridRule.bernoulliPremiumGap HybridRule.realIndividualStoppedHazard
    split_ifs with hactive
    · have ht1 : q.2 ≤ 1 := hactive.1.trans (π.stoppingTime_le_one q.1.2.2.2 q.1.2.1 q.1.2.2.1 q.1.1)
      exact ⟨div_nonneg h.1 (sub_nonneg.mpr ht1), div_le_div_of_nonneg_right h.2 (sub_nonneg.mpr ht1)⟩
    · exact ⟨le_rfl, le_rfl⟩
  have hi : Integrable (π.bernoulliPremiumGap Q κ p w c j)
      ((hybridWorldLaw R μ ν).prod Model.Instance.uniformClock) := by
    apply hcomp.2.1.mono' (π.measurable_bernoulliPremiumGap hπ Q hQ κ hI p hw hc j).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hb q).1]
      exact (hb q).2
  have hconst : (∫ q, π.realIndividualStoppedHazard (j.natAdd n) G q
      ∂(hybridWorldLaw R μ ν).prod Model.Instance.uniformClock) ≤ δ := by
    rw [integral_prod _ hcomp.2.1, ← hcomp.2.2]
    have h := integral_mono hcomp.1 (integrable_const δ) (fun v => by
      change (if _ then δ else 0) ≤ δ
      split_ifs
      · exact le_rfl
      · exact hδ)
    simpa only [integral_const, probReal_univ, one_smul] using h
  exact ⟨hi, integral_nonneg (fun q => (hb q).1), (integral_mono hi hcomp.2.1 (fun q => (hb q).2)).trans hconst⟩

/-- Summed virtual error before taking the rare-probability limit. -/
theorem HybridRule.sum_bernoulliPremiumGap_integral_bound (π : HybridRule (n + k) Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (R : Model.Instance (n + k)) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (p : unitInterval)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (hI : Integrable id κ)
    (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let Q := finitePoissonDesign P κ hκ p k
    (∫ q, (∑ j : Fin k, π.bernoulliPremiumGap Q κ p w c j q)
      ∂(hybridWorldLaw R μ ν).prod Model.Instance.uniformClock) ≤
        (k : ℝ) * (w * (p : ℝ) ^ 2 * ∫ x, x ∂κ) := by
  have h (j : Fin k) := π.bernoulliPremiumGap_integral_bound hπ P R κ hκ p hP hI μ ν hw hc j
  dsimp only at h ⊢
  have hi (j : Fin k) : Integrable (fun q => π.bernoulliPremiumGap (finitePoissonDesign P κ hκ p k) κ p w c j q)
      ((hybridWorldLaw R μ ν).prod Model.Instance.uniformClock) := (h j).1
  rw [integral_finsetSum _ (fun j _ => hi j)]
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin k))) (fun j _ => (h j).2.2)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using hb

end ProphetSecretary.Limiting
