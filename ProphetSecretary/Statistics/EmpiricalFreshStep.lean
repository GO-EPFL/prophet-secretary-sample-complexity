import ProphetSecretary.Statistics.EmpiricalResidualMoments
import ProphetSecretary.Probability.ProductConditioning
import ProphetSecretary.Probability.RevealedCoordinates
import ProphetSecretary.Model.TrainingCoordinates
import ProphetSecretary.Statistics.EmpiricalFutureSamples

/-!
# Conditional moments of a fresh empirical sample

The fresh coordinate's independence is derived from the product reservoir law. A
threshold invariant under the revealed-coordinate mask can therefore be held fixed
inside the actual fresh-sample conditional integral. This is used at fixed scalar
weights; a scalar selected from the still-hidden sample is not treated as fixed.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.empiricalPremiumJump_abs_le_unit (P : Instance n) (i : Fin n)
    (hbound : ∀ᵐ x ∂P.law i, x ≤ 1) (k : ℕ) {θ x : ℝ}
    (hθ : 0 ≤ θ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |P.empiricalPremiumJump k i θ x| ≤ (k : ℝ)⁻¹ := by
  have hXi : Integrable id (P.law i) := by
    apply Integrable.of_bound aestronglyMeasurable_id 1
    filter_upwards [P.nonnegative i, hbound] with x hx hx1
    simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx] using hx1
  have hmean : (∫ x, x ∂P.law i) ≤ 1 := by
    have h : (∫ x, x ∂P.law i) ≤ ∫ _x : ℝ, (1 : ℝ) ∂P.law i :=
      integral_mono_ae hXi (integrable_const (1 : ℝ)) hbound
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hp0 := positivePremium_nonnegative (P.law i) 1 θ
  have hp1 : positivePremium (P.law i) 1 θ ≤ 1 :=
    (positivePremium_le_firstMoment (P.law i) hXi (P.nonnegative i) zero_le_one hθ).trans (by simpa using hmean)
  have hf0 : 0 ≤ max (max 0 x - θ) 0 := le_max_right _ _
  have hf1 : max (max 0 x - θ) 0 ≤ 1 := by rw [max_eq_right hx0]; exact max_le (by linarith) zero_le_one
  have habs : |max (max 0 x - θ) 0 - positivePremium (P.law i) 1 θ| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [Instance.empiricalPremiumJump, abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k))]
  exact (mul_le_mul_of_nonneg_left habs (inv_nonneg.mpr (Nat.cast_nonneg k))).trans_eq (mul_one _)

lemma Instance.measurable_empiricalPremiumJump_product {Γ : Type*} [MeasurableSpace Γ]
    (P : Instance n) (i : Fin n) (hbound : ∀ᵐ x ∂P.law i, x ≤ 1)
    (k : ℕ) {θ : Γ → ℝ} (hθ : Measurable θ) :
    Measurable (fun z : Γ × ℝ => P.empiricalPremiumJump k i (θ z.1) z.2) := by
  have hXi : Integrable id (P.law i) := by
    apply Integrable.of_bound aestronglyMeasurable_id 1
    filter_upwards [P.nonnegative i, hbound] with x hx hx1
    simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx] using hx1
  have hθl : Measurable (fun z : Γ × ℝ => θ z.1) := hθ.comp measurable_fst
  have hp := (positivePremium_continuous (P.law i) hXi 1).measurable.comp hθl
  change Measurable (fun z : Γ × ℝ => (k : ℝ)⁻¹ *
    (max (max 0 z.2 - θ z.1) 0 - positivePremium (P.law i) 1 (θ z.1)))
  exact ((((measurable_const.max measurable_snd).sub hθl).max measurable_const).sub hp).const_mul ((k : ℝ)⁻¹)

lemma Instance.integrable_empiricalPremiumJump_product_pow {Γ : Type*} [MeasurableSpace Γ]
    (P : Instance n) (i : Fin n) (hbound : ∀ᵐ x ∂P.law i, x ≤ 1)
    (ν : Measure Γ) [IsProbabilityMeasure ν] (k p : ℕ)
    {θ : Γ → ℝ} (hθ : Measurable θ) (hθ0 : ∀ y, 0 ≤ θ y) :
    Integrable (fun z : Γ × ℝ => P.empiricalPremiumJump k i (θ z.1) z.2 ^ p) (ν.prod (P.law i)) := by
  have hm := (P.measurable_empiricalPremiumJump_product i hbound k hθ).pow_const p
  apply Integrable.of_bound hm.aestronglyMeasurable (((k : ℝ)⁻¹) ^ p)
  have hx : ∀ᵐ z : Γ × ℝ ∂ν.prod (P.law i), 0 ≤ z.2 ∧ z.2 ≤ 1 := by
    have hi : ∀ᵐ x ∂P.law i, 0 ≤ x ∧ x ≤ 1 := (P.nonnegative i).and hbound
    exact (measurePreserving_snd : MeasurePreserving (Prod.snd : Γ × ℝ → ℝ) (ν.prod (P.law i)) (P.law i)).quasiMeasurePreserving.ae hi
  filter_upwards [hx] with z hz
  rw [Real.norm_eq_abs]
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) (P.empiricalPremiumJump_abs_le_unit i hbound k (hθ0 z.1) hz.1 hz.2) p

/-- Fresh conditional centering and local second/sixth moments. The revealed sigma
algebra and the product-pair law are constructed explicitly. -/
theorem Instance.empiricalFreshJump_conditional_moments {k : ℕ} (P : Instance n)
    (q : Fin n × Fin k) (hbound : ∀ᵐ x ∂P.law q.1, x ≤ 1)
    (s : Finset (Fin n × Fin k)) (hq : q ∉ s)
    {θ : ((Fin n × Fin k) → ℝ) → ℝ} (hθ : Measurable θ)
    (hθ0 : ∀ z, 0 ≤ θ z)
    (hinv : ∀ z, θ (ProphetSecretary.Probability.maskCoordinates s z) = θ z) :
    let ρ := P.trainingCoordinateLaw k
    let info := ProphetSecretary.Probability.revealedCoordinateSigma s
    let d := fun z : (Fin n × Fin k) → ℝ => P.empiricalPremiumJump k q.1 (θ z) (z q)
    ρ[d | info] =ᵐ[ρ] 0 ∧
      (∀ᵐ z ∂ρ, (ρ[(fun z => d z ^ 2) | info]) z ≤ positivePremium (P.law q.1) 1 (θ z) / (k : ℝ) ^ 2) ∧
      (∀ᵐ z ∂ρ, (ρ[(fun z => d z ^ 6) | info]) z ≤ positivePremium (P.law q.1) 1 (θ z) / (k : ℝ) ^ 6) := by
  let ρ := P.trainingCoordinateLaw k
  let past := ρ.map (ProphetSecretary.Probability.maskCoordinates s)
  haveI : IsProbabilityMeasure past := Measure.isProbabilityMeasure_map
    (ProphetSecretary.Probability.measurable_maskCoordinates s).aemeasurable
  have hp : MeasurePreserving (fun z : (Fin n × Fin k) → ℝ =>
      (ProphetSecretary.Probability.maskCoordinates s z, z q)) ρ (past.prod (P.law q.1)) :=
    ProphetSecretary.Probability.revealedCoordinates_fresh_pair_measurePreserving (fun r : Fin n × Fin k => P.law r.1) hq
  have hCE (p : ℕ) : ρ[(fun z => (P.empiricalPremiumJump k q.1 (θ z) (z q)) ^ p) |
      ProphetSecretary.Probability.revealedCoordinateSigma s] =ᵐ[ρ]
      (fun z => ∫ x, P.empiricalPremiumJump k q.1 (θ z) x ^ p ∂P.law q.1) := by
    have h := ProphetSecretary.Probability.condExp_productPair past (P.law q.1) ρ hp
      (F := fun z => P.empiricalPremiumJump k q.1 (θ z.1) z.2 ^ p)
      ((P.measurable_empiricalPremiumJump_product q.1 hbound k hθ).pow_const p)
      (P.integrable_empiricalPremiumJump_product_pow q.1 hbound past k p hθ hθ0)
    simpa only [hinv] using h
  refine ⟨?_, ?_, ?_⟩
  · have h := hCE 1
    simp only [pow_one] at h
    filter_upwards [h] with z hz
    have hm := (P.empiricalPremiumJump_moments q.1 hbound (hθ0 z) k).1
    simpa only [Pi.zero_apply, hm] using hz
  · filter_upwards [hCE 2] with z hz
    exact hz.trans_le (P.empiricalPremiumJump_moments q.1 hbound (hθ0 z) k).2.1
  · filter_upwards [hCE 6] with z hz
    exact hz.trans_le (P.empiricalPremiumJump_moments q.1 hbound (hθ0 z) k).2.2

/-- The canonical empirical continuation discharges the functional nonanticipation
hypothesis using its actual future-row construction. The scalar `z` remains fixed. -/
theorem Instance.canonicalEmpiricalFreshJump_conditional_moments {k : ℕ} [NeZero k]
    (P : Instance n) (i : Fin n) (j : Fin k) (hbound : ∀ᵐ x ∂P.law i, x ≤ 1)
    {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) (s : Finset (Fin n × Fin k)) (hfresh : (i, j) ∉ s)
    (hfuture : ∀ q ∈ futureSampleRows u i, ∀ a : Fin k, (q, a) ∈ s) :
    let ρ := P.trainingCoordinateLaw k
    let info := ProphetSecretary.Probability.revealedCoordinateSigma s
    let θ := empiricalArrivalContinuation (k := k) 1 z u i
    let d := fun a : (Fin n × Fin k) → ℝ => P.empiricalPremiumJump k i (θ a) (a (i, j))
    ρ[d | info] =ᵐ[ρ] 0 ∧
      (∀ᵐ a ∂ρ, (ρ[(fun a => d a ^ 2) | info]) a ≤ positivePremium (P.law i) 1 (θ a) / (k : ℝ) ^ 2) ∧
      (∀ᵐ a ∂ρ, (ρ[(fun a => d a ^ 6) | info]) a ≤ positivePremium (P.law i) 1 (θ a) / (k : ℝ) ^ 6) := by
  apply P.empiricalFreshJump_conditional_moments (i, j) hbound s hfresh
    (measurable_empiricalArrivalContinuation (by norm_num : (0 : ℝ) < 1) hz u i)
  · intro a
    exact (totalEmpiricalInstance (reservoirCoordinates.symm a)).continuationAtArrival_nonnegative
      (totalEmpiricalInstance_integrable _) zero_le_one hz (fun _ => 0) u i
  · exact empiricalArrivalContinuation_mask 1 z u i s hfuture

end ProphetSecretary.Model
