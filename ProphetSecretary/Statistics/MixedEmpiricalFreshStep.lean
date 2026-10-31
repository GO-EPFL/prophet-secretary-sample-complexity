import ProphetSecretary.Statistics.MixedEmpiricalFutureSamples
import ProphetSecretary.Statistics.EmpiricalFreshStep

/-!
# Actual fresh jumps with exact known marginals

Known rows have identically zero jumps and conditional moments. Every unknown
row uses the centered empirical jump at its actual mixed-law continuation.
Future-row invariance licenses holding that continuation fixed when the fresh
independent sample coordinate is integrated.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.mixedPremiumJump (P : Instance n) (known : Finset (Fin n))
    (k : ℕ) (i : Fin n) (θ x : ℝ) : ℝ :=
  if i∈known then 0 else P.empiricalPremiumJump k i θ x

lemma Instance.mixedPremiumJump_known (P : Instance n) (known : Finset (Fin n))
    (k : ℕ) {i : Fin n} (hi : i∈known) (θ x : ℝ) : P.mixedPremiumJump known k i θ x=0 := by
  simp only [Instance.mixedPremiumJump,if_pos hi]

lemma Instance.mixedPremiumJump_abs_le_unit (P : Instance n) (known : Finset (Fin n))
    (i : Fin n) (hbound : ∀ᵐ x ∂P.law i, x≤1) (k : ℕ) {θ x : ℝ}
    (hθ : 0≤θ) (hx0 : 0≤x) (hx1 : x≤1) :
    |P.mixedPremiumJump known k i θ x|≤(k:ℝ)⁻¹ := by
  by_cases hi : i∈known
  · simp only [Instance.mixedPremiumJump,if_pos hi,abs_zero]
    exact inv_nonneg.mpr (Nat.cast_nonneg k)
  · simpa only [Instance.mixedPremiumJump,if_neg hi] using
      P.empiricalPremiumJump_abs_le_unit i hbound k hθ hx0 hx1

lemma Instance.measurable_mixedPremiumJump_product {Γ : Type*} [MeasurableSpace Γ]
    (P : Instance n) (known : Finset (Fin n)) (i : Fin n) (hbound : ∀ᵐ x ∂P.law i, x≤1)
    (k : ℕ) {θ : Γ → ℝ} (hθ : Measurable θ) :
    Measurable (fun q : Γ×ℝ => P.mixedPremiumJump known k i (θ q.1) q.2) := by
  by_cases hi : i∈known
  · simpa only [Instance.mixedPremiumJump,if_pos hi] using (measurable_const : Measurable (fun _ : Γ×ℝ => (0:ℝ)))
  · simpa only [Instance.mixedPremiumJump,if_neg hi] using
      P.measurable_empiricalPremiumJump_product i hbound k hθ

/-- Zero rows are explicit, rather than treated as fictitious independent
empirical errors from an infinite training sample. -/
theorem Instance.canonicalMixedFreshJump_conditional_moments {k : ℕ} [NeZero k]
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    (i : Fin n) (l : Fin k) (hbound : ∀ᵐ x ∂P.law i, x≤1)
    {z : ℝ} (hz : 0≤z) (u : Fin n → ℝ) (s : Finset (Fin n × Fin k)) (hfresh : (i,l)∉s)
    (hfuture : ∀ q∈futureSampleRows u i, q∉known → ∀ j : Fin k, (q,j)∈s) :
    let ρ := P.trainingCoordinateLaw k
    let info := ProphetSecretary.Probability.revealedCoordinateSigma s
    let θ := mixedArrivalContinuation (k:=k) P known 1 z u i
    let d := fun a : (Fin n × Fin k) → ℝ => P.mixedPremiumJump known k i (θ a) (a (i,l))
    ρ[d | info] =ᵐ[ρ] 0 ∧
      (∀ᵐ a ∂ρ, (ρ[(fun a => d a^2) | info]) a≤
        (if i∈known then 0 else positivePremium (P.law i) 1 (θ a))/(k:ℝ)^2) ∧
      (∀ᵐ a ∂ρ, (ρ[(fun a => d a^6) | info]) a≤
        (if i∈known then 0 else positivePremium (P.law i) 1 (θ a))/(k:ℝ)^6) := by
  by_cases hi : i∈known
  · simp [Instance.mixedPremiumJump,hi]
    exact Filter.Eventually.of_forall fun _ => rfl
  · have h := P.empiricalFreshJump_conditional_moments (i,l) hbound s hfresh
      (measurable_mixedArrivalContinuation P hP known zero_lt_one hz u i)
      (fun a => (mixedEmpiricalInstance P known (reservoirCoordinates.symm a)).continuationAtArrival_nonnegative
        (mixedEmpiricalInstance_integrable P hP known _) zero_le_one hz (fun _ => 0) u i)
      (mixedArrivalContinuation_mask P known 1 z u i s hfuture)
    simpa only [Instance.mixedPremiumJump,if_neg hi] using h

end ProphetSecretary.Model
