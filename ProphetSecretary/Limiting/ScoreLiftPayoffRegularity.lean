import ProphetSecretary.Stability.LawCurvature

/-!
# Uniform fixed-policy and benchmark regularity for lifted score families

The policy callback and its independent seed law are held fixed throughout
the likelihood curve. Benchmark and optimized-value differentiation remain
separate statements. The constants depend on the cap and information bound,
not on the number of distributions or the chosen policy.
-/
open MeasureTheory Set
open scoped Classical Topology
namespace ProphetSecretary.Limiting
open ProphetSecretary.Model ProphetSecretary.Probability

 theorem finite_score_fixedPolicy_curvature
    (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {H I : ℝ} (hH : 0≤H) (_hI : 0≤I)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H)
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hMeas : ∀ m i, Measurable (score m i))
    (hBound : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hMean : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0)
    (hInfo : ∀ m, information (P m).law (score m)≤I) :
    ∀ m (π : RandomizedPolicy (sizes m)) lam, lam∈Icc (0:ℝ) 1 →
      let f := fun θ => π.scalarObjective ((P m).likelihoodWidePath (score m) (hMeas m) (hBound m) (hMean m) θ) lam (1-lam)
      (∀ᵐ θ ∂volume.restrict (Ioo (-(1/4):ℝ) (1/4)), |deriv (deriv f) θ|≤8*(H+1)*I) ∧
      (∀ θ∈Icc (-(1/4):ℝ) (1/4), ∀ ρ∈Icc (-(1/4):ℝ) (1/4),
        |deriv f ρ-deriv f θ|≤(8*(H+1)*I)*|ρ-θ|) := by
  intro m π lam hlam
  have hCoef : lam*H+(1-lam)≤H+1 := by
    have h := mul_le_mul_of_nonneg_right hlam.2 hH
    nlinarith only [h,hlam.1]
  have hK : 8*(lam*H+(1-lam))*information (P m).law (score m)≤8*(H+1)*I :=
    mul_le_mul (by linarith only [hCoef]) (hInfo m)
      (information_nonnegative (P m).law (score m)) (by positivity)
  have h := π.law_curvature (P m) hlam.1 (sub_nonneg.mpr hlam.2) hH (hCap m)
    (score m) (hMeas m) (hBound m) (hMean m)
  exact ⟨h.1.mono (fun _ hx => hx.trans hK),fun θ hθ ρ hρ =>
    (h.2 θ hθ ρ hρ).trans (mul_le_mul_of_nonneg_right hK (abs_nonneg _))⟩

theorem finite_score_maximum_curvature
    (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {H I : ℝ} (hH : 0≤H) (_hI : 0≤I)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H)
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hMeas : ∀ m i, Measurable (score m i))
    (hBound : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hMean : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0)
    (hInfo : ∀ m, information (P m).law (score m)≤I) :
    ∀ m θ, θ∈Icc (-(1/4):ℝ) (1/4) →
      let M := fun t => ((P m).likelihoodWidePath (score m) (hMeas m) (hBound m) (hMean m) t).expectedMaximum
      DifferentiableAt ℝ M θ ∧ DifferentiableAt ℝ (deriv M) θ ∧ |deriv (deriv M) θ|≤8*H*I := by
  intro m θ hθ
  have h := (P m).maximum_law_curvature hH (hCap m) (score m) (hMeas m) (hBound m) (hMean m) θ hθ
  exact ⟨h.1,h.2.1,h.2.2.trans (mul_le_mul_of_nonneg_left (hInfo m) (by positivity))⟩
end ProphetSecretary.Limiting
