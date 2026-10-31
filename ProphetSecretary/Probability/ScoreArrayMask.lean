import ProphetSecretary.Probability.WideLikelihoodPath

/-!
# Zero perturbations on exceptional initial array indices

Masking a deterministic set of indices preserves centered component bounds
and a uniform information bound. On an omitted index the actual perturbed
law is constant for every parameter, including the wider extension.
-/
open MeasureTheory
open scoped Classical ENNReal
namespace ProphetSecretary.Probability

noncomputable def maskedArrayScore {sizes : ℕ → ℕ} (keep : ℕ → Prop)
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (m : ℕ) (i : Fin (sizes m)) (x : ℝ) : ℝ :=
  if keep m then score m i x else 0

lemma maskedArrayScore_properties (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (keep : ℕ → Prop) (score : ∀ m, Fin (sizes m) → ℝ → ℝ) {I : ℝ} (hI : 0≤I)
    (hh : ∀ m i, Measurable (score m i)) (hb : ∀ m i x, |score m i x|≤1)
    (hm : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0)
    (hInfo : ∀ m, information (P m).law (score m)≤I) :
    ∀ m, (∀ i, Measurable (maskedArrayScore keep score m i)) ∧
      (∀ i x, |maskedArrayScore keep score m i x|≤1) ∧
      (∀ i, (∫ x, maskedArrayScore keep score m i x ∂(P m).law i)=0) ∧
      information (P m).law (maskedArrayScore keep score m)≤I := by
  intro m
  by_cases hk : keep m
  · have heq : maskedArrayScore keep score m=score m := by
      funext i x
      exact if_pos hk
    rw [heq]
    exact ⟨hh m,hb m,hm m,hInfo m⟩
  · have heq : maskedArrayScore keep score m=(fun _ _ => (0:ℝ)) := by
      funext i x
      exact if_neg hk
    rw [heq]
    refine ⟨(fun _ => measurable_const),(fun _ _ => by norm_num),(fun _ => by simp),?_⟩
    simpa only [information,zero_pow (by norm_num : (2:ℕ)≠0),integral_zero,Finset.sum_const_zero] using hI
end ProphetSecretary.Probability
namespace ProphetSecretary.Model.Instance
open ProphetSecretary.Probability
variable {n : ℕ}

lemma likelihoodWidePath_eq_self_of_zero (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x|≤1)
    (hm : ∀ i, (∫ x, h i x ∂P.law i)=0) (hZero : ∀ i x, h i x=0) (θ : ℝ) :
    P.likelihoodWidePath h hh hb hm θ=P := by
  apply Instance.ext_law
  funext i
  change tiltLaw (P.law i) (h i) (halfParameter θ)=P.law i
  have hi : h i=(fun _ : ℝ => (0:ℝ)) := funext (hZero i)
  rw [hi]
  simp only [tiltLaw,tiltFactor,mul_zero,add_zero,ENNReal.ofReal_one]
  change (P.law i).withDensity (1 : ℝ → ℝ≥0∞)=P.law i
  exact withDensity_one
end ProphetSecretary.Model.Instance
