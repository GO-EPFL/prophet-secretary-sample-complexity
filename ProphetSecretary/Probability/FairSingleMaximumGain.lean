import ProphetSecretary.Probability.FairSigns

/-!
# Fair perturbation of one value at a tied maximum

A centered fair perturbation cannot decrease a two-variable maximum in
expectation. If the two old values agree and the perturbation amplitude is
one, the expected increase is exactly half the nonnegative perturbation size.
This is the individual tie-gain computation in `lem:location`.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Probability

theorem mean_single_signed_maximum_ge (x y h a : ℝ) :
    max x y ≤ ∫ s, max (x+h*(variableSign s (0 : Fin 1)*a)) y ∂fairSigns 1 := by
  by_cases hxy : x≤y
  · rw [max_eq_right hxy]
    have h := integral_mono (integrable_const y) (fairSigns_integrable _)
      (fun s => le_max_right (x+h*(variableSign s (0 : Fin 1)*a)) y)
    simpa only [integral_const,probReal_univ,one_smul] using h
  · rw [max_eq_left (le_of_not_ge hxy)]
    have h := integral_mono (fairSigns_integrable (fun s => x+h*(variableSign s (0 : Fin 1)*a)))
      (fairSigns_integrable _) (fun s => le_max_left (x+h*(variableSign s (0 : Fin 1)*a)) y)
    rw [integral_add (integrable_const x) (fairSigns_integrable _),integral_const_mul,
      integral_mul_const,integral_variableSign,zero_mul,mul_zero] at h
    simpa only [integral_const,probReal_univ,one_smul,add_zero] using h

theorem mean_single_signed_maximum_tie (x h : ℝ) (hh : 0≤h) :
    (∫ s, max (x+h*(variableSign s (0 : Fin 1)*1)) x ∂fairSigns 1)=x+h/2 := by
  have hPoint (s : Fin 1 → Bool) : max (x+h*(variableSign s 0*1)) x=
      (x+h/2)+(h/2)*variableSign s 0 := by
    by_cases hs : s 0=true
    · have hSign : variableSign s 0=1 := if_pos hs
      rw [hSign,one_mul,mul_one,max_eq_left (by linarith : x≤x+h)]
      ring
    · have hSign : variableSign s 0= -1 := if_neg hs
      rw [hSign,mul_one]
      have hMax : max (x+h*(-1)) x=x := max_eq_right (by linarith)
      rw [hMax]
      ring
  rw [integral_congr_ae (Eventually.of_forall hPoint),
    integral_add (integrable_const (x+h/2)) (fairSigns_integrable _),integral_const_mul,
    integral_variableSign,mul_zero,add_zero]
  simp only [integral_const,probReal_univ,one_smul]

theorem mean_single_signed_maximum_threshold_gain (b x y h : ℝ) (hh : 0≤h) :
    max x y+(if x=y ∧ b≤x then h/2 else 0) ≤
      ∫ s, max (x+h*(variableSign s (0 : Fin 1)*(if b≤x then 1 else 0))) y ∂fairSigns 1 := by
  by_cases hTie : x=y ∧ b≤x
  · rcases hTie with ⟨rfl,hLevel⟩
    rw [if_pos ⟨rfl,hLevel⟩,if_pos hLevel,max_self,mean_single_signed_maximum_tie _ _ hh]
  · rw [if_neg hTie,add_zero]
    exact mean_single_signed_maximum_ge x y h _

end ProphetSecretary.Probability
