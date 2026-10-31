import ProphetSecretary.Analysis.PosteriorIncrement

/-!
# A Bayes response from posterior movement control

The chosen index is deterministic. The constants are fixed before the finite
posterior sequence and its score sequence. This is the low-first-moment
small-increment argument following `eq:bayes-brier-identity`.
-/

open Set
namespace ProphetSecretary.Analysis

noncomputable def posteriorResponseAlpha (a D : ℝ) : ℝ := min 1 (a/(2*(D+1)))

lemma posteriorResponseAlpha_positive {a D : ℝ} (ha : 0<a) (hD : 0≤D) :
    0<posteriorResponseAlpha a D := by unfold posteriorResponseAlpha; positivity

lemma posteriorResponseAlpha_le_one (a D : ℝ) : posteriorResponseAlpha a D≤1 := min_le_left _ _

lemma posteriorResponseAlpha_mul {a D : ℝ} (ha : 0<a) (hD : 0≤D) :
    posteriorResponseAlpha a D*D≤a/2 := by
  have hPos : 0<2*(D+1) := by positivity
  have hLe := (le_div_iff₀ hPos).mp (min_le_right (1 : ℝ) (a/(2*(D+1))))
  have hα := (posteriorResponseAlpha_positive ha hD).le
  change posteriorResponseAlpha a D*(2*(D+1))≤a at hLe
  nlinarith only [hLe,hα]

noncomputable def posteriorResponseConstant (a D B K : ℝ) : ℝ := K+B+8/posteriorResponseAlpha a D

lemma posteriorResponseConstant_positive {a D B K : ℝ}
    (ha : 0<a) (hD : 0≤D) (hB : 0≤B) (hK : 0≤K) :
    0<posteriorResponseConstant a D B K := by
  have hα := posteriorResponseAlpha_positive ha hD
  unfold posteriorResponseConstant
  positivity

theorem exists_posterior_response {m : ℕ} (hm : 8≤m) {a D B K : ℝ}
    (ha : 0<a) (hD : 0≤D) (hB : 0≤B)
    (s x payoff : ℕ → ℝ) (hs : ∀ j≤m, s j∈Icc (0 : ℝ) 1)
    (hStep : ∀ j<m, s j≤s (j+1))
    (hx : ∀ j<m, 0≤x j) (hControl : ∀ j<m, s j≤D*x j+B/(m : ℝ))
    (hPayoff : ∀ j<m, a*x j-K/(m : ℝ)-Real.sqrt (s (j+1)-s j)≤payoff j) :
    ∃ j<m, -posteriorResponseConstant a D B K/(m : ℝ)≤payoff j := by
  let α := posteriorResponseAlpha a D
  have hα : 0<α := posteriorResponseAlpha_positive ha hD
  have hαOne : α≤1 := posteriorResponseAlpha_le_one a D
  have hαD : α*D≤a/2 := posteriorResponseAlpha_mul ha hD
  have hmPos : (0 : ℝ)<m := by exact_mod_cast (show 0<m by omega)
  obtain ⟨j,hj,hIncrement⟩ := exists_small_posterior_increment hm s hs hStep hα hαOne
  have hControl' := mul_le_mul_of_nonneg_left (hControl j hj) hα.le
  have hDX := mul_le_mul_of_nonneg_right hαD (hx j hj)
  have hBMean : 0≤B/(m : ℝ) := div_nonneg hB hmPos.le
  have hαB : α*(B/(m : ℝ))≤B/(m : ℝ) := mul_le_of_le_one_left hBMean hαOne
  have hRecip : 8/(α*(m : ℝ))=(8/α)/(m : ℝ) := by ring
  rw [hRecip] at hIncrement
  have hBound := hPayoff j hj
  have hAX := mul_nonneg ha.le (hx j hj)
  refine ⟨j,hj,?_⟩
  unfold posteriorResponseConstant
  change -(K+B+8/α)/(m : ℝ)≤payoff j
  rw [neg_div,add_div,add_div]
  nlinarith only [hIncrement,hControl',hDX,hαB,hBound,hAX]

end ProphetSecretary.Analysis
