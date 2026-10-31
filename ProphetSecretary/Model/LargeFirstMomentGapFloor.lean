import ProphetSecretary.Model.LargeFirstMomentSlack
import ProphetSecretary.Model.BoundarySublevels
import ProphetSecretary.Model.ScalarGapMinimum

/-!
# A uniform scalar-gap floor in the large-first-moment class

The endpoint localization is unconditional. Combining it with the proved
first-moment theorem gives Sstar≥1 and κ>0, fixed before the instance size
and laws, such that W(P)≥κ/(1+L)^4 when S≥Sstar. This is the slack used
by the high class in the proof of `upbayes:theorem`.
-/

open MeasureTheory Set
namespace ProphetSecretary.Model

theorem bounded_largeFirstMoment_gap_floor (mu : ℝ) (hmu : 0<mu) :
    ∃ Sstar κ : ℝ, 1≤Sstar ∧ 0<κ ∧ ∀ (n : ℕ) (P : Instance n),
      (∀ i, ∀ᵐ x ∂P.law i, x≤1) → mu≤P.expectedMaximum → Sstar≤P.totalFirstMoment →
      κ/(1+P.positiveCount)^4≤minimumNormalizedScalarGap P := by
  obtain ⟨a,d,ha,hd,hBoundary⟩ := bounded_boundary_sublevel_localization 1 mu hmu
  let Sstar := max 1 (firstMomentUniformBound a+2)
  let κ := largeFirstMomentGapConstant a d
  have hκ : 0<κ := largeFirstMomentGapConstant_positive ha.1 hd
  refine ⟨Sstar,κ,le_max_left _ _,hκ,?_⟩
  intro n P hcap hMean hS
  have hLarge : firstMomentUniformBound a<P.totalFirstMoment := by
    have h := (le_max_right (1 : ℝ) (firstMomentUniformBound a+2)).trans hS
    linarith only [h]
  obtain ⟨lam,hlam,hEq⟩ := minimumNormalizedScalarGap_attained P (P.integrable_maximum_of_bounded hcap)
  have hOutside (x : ℝ) (hx : x∈Icc (0 : ℝ) 1) (hB : x<a ∨ 1-a<x) :
      d≤normalizedScalarGap P x := by
    have hNot : x∉Icc a (1-a) := by
      simpa only [Set.mem_Icc,not_and_or,not_le] using hB
    exact (hBoundary n P hcap hMean).1 x hx hNot
  have hGap := P.largeFirstMoment_gap_lower_bound_of_outside_slack hcap ha.1 hd hLarge hOutside hlam
  rwa [hEq] at hGap

end ProphetSecretary.Model
