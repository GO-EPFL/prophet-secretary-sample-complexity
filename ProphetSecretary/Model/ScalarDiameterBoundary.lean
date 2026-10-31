import ProphetSecretary.Model.BoundarySublevels
import ProphetSecretary.Reach.Robust

/-!
# Extending the interior scalar diameter estimate to all weights

Uniform endpoint slack supplies one fixed interior interval. The explicit
extension constant is max(K+1,1/d0), independent of the instance size.
This is the last reduction in `updual:modulus`; the interior estimate is
an explicit premise, not an asserted theorem in this file.
-/

open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Model

theorem scalarDiameter_interior_to_global (H : ℝ≥0) (S0 mu : ℝ) (hmu : 0<mu) :
    ∃ δ∈Ioo (0 : ℝ) (1/2), ∀ K : ℝ, 0≤K →
      (∀ (n : ℕ) (P : Instance n), (∀ i, ∀ᵐ x ∂P.law i, x≤(H : ℝ)) →
        P.totalFirstMoment≤S0 → mu≤P.expectedMaximum → ∀ a b : ℝ,
        a∈Icc δ (1-δ) → b∈Icc δ (1-δ) →
        (b-a)^2≤K*(normalizedScalarGap P a+normalizedScalarGap P b)) →
      ∃ Kglobal : ℝ, 0<Kglobal ∧ ∀ (n : ℕ) (P : Instance n),
        (∀ i, ∀ᵐ x ∂P.law i, x≤(H : ℝ)) → P.totalFirstMoment≤S0 → mu≤P.expectedMaximum →
        ∀ a b : ℝ, a∈Icc (0 : ℝ) 1 → b∈Icc (0 : ℝ) 1 →
        (b-a)^2≤Kglobal*(normalizedScalarGap P a+normalizedScalarGap P b) := by
  obtain ⟨δ,d0,hδ,hd0,hSlack⟩ := bounded_boundary_sublevel_localization H mu hmu
  refine ⟨δ,hδ,?_⟩
  intro K hK hInside
  let Kglobal := max (K+1) (1/d0)
  have hKg : 0<Kglobal := lt_of_lt_of_le (by linarith only [hK] : (0 : ℝ)<K+1) (le_max_left _ _)
  refine ⟨Kglobal,hKg,?_⟩
  intro n P hcap hS hMean a b ha hb
  have hP := P.integrable_maximum_of_bounded hcap
  have hGa := normalizedScalarGap_nonnegative P hP ha
  have hGb := normalizedScalarGap_nonnegative P hP hb
  have hSum := add_nonneg hGa hGb
  have hOutside (hLarge : d0≤normalizedScalarGap P a+normalizedScalarGap P b) :
      (b-a)^2≤Kglobal*(normalizedScalarGap P a+normalizedScalarGap P b) := by
    have hSquare : (b-a)^2≤1 := (sq_le_one_iff_abs_le_one _).mpr
      (abs_le.mpr ⟨by linarith only [ha.2,hb.1],by linarith only [ha.1,hb.2]⟩)
    have hScale : 1≤Kglobal*d0 := (div_le_iff₀ hd0).mp (le_max_right (K+1) (1/d0))
    exact hSquare.trans (hScale.trans (mul_le_mul_of_nonneg_left hLarge hKg.le))
  by_cases hA : a∈Icc δ (1-δ)
  · by_cases hB : b∈Icc δ (1-δ)
    · exact (hInside n P hcap hS hMean a b hA hB).trans
        (mul_le_mul_of_nonneg_right (show K≤Kglobal by exact (le_add_of_nonneg_right zero_le_one).trans (le_max_left _ _)) hSum)
    · exact hOutside (by linarith only [(hSlack n P hcap hMean).1 b hb hB,hGa])
  · exact hOutside (by linarith only [(hSlack n P hcap hMean).1 a ha hA,hGb])

end ProphetSecretary.Model
