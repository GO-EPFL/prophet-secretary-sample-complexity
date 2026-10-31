import ProphetSecretary.Probability.RandomMeasureLaw
import ProphetSecretary.Probability.FiniteCoordinateIndependence

/-!
# Independence of random measures from finite evaluations

Evaluations take values in the extended nonnegative reals. This criterion
therefore also applies when an omitted low-mark configuration has infinite
total intensity, without replacing infinite masses by `toReal`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProphetSecretary.Probability

theorem indepFun_randomMeasures_of_finite_evaluations {Ω A B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → Measure A} {Y : Ω → Measure B}
    (hX : Measurable X) (hY : Measurable Y)
    (h : ∀ (I : Finset (MeasurableRegion A)) (J : Finset (MeasurableRegion B)),
      IndepFun (fun ω => fun S : I => X ω S.1.1) (fun ω => fun T : J => Y ω T.1.1) P) :
    IndepFun X Y P := by
  have hEX := measurable_measureEvaluations.comp hX
  have hEY := measurable_measureEvaluations.comp hY
  have hi := indepFun_of_finite_coordinates hEX hEY h
  have hSX : MeasurableSpace.comap (measureEvaluations ∘ X) inferInstance =
      MeasurableSpace.comap X inferInstance := by
    rw [← MeasurableSpace.comap_comp,measureEvaluations_comap]
  have hSY : MeasurableSpace.comap (measureEvaluations ∘ Y) inferInstance =
      MeasurableSpace.comap Y inferInstance := by
    rw [← MeasurableSpace.comap_comp,measureEvaluations_comap]
  have hind := (IndepFun_iff_Indep _ _ P).mp hi
  rw [hSX,hSY] at hind
  exact (IndepFun_iff_Indep X Y P).mpr hind

lemma measure_evaluations_ofReal_real_ae {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    {P : Measure Ω} {X : Ω → Measure A} (hX : ∀ᵐ ω ∂P, X ω Set.univ < ⊤)
    (I : Finset (MeasurableRegion A)) :
    (fun ω => fun S : I => ENNReal.ofReal ((X ω).real S.1.1)) =ᵐ[P]
      (fun ω => fun S : I => X ω S.1.1) := by
  filter_upwards [hX] with ω hω
  funext S
  exact ENNReal.ofReal_toReal (((measure_mono (Set.subset_univ S.1.1)).trans_lt hω).ne)

/-- For almost surely finite random measures the real evaluation criterion is
also valid; the actual finiteness hypotheses discharge every reconstruction. -/
theorem indepFun_finiteRandomMeasures_of_finite_real_evaluations {Ω A B : Type*}
    [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → Measure A} {Y : Ω → Measure B}
    (hX : Measurable X) (hY : Measurable Y)
    (hXF : ∀ᵐ ω ∂P, X ω Set.univ < ⊤) (hYF : ∀ᵐ ω ∂P, Y ω Set.univ < ⊤)
    (h : ∀ (I : Finset (MeasurableRegion A)) (J : Finset (MeasurableRegion B)),
      IndepFun (fun ω => fun S : I => (X ω).real S.1.1) (fun ω => fun T : J => (Y ω).real T.1.1) P) :
    IndepFun X Y P := by
  apply indepFun_randomMeasures_of_finite_evaluations hX hY
  intro I J
  have hI : Measurable (fun x : I → ℝ => fun S : I => ENNReal.ofReal (x S)) :=
    measurable_pi_lambda _ (fun S => (measurable_pi_apply S).ennreal_ofReal)
  have hJ : Measurable (fun x : J → ℝ => fun S : J => ENNReal.ofReal (x S)) :=
    measurable_pi_lambda _ (fun S => (measurable_pi_apply S).ennreal_ofReal)
  exact ((h I J).comp hI hJ).congr
    (measure_evaluations_ofReal_real_ae hXF I) (measure_evaluations_ofReal_real_ae hYF J)

end ProphetSecretary.Probability
