import ProphetSecretary.Model.OuterRetention

/-!
# Deterministic scale consequences of the outer cap-pilot event

Once a positive numerical pilot maximum B obeys its two population tail bounds,
H=1000B has exactly the cap-mean and cap-scale constants in `upouter:cap-pilot`.
The bounds apply pointwise to each realized cutoff satisfying the two tails.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Model.Instance
variable {n : ℕ}

noncomputable def outerPilotCap (B : ℝ≥0) : ℝ≥0 := 1000*B

lemma capPilot_maximum_lower (B : ℝ≥0) (z : ℝ) :
    (B:ℝ)*(if (B:ℝ)≤z then 1 else 0)≤min (max 0 z) (outerPilotCap B:ℝ) := by
  have hB0 : (0:ℝ)≤B := B.property
  have hH : (B:ℝ)≤(outerPilotCap B:ℝ) := by
    change (B:ℝ)≤1000*(B:ℝ)
    linarith only [hB0]
  split_ifs with h
  · rw [mul_one]
    exact le_min (h.trans (le_max_right _ _)) hH
  · rw [mul_zero]
    exact le_min (le_max_left _ _) (outerPilotCap B).property

lemma capPilot_maximum_upper (B : ℝ≥0) (z : ℝ) :
    min z (outerPilotCap B:ℝ)≤B+(outerPilotCap B:ℝ)*(if (B:ℝ)<z then 1 else 0) := by
  split_ifs with h
  · rw [mul_one]
    exact (min_le_right _ _).trans (le_add_of_nonneg_left B.property)
  · rw [mul_zero,add_zero]
    exact (min_le_left _ _).trans (le_of_not_gt h)

/-- The two moment bounds used by the pilot scale estimate. -/
lemma capPilot_expectedMaximum_sandwich (P : Instance n) (hP : Integrable maximum P.valuesLaw) (B : ℝ≥0) :
    (B:ℝ)*P.valuesLaw.real {x | (B:ℝ)≤maximum x}≤(P.cap (outerPilotCap B)).expectedMaximum ∧
    (P.cap (outerPilotCap B)).expectedMaximum≤B+(outerPilotCap B:ℝ)*P.valuesLaw.real {x | (B:ℝ)<maximum x} := by
  let A := {x : Fin n → ℝ | (B:ℝ)≤maximum x}
  let D := {x : Fin n → ℝ | (B:ℝ)<maximum x}
  have hA : MeasurableSet A := measurableSet_le measurable_const measurable_maximum
  have hD : MeasurableSet D := measurableSet_lt measurable_const measurable_maximum
  have hAI : Integrable (A.indicator (fun _ => (1:ℝ))) P.valuesLaw := (integrable_const 1).indicator hA
  have hDI : Integrable (D.indicator (fun _ => (1:ℝ))) P.valuesLaw := (integrable_const 1).indicator hD
  have hCapI : Integrable (fun x => min (maximum x) (outerPilotCap B:ℝ)) P.valuesLaw := hP.inf (integrable_const _)
  simp_rw [P.cap_expectedMaximum]
  constructor
  · have h := integral_mono (hAI.const_mul (B:ℝ)) hCapI (fun x => by
      have hPoint := capPilot_maximum_lower B (maximum x)
      simpa only [A,Set.indicator_apply,Set.mem_setOf_eq,max_eq_right (maximum_nonnegative _)] using hPoint)
    simpa only [integral_const_mul,integral_indicator_const (1:ℝ) hA,smul_eq_mul,mul_one,A] using h
  · have hUI : Integrable (fun x => (B:ℝ)+(outerPilotCap B:ℝ)*D.indicator (fun _ => (1:ℝ)) x) P.valuesLaw :=
      (integrable_const (B:ℝ)).add (hDI.const_mul (outerPilotCap B:ℝ))
    have h := integral_mono hCapI hUI (fun x => by
      change min (maximum x) (outerPilotCap B:ℝ)≤(B:ℝ)+(outerPilotCap B:ℝ)*D.indicator (fun _ => (1:ℝ)) x
      simpa only [D,Set.indicator_apply,Set.mem_setOf_eq] using capPilot_maximum_upper B (maximum x))
    simpa only [integral_add (integrable_const (B:ℝ)) (hDI.const_mul (outerPilotCap B:ℝ)),integral_const,probReal_univ,one_smul,
      integral_const_mul,integral_indicator_const (1:ℝ) hD,smul_eq_mul,mul_one,one_mul,D] using h

/-- `upouter:capmean` and `upouter:capscale`, conditional only on the explicitly
stated realized pilot event. The hypotheses are the two population tail bounds at the realized pilot cutoff. -/
theorem capPilot_scale_bounds (P : Instance n) (hP : Integrable maximum P.valuesLaw)
    (B : ℝ≥0) (hB : 0<(B:ℝ))
    (hStrict : P.valuesLaw.real {x | (B:ℝ)<maximum x}≤3/1000)
    (hClosed : 1/1000≤P.valuesLaw.real {x | (B:ℝ)≤maximum x}) :
    1/1000000≤(P.cap (outerPilotCap B)).expectedMaximum/(outerPilotCap B:ℝ) ∧
    (P.cap (outerPilotCap B)).expectedMaximum/(outerPilotCap B:ℝ)≤1/250 ∧
    P.valuesLaw.real {x | (outerPilotCap B:ℝ)≤maximum x}≤3/1000 ∧
    (outerPilotCap B:ℝ)≤1000000*(P.cap (outerPilotCap B)).expectedMaximum ∧
    1000000*(P.cap (outerPilotCap B)).expectedMaximum≤1000000*P.expectedMaximum := by
  have hH : (outerPilotCap B:ℝ)=1000*(B:ℝ) := rfl
  have hH0 : 0<(outerPilotCap B:ℝ) := by rw [hH];positivity
  have hSand := P.capPilot_expectedMaximum_sandwich hP B
  have hLo := mul_le_mul_of_nonneg_left hClosed B.property
  have hUp := mul_le_mul_of_nonneg_left hStrict hH0.le
  have hLower : (outerPilotCap B:ℝ)/1000000≤(P.cap (outerPilotCap B)).expectedMaximum := by
    calc
      (outerPilotCap B:ℝ)/1000000=(B:ℝ)*(1/1000) := by rw [hH];ring
      _≤(B:ℝ)*P.valuesLaw.real {x | (B:ℝ)≤maximum x} := hLo
      _≤(P.cap (outerPilotCap B)).expectedMaximum := hSand.1
  refine ⟨(le_div_iff₀ hH0).mpr (by nlinarith only [hLower]),(div_le_iff₀ hH0).mpr ?_,?_,?_,?_⟩
  · calc
      (P.cap (outerPilotCap B)).expectedMaximum≤(B:ℝ)+(outerPilotCap B:ℝ)*P.valuesLaw.real {x | (B:ℝ)<maximum x} := hSand.2
      _≤(B:ℝ)+(outerPilotCap B:ℝ)*(3/1000) := add_le_add (le_refl (B:ℝ)) hUp
      _=(1/250:ℝ)*(outerPilotCap B:ℝ) := by rw [hH];ring
  · apply le_trans (b:=P.valuesLaw.real {x | (B:ℝ)<maximum x}) _ hStrict
    refine measureReal_mono ?_ (measure_ne_top _ _)
    intro x hx
    change (B:ℝ)<maximum x
    change (outerPilotCap B:ℝ)≤maximum x at hx
    rw [hH] at hx
    nlinarith only [hx,hB]
  · nlinarith only [hLower]
  · exact mul_le_mul_of_nonneg_left (P.cap_expectedMaximum_le (outerPilotCap B) hP) (by norm_num)

end ProphetSecretary.Model.Instance
