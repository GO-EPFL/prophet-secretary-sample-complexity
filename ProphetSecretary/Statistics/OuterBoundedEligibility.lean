import ProphetSecretary.Model.OuterMeshLaw
import ProphetSecretary.Model.OuterPilotScale

/-!
# Eligibility of the outer transformed instance

The cap-pilot inequalities and a sufficiently fine mesh imply the normalized
mean interval of `upouter:interface`. Capping and rounding do not increase the
positive tail count, and the numerical grid includes both endpoints regardless
of their population probabilities.
-/

open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Model.Instance
variable {n : ℕ}

lemma outerTransformedInstance_mean_eligible (P : Instance n) (m : ℕ) (hm : 2000000≤m)
    (t : ℝ × ℝ) (H : ℝ≥0) (hH : (0:ℝ)<H)
    (hLo : 1/1000000≤((P.retainedAtTag t).cap H).expectedMaximum/(H:ℝ))
    (hHi : ((P.retainedAtTag t).cap H).expectedMaximum/(H:ℝ)≤1/250) :
    1/10000000≤(P.outerTransformedInstance m (by omega) t H).expectedMaximum ∧
      (P.outerTransformedInstance m (by omega) t H).expectedMaximum≤1/80 := by
  have hRound := P.outerTransformedInstance_mean_bounds m (by omega) t H hH
  have hmR : (2000000:ℝ)≤m := by exact_mod_cast hm
  have hInv : 1/(m:ℝ)≤1/2000000 := by
    apply (div_le_div_iff₀ (show (0:ℝ)<m by positivity) (by norm_num : (0:ℝ)<2000000)).mpr
    nlinarith only [hmR]
  constructor <;> linarith

/-- Every bounded-interface hypothesis for the actual positive-pilot branch. -/
theorem outerTransformedInstance_pilot_eligible (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (m : ℕ) (hm : 2000000≤m)
    (t : ℝ × ℝ) (B : ℝ≥0) (hB : (0:ℝ)<B)
    (hStrict : (P.retainedAtTag t).valuesLaw.real {x | (B:ℝ)<Instance.maximum x}≤3/1000)
    (hClosed : 1/1000≤(P.retainedAtTag t).valuesLaw.real {x | (B:ℝ)≤Instance.maximum x})
    (hCount : (P.retainedAtTag t).positiveCount≤2*Real.log (m:ℝ)) :
    let Q := P.outerTransformedInstance m (by omega) t (outerPilotCap B)
    (1/10000000≤Q.expectedMaximum ∧ Q.expectedMaximum≤1/80) ∧
    Q.positiveCount≤2*Real.log (m:ℝ) ∧
    (∀ i, ∀ᵐ x ∂Q.law i, x∈meshGrid 1 m) ∧
    (∀ i, ∀ᵐ x ∂Q.law i, x≤1) ∧
    (0:ℝ)∈meshGrid 1 m ∧ (1:ℝ)∈meshGrid 1 m := by
  have hH : (0:ℝ)<(outerPilotCap B:ℝ) := by change 0<1000*(B:ℝ);positivity
  have hPilot := (P.retainedAtTag t).capPilot_scale_bounds (P.retainedAtTag_integrable_maximum hP t) B hB hStrict hClosed
  exact ⟨outerTransformedInstance_mean_eligible P m hm t (outerPilotCap B) hH hPilot.1 hPilot.2.1,
    (P.outerTransformedInstance_positiveCount_le m (by omega) t hH).trans hCount,
    P.outerTransformedInstance_grid m (by omega) t (outerPilotCap B),
    P.outerTransformedInstance_bounded m (by omega) t (outerPilotCap B),
    zero_mem_meshGrid 1 m,cap_mem_meshGrid 1 m (by omega)⟩

end ProphetSecretary.Statistics
