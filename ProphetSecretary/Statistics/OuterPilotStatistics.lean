import ProphetSecretary.Probability.IndicatorSampleTails
import ProphetSecretary.Probability.FiniteOrderStatistic
import ProphetSecretary.Probability.CDFQuantileBracket
import Mathlib.Algebra.Order.Floor.Ring

/-!
# The actual numerical cap pilot and its confidence event

The pilot statistic is the r-th largest of q=500r numerical sample maxima.
Two fixed-law quantiles are used only in the proof, never supplied to the
algorithm. Closed and strict sample counts treat arbitrary atoms correctly.
Numerical confidence event `upouter:pilot-event` for iid sample maxima.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics
open ProphetSecretary.Probability

lemma outerPilotRank_bound (r : ℕ) : r≤Fintype.card (Fin (500*r)) := by simp;omega

noncomputable def numericalPilotOrder (r : ℕ) (hr : 0<r) (a : Fin (500*r) → ℝ) : ℝ :=
  sampleOrderStatistic r hr (outerPilotRank_bound r) a

lemma measurable_numericalPilotOrder (r : ℕ) (hr : 0<r) : Measurable (numericalPilotOrder r hr) :=
  measurable_sampleOrderStatistic r hr (outerPilotRank_bound r)

lemma probReal_Ioi_eq_one_sub_Iic (μ : Measure ℝ) [IsProbabilityMeasure μ] (b : ℝ) :
    μ.real (Ioi b)=1-μ.real (Iic b) := by
  simpa only [Set.compl_Iic] using probReal_compl_eq_one_sub (μ:=μ) (measurableSet_Iic (a:=b))

lemma probReal_Ici_eq_one_sub_Iio (μ : Measure ℝ) [IsProbabilityMeasure μ] (b : ℝ) :
    μ.real (Ici b)=1-μ.real (Iio b) := by
  simpa only [Set.compl_Iio] using probReal_compl_eq_one_sub (μ:=μ) (measurableSet_Iio (a:=b))

lemma numericalPilot_strict_tail_failure (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℕ) (hr : 0<r) :
    (Measure.pi (fun _ : Fin (500*r) => μ)).real
      {a | 3/1000<μ.real (Ioi (numericalPilotOrder r hr a))}≤Real.exp (-(r:ℝ)/12) := by
  obtain ⟨x,hOpen,hClosed,_⟩ := exists_cdf_probability_bracket μ (q:=(997/1000:ℝ)) (by norm_num)
  have hp : 3/1000≤μ.real (Ici x) := by
    rw [probReal_Ici_eq_one_sub_Iio]
    linarith only [hOpen]
  apply le_trans (b:=(Measure.pi (fun _ : Fin (500*r) => μ)).real {a | sampleEventCount (Ici x) a<r})
  · refine measureReal_mono ?_ (measure_ne_top _ _)
    intro a ha
    change 3/1000<μ.real (Ioi (numericalPilotOrder r hr a)) at ha
    have hBad : μ.real (Iic (numericalPilotOrder r hr a))<997/1000 := by
      rw [probReal_Ioi_eq_one_sub_Iic] at ha
      linarith only [ha]
    have hBx : numericalPilotOrder r hr a<x := by
      by_contra h
      have hMono := measureReal_mono (μ:=μ) (Set.Iic_subset_Iic.mpr (le_of_not_gt h)) (measure_ne_top _ _)
      linarith only [hMono,hClosed,hBad]
    exact (sampleOrderStatistic_lt_iff r hr (outerPilotRank_bound r) a x).mp hBx
  · exact iid_sample_count_lower μ measurableSet_Ici r hp

lemma numericalPilot_closed_tail_failure (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℕ) (hr : 0<r) :
    (Measure.pi (fun _ : Fin (500*r) => μ)).real
      {a | μ.real (Ici (numericalPilotOrder r hr a))<1/1000}≤Real.exp (-(r:ℝ)/6) := by
  obtain ⟨x,hOpen,hClosed,_⟩ := exists_cdf_probability_bracket μ (q:=(999/1000:ℝ)) (by norm_num)
  have hp : μ.real (Ioi x)≤1/1000 := by
    rw [probReal_Ioi_eq_one_sub_Iic]
    linarith only [hClosed]
  apply le_trans (b:=(Measure.pi (fun _ : Fin (500*r) => μ)).real {a | r≤sampleEventCount (Ioi x) a})
  · refine measureReal_mono ?_ (measure_ne_top _ _)
    intro a ha
    change μ.real (Ici (numericalPilotOrder r hr a))<1/1000 at ha
    have hBad : 999/1000<μ.real (Iio (numericalPilotOrder r hr a)) := by
      rw [probReal_Ici_eq_one_sub_Iio] at ha
      linarith only [ha]
    have hxB : x<numericalPilotOrder r hr a := by
      by_contra h
      have hMono := measureReal_mono (μ:=μ) (Set.Iio_subset_Iio (le_of_not_gt h)) (measure_ne_top _ _)
      linarith only [hMono,hOpen,hBad]
    exact (lt_sampleOrderStatistic_iff r hr (outerPilotRank_bound r) a x).mp hxB
  · exact iid_sample_count_upper μ measurableSet_Ioi r hp

noncomputable def numericalPilotSuccess (μ : Measure ℝ) (r : ℕ) (hr : 0<r) : Set (Fin (500*r) → ℝ) :=
  {a | μ.real (Ioi (numericalPilotOrder r hr a))≤3/1000 ∧ 1/1000≤μ.real (Ici (numericalPilotOrder r hr a))}

lemma measurableSet_numericalPilotSuccess (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℕ) (hr : 0<r) :
    MeasurableSet (numericalPilotSuccess μ r hr) := by
  have hStrict : Antitone (fun b : ℝ => μ.real (Ioi b)) := fun a b hab =>
    measureReal_mono (Set.Ioi_subset_Ioi hab) (measure_ne_top _ _)
  have hClosed : Antitone (fun b : ℝ => μ.real (Ici b)) := fun a b hab =>
    measureReal_mono (Set.Ici_subset_Ici.mpr hab) (measure_ne_top _ _)
  exact (measurableSet_le (hStrict.measurable.comp (measurable_numericalPilotOrder r hr)) measurable_const).inter
    (measurableSet_le measurable_const (hClosed.measurable.comp (measurable_numericalPilotOrder r hr)))

lemma numericalPilot_failure_le_two_exp (μ : Measure ℝ) [IsProbabilityMeasure μ] (r : ℕ) (hr : 0<r) :
    (Measure.pi (fun _ : Fin (500*r) => μ)).real (numericalPilotSuccess μ r hr)ᶜ≤2*Real.exp (-(r:ℝ)/12) := by
  have hSet : (numericalPilotSuccess μ r hr)ᶜ=
      {a | 3/1000<μ.real (Ioi (numericalPilotOrder r hr a))}∪
      {a | μ.real (Ici (numericalPilotOrder r hr a))<1/1000} := by
    ext a
    simp only [numericalPilotSuccess,Set.mem_compl_iff,Set.mem_setOf_eq,Set.mem_union,not_and_or,not_le]
  rw [hSet]
  have hUnion := measureReal_union_le (μ:=Measure.pi (fun _ : Fin (500*r) => μ))
    {a | 3/1000<μ.real (Ioi (numericalPilotOrder r hr a))}
    {a | μ.real (Ici (numericalPilotOrder r hr a))<1/1000}
  have h1 := numericalPilot_strict_tail_failure μ r hr
  have h2 := numericalPilot_closed_tail_failure μ r hr
  have hExp : Real.exp (-(r:ℝ)/6)≤Real.exp (-(r:ℝ)/12) :=
    Real.exp_le_exp.mpr (by nlinarith only [(Nat.cast_nonneg r : (0:ℝ)≤(r:ℝ))])
  linarith only [hUnion,h1,h2,hExp]

noncomputable def outerPilotRank (m : ℕ) : ℕ := ⌈12*Real.log (2*(m:ℝ))⌉₊
noncomputable def outerPilotRounds (m : ℕ) : ℕ := 500*outerPilotRank m

lemma outerPilotRank_pos {m : ℕ} (hm : 1≤m) : 0<outerPilotRank m := by
  apply Nat.one_le_ceil_iff.mpr
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm
  exact mul_pos (by norm_num) (Real.log_pos (by linarith only [hmR]))

lemma outerPilotRounds_div (m : ℕ) : outerPilotRounds m/500=outerPilotRank m := by simp [outerPilotRounds]

/-- Source pilot confidence 1−1/m, for arbitrary real laws and their atoms. -/
theorem outerPilot_failure_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] {m : ℕ} (hm : 1≤m) :
    (Measure.pi (fun _ : Fin (outerPilotRounds m) => μ)).real
      (numericalPilotSuccess μ (outerPilotRank m) (outerPilotRank_pos hm))ᶜ≤1/(m:ℝ) := by
  have h := numericalPilot_failure_le_two_exp μ (outerPilotRank m) (outerPilotRank_pos hm)
  have hCeil : 12*Real.log (2*(m:ℝ))≤(outerPilotRank m:ℝ) := Nat.le_ceil _
  have hmR : (0:ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hExp : Real.exp (-(outerPilotRank m:ℝ)/12)≤Real.exp (-Real.log (2*(m:ℝ))) :=
    Real.exp_le_exp.mpr (by linarith only [hCeil])
  have hScale : 2*Real.exp (-Real.log (2*(m:ℝ)))=1/(m:ℝ) := by
    rw [Real.exp_neg,Real.exp_log (by positivity : (0:ℝ)<2*(m:ℝ))]
    field_simp
  exact h.trans ((mul_le_mul_of_nonneg_left hExp (by norm_num)).trans_eq hScale)

theorem outerPilot_success_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] {m : ℕ} (hm : 1≤m) :
    1-1/(m:ℝ)≤(Measure.pi (fun _ : Fin (outerPilotRounds m) => μ)).real
      (numericalPilotSuccess μ (outerPilotRank m) (outerPilotRank_pos hm)) := by
  have h : (Measure.pi (fun _ : Fin (500*outerPilotRank m) => μ)).real
      (numericalPilotSuccess μ (outerPilotRank m) (outerPilotRank_pos hm))ᶜ≤1/(m:ℝ) := outerPilot_failure_probability μ hm
  rw [probReal_compl_eq_one_sub (measurableSet_numericalPilotSuccess μ _ _)] at h
  change 1-1/(m:ℝ)≤(Measure.pi (fun _ : Fin (500*outerPilotRank m) => μ)).real
    (numericalPilotSuccess μ (outerPilotRank m) (outerPilotRank_pos hm))
  linarith only [h]

end ProphetSecretary.Statistics
