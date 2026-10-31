import Mathlib.Probability.CDF
import Mathlib.Topology.Order.Monotone

/-!
# A real probability CDF brackets every interior probability

Right continuity at the infimum of a CDF superlevel set gives a numerical
threshold whose open and closed lower probabilities straddle the chosen level.
This permits atom jumps; no continuity or density of the law is assumed.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace ProphetSecretary.Probability

/-- The lower probability may jump over q at x, but cannot skip the interval
between its open and closed CDF values. -/
theorem exists_cdf_probability_bracket (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {q : ℝ} (hq : q∈Ioo (0:ℝ) 1) :
    ∃ x : ℝ, μ.real (Iio x)≤q ∧ q≤μ.real (Iic x) ∧ ∀ y<x, cdf μ y<q := by
  let F := cdf μ
  let A := {x : ℝ | q≤F x}
  have hLoEvent : ∀ᶠ x : ℝ in atBot, F x<q :=
    (tendsto_cdf_atBot μ).eventually (gt_mem_nhds hq.1)
  have hHiEvent : ∀ᶠ x : ℝ in atTop, q<F x :=
    (tendsto_cdf_atTop μ).eventually (lt_mem_nhds hq.2)
  obtain ⟨l,hl⟩ := hLoEvent.exists
  obtain ⟨u,hu⟩ := hHiEvent.exists
  have hA : A.Nonempty := ⟨u,hu.le⟩
  have hAbdd : BddBelow A := by
    refine ⟨l,?_⟩
    intro x hx
    by_contra h
    have hxL : x<l := lt_of_not_ge h
    have hFx := F.mono hxL.le
    exact (not_le_of_gt hl) ((hx.trans hFx))
  let x := sInf A
  have hBefore (y : ℝ) (hy : y<x) : F y<q := by
    by_contra h
    have hyA : y∈A := le_of_not_gt h
    have hInf := csInf_le hAbdd hyA
    exact (not_le_of_gt hy) hInf
  have hCont : ContinuousWithinAt F A x :=
    (F.right_continuous x).mono (fun y hy => csInf_le hAbdd hy)
  have hMap : F x=sInf (F '' A) :=
    MonotoneOn.map_csInf_of_continuousWithinAt hCont (F.mono.monotoneOn A) hA hAbdd
  have hAt : q≤F x := by
    rw [hMap]
    exact le_csInf (hA.image F) (fun z hz => by rcases hz with ⟨y,hy,rfl⟩;exact hy)
  have hLeft : Function.leftLim F x≤q := by
    rw [F.mono.leftLim_eq_sSup]
    apply csSup_le
    · exact ⟨F (x-1),⟨x-1,by simp,rfl⟩⟩
    · rintro z ⟨y,hy,rfl⟩
      exact (hBefore y hy).le
  have hLeft0 : 0≤Function.leftLim F x :=
    (cdf_nonneg μ (x-1)).trans (F.mono.le_leftLim (by linarith : x-1<x))
  have hOpen : μ.real (Iio x)=Function.leftLim F x := by
    change (μ (Iio x)).toReal=Function.leftLim F x
    conv_lhs => rw [←measure_cdf μ]
    rw [(cdf μ).measure_Iio (tendsto_cdf_atBot μ),sub_zero,ENNReal.toReal_ofReal hLeft0]
  refine ⟨x,?_,?_,hBefore⟩
  · rwa [hOpen]
  · simpa only [F,cdf_eq_real] using hAt

end ProphetSecretary.Probability
