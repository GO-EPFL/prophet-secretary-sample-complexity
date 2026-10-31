import ProphetSecretary.Limiting.IncreasingRestrictionIndependence

/-!
# Independence of the retained high cloud and the entire omitted low cloud

Lower windows increase toward the reserve. Their counting masses may tend
to infinity; no finite-mass or `toReal` argument is used in that last limit.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Limiting.CountableInstance

variable (B : CountableInstance)

theorem high_low_positive_independent {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    IndepFun (fun ω => (bandCountingMeasure ω).restrict (univ ×ˢ Ioi b))
      (fun ω => (bandCountingMeasure ω).restrict (univ ×ˢ Ioc (B.terminal : ℝ) b))
      B.bandConfigurationsLaw := by
  let a : ℝ := B.terminal
  let c := fun n : ℕ => a+(b-a)/((n : ℝ)+1)
  let W := fun n : ℕ => (univ ×ˢ Ioc (c n) b : Set Point)
  have hGap : 0 < b-a := sub_pos.mpr hb
  have hc (n : ℕ) : a < c n := by
    dsimp only [c]
    exact lt_add_of_pos_right a (div_pos hGap (by positivity))
  have hcb (n : ℕ) : c n ≤ b := by
    dsimp only [c]
    calc
      a+(b-a)/((n : ℝ)+1) ≤ a+(b-a) := add_le_add le_rfl (div_le_self hGap.le (by have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n; linarith))
      _ = b := by ring
  have hAnti : Antitone c := by
    intro i j hij
    dsimp only [c]
    apply add_le_add (le_refl a)
    apply div_le_div_of_nonneg_left hGap.le (by positivity)
    exact_mod_cast Nat.add_le_add_right hij 1
  have hT : Tendsto c atTop (𝓝 a) := by
    have h := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (b-a)).const_add a
    simpa only [c,mul_one_div,mul_zero,add_zero] using h
  have hMono : Monotone W := by
    intro i j hij p hp
    exact ⟨hp.1,(hAnti hij).trans_lt hp.2.1,hp.2.2⟩
  have hUnion : (⋃ n, W n) = (univ ×ˢ Ioc a b : Set Point) := by
    ext p
    simp only [W,mem_iUnion,mem_prod,mem_univ,true_and,mem_Ioc]
    constructor
    · rintro ⟨n,hn,hb'⟩
      exact ⟨(hc n).trans hn,hb'⟩
    · intro hp
      obtain ⟨n,hn⟩ := (hT.eventually (gt_mem_nhds hp.1)).exists
      exact ⟨n,hn,hp.2⟩
  have hHigh : Measurable (fun ω => (bandCountingMeasure ω).restrict (univ ×ˢ Ioi b)) :=
    (measurable_restrict_pointMeasure (MeasurableSet.univ.prod measurableSet_Ioi)).comp
      measurable_bandCountingMeasure
  have hInd := indepFun_restrict_iUnion measurable_bandCountingMeasure hHigh W
    (fun _ => MeasurableSet.univ.prod measurableSet_Ioc) hMono
    (fun n => (B.high_low_window_independent (hc n) (hcb n)).symm)
  rw [hUnion] at hInd
  exact hInd.symm

end ProphetSecretary.Limiting.CountableInstance
