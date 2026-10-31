import ProphetSecretary.Limiting.CountableAtomCDF

/-!
# A pointwise lower bound for symmetric atom prophet gain

Below the atom, the negative CDF contribution is bounded using the deleted
maximum CDF at that atom. Above it, monotonicity gives the corresponding
positive contribution. The two intervals have the same length.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal
namespace ProphetSecretary.Limiting.CountableInstance

lemma maximumCdf_monotone (B : CountableInstance) : Monotone B.maximumCdf := by
  intro s t hst
  exact measureReal_mono (fun _ hv => hv.trans hst)

lemma symmetricAtomPath_cdf_gain_lower (B : CountableInstance) (hZero : B.terminal=0)
    {x h t : ℝ} (hx : 0<x) (hh : 0<h) (ht : 0<t)
    (hNear : |h|≤ individualValueRadius 1 (x/2)) :
    (Ico (x-h) x).indicator
        (fun _ => (B.scaleBand {x} 0).maximumCdf x*
          (Real.exp (-B.intensity.real {x})-Real.exp (-B.intensity.real {x}/2))) t+
      (Ico x (x+h)).indicator
        (fun _ => (B.scaleBand {x} 0).maximumCdf x*(1-Real.exp (-B.intensity.real {x}/2))) t≤
      B.maximumCdf t-(B.symmetricAtomPath hZero x hx h).maximumCdf t := by
  let Q := B.scaleBand {x} 0
  let m := B.intensity.real {x}
  have hm : 0≤m := ENNReal.toReal_nonneg
  have hExp : Real.exp (-m)≤Real.exp (-m/2) := Real.exp_le_exp.mpr (by linarith)
  have hExpOne : Real.exp (-m/2)≤1 := Real.exp_le_one_iff.mpr (by linarith)
  have hFactor := B.maximumCdf_atom_factor hZero x t ht
  have hSplit := B.maximumCdf_symmetricAtomPath hZero hx ht hNear
  rw [hFactor,hSplit]
  change (Ico (x-h) x).indicator (fun _ => Q.maximumCdf x*(Real.exp (-m)-Real.exp (-m/2))) t+
      (Ico x (x+h)).indicator (fun _ => Q.maximumCdf x*(1-Real.exp (-m/2))) t≤
      Q.maximumCdf t*Real.exp (-(m*(if t<x then 1 else 0)))-
        Q.maximumCdf t*Real.exp (-(m/2*(if t<x+h then 1 else 0)+m/2*(if t<x-h then 1 else 0)))
  by_cases htx : t<x
  · have hth : t<x+h := by linarith
    by_cases htl : t<x-h
    · have hnLeft : t∉Ico (x-h) x := by exact fun hz => (not_le_of_gt htl) hz.1
      have hnRight : t∉Ico x (x+h) := by exact fun hz => (not_le_of_gt htx) hz.1
      rw [Set.indicator_of_notMem hnLeft,Set.indicator_of_notMem hnRight,
        if_pos htx,if_pos hth,if_pos htl]
      simp only [mul_one,add_halves,sub_self,add_zero,le_refl]
    · have hLeft : t∈Ico (x-h) x := ⟨not_lt.mp htl,htx⟩
      have hnRight : t∉Ico x (x+h) := by exact fun hz => (not_le_of_gt htx) hz.1
      rw [Set.indicator_of_mem hLeft,Set.indicator_of_notMem hnRight,
        if_pos htx,if_pos hth,if_neg htl]
      simp only [mul_one,mul_zero,add_zero,neg_div]
      have h := mul_le_mul_of_nonpos_right (Q.maximumCdf_monotone htx.le) (sub_nonpos.mpr hExp)
      simpa only [mul_sub,neg_div] using h
  · have hxl : x≤t := not_lt.mp htx
    have htl : ¬t<x-h := by linarith
    have hnLeft : t∉Ico (x-h) x := fun hz => htx hz.2
    by_cases hth : t<x+h
    · have hRight : t∈Ico x (x+h) := ⟨hxl,hth⟩
      rw [Set.indicator_of_notMem hnLeft,Set.indicator_of_mem hRight,
        if_neg htx,if_pos hth,if_neg htl]
      simp only [mul_one,mul_zero,zero_add,add_zero,neg_zero,Real.exp_zero,neg_div]
      have h := mul_le_mul_of_nonneg_right (Q.maximumCdf_monotone hxl) (sub_nonneg.mpr hExpOne)
      simpa only [mul_sub,mul_one,neg_div] using h
    · have hnRight : t∉Ico x (x+h) := fun hz => hth hz.2
      rw [Set.indicator_of_notMem hnLeft,Set.indicator_of_notMem hnRight,
        if_neg htx,if_neg hth,if_neg htl]
      simp only [mul_zero,neg_zero,Real.exp_zero,mul_one,sub_self,add_zero,le_refl]

end ProphetSecretary.Limiting.CountableInstance
