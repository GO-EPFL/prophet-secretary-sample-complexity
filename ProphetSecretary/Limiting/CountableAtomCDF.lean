import ProphetSecretary.Limiting.CountableAtomValuePath
import ProphetSecretary.Limiting.CountableBandBenchmarkSecant

/-!
# Maximum distribution when a Poisson atom splits symmetrically

The remaining cloud has its actual deleted-atom distribution. Independent
Poisson half-atoms give explicit exponential factors at the three relevant
mark levels, with all real tail masses finite.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal BigOperators
namespace ProphetSecretary.Limiting.CountableInstance

lemma intensity_atom_finite (B : CountableInstance) (hZero : B.terminal=0)
    {x : ℝ} (hx : 0<x) : B.intensity {x}<⊤ := by
  apply lt_of_le_of_lt (measure_mono ?_) (B.intensity_tail_finite (x/2) (by simpa only [hZero,NNReal.coe_zero] using half_pos hx))
  intro y hy
  have hyx : y=x := mem_singleton_iff.mp hy
  rw [hyx]
  exact half_lt_self hx

private lemma half_atom_tail_real (μ : Measure ℝ) (x y t : ℝ) :
    ((μ {x}/2) • Measure.dirac y).real (Ioi t)=
      μ.real {x}/2*(if t<y then 1 else 0) := by
  by_cases hty : t<y
  · simp [measureReal_def,Measure.smul_apply,Measure.dirac_apply',hty,ENNReal.toReal_div]
  · simp [measureReal_def,Measure.smul_apply,Measure.dirac_apply',hty]

lemma symmetricAtomPath_intensity_tail_real (B : CountableInstance) (hZero : B.terminal=0)
    {x h t : ℝ} (hx : 0<x) (ht : 0<t) (hNear : |h|≤ individualValueRadius 1 (x/2)) :
    (B.symmetricAtomPath hZero x hx h).intensity.real (Ioi t)=
      B.intensity.real (Ioi t∩{x}ᶜ)+B.intensity.real {x}/2*(if t<x+h then 1 else 0)+
        B.intensity.real {x}/2*(if t<x-h then 1 else 0) := by
  have hAtom := (B.intensity_atom_finite hZero hx).ne
  have hTail := (B.intensity_tail_finite t (by simpa only [hZero,NNReal.coe_zero] using ht)).ne
  have hComp : (B.intensity.restrict {x}ᶜ) (Ioi t)≠⊤ := by
    rw [Measure.restrict_apply measurableSet_Ioi]
    exact ne_top_of_le_ne_top hTail (measure_mono inter_subset_left)
  have hDirac (y : ℝ) : ((B.intensity {x}/2) • Measure.dirac y) (Ioi t)≠⊤ := by
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_ne_top (ENNReal.div_ne_top hAtom (by norm_num)) (measure_ne_top _ _)
  rw [B.symmetricAtomPath_intensity hZero x hx hNear,
    measureReal_add_apply (by rw [Measure.add_apply]; exact ENNReal.add_ne_top.mpr ⟨hComp,hDirac _⟩) (hDirac _),
    measureReal_add_apply hComp (hDirac _),measureReal_restrict_apply measurableSet_Ioi,
    half_atom_tail_real,half_atom_tail_real]

lemma maximumCdf_symmetricAtomPath (B : CountableInstance) (hZero : B.terminal=0)
    {x h t : ℝ} (hx : 0<x) (ht : 0<t) (hNear : |h|≤ individualValueRadius 1 (x/2)) :
    (B.symmetricAtomPath hZero x hx h).maximumCdf t=
      (B.scaleBand {x} 0).maximumCdf t*
        Real.exp (-(B.intensity.real {x}/2*(if t<x+h then 1 else 0)+
          B.intensity.real {x}/2*(if t<x-h then 1 else 0))) := by
  have hNew := (B.symmetricAtomPath hZero x hx h).maximum_probability_Iic ht
  change ((B.symmetricAtomPath hZero x hx h).valueLaw
    {v | (B.symmetricAtomPath hZero x hx h).maximum v≤t})=_ at hNew
  change ((B.symmetricAtomPath hZero x hx h).valueLaw
    {v | (B.symmetricAtomPath hZero x hx h).maximum v≤t}).toReal=_
  rw [hNew,ENNReal.toReal_mul,ENNReal.toReal_ofReal (Real.exp_pos _).le,
    B.symmetricAtomPath_intensity_tail_real hZero hx ht hNear]
  have hQ := B.maximumCdf_scaleBand (measurableSet_singleton x) 0
    (by simpa only [hZero,NNReal.coe_zero] using ht)
  simp only [NNReal.coe_zero,zero_mul,add_zero] at hQ
  rw [hQ]
  have hExp : Real.exp (-(B.intensity.real (Ioi t∩{x}ᶜ)+
      B.intensity.real {x}/2*(if t<x+h then 1 else 0)+B.intensity.real {x}/2*(if t<x-h then 1 else 0)))=
      Real.exp (-B.intensity.real (Ioi t∩{x}ᶜ))*
        Real.exp (-(B.intensity.real {x}/2*(if t<x+h then 1 else 0)+B.intensity.real {x}/2*(if t<x-h then 1 else 0))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hExp]
  change Real.exp (-B.intensity.real (Ioi t∩{x}ᶜ))*
    Real.exp (-(B.intensity.real {x}/2*(if t<x+h then 1 else 0)+
      B.intensity.real {x}/2*(if t<x-h then 1 else 0)))*
    (∏' i, (B.individuals i : Measure ℝ) (Iic t)).toReal=_
  ring

lemma maximumCdf_atom_factor (B : CountableInstance) (hZero : B.terminal=0)
    (x t : ℝ) (ht : 0<t) :
    B.maximumCdf t=(B.scaleBand {x} 0).maximumCdf t*
      Real.exp (-(B.intensity.real {x}*(if t<x then 1 else 0))) := by
  have hOne := B.maximumCdf_scaleBand (measurableSet_singleton x) 1
    (by simpa only [hZero,NNReal.coe_zero] using ht)
  rw [B.scaleBand_one] at hOne
  have hZeroCDF := B.maximumCdf_scaleBand (measurableSet_singleton x) 0
    (by simpa only [hZero,NNReal.coe_zero] using ht)
  simp only [NNReal.coe_zero,NNReal.coe_one,zero_mul,one_mul,add_zero] at hOne hZeroCDF
  have hBand : B.intensity.real (Ioi t∩{x})=B.intensity.real {x}*(if t<x then 1 else 0) := by
    by_cases htx : t<x
    · have he : Ioi t∩{x}=({x} : Set ℝ) := by
        ext z
        simp only [mem_inter_iff,mem_Ioi,mem_singleton_iff]
        constructor
        · exact And.right
        · rintro rfl
          exact ⟨htx,rfl⟩
      rw [he,if_pos htx,mul_one]
    · have he : Ioi t∩{x}=(∅ : Set ℝ) := by
        ext z
        simp only [mem_inter_iff,mem_Ioi,mem_singleton_iff,mem_empty_iff_false]
        constructor
        · rintro ⟨hz,rfl⟩
          exact htx hz
        · exact False.elim
      rw [he,if_neg htx,mul_zero,measureReal_empty]
  rw [hOne,hZeroCDF,hBand,neg_add,Real.exp_add]
  ring

end ProphetSecretary.Limiting.CountableInstance
