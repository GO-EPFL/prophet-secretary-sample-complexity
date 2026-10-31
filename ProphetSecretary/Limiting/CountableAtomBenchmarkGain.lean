import ProphetSecretary.Limiting.CountableAtomCDFGain

/-!
# Quantitative prophet gain from splitting a Poisson atom

The CDF comparison is integrated on the common enlarged cap. Two adjacent
intervals of length h give the strictly positive coefficient
F(x)(1-exp(-mu{x}/2))^2 whenever the atom can be a maximum.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal
namespace ProphetSecretary.Limiting.CountableInstance

lemma symmetricAtomPath_expectedMaximum_gain (B : CountableInstance) (hZero : B.terminal=0)
    {x h : ℝ} (hx : 0<x) (hxCap : x≤(B.cap : ℝ)) (hh : 0<h) (hhx : h<x) (hh1 : h≤1)
    (hNear : |h|≤ individualValueRadius 1 (x/2)) :
    B.expectedMaximum+h*(B.scaleBand {x} 0).maximumCdf x*
        (1-Real.exp (-B.intensity.real {x}/2))^2≤
      (B.symmetricAtomPath hZero x hx h).expectedMaximum := by
  let P := B.symmetricAtomPath hZero x hx h
  let Q := B.scaleBand {x} 0
  let H := B.cap+1
  let ν := volume.restrict (Ioc (0 : ℝ) H)
  let l := Q.maximumCdf x*(Real.exp (-B.intensity.real {x})-Real.exp (-B.intensity.real {x}/2))
  let r := Q.maximumCdf x*(1-Real.exp (-B.intensity.real {x}/2))
  let L := (Ico (x-h) x).indicator (fun _ : ℝ => l)
  let R := (Ico x (x+h)).indicator (fun _ : ℝ => r)
  have hL : Integrable L ν := (integrable_const l).indicator measurableSet_Ico
  have hR : Integrable R ν := (integrable_const r).indicator measurableSet_Ico
  have hBaseI : Integrable (fun t => 1-B.maximumCdf t) ν := B.integrable_one_sub_maximumCdf H
  have hNewI : Integrable (fun t => 1-P.maximumCdf t) ν := P.integrable_one_sub_maximumCdf H
  have hLeftSubset : Ico (x-h) x⊆Ioc (0 : ℝ) H := by
    intro t ht
    dsimp only [H]
    simp only [NNReal.coe_add,NNReal.coe_one]
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hRightSubset : Ico x (x+h)⊆Ioc (0 : ℝ) H := by
    intro t ht
    dsimp only [H]
    simp only [NNReal.coe_add,NNReal.coe_one]
    exact ⟨hx.trans_le ht.1,by linarith [ht.2]⟩
  have hVolumeL : ν.real (Ico (x-h) x)=h := by
    rw [measureReal_restrict_apply measurableSet_Ico,inter_eq_left.mpr hLeftSubset,
      Real.volume_real_Ico_of_le (by linarith : x-h≤x)]
    ring
  have hVolumeR : ν.real (Ico x (x+h))=h := by
    rw [measureReal_restrict_apply measurableSet_Ico,inter_eq_left.mpr hRightSubset,
      Real.volume_real_Ico_of_le (by linarith : x≤x+h)]
    ring
  have hPoint : ∀ᵐ t ∂ν, L t+R t≤(1-P.maximumCdf t)-(1-B.maximumCdf t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have h := B.symmetricAtomPath_cdf_gain_lower hZero hx hh ht.1 hNear
    change L t+R t≤B.maximumCdf t-P.maximumCdf t at h
    linarith only [h]
  have hI := integral_mono_ae (hL.add hR) (hNewI.sub hBaseI) hPoint
  change (∫ t, L t+R t ∂ν)≤∫ t, (1-P.maximumCdf t)-(1-B.maximumCdf t) ∂ν at hI
  have hMeanL : (∫ t, L t ∂ν)=h*l := by
    dsimp only [L]
    rw [integral_indicator_const _ measurableSet_Ico,smul_eq_mul,hVolumeL]
  have hMeanR : (∫ t, R t ∂ν)=h*r := by
    dsimp only [R]
    rw [integral_indicator_const _ measurableSet_Ico,smul_eq_mul,hVolumeR]
  rw [integral_add hL hR,hMeanL,hMeanR,integral_sub hNewI hBaseI] at hI
  have hBase : B.expectedMaximum=∫ t, 1-B.maximumCdf t ∂ν :=
    (B.withCap H (by dsimp only [H]; simp)).expectedMaximum_eq_integral_one_sub_maximumCdf
  have hNew : P.expectedMaximum=∫ t, 1-P.maximumCdf t ∂ν :=
    P.expectedMaximum_eq_integral_one_sub_maximumCdf
  rw [← hBase,← hNew] at hI
  have hExp : (Real.exp (-B.intensity.real {x}/2))^2=Real.exp (-B.intensity.real {x}) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  dsimp only [l,r] at hI
  change B.expectedMaximum+h*Q.maximumCdf x*(1-Real.exp (-B.intensity.real {x}/2))^2≤P.expectedMaximum
  have hRewrite : h*Q.maximumCdf x*(1-Real.exp (-B.intensity.real {x}/2))^2=
      h*(Q.maximumCdf x*(Real.exp (-B.intensity.real {x})-Real.exp (-B.intensity.real {x}/2)))+
      h*(Q.maximumCdf x*(1-Real.exp (-B.intensity.real {x}/2))) := by
    rw [← hExp]
    ring
  rw [hRewrite]
  linarith only [hI]

end ProphetSecretary.Limiting.CountableInstance
