import ProphetSecretary.Statistics.CalibrationMasterPointwise
import ProphetSecretary.Model.UnitScalarGap

/-!
# The selected coefficient and calibration covariance

A deterministic true-law gap minimizer controls the random selected
coefficient through the quadratic diameter estimate. This reference is
fixed before training and is unrelated to the ratio-minimizing weight.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {Ω : Type*} [MeasurableSpace Ω]

lemma integral_mul_abs_le_sqrt (D : Measure Ω) [IsFiniteMeasure D] {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) (A B : ℝ)
    (hA : ∀ x, |f x|≤A) (hB : ∀ x, |g x|≤B) :
    |∫ x, f x*g x ∂D| ≤ Real.sqrt (∫ x, (f x)^2 ∂D)*Real.sqrt (∫ x, (g x)^2 ∂D) := by
  have hF : MemLp f (ENNReal.ofReal 2) D := MemLp.of_bound hf.aestronglyMeasurable A
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hA x)
  have hG : MemLp g (ENNReal.ofReal 2) D := MemLp.of_bound hg.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)
  have hConj : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num,by norm_num⟩
  have h := integral_mul_norm_le_Lp_mul_Lq hConj hF hG
  have hPower (x : ℝ) : ‖x‖^(2 : ℝ)=x^2 := by rw [Real.rpow_two,Real.norm_eq_abs,sq_abs]
  simp only [hPower,← Real.sqrt_eq_rpow] at h
  exact (abs_integral_le_integral_abs.trans (by simpa only [abs_mul,Real.norm_eq_abs] using h))

lemma coefficient_distance_sq {z z' : ℝ} (hz : z∈Icc (0 : ℝ) (1/4))
    (hz' : z'∈Icc (0 : ℝ) (1/4)) :
    (z-z')^2≤4*(normalizedCoefficient z'-normalizedCoefficient z)^2 := by
  let l := normalizedCoefficient z
  let l' := normalizedCoefficient z'
  have h := (normalizedCoefficient_identities hz.1).1
  have h' := (normalizedCoefficient_identities hz'.1).1
  have he : z-z'=(l'-l)*((1+z)*(1+z')) := by
    calc
      z-z' = (1+z)*1-1*(1+z') := by ring
      _ = (1+z)*(l'*(1+z'))-(l*(1+z))*(1+z') := by rw [h,h']
      _ = _ := by ring
  have hProd0 : 0≤(1+z)*(1+z') := mul_nonneg (by linarith [hz.1]) (by linarith [hz'.1])
  have hProd : (1+z)*(1+z')≤2 := by
    have hB : (1+z)*(1+z')≤(5/4 : ℝ)*(5/4) := mul_le_mul
      (by linarith [hz.2]) (by linarith [hz'.2]) (by linarith [hz'.1]) (by norm_num)
    linarith
  rw [he,mul_pow]
  have hP := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hProd0 hProd 2) (sq_nonneg (l'-l))
  norm_num at hP
  simpa only [mul_comm] using hP

lemma calibration_covariance_coarse (D : Measure Ω) [IsProbabilityMeasure D] {Z g : Ω → ℝ}
    (hZ : Measurable Z) (hg : Measurable g)
    (hZrange : ∀ x, Z x∈Icc (0 : ℝ) (1/4)) (hgRange : ∀ x, |g x|≤1)
    {m : ℕ} [NeZero m] (hg2 : (∫ x, (g x)^2 ∂D)≤4/(m : ℝ)) :
    |∫ x, Z x*g x ∂D|≤1/(2*Real.sqrt (m : ℝ)) := by
  have h1 (x : Ω) : |Z x|≤1/4 := by rw [abs_of_nonneg (hZrange x).1]; exact (hZrange x).2
  have hZI : Integrable (fun x => Z x^2) D := Integrable.of_bound
    (hZ.pow_const 2).aestronglyMeasurable (1/16)
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have h := pow_le_pow_left₀ (hZrange x).1 (hZrange x).2 2
      norm_num at h ⊢
      exact h)
  have hZ2 : (∫ x,Z x^2 ∂D)≤1/16 := by
    have h := integral_mono hZI (integrable_const (1/16 : ℝ)) (fun x => by
      have h := pow_le_pow_left₀ (hZrange x).1 (hZrange x).2 2
      norm_num at h ⊢
      exact h)
    simpa only [integral_const,probReal_univ,one_smul] using h
  have hS := integral_mul_abs_le_sqrt D hZ hg (1/4) 1 h1 hgRange
  refine hS.trans ((mul_le_mul (Real.sqrt_le_sqrt hZ2) (Real.sqrt_le_sqrt hg2)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq ?_)
  have h4 : Real.sqrt (4 : ℝ)=2 := (Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)).mpr (by norm_num)
  rw [Real.sqrt_div (by norm_num : (0 : ℝ)≤4),h4]
  have hQ : Real.sqrt (1/16 : ℝ)=1/4 := (Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)).mpr (by norm_num)
  rw [hQ]
  ring

lemma calibration_covariance_sharp {n m : ℕ} [NeZero m] (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (D : Measure Ω) [IsProbabilityMeasure D]
    {Z g : Ω → ℝ} (hZ : Measurable Z) (hg : Measurable g)
    (hZrange : ∀ x, Z x∈Icc (0 : ℝ) (1/4)) (hgRange : ∀ x, |g x|≤1)
    (hgMean : |∫ x,g x ∂D|≤1/((m : ℝ)+1)) (hg2 : (∫ x,(g x)^2 ∂D)≤4/(m : ℝ))
    {K : ℝ} (hK : 0≤K)
    (hDiam : ∀ a b : ℝ, a∈Icc (0 : ℝ) 1 → b∈Icc (0 : ℝ) 1 →
      (b-a)^2≤K*(normalizedScalarGap P a+normalizedScalarGap P b)) :
    (∫ x,Z x*g x ∂D)≤
      Real.sqrt (32*K)*Real.sqrt ((∫ x,normalizedScalarGap P (normalizedCoefficient (Z x)) ∂D)/(m : ℝ))+
        1/(4*(m : ℝ)) := by
  have hP := P.integrable_maximum_of_bounded hcap
  obtain ⟨lam,hlam,hMin⟩ := normalizedScalarGap_exists_minimizer_on P hP
    (by norm_num : (0 : ℝ)≤4/5) (by norm_num : (4/5 : ℝ)≤1) le_rfl
  let z := (1-lam)/lam
  have hlpos : 0<lam := (by norm_num : (0 : ℝ)<4/5).trans_le hlam.1
  have hz : z∈Icc (0 : ℝ) (1/4) := ⟨div_nonneg (sub_nonneg.mpr hlam.2) hlpos.le,
    (div_le_iff₀ hlpos).mpr (by linarith [hlam.1])⟩
  have he : normalizedCoefficient z=lam := by
    unfold normalizedCoefficient
    dsimp [z]
    field_simp [hlpos.ne']
    ring
  have hWeight : Measurable (fun x => normalizedCoefficient (Z x)) :=
    measurable_const.div (measurable_const.add hZ)
  have hRange (x : Ω) : normalizedCoefficient (Z x)∈Icc (0 : ℝ) 1 := by
    have h := normalizedCoefficient_mem (hZrange x)
    exact ⟨(by norm_num : (0 : ℝ)≤4/5).trans h.1,h.2⟩
  let F := fun x => normalizedScalarGap P (normalizedCoefficient (Z x))
  have hFI : Integrable F D := Integrable.of_bound
    (P.measurable_normalizedGap_of_weight hP hWeight hRange).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by
      have h := P.normalizedScalarGap_mem_unit hcap (hRange x)
      change ‖F x‖≤1
      rw [Real.norm_eq_abs,abs_of_nonneg h.1]
      exact h.2)
  have hF0 (x : Ω) : 0≤F x := normalizedScalarGap_nonnegative P hP (hRange x)
  let f := fun x => Z x-z
  have hf : Measurable f := hZ.sub_const z
  have hfB (x : Ω) : |f x|≤1 := by
    apply abs_le.mpr
    dsimp [f]
    constructor <;> linarith [(hZrange x).1,(hZrange x).2,hz.1,hz.2]
  have hf2I : Integrable (fun x => f x^2) D :=
    Integrable.of_bound (hf.pow_const 2).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg (f x)) (hfB x) 2)
  have hf2 (x : Ω) : f x^2≤(8*K)*F x := by
    have hA := coefficient_distance_sq (hZrange x) hz
    rw [he] at hA
    have hB := hDiam (normalizedCoefficient (Z x)) lam (hRange x)
      ⟨(by norm_num : (0 : ℝ)≤4/5).trans hlam.1,hlam.2⟩
    have hC := hMin (normalizedCoefficient (Z x)) (normalizedCoefficient_mem (hZrange x))
    change (lam-normalizedCoefficient (Z x))^2≤K*(F x+normalizedScalarGap P lam) at hB
    change normalizedScalarGap P lam≤F x at hC
    change f x^2≤4*(lam-normalizedCoefficient (Z x))^2 at hA
    nlinarith only [hA,hB,mul_le_mul_of_nonneg_left hC hK]
  have hf2mean := integral_mono hf2I (hFI.const_mul (8*K)) hf2
  rw [integral_const_mul] at hf2mean
  have hgI : Integrable g D := Integrable.of_bound hg.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hgRange x)
  have hfgI : Integrable (fun x => f x*g x) D :=
    hgI.bdd_mul hf.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using hfB x)
  have hSplit : (∫ x,Z x*g x ∂D)=z*(∫ x,g x ∂D)+(∫ x,f x*g x ∂D) := by
    calc
      _ = ∫ x,z*g x+f x*g x ∂D := integral_congr_ae (Filter.Eventually.of_forall fun x => by dsimp [f]; ring)
      _ = _ := by rw [integral_add (hgI.const_mul z) hfgI,integral_const_mul]
  have hm : (0 : ℝ)<m := Nat.cast_pos.mpr (NeZero.pos m)
  have hBias : z*(∫ x,g x ∂D)≤1/(4*(m : ℝ)) := by
    calc
      _ ≤ z*|∫ x,g x ∂D| := mul_le_mul_of_nonneg_left (le_abs_self _) hz.1
      _ ≤ (1/4)*(1/((m : ℝ)+1)) := mul_le_mul hz.2 hgMean (abs_nonneg _) (by norm_num)
      _ ≤ _ := by rw [show 1/(4*(m : ℝ))=(1/4)*(1/(m : ℝ)) by ring]
                  exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le hm (by linarith)) (by norm_num)
  have hCS := integral_mul_abs_le_sqrt D hf hg 1 1 hfB hgRange
  have hVar : (∫ x,f x*g x ∂D)≤Real.sqrt (32*K)*Real.sqrt ((∫ x,F x ∂D)/(m : ℝ)) := by
    refine (le_abs_self _).trans (hCS.trans ((mul_le_mul (Real.sqrt_le_sqrt hf2mean)
      (Real.sqrt_le_sqrt hg2) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans_eq ?_))
    rw [← Real.sqrt_mul (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ)≤8) hK) (integral_nonneg hF0)),
      ← Real.sqrt_mul (show 0≤32*K by positivity)]
    congr 1
    ring
  rw [hSplit]
  linarith only [hBias,hVar]

end ProphetSecretary.Statistics.Calibration
