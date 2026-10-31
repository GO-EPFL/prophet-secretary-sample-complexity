import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-!
# Splitting one atom into independent fair value displacements

The unchanged complement and the two shifted half-atoms are explicit
measures. These identities apply to sigma-finite intensities with infinite
total mass as well as probability laws.
-/
open MeasureTheory Set
open scoped Classical ENNReal
namespace ProphetSecretary.Probability

noncomputable def moveAtom (x y z : ℝ) : ℝ := if z=x then y else z

lemma measurable_moveAtom (x y : ℝ) : Measurable (moveAtom x y) :=
  measurable_const.piecewise (measurableSet_singleton x) measurable_id

lemma map_moveAtom (μ : Measure ℝ) (x y : ℝ) :
    μ.map (moveAtom x y)=μ.restrict {x}ᶜ+μ {x} • Measure.dirac y := by
  have hComp : (μ.restrict {x}ᶜ).map (moveAtom x y)=μ.restrict {x}ᶜ := by
    calc
      _ = (μ.restrict {x}ᶜ).map id := by
        apply Measure.map_congr
        filter_upwards [ae_restrict_mem (measurableSet_singleton x).compl] with z hz
        exact if_neg hz
      _ = _ := Measure.map_id
  calc
    _ = (μ.restrict {x}+μ.restrict {x}ᶜ).map (moveAtom x y) := by
      rw [Measure.restrict_add_restrict_compl (measurableSet_singleton x)]
    _ = (μ.restrict {x}).map (moveAtom x y)+(μ.restrict {x}ᶜ).map (moveAtom x y) :=
      Measure.map_add _ _ (measurable_moveAtom x y)
    _ = _ := by
      rw [hComp,Measure.restrict_singleton,Measure.map_smul,Measure.map_dirac]
      simp only [moveAtom]
      exact add_comm _ _

noncomputable def fairBoolLaw : Measure Bool :=
  (1/2 : ℝ≥0∞) • Measure.dirac true+(1/2 : ℝ≥0∞) • Measure.dirac false

instance fairBoolLaw_probability : IsProbabilityMeasure fairBoolLaw := by
  constructor
  simp only [fairBoolLaw,Measure.add_apply,Measure.smul_apply,measure_univ,smul_eq_mul,mul_one]
  exact ENNReal.add_halves 1

noncomputable def boolSign (s : Bool) : ℝ := if s then 1 else -1

lemma integral_boolSign : (∫ s, boolSign s ∂fairBoolLaw)=0 := by
  rw [fairBoolLaw,integral_add_measure,integral_smul_measure,integral_smul_measure]
  · norm_num [boolSign]
  · exact (integrable_dirac (by finiteness)).smul_measure (by norm_num)
  · exact (integrable_dirac (by finiteness)).smul_measure (by norm_num)

noncomputable def signedAtomDisplay (x h : ℝ) (z : ℝ × Bool) : ℝ :=
  if z.1=x then x+h*boolSign z.2 else z.1

lemma measurable_signedAtomDisplay (x h : ℝ) : Measurable (signedAtomDisplay x h) := by
  exact ((measurable_const.add ((measurable_of_finite boolSign).comp measurable_snd |>.const_mul h))).piecewise
    ((measurableSet_singleton x).preimage measurable_fst) measurable_fst

lemma map_signedAtomDisplay (μ : Measure ℝ) [SFinite μ] (x h : ℝ) :
    (μ.prod fairBoolLaw).map (signedAtomDisplay x h)=
      μ.restrict {x}ᶜ+(μ {x}/2) • Measure.dirac (x+h)+(μ {x}/2) • Measure.dirac (x-h) := by
  rw [fairBoolLaw,Measure.prod_add,Measure.prod_smul_right,Measure.prod_smul_right,
    Measure.map_add _ _ (measurable_signedAtomDisplay x h),Measure.map_smul,Measure.map_smul,
    Measure.prod_dirac,Measure.prod_dirac,
    Measure.map_map (measurable_signedAtomDisplay x h) measurable_prodMk_right,
    Measure.map_map (measurable_signedAtomDisplay x h) measurable_prodMk_right]
  have hTrue : (fun z : ℝ => signedAtomDisplay x h (z,true))=moveAtom x (x+h) := by
    funext z
    simp [signedAtomDisplay,boolSign,moveAtom]
  have hFalse : (fun z : ℝ => signedAtomDisplay x h (z,false))=moveAtom x (x-h) := by
    funext z
    simp [signedAtomDisplay,boolSign,sub_eq_add_neg,moveAtom]
  simp only [Function.comp_def]
  rw [hTrue,hFalse,map_moveAtom,map_moveAtom,smul_add,smul_add,smul_smul,smul_smul]
  simp only [← add_assoc]
  have hHalf : (1/2 : ℝ≥0∞)+(1/2)=1 := ENNReal.add_halves 1
  calc
    _ = ((1/2 : ℝ≥0∞)+(1/2)) • μ.restrict {x}ᶜ+
        ((1/2 : ℝ≥0∞)*μ {x}) • Measure.dirac (x+h)+
        ((1/2 : ℝ≥0∞)*μ {x}) • Measure.dirac (x-h) := by
      rw [add_smul]
      ac_rfl
    _ = _ := by rw [hHalf,one_smul]; simp only [div_eq_mul_inv,one_mul,mul_comm]

end ProphetSecretary.Probability
