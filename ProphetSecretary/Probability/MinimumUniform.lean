import ProphetSecretary.Probability.OrderCDFUniform
import ProphetSecretary.Probability.BoundedCDFMean
import ProphetSecretary.Analysis.BernoulliVoidComparison
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The minimum of independent uniforms

The strict and closed tail formulas give the Beta(1,m) CDF. Layer cake gives
its mean 1/(m+1), and the finite product difference bound gives the m^(-2)
lower-tail estimate used by `upouter:beta`.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Probability

lemma uniformMinimum_indices_nonempty {m : ℕ} (hm : 1≤m) : (Finset.univ : Finset (Fin m)).Nonempty :=
  ⟨⟨0,by omega⟩,Finset.mem_univ _⟩

noncomputable def uniformMinimum (m : ℕ) (hm : 1≤m) (a : Fin m → ℝ) : ℝ :=
  Finset.univ.inf' (uniformMinimum_indices_nonempty hm) a

lemma measurable_uniformMinimum (m : ℕ) (hm : 1≤m) : Measurable (uniformMinimum m hm) := by
  have h : Measurable (Finset.univ.inf' (uniformMinimum_indices_nonempty hm) (fun i (a : Fin m → ℝ) => a i)) :=
    Finset.inf'_induction (uniformMinimum_indices_nonempty hm) _ (fun _f hf _g hg => hf.inf hg)
      (fun i _ => measurable_pi_apply i)
  convert h using 1
  funext a
  simp only [uniformMinimum,Finset.inf'_apply]

lemma uniformMinimum_mem_unit (m : ℕ) (hm : 1≤m) :
    ∀ᵐ a ∂Model.Instance.clocksLaw m, uniformMinimum m hm a∈Icc (0:ℝ) 1 := by
  filter_upwards [Model.Instance.clocks_mem_unitInterval (n:=m)] with a ha
  refine ⟨?_,?_⟩
  · exact Finset.le_inf' (uniformMinimum_indices_nonempty hm) a (fun i _ => (ha i).1)
  · exact (Finset.inf'_le a (Finset.mem_univ (⟨0,by omega⟩ : Fin m))).trans (ha ⟨0,by omega⟩).2

lemma integrable_uniformMinimum (m : ℕ) (hm : 1≤m) :
    Integrable (uniformMinimum m hm) (Model.Instance.clocksLaw m) := by
  apply Integrable.of_bound (measurable_uniformMinimum m hm).aestronglyMeasurable 1
  filter_upwards [uniformMinimum_mem_unit m hm] with a ha
  rw [Real.norm_eq_abs,abs_of_nonneg ha.1]
  exact ha.2

lemma uniformClock_open_lower {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    Model.Instance.uniformClock.real (Iio t)=t := by
  have hEq : Iio t =ᵐ[Model.Instance.uniformClock] Iic t := by
    filter_upwards [Model.Instance.uniformClock.ae_ne t] with u hu
    apply propext
    change u<t ↔ u≤t
    exact ⟨le_of_lt,fun h => lt_of_le_of_ne h hu⟩
  rw [measureReal_congr hEq,uniformClock_lowerCDF,min_eq_left ht.2,max_eq_left ht.1]

lemma uniformClock_closed_tail {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    Model.Instance.uniformClock.real (Ici t)=1-t := by
  have h := probReal_compl_eq_one_sub (μ:=Model.Instance.uniformClock) (measurableSet_Iio (a:=t))
  simpa only [Set.compl_Iio,uniformClock_open_lower ht] using h

lemma uniformMinimum_strict_tail (m : ℕ) (hm : 1≤m) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (Model.Instance.clocksLaw m).real {a | t<uniformMinimum m hm a}=(1-t)^m := by
  have hSet : {a : Fin m → ℝ | t<uniformMinimum m hm a}=Set.univ.pi (fun _ : Fin m => Ioi t) := by
    ext a
    simp only [Set.mem_setOf_eq,uniformMinimum,Finset.lt_inf'_iff,Finset.mem_univ,forall_true_left,Set.mem_pi,Set.mem_univ,Set.mem_Ioi]
  change ((Model.Instance.clocksLaw m) {a | t<uniformMinimum m hm a}).toReal=_
  rw [hSet,Model.Instance.clocksLaw,Measure.pi_pi,ENNReal.toReal_prod]
  simp only [uniformClock_tail ht.1,ENNReal.toReal_ofReal (sub_nonneg.mpr ht.2),Finset.prod_const,Finset.card_univ,Fintype.card_fin]

lemma uniformMinimum_closed_tail (m : ℕ) (hm : 1≤m) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (Model.Instance.clocksLaw m).real {a | t≤uniformMinimum m hm a}=(1-t)^m := by
  have hSet : {a : Fin m → ℝ | t≤uniformMinimum m hm a}=Set.univ.pi (fun _ : Fin m => Ici t) := by
    ext a
    simp only [Set.mem_setOf_eq,uniformMinimum,Finset.le_inf'_iff,Finset.mem_univ,forall_true_left,Set.mem_pi,Set.mem_univ,Set.mem_Ici]
  change ((Model.Instance.clocksLaw m) {a | t≤uniformMinimum m hm a}).toReal=_
  rw [hSet,Model.Instance.clocksLaw,Measure.pi_pi,ENNReal.toReal_prod]
  change (∏ _i : Fin m, Model.Instance.uniformClock.real (Ici t))=_
  simp only [uniformClock_closed_tail ht,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

/-- The Beta(1,m) CDF, with strict comparison also valid at atoms of the offers. -/
lemma uniformMinimum_cdf (m : ℕ) (hm : 1≤m) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    (Model.Instance.clocksLaw m).real {a | uniformMinimum m hm a<t}=1-(1-t)^m := by
  have hSet : {a : Fin m → ℝ | uniformMinimum m hm a<t}={a | t≤uniformMinimum m hm a}ᶜ := by
    ext a
    simp only [Set.mem_setOf_eq,Set.mem_compl_iff,not_le]
  rw [hSet,probReal_compl_eq_one_sub (measurableSet_le measurable_const (measurable_uniformMinimum m hm)),uniformMinimum_closed_tail m hm ht]

lemma integral_uniformMinimum (m : ℕ) (hm : 1≤m) :
    (∫ a, uniformMinimum m hm a ∂Model.Instance.clocksLaw m)=1/((m:ℝ)+1) := by
  rw [integral_eq_bounded_strict_layercake (Model.Instance.clocksLaw m) (measurable_uniformMinimum m hm) (1:ℝ≥0) (uniformMinimum_mem_unit m hm)]
  change (∫ t in Ioc (0:ℝ) 1, (Model.Instance.clocksLaw m).real {a | t<uniformMinimum m hm a})=1/((m:ℝ)+1)
  have hEq : (fun t : ℝ => (Model.Instance.clocksLaw m).real {a | t<uniformMinimum m hm a}) =ᵐ[volume.restrict (Ioc (0:ℝ) 1)]
      (fun t => (1-t)^m) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact uniformMinimum_strict_tail m hm ⟨ht.1.le,ht.2⟩
  rw [integral_congr_ae hEq,←intervalIntegral.integral_of_le (show (0:ℝ)≤1 by norm_num)]
  rw [intervalIntegral.integral_comp_sub_left (f:=fun t : ℝ => t^m) 1,integral_pow]
  norm_num

lemma uniformMinimum_small_probability (m : ℕ) (hm : 1≤m) :
    (Model.Instance.clocksLaw m).real {a | uniformMinimum m hm a<1/(m:ℝ)^2}≤1/(m:ℝ) := by
  have hmR : (1:ℝ)≤m := by exact_mod_cast hm
  have hm0 : (m:ℝ)≠0 := by positivity
  have hLevel : 1/(m:ℝ)^2∈Icc (0:ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one (by positivity : (0:ℝ)<(m:ℝ)^2)).mpr (by nlinarith only [hmR])
  rw [uniformMinimum_cdf m hm hLevel]
  have hProd := ProphetSecretary.Analysis.product_difference_le_sum (Finset.univ : Finset (Fin m))
    (fun _ => (1:ℝ)) (fun _ => 1-1/(m:ℝ)^2) (fun _ => 1/(m:ℝ)^2)
    (fun _ => sub_nonneg.mpr hLevel.2) (fun _ => sub_le_self 1 hLevel.1) (fun _ => le_rfl) (fun _ => by ring_nf;exact le_rfl)
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,one_pow,Finset.sum_const,nsmul_eq_mul] at hProd
  have hScale : (m:ℝ)*(1/(m:ℝ)^2)=1/(m:ℝ) := by
    rw [mul_one_div,pow_two,←div_div,div_self hm0]
  rwa [hScale] at hProd

end ProphetSecretary.Probability
