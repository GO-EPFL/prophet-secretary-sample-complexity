import ProphetSecretary.Limiting.PoissonCounts
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Function.Floor

/-!
# Independent counts in disjoint measurable Poisson regions

The generating functional of the constructed finite configuration proves the
joint count law. Independence is derived, rather than assumed as part of an
interface for the process. Counts include every point after stopping as well.
-/

open MeasureTheory ProbabilityTheory Set Complex
open scoped BigOperators Classical ENNReal NNReal

namespace ProphetSecretary.Limiting

variable {ι : Type*} [Fintype ι]

lemma pointFactor_prod_disjoint {S : ι → Set Point}
    (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (z : ι → ℂ) (p : Point) :
    (∏ i, pointFactor (S i) (z i) p) = 1 + ∑ i, (S i).indicator (fun _ => z i-1) p := by
  by_cases h : ∃ j, p ∈ S j
  · obtain ⟨j,hj⟩ := h
    have ho : ∀ i, i ≠ j → p ∉ S i := fun i hij hi => (Set.disjoint_left.mp (hd hij)) hi hj
    rw [Finset.prod_eq_single j, Finset.sum_eq_single j]
    · simp [pointFactor,hj]
    · intro i _ hij
      exact indicator_of_notMem (ho i hij) _
    · simp
    · intro i _ hij
      simp [pointFactor,ho i hij]
    · simp
  · have hn : ∀ i, p ∉ S i := by simpa only [not_exists] using h
    simp [pointFactor,hn]

lemma pointProd_prod_pointFactor (S : ι → Set Point) (z : ι → ℂ) (ω : Configuration) :
    pointProd (fun p => ∏ i, pointFactor (S i) (z i) p) ω = ∏ i, z i ^ pointCount (S i) ω := by
  unfold pointProd
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro i _
  exact pointProd_pointFactor (S i) (z i) ω

lemma integral_prod_pointFactor (μ : FiniteMeasure ℝ) {S : ι → Set Point}
    (hS : ∀ i, MeasurableSet (S i)) (hd : Pairwise (fun i j => Disjoint (S i) (S j))) (z : ι → ℂ) :
    (∫ p, ∏ i, pointFactor (S i) (z i) p ∂pointLaw μ) =
      1 + ∑ i, ((pointLaw μ).real (S i) : ℂ) * (z i-1) := by
  simp_rw [pointFactor_prod_disjoint hd z]
  rw [integral_add (integrable_const (1 : ℂ))
    (integrable_finsetSum _ (fun i _ => (integrable_const (z i-1)).indicator (hS i))),
    integral_finsetSum _ (fun i _ => (integrable_const (z i-1)).indicator (hS i))]
  simp only [integral_const,probReal_univ,one_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_indicator (hS i),integral_const]
  simp

/-- Joint generating function, for arbitrary finite disjoint measurable regions. -/
theorem generating_functional_disjoint_counts (μ : FiniteMeasure ℝ) {S : ι → Set Point}
    (hS : ∀ i, MeasurableSet (S i)) (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    (∫ ω, ∏ i, z i ^ pointCount (S i) ω ∂configurationLaw μ) =
      ∏ i, Complex.exp (((countRate μ (S i) : ℝ) : ℂ) * (z i-1)) := by
  have hm : Measurable (fun p => ∏ i, pointFactor (S i) (z i) p) :=
    Finset.measurable_fun_prod _ (fun i _ => measurable_pointFactor (hS i) (z i))
  have hb (p : Point) : ‖∏ i, pointFactor (S i) (z i) p‖ ≤ 1 := by
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i _ => pointFactor_norm_le_one (S i) (hz i) p)
  have he := generating_functional μ _ hm hb
  simp_rw [pointProd_prod_pointFactor] at he
  rw [integral_prod_pointFactor μ hS hd] at he
  rw [← Complex.exp_sum]
  apply he.trans
  congr 1
  rw [add_sub_cancel_left,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [countRate_coe]
  push_cast
  ring

lemma exp_sum_pointCounts (S : ι → Set Point) (t : ι → ℝ) (ω : Configuration) :
    Complex.exp ((((∑ i, (pointCount (S i) ω : ℝ)*t i) : ℝ) : ℂ)*Complex.I) =
      ∏ i, Complex.exp ((t i : ℂ)*Complex.I)^pointCount (S i) ω := by
  rw [Complex.ofReal_sum,Finset.sum_mul,Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Actual real-valued counts are mutually independent on disjoint regions. -/
theorem iIndepFun_pointCount_real (μ : FiniteMeasure ℝ) {S : ι → Set Point}
    (hS : ∀ i, MeasurableSet (S i)) (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    iIndepFun (fun i ω => (pointCount (S i) ω : ℝ)) (configurationLaw μ) := by
  have hX (i) : Measurable (fun ω => (pointCount (S i) ω : ℝ)) :=
    (Measurable.of_discrete : Measurable (fun N : ℕ => (N : ℝ))).comp (measurable_pointCount (hS i))
  apply (iIndepFun_iff_charFun_pi (fun i => (hX i).aemeasurable)).mpr
  intro t
  have hm : Measurable (fun ω => WithLp.toLp 2 (fun i => (pointCount (S i) ω : ℝ))) :=
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.comp (measurable_pi_lambda _ hX)
  rw [charFun_apply,integral_map hm.aemeasurable (by fun_prop)]
  simp only [PiLp.inner_apply,Real.inner_apply]
  simp_rw [exp_sum_pointCounts]
  rw [generating_functional_disjoint_counts μ hS hd
    (fun i => Complex.exp ((t i : ℂ)*Complex.I)) (fun i => by simp [Complex.norm_exp])]
  apply Finset.prod_congr rfl
  intro i _
  exact (charFun_pointCount μ (hS i) (t i)).symm

/-- Natural-valued disjoint-region counts are mutually independent. -/
theorem iIndepFun_pointCount (μ : FiniteMeasure ℝ) {S : ι → Set Point}
    (hS : ∀ i, MeasurableSet (S i)) (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    iIndepFun (fun i => pointCount (S i)) (configurationLaw μ) := by
  have h := (iIndepFun_pointCount_real μ hS hd).comp (fun _ => Nat.floor)
    (fun _ => Nat.measurable_floor)
  simpa only [Function.comp_def,Nat.floor_natCast] using h

/-- The actual joint count law is the product of its Poisson marginals. -/
theorem pointCount_joint_law (μ : FiniteMeasure ℝ) {S : ι → Set Point}
    (hS : ∀ i, MeasurableSet (S i)) (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    (configurationLaw μ).map (fun ω i => pointCount (S i) ω) =
      Measure.pi (fun i => poissonMeasure (countRate μ (S i))) := by
  have h := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pointCount (hS i)).aemeasurable)).mp
    (iIndepFun_pointCount μ hS hd)
  calc
    _ = Measure.pi (fun i => (configurationLaw μ).map (pointCount (S i))) := h
    _ = _ := by
      congr 1
      funext i
      exact pointCount_law μ (hS i)

lemma pointCount_joint_measurePreserving (μ : FiniteMeasure ℝ) {S : ι → Set Point}
    (hS : ∀ i, MeasurableSet (S i)) (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    MeasurePreserving (fun ω i => pointCount (S i) ω) (configurationLaw μ)
      (Measure.pi (fun i => poissonMeasure (countRate μ (S i)))) :=
  ⟨measurable_pi_lambda _ (fun i => measurable_pointCount (hS i)),pointCount_joint_law μ hS hd⟩

end ProphetSecretary.Limiting
