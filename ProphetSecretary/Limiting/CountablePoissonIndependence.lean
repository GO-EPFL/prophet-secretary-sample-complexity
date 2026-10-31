import ProphetSecretary.Limiting.CountablePoissonCounts
import Mathlib.Probability.Independence.Integration

/-!
# Joint counts for the countable Poisson construction

Finite independent construction bands first give an exact joint generating
function. Above the reserve the actual total counting measure agrees with a
finite band sum. Thus independence of disjoint observed regions is derived
from the actual common probability space.
-/

open MeasureTheory ProbabilityTheory Set Filter Complex
open scoped Classical NNReal ENNReal BigOperators

namespace ProphetSecretary.Limiting.CountableInstance

variable (B : CountableInstance) {ι : Type*} [Fintype ι]

theorem finiteBands_joint_generating (N : ℕ) {S : ι → Set Point}
    (hS : ∀ i, MeasurableSet (S i)) (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    (∫ ω, ∏ i, z i ^ (∑ k : Fin N, pointCount (S i) (ω k)) ∂B.bandConfigurationsLaw) =
      ∏ i, Complex.exp ((((∑ k : Fin N, countRate (B.bandIntensity k) (S i) : ℝ≥0) : ℝ) : ℂ)*(z i-1)) := by
  let g : Configuration → ℂ := fun ω => ∏ i, z i ^ pointCount (S i) ω
  have hg : Measurable g := Finset.measurable_fun_prod _ (fun i _ =>
    (Measurable.of_discrete : Measurable (fun m : ℕ => z i ^ m)).comp (measurable_pointCount (hS i)))
  have hI := (iIndepFun.precomp (g := fun k : Fin N => (k : ℕ)) Fin.val_injective
    B.bandConfigurations_independent).comp (fun _ => g) (fun _ => hg)
  have hprod := hI.integral_fun_prod_eq_prod_integral
    (fun k => (hg.comp (measurable_pi_apply (k : ℕ))).aestronglyMeasurable)
  have hpoint (ω : BandConfigurations) :
      (∏ i, z i ^ (∑ k : Fin N, pointCount (S i) (ω k))) = ∏ k : Fin N, g (ω k) := by
    calc
      _ = ∏ i, ∏ k : Fin N, z i ^ pointCount (S i) (ω k) := by
        apply Finset.prod_congr rfl
        intro i _
        exact (Finset.prod_pow_eq_pow_sum _ _ _).symm
      _ = _ := Finset.prod_comm
  calc
    _ = ∫ ω, ∏ k : Fin N, g (ω k) ∂B.bandConfigurationsLaw :=
      integral_congr_ae (Filter.Eventually.of_forall hpoint)
    _ = ∏ k : Fin N, ∫ ω, g (ω k) ∂B.bandConfigurationsLaw := hprod
    _ = ∏ k : Fin N, ∏ i, Complex.exp (((countRate (B.bandIntensity k) (S i) : ℝ) : ℂ)*(z i-1)) := by
      apply Finset.prod_congr rfl
      intro k _
      have he := (B.bandConfiguration_measurePreserving k).hasLaw.integral_comp hg.aestronglyMeasurable
      change (∫ ω, g (ω k) ∂B.bandConfigurationsLaw) = _ at he
      rw [he]
      exact generating_functional_disjoint_counts (B.bandIntensity k) hS hd z hz
    _ = ∏ i, Complex.exp (∑ k : Fin N, ((countRate (B.bandIntensity k) (S i) : ℝ) : ℂ)*(z i-1)) := by
      rw [Finset.prod_comm]
      simp only [Complex.exp_sum]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i _
      congr 1
      rw [NNReal.coe_sum,Complex.ofReal_sum,Finset.sum_mul]

theorem bandPointCounts_joint_generating {b : ℝ} (hb : (B.terminal : ℝ) < b)
    {S : ι → Set Point} (hS : ∀ i, MeasurableSet (S i))
    (hsub : ∀ i, S i ⊆ univ ×ˢ Ioi b) (hd : Pairwise (fun i j => Disjoint (S i) (S j)))
    (z : ι → ℂ) (hz : ∀ i, ‖z i‖ ≤ 1) :
    (∫ ω, ∏ i, z i ^ bandPointCount (S i) ω ∂B.bandConfigurationsLaw) =
      ∏ i, Complex.exp (((B.poissonRegionRate (S i) : ℝ) : ℂ)*(z i-1)) := by
  obtain ⟨K,hK⟩ := B.eventually_bands_below hb
  have heq : ∀ᵐ ω ∂B.bandConfigurationsLaw, ∀ i,
      bandPointCount (S i) ω = ∑ k : Fin (K+1), pointCount (S i) (ω k) := by
    filter_upwards [ae_all_iff.mpr (fun i => B.bandPointCount_region_eq_sum (hS i) (hsub i) hK)] with ω hω
    intro i
    exact (hω i).trans (Finset.sum_range (n := K+1) (fun k : ℕ => pointCount (S i) (ω k)))
  have hrate i : (∑ k : Fin (K+1), countRate (B.bandIntensity k) (S i)) = B.poissonRegionRate (S i) := by
    exact (Finset.sum_range (n := K+1) (fun k : ℕ => countRate (B.bandIntensity k) (S i))).symm.trans
      (B.poissonRegionRate_eq_sum (hS i) (hsub i) hK).symm
  calc
    _ = ∫ ω, ∏ i, z i ^ (∑ k : Fin (K+1), pointCount (S i) (ω k)) ∂B.bandConfigurationsLaw := by
      apply integral_congr_ae
      filter_upwards [heq] with ω hω
      simp_rw [hω]
    _ = _ := by
      rw [B.finiteBands_joint_generating (K+1) hS hd z hz]
      simp only [hrate]

private lemma exp_sum_bandPointCounts (S : ι → Set Point) (t : ι → ℝ) (ω : BandConfigurations) :
    Complex.exp ((((∑ i, (bandPointCount (S i) ω : ℝ)*t i) : ℝ) : ℂ)*Complex.I) =
      ∏ i, Complex.exp ((t i : ℂ)*Complex.I)^bandPointCount (S i) ω := by
  rw [Complex.ofReal_sum,Finset.sum_mul,Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Actual counts of disjoint regions above the reserve are independent. -/
theorem iIndepFun_bandPointCount_real {b : ℝ} (hb : (B.terminal : ℝ) < b)
    {S : ι → Set Point} (hS : ∀ i, MeasurableSet (S i))
    (hsub : ∀ i, S i ⊆ univ ×ˢ Ioi b) (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    iIndepFun (fun i ω => (bandPointCount (S i) ω : ℝ)) B.bandConfigurationsLaw := by
  have hX (i) : Measurable (fun ω => (bandPointCount (S i) ω : ℝ)) :=
    (Measurable.of_discrete : Measurable (fun m : ℕ => (m : ℝ))).comp (measurable_bandPointCount (hS i))
  apply (iIndepFun_iff_charFun_pi (fun i => (hX i).aemeasurable)).mpr
  intro t
  have hm : Measurable (fun ω => WithLp.toLp 2 (fun i => (bandPointCount (S i) ω : ℝ))) :=
    (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.comp (measurable_pi_lambda _ hX)
  rw [charFun_apply,integral_map hm.aemeasurable (by fun_prop)]
  simp only [PiLp.inner_apply,Real.inner_apply]
  simp_rw [exp_sum_bandPointCounts]
  rw [B.bandPointCounts_joint_generating hb hS hsub hd
    (fun i => Complex.exp ((t i : ℂ)*Complex.I)) (fun i => by simp [Complex.norm_exp])]
  apply Finset.prod_congr rfl
  intro i _
  have hmap : B.bandConfigurationsLaw.map (fun ω => (bandPointCount (S i) ω : ℝ)) =
      (poissonMeasure (B.poissonRegionRate (S i))).map (Nat.cast : ℕ → ℝ) := by
    calc
      _ = (B.bandConfigurationsLaw.map (bandPointCount (S i))).map (Nat.cast : ℕ → ℝ) :=
        (Measure.map_map (by fun_prop) (measurable_bandPointCount (hS i))).symm
      _ = _ := congrArg (fun μ : Measure ℕ => μ.map (Nat.cast : ℕ → ℝ))
        (B.bandPointCount_hasLaw hb (hS i) (hsub i)).map_eq
  rw [hmap,charFun_map_cast_poissonMeasure]

theorem iIndepFun_bandPointCount {b : ℝ} (hb : (B.terminal : ℝ) < b)
    {S : ι → Set Point} (hS : ∀ i, MeasurableSet (S i))
    (hsub : ∀ i, S i ⊆ univ ×ˢ Ioi b) (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    iIndepFun (fun i => bandPointCount (S i)) B.bandConfigurationsLaw := by
  have h := (B.iIndepFun_bandPointCount_real hb hS hsub hd).comp (fun _ => Nat.floor)
    (fun _ => Nat.measurable_floor)
  simpa only [Function.comp_def,Nat.floor_natCast] using h

/-- The constructed countable process has the actual product Poisson count law
on every finite disjoint family contained above a common strict cutoff. -/
theorem bandPointCounts_joint_hasLaw {b : ℝ} (hb : (B.terminal : ℝ) < b)
    {S : ι → Set Point} (hS : ∀ i, MeasurableSet (S i))
    (hsub : ∀ i, S i ⊆ univ ×ˢ Ioi b) (hd : Pairwise (fun i j => Disjoint (S i) (S j))) :
    HasLaw (fun ω i => bandPointCount (S i) ω)
      (Measure.pi (fun i => poissonMeasure (B.poissonRegionRate (S i)))) B.bandConfigurationsLaw :=
  (B.iIndepFun_bandPointCount hb hS hsub hd).hasLaw_pi
    (fun i => B.bandPointCount_hasLaw hb (hS i) (hsub i))

end ProphetSecretary.Limiting.CountableInstance
