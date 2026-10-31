import ProphetSecretary.Limiting.PoissonCounts
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Function.Floor

/-!
# Independent counts of disjoint finite-intensity bands

A finite family of disjoint time/mark sets has a factorized generating function.
Characteristic-function uniqueness then yields mutual independence of its actual
counts. In particular, disjoint time increments have independent Poisson counts.
-/

open MeasureTheory ProbabilityTheory Set Complex
open scoped BigOperators Classical ENNReal NNReal

namespace ProphetSecretary.Limiting

variable {ι : Type*} [Fintype ι]

noncomputable def partitionFactor (S : ι → Set Point) (z : ι → ℂ) (p : Point) : ℂ :=
  ∏ j, pointFactor (S j) (z j) p

lemma measurable_partitionFactor (S : ι → Set Point) (hS : ∀ j, MeasurableSet (S j)) (z : ι → ℂ) :
    Measurable (partitionFactor S z) :=
  Finset.measurable_fun_prod _ (fun j _ => measurable_pointFactor (hS j) (z j))

lemma partitionFactor_norm_le_one (S : ι → Set Point) (z : ι → ℂ) (hz : ∀ j, ‖z j‖ ≤ 1) (p : Point) :
    ‖partitionFactor S z p‖ ≤ 1 := by
  unfold partitionFactor
  rw [Complex.norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun j _ => pointFactor_norm_le_one (S j) (hz j) p)

lemma pointProd_partitionFactor (S : ι → Set Point) (z : ι → ℂ) (ω : Configuration) :
    pointProd (partitionFactor S z) ω = ∏ j, z j ^ pointCount (S j) ω := by
  unfold pointProd partitionFactor
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  exact pointProd_pointFactor (S j) (z j) ω

lemma partitionFactor_eq_of_disjoint (S : ι → Set Point)
    (hdisj : Pairwise (fun j k => Disjoint (S j) (S k))) (z : ι → ℂ) (p : Point) :
    partitionFactor S z p = 1 + ∑ j, (S j).indicator (fun _ => z j - 1) p := by
  by_cases hex : ∃ j, p ∈ S j
  · obtain ⟨j, hj⟩ := hex
    have hother (k : ι) (hkj : k ≠ j) : p ∉ S k := fun hk => (Set.disjoint_left.mp (hdisj hkj)) hk hj
    have hp : partitionFactor S z p = z j := by
      unfold partitionFactor
      rw [Finset.prod_eq_single j]
      · simp [pointFactor, hj]
      · intro k _ hkj
        exact if_neg (hother k hkj)
      · intro hn; exact False.elim (hn (Finset.mem_univ j))
    have hs : (∑ k, (S k).indicator (fun _ => z k - 1) p) = z j - 1 := by
      rw [Finset.sum_eq_single j]
      · exact Set.indicator_of_mem hj _
      · intro k _ hkj
        exact Set.indicator_of_notMem (hother k hkj) _
      · intro hn; exact False.elim (hn (Finset.mem_univ j))
    rw [hp, hs]
    ring
  · have hn : ∀ j, p ∉ S j := fun j hj => hex ⟨j, hj⟩
    simp [partitionFactor, pointFactor, hn]

lemma integral_partitionFactor (μ : FiniteMeasure ℝ) (S : ι → Set Point)
    (hS : ∀ j, MeasurableSet (S j)) (hdisj : Pairwise (fun j k => Disjoint (S j) (S k))) (z : ι → ℂ) :
    (∫ p, partitionFactor S z p ∂pointLaw μ) =
      1 + ∑ j, ((pointLaw μ).real (S j) : ℂ) * (z j - 1) := by
  have he : partitionFactor S z = fun p => 1 + ∑ j, (S j).indicator (fun _ => z j - 1) p :=
    funext (partitionFactor_eq_of_disjoint S hdisj z)
  have hi (j : ι) : Integrable ((S j).indicator (fun _ => z j - 1)) (pointLaw μ) :=
    (integrable_const (z j - 1)).indicator (hS j)
  rw [he, integral_add (integrable_const (1 : ℂ)) (integrable_finsetSum _ (fun j _ => hi j)),
    integral_finsetSum _ (fun j _ => hi j)]
  simp only [integral_const, probReal_univ, one_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_indicator (hS j), integral_const]
  simp only [measureReal_def, Measure.restrict_apply_univ, Complex.real_smul]

lemma generating_disjoint_counts (μ : FiniteMeasure ℝ) (S : ι → Set Point)
    (hS : ∀ j, MeasurableSet (S j)) (hdisj : Pairwise (fun j k => Disjoint (S j) (S k)))
    (z : ι → ℂ) (hz : ∀ j, ‖z j‖ ≤ 1) :
    (∫ ω, ∏ j, z j ^ pointCount (S j) ω ∂configurationLaw μ) =
      ∏ j, Complex.exp (((countRate μ (S j) : ℝ) : ℂ) * (z j - 1)) := by
  simp_rw [← pointProd_partitionFactor]
  rw [generating_functional μ _ (measurable_partitionFactor S hS z) (partitionFactor_norm_le_one S z hz),
    integral_partitionFactor μ S hS hdisj z]
  have he : (((μ.mass : ℝ) : ℂ) *
      ((1 + ∑ j, ((pointLaw μ).real (S j) : ℂ) * (z j - 1)) - 1)) =
        ∑ j, (((countRate μ (S j) : ℝ) : ℂ) * (z j - 1)) := by
    rw [show (1 + ∑ j, ((pointLaw μ).real (S j) : ℂ) * (z j - 1)) - 1 =
      ∑ j, ((pointLaw μ).real (S j) : ℂ) * (z j - 1) by ring, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [countRate_coe]
    push_cast
    ring
  rw [he, Complex.exp_sum]

lemma linear_nat_vector (L : (ι → ℝ) →L[ℝ] ℝ) (c : ι → ℕ) :
    L (fun j => (c j : ℝ)) = ∑ j, (c j : ℝ) * L (Pi.single j 1) := by
  have hv : (fun j => (c j : ℝ)) = ∑ j, Pi.single j (c j : ℝ) := by
    funext k
    simp
  rw [hv, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hs : Pi.single j (c j : ℝ) = (c j : ℝ) • Pi.single j (1 : ℝ) := by
    funext k
    by_cases hkj : k = j <;> simp [hkj]
  rw [hs, map_smul, smul_eq_mul]

lemma exp_linear_nat_vector (L : (ι → ℝ) →L[ℝ] ℝ) (c : ι → ℕ) :
    Complex.exp ((L (fun j => (c j : ℝ)) : ℝ) * Complex.I) =
      ∏ j, (Complex.exp ((L (Pi.single j 1) : ℝ) * Complex.I)) ^ c j := by
  rw [linear_nat_vector]
  push_cast
  rw [Finset.sum_mul, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro j _
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

lemma generating_pointCount (μ : FiniteMeasure ℝ) {S : Set Point} (hS : MeasurableSet S)
    (z : ℂ) (hz : ‖z‖ ≤ 1) :
    (∫ ω, z ^ pointCount S ω ∂configurationLaw μ) =
      Complex.exp (((countRate μ S : ℝ) : ℂ) * (z - 1)) := by
  calc
    _ = ∫ ω, pointProd (pointFactor S z) ω ∂configurationLaw μ := by simp_rw [pointProd_pointFactor]
    _ = _ := generating_functional μ _ (measurable_pointFactor hS z) (pointFactor_norm_le_one S hz)
    _ = _ := by
      rw [integral_pointFactor μ hS]
      congr 1
      rw [countRate_coe]
      push_cast
      ring

omit [Fintype ι] in
lemma linear_single_scalar (L : (ι → ℝ) →L[ℝ] ℝ) (j : ι) (t : ℝ) :
    L (Pi.single j t) = t * L (Pi.single j 1) := by
  have hs : Pi.single j t = t • Pi.single j (1 : ℝ) := by
    funext k
    by_cases hkj : k = j <;> simp [hkj]
  rw [hs, map_smul, smul_eq_mul]

lemma independent_real_counts (μ : FiniteMeasure ℝ) (S : ι → Set Point)
    (hS : ∀ j, MeasurableSet (S j)) (hdisj : Pairwise (fun j k => Disjoint (S j) (S k))) :
    iIndepFun (fun j (ω : Configuration) => (pointCount (S j) ω : ℝ)) (configurationLaw μ) := by
  have hX (j : ι) : Measurable (fun ω => (pointCount (S j) ω : ℝ)) :=
    (Measurable.of_discrete : Measurable (fun N : ℕ => (N : ℝ))).comp (measurable_pointCount (hS j))
  apply (iIndepFun_iff_charFunDual_pi (fun j => (hX j).aemeasurable)).mpr
  intro L
  let z := fun j : ι => Complex.exp ((L (Pi.single j 1) : ℝ) * Complex.I)
  have hz (j : ι) : ‖z j‖ ≤ 1 := by simp [z, Complex.norm_exp]
  have hm : Measurable (fun (ω : Configuration) (j : ι) => (pointCount (S j) ω : ℝ)) := measurable_pi_lambda _ hX
  rw [charFunDual_apply, integral_map hm.aemeasurable (by fun_prop)]
  simp_rw [exp_linear_nat_vector]
  change (∫ ω, ∏ j, z j ^ pointCount (S j) ω ∂configurationLaw μ) = _
  rw [generating_disjoint_counts μ S hS hdisj z hz]
  apply Finset.prod_congr rfl
  intro j _
  rw [charFunDual_apply, integral_map (hX j).aemeasurable (by fun_prop)]
  have he (ω : Configuration) :
      Complex.exp (((L.comp (.single ℝ (fun _ : ι => ℝ) j)) (pointCount (S j) ω : ℝ) : ℝ) * Complex.I) =
        z j ^ pointCount (S j) ω := by
    change Complex.exp ((L (Pi.single j (pointCount (S j) ω : ℝ)) : ℝ) * Complex.I) = _
    rw [linear_single_scalar, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [he]
  exact (generating_pointCount μ (hS j) (z j) (hz j)).symm

/-- Counts in every finite measurable disjoint family are mutually independent.
Their individual Poisson laws are supplied by `pointCount_law`. -/
lemma independent_counts (μ : FiniteMeasure ℝ) (S : ι → Set Point)
    (hS : ∀ j, MeasurableSet (S j)) (hdisj : Pairwise (fun j k => Disjoint (S j) (S k))) :
    iIndepFun (fun j => pointCount (S j)) (configurationLaw μ) := by
  have h := (independent_real_counts μ S hS hdisj).comp
    (fun _ (t : ℝ) => ⌊t⌋₊) (fun _ => measurable_id.nat_floor)
  simpa only [Function.comp_def, Nat.floor_natCast] using h

lemma independent_time_counts (μ : FiniteMeasure ℝ) (T : ι → Set ℝ)
    (hT : ∀ j, MeasurableSet (T j)) (hdisj : Pairwise (fun j k => Disjoint (T j) (T k)))
    (B : ι → Set ℝ) (hB : ∀ j, MeasurableSet (B j)) :
    iIndepFun (fun j => pointCount (T j ×ˢ B j)) (configurationLaw μ) := by
  apply independent_counts μ _ (fun j => (hT j).prod (hB j))
  intro j k hjk
  apply Set.disjoint_left.mpr
  intro p hpj hpk
  exact (Set.disjoint_left.mp (hdisj hjk)) hpj.1 hpk.1

lemma countRate_interval (μ : FiniteMeasure ℝ) (B : Set ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 1) :
    (countRate μ (Ioc s t ×ˢ B) : ℝ) = (t - s) * (μ : Measure ℝ).real B := by
  have hset : Ioc s t ∩ Icc (0 : ℝ) 1 = Ioc s t := by
    ext u
    constructor
    · exact And.left
    · intro hu
      exact ⟨hu, hs.trans hu.1.le, hu.2.trans ht⟩
  rw [countRate_coe_eq_intensity]
  change ((ProphetSecretary.Model.Instance.uniformClock.prod (μ : Measure ℝ)) (Ioc s t ×ˢ B)).toReal = _
  rw [Measure.prod_prod, ENNReal.toReal_mul]
  have hu : ProphetSecretary.Model.Instance.uniformClock (Ioc s t) = ENNReal.ofReal (t - s) := by
    rw [ProphetSecretary.Model.Instance.uniformClock, Measure.restrict_apply measurableSet_Ioc, hset, Real.volume_Ioc]
  rw [hu, ENNReal.toReal_ofReal (sub_nonneg.mpr hst)]
  rfl

end ProphetSecretary.Limiting
