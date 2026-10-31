import ProphetSecretary.Limiting.Campbell
import ProphetSecretary.Limiting.ConfigurationMeasurability
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Finite marked Poisson Palm identity

Deleting a distinguished actual point leaves the same iid array law at one lower
count. The Poisson mass recursion converts the sum over actual occurrences into
integration against the intensity and an independent base configuration. The
auxiliary policy seed is retained, and no point count is supplied to a rule.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical ENNReal NNReal

namespace ProphetSecretary.Limiting

variable {Seed : Type*} [MeasurableSpace Seed]

def erasePoint : (ω : Configuration) → Fin ω.1 → Configuration
  | ⟨0, _v⟩, j => Fin.elim0 j
  | ⟨m + 1, v⟩, j => configurationMk m (fun k => v (j.succAbove k))

def palmCandidate {m : ℕ} (j : Fin (m + 1)) (v : (Fin (m + 1) → Point) × Seed) : Point × World Seed :=
  (v.1 j, (configurationMk m (fun k => v.1 (j.succAbove k)), v.2))

lemma measurable_palmCandidate {m : ℕ} (j : Fin (m + 1)) : Measurable (@palmCandidate Seed m j) := by
  have hv : Measurable (fun v : (Fin (m + 1) → Point) × Seed => fun k : Fin m => v.1 (j.succAbove k)) :=
    measurable_pi_lambda _ (fun k => (measurable_pi_apply (j.succAbove k)).comp measurable_fst)
  exact ((measurable_pi_apply j).comp measurable_fst).prodMk
    (((measurable_configuration_mk m).comp hv).prodMk measurable_snd)

lemma world_fiber_measurePreserving (μ : FiniteMeasure ℝ) (ν : Measure Seed) [SFinite ν] (N : ℕ) :
    MeasurePreserving (fun v : (Fin N → Point) × Seed => (configurationMk N v.1, v.2))
      ((arrayLaw μ N).prod ν) ((fiberLaw μ N).prod ν) := by
  have h : MeasurePreserving (configurationMk N) (arrayLaw μ N) (fiberLaw μ N) :=
    ⟨measurable_configuration_mk N, rfl⟩
  exact h.prod (MeasurePreserving.id ν)

/-- A candidate point is independent of the actually constructed deleted array
and independent auxiliary randomness, under the conditional iid array law. -/
lemma palmCandidate_measurePreserving (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {m : ℕ} (j : Fin (m + 1)) :
    MeasurePreserving (palmCandidate j) ((arrayLaw μ (m + 1)).prod ν)
      ((pointLaw μ).prod ((fiberLaw μ m).prod ν)) := by
  have hsplit := (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => pointLaw μ) j).prod
    (MeasurePreserving.id ν)
  have hassoc := measurePreserving_prodAssoc (pointLaw μ) (arrayLaw μ m) ν
  have hlast := (MeasurePreserving.id (pointLaw μ)).prod (world_fiber_measurePreserving μ ν m)
  exact hlast.comp (hassoc.comp hsplit)

noncomputable def meckeSum (F : Point × World Seed → ℝ≥0∞) (v : World Seed) : ℝ≥0∞ :=
  ∑ j : Fin v.1.1, F (v.1.2 j, (erasePoint v.1 j, v.2))

lemma measurable_meckeSum (F : Point × World Seed → ℝ≥0∞) (hF : Measurable F) : Measurable (meckeSum F) := by
  apply measurable_of_configuration_prod_branches
  intro N
  cases N with
  | zero =>
    change Measurable (fun _ : (Fin 0 → Point) × Seed => (0 : ℝ≥0∞))
    exact measurable_const
  | succ m =>
    change Measurable (fun v : (Fin (m + 1) → Point) × Seed => ∑ j : Fin (m + 1), F (palmCandidate j v))
    exact Finset.measurable_fun_sum _ (fun j _ => hF.comp (measurable_palmCandidate j))

lemma worldLaw_eq_sum_fibers (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    worldLaw μ ν = Measure.sum (fun N : ℕ => ENNReal.ofReal (poissonWeight μ.mass N) • ((fiberLaw μ N).prod ν)) := by
  rw [worldLaw, configurationLaw, Measure.prod_sum_left]
  simp_rw [Measure.prod_smul_left]

lemma lintegral_meckeSum_fiber_zero (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (F : Point × World Seed → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, meckeSum F v ∂(fiberLaw μ 0).prod ν) = 0 := by
  rw [← (world_fiber_measurePreserving μ ν 0).lintegral_comp (measurable_meckeSum F hF)]
  simp [meckeSum, configurationMk]

lemma lintegral_meckeSum_fiber_succ (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (F : Point × World Seed → ℝ≥0∞) (hF : Measurable F) (m : ℕ) :
    (∫⁻ v, meckeSum F v ∂(fiberLaw μ (m + 1)).prod ν) = ((m + 1 : ℕ) : ℝ≥0∞) *
      ∫⁻ q, F q ∂(pointLaw μ).prod ((fiberLaw μ m).prod ν) := by
  rw [← (world_fiber_measurePreserving μ ν (m + 1)).lintegral_comp (measurable_meckeSum F hF)]
  change (∫⁻ v : (Fin (m + 1) → Point) × Seed, ∑ j : Fin (m + 1), F (palmCandidate j v)
    ∂(arrayLaw μ (m + 1)).prod ν) = _
  rw [lintegral_finsetSum' (Finset.univ : Finset (Fin (m + 1)))
    (f := fun j (v : (Fin (m + 1) → Point) × Seed) => F (palmCandidate j v))
    (fun j _ => (hF.comp (measurable_palmCandidate j)).aemeasurable)]
  have he (j : Fin (m + 1)) :
      (∫⁻ v : (Fin (m + 1) → Point) × Seed, F (palmCandidate j v) ∂(arrayLaw μ (m + 1)).prod ν) =
        ∫⁻ q, F q ∂(pointLaw μ).prod ((fiberLaw μ m).prod ν) :=
    (palmCandidate_measurePreserving μ ν j).lintegral_comp hF
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma poissonWeight_succ_ennreal (r : ℝ≥0) (m : ℕ) :
    ENNReal.ofReal (poissonWeight r (m + 1)) * ((m + 1 : ℕ) : ℝ≥0∞) =
      (r : ℝ≥0∞) * ENNReal.ofReal (poissonWeight r m) := by
  have hw : 0 ≤ poissonWeight r (m + 1) := by unfold poissonWeight; positivity
  have hc : ENNReal.ofReal (m + 1 : ℝ) = ((m + 1 : ℕ) : ℝ≥0∞) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (ENNReal.ofReal_natCast (m + 1))
  calc
    _ = ENNReal.ofReal (poissonWeight r (m + 1)) * ENNReal.ofReal (m + 1 : ℝ) := by rw [hc]
    _ = ENNReal.ofReal (poissonWeight r (m + 1) * (m + 1 : ℝ)) := (ENNReal.ofReal_mul hw).symm
    _ = ENNReal.ofReal ((r : ℝ) * poissonWeight r m) := congrArg ENNReal.ofReal (poissonWeight_succ r m)
    _ = ENNReal.ofReal (r : ℝ) * ENNReal.ofReal (poissonWeight r m) := ENNReal.ofReal_mul r.property
    _ = _ := by rw [ENNReal.ofReal_coe_nnreal]

/-- Actual finite-intensity marked Poisson Mecke identity, with independent seed.
The deleted configuration on the left is constructed occurrence by occurrence. -/
lemma mecke (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (F : Point × World Seed → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, meckeSum F v ∂worldLaw μ ν) =
      ∫⁻ q, F q ∂(intensity μ).prod (worldLaw μ ν) := by
  let I := fun N : ℕ => ∫⁻ q, F q ∂(pointLaw μ).prod ((fiberLaw μ N).prod ν)
  have hleft : (∫⁻ v, meckeSum F v ∂worldLaw μ ν) =
      ∑' N : ℕ, ENNReal.ofReal (poissonWeight μ.mass N) * ∫⁻ v, meckeSum F v ∂(fiberLaw μ N).prod ν := by
    rw [worldLaw_eq_sum_fibers, lintegral_sum_measure]
    simp_rw [lintegral_smul_measure, smul_eq_mul]
  have hright : (∫⁻ q, F q ∂(intensity μ).prod (worldLaw μ ν)) =
      (μ.mass : ℝ≥0∞) * ∑' N : ℕ, ENNReal.ofReal (poissonWeight μ.mass N) * I N := by
    rw [intensity_eq_mass_smul_pointLaw, Measure.prod_smul_left, lintegral_smul_measure,
      worldLaw_eq_sum_fibers, Measure.prod_sum_right, lintegral_sum_measure]
    simp_rw [Measure.prod_smul_right, lintegral_smul_measure, smul_eq_mul]
    rfl
  rw [hleft, hright]
  calc
    _ = ENNReal.ofReal (poissonWeight μ.mass 0) * (∫⁻ v, meckeSum F v ∂(fiberLaw μ 0).prod ν) +
        ∑' m : ℕ, ENNReal.ofReal (poissonWeight μ.mass (m + 1)) *
          ∫⁻ v, meckeSum F v ∂(fiberLaw μ (m + 1)).prod ν := tsum_eq_zero_add' ENNReal.summable
    _ = ∑' m : ℕ, ENNReal.ofReal (poissonWeight μ.mass (m + 1)) * (((m + 1 : ℕ) : ℝ≥0∞) * I m) := by
      rw [lintegral_meckeSum_fiber_zero μ ν F hF, mul_zero, zero_add]
      simp_rw [lintegral_meckeSum_fiber_succ μ ν F hF]
      rfl
    _ = ∑' m : ℕ, (μ.mass : ℝ≥0∞) * (ENNReal.ofReal (poissonWeight μ.mass m) * I m) := by
      congr 1
      funext m
      rw [← mul_assoc, poissonWeight_succ_ennreal]
      exact mul_assoc _ _ _
    _ = _ := ENNReal.tsum_mul_left

lemma mecke_iterated (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (F : Point × World Seed → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, meckeSum F v ∂worldLaw μ ν) =
      ∫⁻ p, ∫⁻ v, F (p, v) ∂worldLaw μ ν ∂intensity μ := by
  rw [mecke μ ν F hF, lintegral_prod _ hF.aemeasurable]

end ProphetSecretary.Limiting
