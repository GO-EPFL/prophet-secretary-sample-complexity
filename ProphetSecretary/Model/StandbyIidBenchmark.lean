import ProphetSecretary.Model.StandbyIidReward

/-! # Prophet benchmark of a standby and iid offers
Only the independent value law is used in these analytical tail calculations.
The formulas do not supply future offers to the online observer.
-/
open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Model

lemma maximum_standby_coordinates {m : ℕ} (a : ℝ) (ha : 0 ≤ a) (x : Fin (m + 1) → ℝ)
    (hx : x 0 = a) :
    Instance.maximum x = max a (Instance.maximum (fun i : Fin m ↦ x i.succ)) := by
  apply le_antisymm
  · apply Instance.maximum_le x (ha.trans (le_max_left _ _))
    intro i
    cases i using Fin.cases with
    | zero => rw [hx]; exact le_max_left _ _
    | succ i => exact (Instance.le_maximum (fun j : Fin m ↦ x j.succ) i).trans (le_max_right _ _)
  · apply max_le
    · simpa only [hx] using Instance.le_maximum x 0
    · apply Instance.maximum_le _ (Instance.maximum_nonnegative x)
      intro i
      exact Instance.le_maximum x i.succ

lemma standbyIidInstance_expectedMaximum (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (a : ℝ) (ha : 0 ≤ a) (m : ℕ) :
    (standbyIidInstance μ hμ a ha m).expectedMaximum =
      ∫ x : Fin m → ℝ, max a (Instance.maximum x) ∂Measure.pi (fun _ : Fin m ↦ μ) := by
  let P := standbyIidInstance μ hμ a ha m
  have hp := P.restrictValues_measurePreserving (Fin.succAboveEmb (0 : Fin (m + 1)))
  have hX : ∀ᵐ x ∂P.valuesLaw, x 0 = a := by
    have h : ∀ᵐ z ∂P.law 0, z = a := by simp [P]
    exact (measurePreserving_eval P.law 0).quasiMeasurePreserving.ae h
  have hEq : Instance.maximum =ᵐ[P.valuesLaw] fun x ↦ max a (Instance.maximum (fun i : Fin m ↦ x i.succ)) :=
    hX.mono (fun x hx ↦ maximum_standby_coordinates a ha x hx)
  unfold Instance.expectedMaximum
  rw [integral_congr_ae hEq]
  have hm : Measurable (fun x : Fin m → ℝ ↦ max a (Instance.maximum x)) := measurable_const.max Instance.measurable_maximum
  have he := integral_map (μ := P.valuesLaw) hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at he
  change (∫ x : Fin m → ℝ, max a (Instance.maximum x) ∂(P.child 0).valuesLaw) = _ at he
  rw [standbyIidInstance_child_zero] at he
  exact he.symm

def anyOfferAtLeast {m : ℕ} (b : ℝ) : Set (Fin m → ℝ) := {x | ∃ i, b ≤ x i}

lemma measurableSet_anyOfferAtLeast {m : ℕ} (b : ℝ) : MeasurableSet (@anyOfferAtLeast m b) := by
  change MeasurableSet {x : Fin m → ℝ | ∃ i : Fin m, b ≤ x i}
  simpa only [Set.iUnion_setOf] using MeasurableSet.iUnion (fun i : Fin m ↦
    measurableSet_le measurable_const (measurable_pi_apply i))

lemma iid_anyOfferAtLeast_probability (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℕ) (b : ℝ) :
    (Measure.pi (fun _ : Fin m ↦ μ)).real (anyOfferAtLeast b) = 1 - (μ.real (Iio b)) ^ m := by
  have hEq : anyOfferAtLeast b = (Set.pi univ (fun _ : Fin m ↦ Iio b))ᶜ := by
    ext x
    simp only [anyOfferAtLeast, mem_setOf_eq, mem_compl_iff, mem_pi, mem_univ,
      forall_const, mem_Iio, not_forall, not_lt]
  rw [hEq, measureReal_compl (MeasurableSet.pi Set.countable_univ (fun _ _ ↦ measurableSet_Iio)), probReal_univ]
  congr 1
  unfold Measure.real
  rw [Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow]

lemma two_level_standby_lower {m : ℕ} {a b J : ℝ} (_hab : a ≤ b) (hbJ : b ≤ J)
    (x : Fin m → ℝ) :
    a + (b - a) * (anyOfferAtLeast b).indicator (fun _ ↦ (1 : ℝ)) x +
      (J - b) * (anyOfferAtLeast J).indicator (fun _ ↦ (1 : ℝ)) x ≤ max a (Instance.maximum x) := by
  by_cases hJ : x ∈ anyOfferAtLeast J
  · obtain ⟨i, hi⟩ := hJ
    have hb : x ∈ anyOfferAtLeast b := ⟨i, hbJ.trans hi⟩
    rw [Set.indicator_of_mem hb, Set.indicator_of_mem (show x ∈ anyOfferAtLeast J from ⟨i, hi⟩)]
    have hl := hi.trans ((Instance.le_maximum x i).trans (le_max_right a _))
    linarith
  · rw [Set.indicator_of_notMem hJ]
    by_cases hb : x ∈ anyOfferAtLeast b
    · obtain ⟨i, hi⟩ := hb
      rw [Set.indicator_of_mem (show x ∈ anyOfferAtLeast b from ⟨i, hi⟩)]
      have hl := hi.trans ((Instance.le_maximum x i).trans (le_max_right a _))
      linarith
    · rw [Set.indicator_of_notMem hb]
      simpa only [mul_zero, add_zero] using le_max_left a (Instance.maximum x)

lemma standbyIidInstance_expectedMaximum_ge_two_levels (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, 0 ≤ x) (hi : Integrable id μ) {a b J : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hbJ : b ≤ J) (m : ℕ) :
    a + (b - a) * (1 - (μ.real (Iio b)) ^ m) + (J - b) * (1 - (μ.real (Iio J)) ^ m) ≤
      (standbyIidInstance μ hμ a ha m).expectedMaximum := by
  let ν := Measure.pi (fun _ : Fin m ↦ μ)
  have hb := measurableSet_anyOfferAtLeast (m := m) b
  have hJ := measurableSet_anyOfferAtLeast (m := m) J
  have hIb : Integrable ((anyOfferAtLeast b).indicator (fun _ ↦ (1 : ℝ))) ν := (integrable_const 1).indicator hb
  have hIJ : Integrable ((anyOfferAtLeast J).indicator (fun _ ↦ (1 : ℝ))) ν := (integrable_const 1).indicator hJ
  have hMax : Integrable (fun x : Fin m → ℝ ↦ max a (Instance.maximum x)) ν :=
    (integrable_const a).sup (iidOfferInstance_integrable μ hμ hi m)
  have hInt := integral_mono (((integrable_const a).add (hIb.const_mul (b - a))).add (hIJ.const_mul (J - b))) hMax
    (two_level_standby_lower hab hbJ)
  simp only [Pi.add_apply] at hInt
  rw [integral_add (f := fun x : Fin m → ℝ ↦ a + (b - a) * (anyOfferAtLeast b).indicator (fun _ ↦ (1 : ℝ)) x)
      (g := fun x ↦ (J - b) * (anyOfferAtLeast J).indicator (fun _ ↦ (1 : ℝ)) x) ((integrable_const a).add (hIb.const_mul (b - a))) (hIJ.const_mul (J - b)),
    integral_add (integrable_const a) (hIb.const_mul (b - a)), integral_const_mul, integral_const_mul,
    integral_const, probReal_univ, one_smul] at hInt
  have hEb : (∫ x : Fin m → ℝ, (anyOfferAtLeast b).indicator (fun _ ↦ (1 : ℝ)) x ∂ν) = ν.real (anyOfferAtLeast b) := by
    simpa only [Set.indicator, Pi.one_apply] using integral_indicator_one (μ := ν) hb
  have hEJ : (∫ x : Fin m → ℝ, (anyOfferAtLeast J).indicator (fun _ ↦ (1 : ℝ)) x ∂ν) = ν.real (anyOfferAtLeast J) := by
    simpa only [Set.indicator, Pi.one_apply] using integral_indicator_one (μ := ν) hJ
  rw [hEb, hEJ] at hInt
  dsimp only [ν] at hInt
  rw [iid_anyOfferAtLeast_probability μ m b, iid_anyOfferAtLeast_probability μ m J] at hInt
  rw [standbyIidInstance_expectedMaximum μ hμ a ha m]
  exact hInt

end ProphetSecretary.Model
