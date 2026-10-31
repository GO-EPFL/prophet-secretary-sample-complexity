import ProphetSecretary.Statistics.FiniteGridPilotWeight
import ProphetSecretary.Statistics.FinitePriorClassifier
import ProphetSecretary.Statistics.FinitePriorBrier
import ProphetSecretary.Model.UnitScalarGap
import ProphetSecretary.Statistics.SmallMeanPilotBound
import Mathlib.Probability.HasLaw

/-!
# The actual visible pilot in a finite-prior experiment

The pilot reads only the first m training columns. Its true-gap expectation
is identified with the prior average of the actual iid m-sample laws. The
atom is used only analytically; neither it nor the ONLINE column is an
input to the pilot.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n m N : ℕ} [NeZero m]

noncomputable def finitePriorPilot (N m : ℕ) [NeZero m] (hN : m≤N) (G : Finset ℝ)
    (lo hi : ℝ) (h0 : 0≤lo) (h1 : hi≤1) (hlohi : lo≤hi) : ValueArray n N → ℝ :=
  fun d => finiteGridPilotWeight G lo hi h0 h1 hlohi (classifierPrefixRead n N m hN d)

lemma measurable_finitePriorPilot (hN : m≤N) (G : Finset ℝ) (lo hi : ℝ)
    (h0 : 0≤lo) (h1 : hi≤1) (hlohi : lo≤hi) :
    Measurable (finitePriorPilot (n:=n) N m hN G lo hi h0 h1 hlohi) :=
  (measurable_finiteGridPilotWeight G lo hi h0 h1 hlohi).comp (measurable_classifierPrefixRead n N m hN)

lemma finitePriorPilot_mem_unit (hN : m≤N) (G : Finset ℝ) (lo hi : ℝ)
    (h0 : 0≤lo) (h1 : hi≤1) (hlohi : lo≤hi) (d : ValueArray n N) :
    finitePriorPilot N m hN G lo hi h0 h1 hlohi d∈Icc (0 : ℝ) 1 := by
  have h := finiteGridPilotWeight_mem G lo hi h0 h1 hlohi (classifierPrefixRead n N m hN d)
  exact ⟨h0.trans h.1,h.2.trans h1⟩

theorem integral_finitePriorPilot_gap (F : FinitePrior n) (hN : m≤N) (G : Finset ℝ) (lo hi : ℝ)
    (h0 : 0≤lo) (h1 : hi≤1) (hlohi : lo≤hi)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1) :
    (∫ ω, normalizedScalarGap (F.offerInstance ω.1)
      (finitePriorPilot N m hN G lo hi h0 h1 hlohi (F.observe N 0 m ω)) ∂F.law N) =
    ∑ θ : Fin F.size, (F.weight θ : ℝ)*
      (∫ y, normalizedScalarGap (F.offerInstance θ) (finiteGridPilotWeight G lo hi h0 h1 hlohi y)
        ∂(F.offerInstance θ).trainingCoordinateLaw m) := by
  let p := finitePriorPilot (n:=n) N m hN G lo hi h0 h1 hlohi
  let f := fun ω : BaseWorld F N => normalizedScalarGap (F.offerInstance ω.1) (p (F.observe N 0 m ω))
  have hp : Measurable p := measurable_finitePriorPilot hN G lo hi h0 h1 hlohi
  have hUnit (d) : p d∈Icc (0 : ℝ) 1 := finitePriorPilot_mem_unit hN G lo hi h0 h1 hlohi d
  have hWeight := hp.comp (F.measurable_observe N 0 m)
  have hMeas : Measurable f := measurable_countable_choice measurable_fst (fun θ =>
    (F.offerInstance θ).measurable_normalizedGap_of_weight
      ((F.offerInstance θ).integrable_maximum_of_bounded (hcap θ)) hWeight (fun ω => hUnit _))
  have hBound (ω : BaseWorld F N) : ‖f ω‖≤1 := by
    have h := (F.offerInstance ω.1).normalizedScalarGap_mem_unit (hcap ω.1) (hUnit (F.observe N 0 m ω))
    change ‖normalizedScalarGap (F.offerInstance ω.1) (p (F.observe N 0 m ω))‖≤1
    rw [Real.norm_eq_abs,abs_of_nonneg h.1]
    exact h.2
  have hAtom (θ : Fin F.size) : Integrable f (F.atomLaw N θ) :=
    Integrable.of_bound hMeas.aestronglyMeasurable 1 (Eventually.of_forall hBound)
  change (∫ ω, f ω ∂F.law N)=_
  rw [law,integral_finsetSum_measure (fun θ _ => (hAtom θ).smul_measure_nnreal)]
  simp only [integral_smul_nnreal_measure,NNReal.smul_def,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro θ _
  congr 1
  have hFirst : MeasurePreserving (Prod.fst : BaseWorld F N → Fin F.size) (F.atomLaw N θ) (Measure.dirac θ) := by
    change MeasurePreserving Prod.fst ((Measure.dirac θ).prod ((F.offerInstance θ).trainingCoordinateLaw (N+1))) _
    exact measurePreserving_fst
  have hDirac : ∀ᵐ t ∂(Measure.dirac θ : Measure (Fin F.size)), t=θ := by simp
  have hKey : ∀ᵐ ω ∂F.atomLaw N θ, ω.1=θ := hFirst.quasiMeasurePreserving.ae hDirac
  have hTest : Measurable (fun y : (Fin n × Fin m) → ℝ =>
      normalizedScalarGap (F.offerInstance θ) (finiteGridPilotWeight G lo hi h0 h1 hlohi y)) :=
    (F.offerInstance θ).measurable_normalizedGap_of_weight
      ((F.offerInstance θ).integrable_maximum_of_bounded (hcap θ))
      (measurable_finiteGridPilotWeight G lo hi h0 h1 hlohi)
      (fun y => by have h := finiteGridPilotWeight_mem G lo hi h0 h1 hlohi y;exact ⟨h0.trans h.1,h.2.trans h1⟩)
  apply Eq.trans _ ((F.classifierPrefix_atom_measurePreserving N m hN θ).hasLaw.integral_comp hTest.aestronglyMeasurable)
  apply integral_congr_ae
  filter_upwards [hKey] with ω hω
  change normalizedScalarGap (F.offerInstance ω.1) (p (F.observe N 0 m ω))=_
  rw [hω]
  have hRead := F.classifierPrefix_eq_observed N m hN ω
  exact congrArg (fun y => normalizedScalarGap (F.offerInstance θ) (finiteGridPilotWeight G lo hi h0 h1 hlohi y)) hRead.symm

/-- Integrate the true iid pilot bounds under the finite-prior experiment. -/
theorem integral_finitePriorPilot_gap_le (F : FinitePrior n) (hN : m≤N) (G : Finset ℝ)
    {b Kc Kp S0 : ℝ} (hb : b∈Ioo (4/5 : ℝ) 1) (hKp : 0≤Kp)
    (hcap : ∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1)
    (hS : ∀ θ, (F.offerInstance θ).totalFirstMoment≤S0)
    (hPilot : ∀ θ, (∫ y, normalizedScalarGap (F.offerInstance θ)
      (finiteGridPilotWeight G (4/5) b (by norm_num) hb.2.le hb.1.le y)
      ∂(F.offerInstance θ).trainingCoordinateLaw m)≤
      Kc*minimumNormalizedScalarGap (F.offerInstance θ)+
        Kp*(1+(F.offerInstance θ).totalFirstMoment)^2/(m : ℝ)) :
    (∫ ω, normalizedScalarGap (F.offerInstance ω.1)
      (finitePriorPilot N m hN G (4/5) b (by norm_num) hb.2.le hb.1.le
        (F.observe N 0 m ω)) ∂F.law N)≤
      Kc*(∑ θ : Fin F.size, (F.weight θ : ℝ)*minimumNormalizedScalarGap (F.offerInstance θ))+
        Kp*(1+S0)^2/(m : ℝ) := by
  rw [integral_finitePriorPilot_gap F hN G (4/5) b (by norm_num) hb.2.le hb.1.le hcap]
  have hSum : (∑ θ : Fin F.size, (F.weight θ : ℝ))=1 := by exact_mod_cast F.weight_sum
  calc
    _ ≤ ∑ θ : Fin F.size, (F.weight θ : ℝ)*
        (Kc*minimumNormalizedScalarGap (F.offerInstance θ)+Kp*(1+S0)^2/(m : ℝ)) := by
      apply Finset.sum_le_sum
      intro θ _
      apply mul_le_mul_of_nonneg_left _ (F.weight θ).coe_nonneg
      have hP := hPilot θ
      have hNonneg : 0≤(F.offerInstance θ).totalFirstMoment :=
        Finset.sum_nonneg (fun i _ => integral_nonneg_of_ae ((F.offerInstance θ).nonnegative i))
      have hSq : (1+(F.offerInstance θ).totalFirstMoment)^2≤(1+S0)^2 := by
        nlinarith only [sq_nonneg (S0-(F.offerInstance θ).totalFirstMoment),hS θ,hNonneg]
      have hErr := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hSq hKp) (Nat.cast_nonneg m)
      exact hP.trans (add_le_add_right hErr _)
    _ = _ := by
      simp only [mul_add,Finset.sum_add_distrib]
      rw [←Finset.sum_mul,hSum,one_mul,Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro θ _
      ring

/-- Prior averaging of the actual pilot guarantee. All constants and the
interval are chosen before the number of variables or the finite prior. -/
theorem exists_finitePriorPilot_bound (mu : ℝ) (hmu : 0<mu) :
    ∃ b : ℝ, ∃ hb : b∈Ioo (4/5 : ℝ) 1, ∃ Kc Kpilot : ℝ, 0<Kc ∧ 0<Kpilot ∧
      ∀ (n N m : ℕ) [NeZero m] (F : FinitePrior n) (hN : m≤N) (G : Finset ℝ) (S0 : ℝ),
        (∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1) →
        (∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x∈G) →
        (∀ θ, mu≤(F.offerInstance θ).expectedMaximum) →
        (∀ θ, (F.offerInstance θ).expectedMaximum≤1/80) →
        (∀ θ, (F.offerInstance θ).totalFirstMoment≤S0) →
        (∫ ω, normalizedScalarGap (F.offerInstance ω.1)
          (finitePriorPilot N m hN G (4/5) b (by norm_num) hb.2.le hb.1.le
            (F.observe N 0 m ω)) ∂F.law N) ≤
          Kc*(∑ θ : Fin F.size, (F.weight θ : ℝ)*minimumNormalizedScalarGap (F.offerInstance θ))+
            Kpilot*(1+S0)^2/(m : ℝ) := by
  obtain ⟨b,hb,Kc,Kp,hKc,hKp,hAll⟩ := bounded_smallMean_clamp_and_pilot mu hmu
  refine ⟨b,hb,Kc,Kp,hKc,hKp,?_⟩
  intro n N m hm F hN G S0 hcap hG hMean hSmall hS
  exact integral_finitePriorPilot_gap_le F hN G hb hKp.le hcap hS
    (fun θ => (hAll n (F.offerInstance θ) (hcap θ) (hMean θ) (hSmall θ)).2 m G (hG θ))

end ProphetSecretary.Statistics.FinitePrior
