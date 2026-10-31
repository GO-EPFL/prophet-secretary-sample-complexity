import ProphetSecretary.Probability.FiniteRoundingCoupling
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Independent product coupling for finite probability rounding

Each coordinate is coupled by keeping its atom or replacing it with zero.
The probability that any coordinate changes is at most the sum of moved
masses. For training and online data the coordinate index includes every
sample and the independent online copy, so adaptive policies are covered.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Probability

variable {ι Θ : Type*} [Fintype ι] [Fintype Θ] [DecidableEq Θ]
  [MeasurableSpace Θ] [MeasurableSingletonClass Θ]

noncomputable def roundingProductCoupling (p : ι → Θ → ℝ)
    (hp : ∀ i, p i∈stdSimplex ℝ Θ) (N : ℕ) (hN : 0<N) (z : Θ) : Measure (ι → Θ × Θ) :=
  Measure.pi (fun i => roundingCoupling (p i) (hp i) N hN z)

instance roundingProductCoupling_probability (p : ι → Θ → ℝ)
    (hp : ∀ i, p i∈stdSimplex ℝ Θ) (N : ℕ) (hN : 0<N) (z : Θ) :
    IsProbabilityMeasure (roundingProductCoupling p hp N hN z) := by
  unfold roundingProductCoupling
  infer_instance

lemma roundingProductCoupling_fst (p : ι → Θ → ℝ)
    (hp : ∀ i, p i∈stdSimplex ℝ Θ) (N : ℕ) (hN : 0<N) (z : Θ) :
    MeasurePreserving (fun a i => (a i).1) (roundingProductCoupling p hp N hN z)
      (Measure.pi (fun i => finiteSimplexLaw (p i) (hp i))) :=
  measurePreserving_pi _ _ (fun i => roundingCoupling_fst (p i) (hp i) N hN z)

lemma roundingProductCoupling_snd (p : ι → Θ → ℝ)
    (hp : ∀ i, p i∈stdSimplex ℝ Θ) (N : ℕ) (hN : 0<N) (z : Θ) :
    MeasurePreserving (fun a i => (a i).2) (roundingProductCoupling p hp N hN z)
      (Measure.pi (fun i => finiteSimplexLaw (roundedProbability (p i) N z)
        (roundedProbability_simplex (p i) (hp i) hN z))) :=
  measurePreserving_pi _ _ (fun i => roundingCoupling_snd (p i) (hp i) N hN z)

lemma roundingProductCoupling_mismatch_le (p : ι → Θ → ℝ)
    (hp : ∀ i, p i∈stdSimplex ℝ Θ) (N : ℕ) (hN : 0<N) (z : Θ) :
    (roundingProductCoupling p hp N hN z).real {a | ∃ i, (a i).1≠(a i).2} ≤
      ∑ i, roundingLoss (p i) N z := by
  have hSet : {a : ι → Θ × Θ | ∃ i, (a i).1≠(a i).2} =
      ⋃ i, {a | (a i).1≠(a i).2} := by ext a; simp
  rw [hSet]
  apply (measureReal_iUnion_fintype_le _).trans
  apply Finset.sum_le_sum
  intro i _
  have he := measurePreserving_eval (fun j => roundingCoupling (p j) (hp j) N hN z) i
  have hMap : (roundingProductCoupling p hp N hN z).map (Function.eval i)=roundingCoupling (p i) (hp i) N hN z := he.map_eq
  have hMass := map_measureReal_apply (μ:=roundingProductCoupling p hp N hN z) he.measurable
    (Set.toFinite {ab : Θ × Θ | ab.1≠ab.2}).measurableSet
  rw [hMap,roundingCoupling_mismatch] at hMass
  exact hMass.symm.le

lemma roundingProductCoupling_mismatch_card_bound (p : ι → Θ → ℝ)
    (hp : ∀ i, p i∈stdSimplex ℝ Θ) (N : ℕ) (hN : 0<N) (z : Θ) :
    (roundingProductCoupling p hp N hN z).real {a | ∃ i, (a i).1≠(a i).2} ≤
      (Fintype.card ι : ℝ)*((Fintype.card Θ-1 : ℕ) : ℝ)/(N : ℝ) := by
  apply (roundingProductCoupling_mismatch_le p hp N hN z).trans
  calc
    _ ≤ ∑ _i : ι, (((Fintype.card Θ-1 : ℕ) : ℝ)/(N : ℝ)) :=
      Finset.sum_le_sum (fun i _ => roundingLoss_le (p i) N hN z)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

lemma roundingProductCoupling_value_le (p : ι → Θ → ℝ)
    (hp : ∀ i, p i∈stdSimplex ℝ Θ) (N : ℕ) (hN : 0<N) (z : Θ)
    (v : Θ → ℝ) (hv : ∀ a, 0≤v a) (hz : v z=0) :
    ∀ᵐ a ∂roundingProductCoupling p hp N hN z, ∀ i, v (a i).2 ≤ v (a i).1 := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval (fun j => roundingCoupling (p j) (hp j) N hN z) i).quasiMeasurePreserving.ae
    (roundingCoupling_value_le (p i) (hp i) N hN z v hv hz)

lemma roundingProductCoupling_observable_error {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (p : ι → Θ → ℝ)
    (hp : ∀ i, p i∈stdSimplex ℝ Θ) (N : ℕ) (hN : 0<N) (z : Θ)
    (f : (ι → Θ) × Seed → ℝ) (hf : Measurable f) {D : ℝ} (hD : 0≤D)
    (hfBound : ∀ a, 0≤f a ∧ f a≤D) :
    |(∫ a, f a ∂(Measure.pi (fun i => finiteSimplexLaw (p i) (hp i))).prod ν)-
      ∫ a, f a ∂(Measure.pi (fun i => finiteSimplexLaw (roundedProbability (p i) N z)
        (roundedProbability_simplex (p i) (hp i) hN z))).prod ν| ≤
      D*∑ i, roundingLoss (p i) N z := by
  let γ := roundingProductCoupling p hp N hN z
  let μ := γ.prod ν
  let F : (ι → Θ × Θ) × Seed → (ι → Θ) × Seed := fun a => ((fun i => (a.1 i).1),a.2)
  let G : (ι → Θ × Θ) × Seed → (ι → Θ) × Seed := fun a => ((fun i => (a.1 i).2),a.2)
  have hF : MeasurePreserving F μ ((Measure.pi (fun i => finiteSimplexLaw (p i) (hp i))).prod ν) :=
    (roundingProductCoupling_fst p hp N hN z).prod (MeasurePreserving.id ν)
  have hG : MeasurePreserving G μ
      ((Measure.pi (fun i => finiteSimplexLaw (roundedProbability (p i) N z)
        (roundedProbability_simplex (p i) (hp i) hN z))).prod ν) :=
    (roundingProductCoupling_snd p hp N hN z).prod (MeasurePreserving.id ν)
  have hIF : Integrable (f ∘ F) μ := Integrable.of_bound (hf.comp hF.measurable).aestronglyMeasurable D
    (Filter.Eventually.of_forall (fun a => by
      change |f (F a)|≤D
      rw [abs_of_nonneg (hfBound (F a)).1]
      exact (hfBound (F a)).2))
  have hIG : Integrable (f ∘ G) μ := Integrable.of_bound (hf.comp hG.measurable).aestronglyMeasurable D
    (Filter.Eventually.of_forall (fun a => by
      change |f (G a)|≤D
      rw [abs_of_nonneg (hfBound (G a)).1]
      exact (hfBound (G a)).2))
  have hXF : ProbabilityTheory.HasLaw F _ μ := ⟨hF.measurable.aemeasurable,hF.map_eq⟩
  have hXG : ProbabilityTheory.HasLaw G _ μ := ⟨hG.measurable.aemeasurable,hG.map_eq⟩
  rw [← hXF.integral_comp hf.aestronglyMeasurable, ← hXG.integral_comp hf.aestronglyMeasurable,
    ← integral_sub hIF hIG]
  let E : Set ((ι → Θ × Θ) × Seed) := {a | ∃ i, (a.1 i).1≠(a.1 i).2}
  have hE : MeasurableSet E := (Set.toFinite {a : ι → Θ × Θ | ∃ i, (a i).1≠(a i).2}).measurableSet.preimage measurable_fst
  have hEVal : μ.real E=γ.real {a | ∃ i, (a i).1≠(a i).2} := by
    have hFirst : MeasurePreserving Prod.fst μ γ := measurePreserving_fst
    have hMass := map_measureReal_apply (μ:=μ) hFirst.measurable
      (Set.toFinite {a : ι → Θ × Θ | ∃ i, (a i).1≠(a i).2}).measurableSet
    rw [hFirst.map_eq] at hMass
    exact hMass.symm
  calc
    _ ≤ ∫ a, |f (F a)-f (G a)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ a, E.indicator (fun _ => D) a ∂μ := by
      apply integral_mono (hIF.sub hIG).abs ((integrable_const D).indicator hE)
      intro a
      change |f (F a)-f (G a)| ≤ E.indicator (fun _ => D) a
      by_cases ha : a∈E
      · rw [Set.indicator_of_mem ha]
        exact abs_le.mpr ⟨by linarith only [(hfBound (F a)).1,(hfBound (G a)).2],
          by linarith only [(hfBound (F a)).2,(hfBound (G a)).1]⟩
      · have hSame : F a=G a := by
          apply Prod.ext
          · funext i
            exact Classical.not_not.mp (fun hi => ha ⟨i,hi⟩)
          · rfl
        simp [Set.indicator_of_notMem ha,hSame]
    _ = D*μ.real E := by rw [integral_indicator_const _ hE,smul_eq_mul,mul_comm]
    _ ≤ D*∑ i, roundingLoss (p i) N z := by
      rw [hEVal]
      exact mul_le_mul_of_nonneg_left (roundingProductCoupling_mismatch_le p hp N hN z) hD

end ProphetSecretary.Probability
