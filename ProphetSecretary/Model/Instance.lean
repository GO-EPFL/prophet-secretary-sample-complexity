import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Order.Lattice

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal

namespace ProphetSecretary.Model

/-- A finite independent instance. Nonnegativity is almost sure and no boundedness or
finite-support restriction is imposed. Integrability is stated separately. -/
structure Instance (n : ℕ) where
  law : Fin n → Measure ℝ
  probability : ∀ i, IsProbabilityMeasure (law i)
  nonnegative : ∀ i, ∀ᵐ x ∂law i, 0 ≤ x

attribute [instance] Instance.probability

namespace Instance

variable {n : ℕ} (P : Instance n)

/-- Product distribution of the complete offer vector. -/
noncomputable def valuesLaw : Measure (Fin n → ℝ) := Measure.pi P.law

instance valuesLaw_probability : IsProbabilityMeasure P.valuesLaw := by
  dsimp [valuesLaw]
  infer_instance

/-- Independent uniforms on `[0,1]`, including endpoints (which are null). -/
noncomputable def uniformClock : Measure ℝ := volume.restrict (Icc (0 : ℝ) 1)

instance uniformClock_probability : IsProbabilityMeasure uniformClock := by
  constructor
  simp [uniformClock]

noncomputable def clocksLaw (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun _ => uniformClock)

instance clocksLaw_probability : IsProbabilityMeasure (clocksLaw n) := by
  dsimp [clocksLaw]
  infer_instance

/-- The seed is independent auxiliary randomness; it may itself encode training data. -/
noncomputable def worldLaw {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) :
    Measure ((Fin n → ℝ) × ((Fin n → ℝ) × Seed)) :=
  P.valuesLaw.prod ((clocksLaw n).prod ν)

instance worldLaw_probability {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] : IsProbabilityMeasure (P.worldLaw ν) := by
  dsimp [worldLaw]
  infer_instance

/-- The realized maximum, with value zero for the empty instance. The extra `none`
coordinate implements that convention and is harmless for nonnegative offers. -/
noncomputable def maximum (x : Fin n → ℝ) : ℝ :=
  Finset.univ.sup' (by exact ⟨none, Finset.mem_univ _⟩)
    (fun j : Option (Fin n) => j.elim 0 x)

lemma maximum_nonnegative (x : Fin n → ℝ) : 0 ≤ maximum x := by
  exact Finset.le_sup' (fun j : Option (Fin n) => j.elim 0 x) (Finset.mem_univ none)

lemma le_maximum (x : Fin n → ℝ) (i : Fin n) : x i ≤ maximum x := by
  exact Finset.le_sup' (fun j : Option (Fin n) => j.elim 0 x) (Finset.mem_univ (some i))

lemma maximum_le (x : Fin n → ℝ) {b : ℝ} (hb : 0 ≤ b) (h : ∀ i, x i ≤ b) :
    maximum x ≤ b := by
  apply Finset.sup'_le
  intro j _
  cases j with
  | none => exact hb
  | some i => exact h i

lemma measurable_maximum : Measurable (@maximum n) := by
  have h : Measurable ((Finset.univ : Finset (Option (Fin n))).sup'
      (by exact ⟨none, Finset.mem_univ _⟩)
      (fun j : Option (Fin n) => fun x : Fin n → ℝ => j.elim 0 x)) := by
    apply Finset.measurable_sup'
    intro j _
    cases j with
    | none => exact measurable_const
    | some i => exact measurable_pi_apply i
  convert h using 1
  funext x
  exact (Finset.sup'_apply _ _ _).symm

lemma maximum_le_sum_abs (x : Fin n → ℝ) : maximum x ≤ ∑ i, |x i| := by
  apply maximum_le x (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  intro i
  exact (le_abs_self _).trans (Finset.single_le_sum (fun j _ => abs_nonneg (x j))
    (Finset.mem_univ i))

lemma integrable_coordinate (h : ∀ i, Integrable id (P.law i)) (i : Fin n) :
    Integrable (fun x : Fin n → ℝ => x i) P.valuesLaw := by
  exact (measurePreserving_eval P.law i).integrable_comp_of_integrable (h i)

lemma integrable_maximum (h : ∀ i, Integrable id (P.law i)) :
    Integrable maximum P.valuesLaw := by
  have hsum : Integrable (fun x : Fin n → ℝ => ∑ i, |x i|) P.valuesLaw := by
    exact integrable_finsetSum _ (fun i _ => (P.integrable_coordinate h i).abs)
  apply hsum.mono' measurable_maximum.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs, abs_of_nonneg (maximum_nonnegative x)] using maximum_le_sum_abs x

lemma ae_nonnegative : ∀ᵐ x ∂P.valuesLaw, ∀ i, 0 ≤ x i := by
  rw [ae_all_iff]
  intro i
  exact (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (P.nonnegative i)

lemma integrable_coordinate_of_maximum (h : Integrable maximum P.valuesLaw) (i : Fin n) :
    Integrable (fun x : Fin n → ℝ => x i) P.valuesLaw := by
  apply h.mono' (measurable_pi_apply i).aestronglyMeasurable
  filter_upwards [P.ae_nonnegative] with x hx
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hx i)] using le_maximum x i

lemma integrable_maximum_iff :
    Integrable maximum P.valuesLaw ↔ ∀ i, Integrable id (P.law i) := by
  refine ⟨fun h i => ?_, P.integrable_maximum⟩
  exact ((measurePreserving_eval P.law i).integrable_comp aestronglyMeasurable_id).mp
    (P.integrable_coordinate_of_maximum h i)

lemma maximum_le_sum {x : Fin n → ℝ} (hx : ∀ i, 0 ≤ x i) :
    maximum x ≤ ∑ i, x i := by
  apply maximum_le x (Finset.sum_nonneg fun i _ => hx i)
  intro i
  exact Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)

/-- `M(P)` in the manuscript. Only used as an expectation when `maximum` is integrable. -/
noncomputable def expectedMaximum : ℝ := ∫ x, maximum x ∂P.valuesLaw

/-- `S(P)`: the sum of marginal first moments. -/
noncomputable def totalFirstMoment : ℝ := ∑ i, ∫ x, x ∂P.law i

/-- `L_b(P)`: the expected number of offers strictly above `b`. -/
noncomputable def tailCount (b : ℝ) : ℝ := ∑ i, (P.law i (Ioi b)).toReal

/-- `L(P)`: the expected number of positive offers. -/
noncomputable def positiveCount : ℝ := P.tailCount 0

lemma expectedMaximum_nonnegative : 0 ≤ P.expectedMaximum := by
  exact integral_nonneg fun _ => maximum_nonnegative _

lemma tailCount_nonnegative (b : ℝ) : 0 ≤ P.tailCount b := by
  exact Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg

lemma tailCount_le_card (b : ℝ) : P.tailCount b ≤ n := by
  calc
    P.tailCount b ≤ ∑ _ : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact ENNReal.toReal_le_of_le_ofReal (by norm_num) (by simpa using (prob_le_one (μ := P.law i) (s := Ioi b)))
    _ = n := by simp

lemma tailCount_antitone : Antitone P.tailCount := by
  intro a b hab
  apply Finset.sum_le_sum
  intro i _
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun _ hx => hab.trans_lt hx))

lemma integral_coordinate (i : Fin n) :
    ∫ x : Fin n → ℝ, x i ∂P.valuesLaw = ∫ x : ℝ, x ∂P.law i := by
  have hm := (measurePreserving_eval P.law i).map_eq
  change P.valuesLaw.map (fun x => x i) = P.law i at hm
  rw [← hm]
  exact (integral_map (μ := P.valuesLaw) (φ := fun x : Fin n → ℝ => x i)
    (f := id) (measurable_pi_apply i).aemeasurable aestronglyMeasurable_id).symm

lemma expectedMaximum_le_totalFirstMoment (h : Integrable maximum P.valuesLaw) :
    P.expectedMaximum ≤ P.totalFirstMoment := by
  have hi := P.integrable_maximum_iff.mp h
  calc
    P.expectedMaximum ≤ ∫ x, ∑ i, x i ∂P.valuesLaw := by
      apply integral_mono_ae h (integrable_finsetSum _ (fun i _ => P.integrable_coordinate hi i))
      exact P.ae_nonnegative.mono fun x hx => maximum_le_sum hx
    _ = P.totalFirstMoment := by
      rw [integral_finsetSum _ (fun i _ => P.integrable_coordinate hi i)]
      apply Finset.sum_congr rfl
      intro i _
      exact P.integral_coordinate i

lemma totalFirstMoment_le_card_mul_expectedMaximum (h : Integrable maximum P.valuesLaw) :
    P.totalFirstMoment ≤ n * P.expectedMaximum := by
  calc
    P.totalFirstMoment ≤ ∑ _ : Fin n, P.expectedMaximum := by
      apply Finset.sum_le_sum
      intro i _
      rw [← P.integral_coordinate i]
      exact integral_mono_ae (P.integrable_coordinate_of_maximum h i) h
        (Filter.Eventually.of_forall fun x => le_maximum x i)
    _ = n * P.expectedMaximum := by simp [nsmul_eq_mul]

/-- An auxiliary bounded instance may have expected maximum zero. -/
lemma integrable_maximum_of_bounded {H : ℝ}
    (h : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) : Integrable maximum P.valuesLaw := by
  apply P.integrable_maximum
  intro i
  apply Integrable.of_bound aestronglyMeasurable_id H
  filter_upwards [P.nonnegative i, h i] with x hx hbound
  simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg hx] using hbound

lemma expectedMaximum_le_of_bounded {H : ℝ} (hH : 0 ≤ H)
    (h : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) : P.expectedMaximum ≤ H := by
  have hb : ∀ᵐ x ∂P.valuesLaw, ∀ i, x i ≤ H := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (h i)
  calc
    P.expectedMaximum ≤ ∫ _ : Fin n → ℝ, H ∂P.valuesLaw := by
      apply integral_mono_ae (P.integrable_maximum_of_bounded h) (integrable_const H)
      exact hb.mono fun x hx => maximum_le x hH hx
    _ = H := by simp

/-- The positive finite benchmark restriction. Bounded auxiliary instances need not satisfy it. -/
def HasPositiveFiniteMaximum : Prop :=
  Integrable maximum P.valuesLaw ∧ 0 < P.expectedMaximum

end Instance
end ProphetSecretary.Model
