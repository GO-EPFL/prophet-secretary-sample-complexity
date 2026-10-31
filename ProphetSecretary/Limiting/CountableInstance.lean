import ProphetSecretary.Limiting.HybridScalarObjectives
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Countable individual laws and finite truncations

The data in `def:limiting-body` are represented after erasing anonymous marks at
most the terminal reserve, as permitted there. Individual laws are never erased:
their zero arrivals remain observations. Product laws below construct the
independent individual values, clocks, and auxiliary randomness. General observable
histories and admissible stopping rules are defined from these independent laws.
The instance fields specify laws, support and positive-level tail finiteness.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting

structure CountableInstance where
  cap : ℝ≥0
  terminal : ℝ≥0
  terminal_le_cap : terminal ≤ cap
  individuals : ℕ → ProbabilityMeasure ℝ
  individual_supported : ∀ i, ∀ᵐ x ∂(individuals i : Measure ℝ), x ∈ Icc (0 : ℝ) cap
  intensity : Measure ℝ
  intensity_supported : ∀ᵐ x ∂intensity, x ∈ Ioc (terminal : ℝ) cap
  individual_tail_finite : ∀ b : ℝ, (terminal : ℝ) < b →
    (∑' i, (individuals i : Measure ℝ) (Ioi b)) < ⊤
  intensity_tail_finite : ∀ b : ℝ, (terminal : ℝ) < b → intensity (Ioi b) < ⊤

namespace CountableInstance

variable (B : CountableInstance)

noncomputable def individualValuesLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun i => (B.individuals i : Measure ℝ))

instance individualValuesLaw_probability : IsProbabilityMeasure B.individualValuesLaw := by
  unfold individualValuesLaw
  infer_instance

noncomputable def individualClocksLaw : Measure (ℕ → ℝ) :=
  Measure.infinitePi (fun _ : ℕ => Model.Instance.uniformClock)

instance individualClocksLaw_probability : IsProbabilityMeasure individualClocksLaw := by
  unfold individualClocksLaw
  infer_instance

lemma individualValues_independent :
    iIndepFun (fun i (x : ℕ → ℝ) => x i) B.individualValuesLaw :=
  iIndepFun_infinitePi (fun _ => measurable_id)

lemma individualClocks_independent :
    iIndepFun (fun i (u : ℕ → ℝ) => u i) individualClocksLaw :=
  iIndepFun_infinitePi (fun _ => measurable_id)

lemma individualValue_measurePreserving (i : ℕ) :
    MeasurePreserving (fun x : ℕ → ℝ => x i) B.individualValuesLaw (B.individuals i : Measure ℝ) :=
  measurePreserving_eval_infinitePi _ i

lemma individualClock_measurePreserving (i : ℕ) :
    MeasurePreserving (fun u : ℕ → ℝ => u i) individualClocksLaw Model.Instance.uniformClock :=
  measurePreserving_eval_infinitePi _ i

noncomputable def individualWorldLaw {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) :
    Measure ((ℕ → ℝ) × ((ℕ → ℝ) × Seed)) :=
  B.individualValuesLaw.prod (individualClocksLaw.prod ν)

instance individualWorldLaw_probability {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] : IsProbabilityMeasure (B.individualWorldLaw ν) := by
  unfold individualWorldLaw
  infer_instance

lemma individual_values_clocks_seed_independent {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    IndepFun Prod.fst Prod.snd (B.individualWorldLaw ν) :=
  indepFun_prod measurable_id measurable_id

lemma individual_values_supported :
    ∀ᵐ x ∂B.individualValuesLaw, ∀ i, x i ∈ Icc (0 : ℝ) B.cap := by
  apply ae_all_iff.mpr
  intro i
  exact (B.individualValue_measurePreserving i).quasiMeasurePreserving.ae (B.individual_supported i)

/-- Almost surely, only finitely many individuals exceed any fixed level above
reserve. This follows from the source tail condition by Borel--Cantelli; it is
not assumed in the execution interface. -/
lemma ae_finite_individuals_above {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    ∀ᵐ x ∂B.individualValuesLaw, {i : ℕ | b < x i}.Finite := by
  apply ae_finite_setOf_mem
  have he (i : ℕ) : B.individualValuesLaw {x : ℕ → ℝ | b < x i} =
      (B.individuals i : Measure ℝ) (Ioi b) := by
    exact (B.individualValue_measurePreserving i).measure_preimage measurableSet_Ioi.nullMeasurableSet
  have hsum : (∑' i, B.individualValuesLaw {x : ℕ → ℝ | b < x i}) =
      ∑' i, (B.individuals i : Measure ℝ) (Ioi b) := tsum_congr he
  exact hsum.trans_ne (B.individual_tail_finite b hb).ne

noncomputable def individualPrefix (N : ℕ) : Model.Instance N where
  law i := (B.individuals i.val : Measure ℝ)
  probability _ := inferInstance
  nonnegative i := (B.individual_supported i.val).mono fun _ hx => hx.1

noncomputable def intensityAbove (b : ℝ) (hb : (B.terminal : ℝ) < b) : FiniteMeasure ℝ :=
  ⟨B.intensity.restrict (Ioi b), ⟨by simpa using (B.intensity_tail_finite b hb)⟩⟩

/-- A genuine finite-intensity hybrid truncation: all first N identities remain,
including zeros, and only anonymous marks at most b are removed. -/
noncomputable def truncation (N : ℕ) (b : ℝ) (hb : (B.terminal : ℝ) < b) :
    FiniteIntensityHybridInstance N where
  cap := B.cap
  terminal := B.terminal
  terminal_le_cap := B.terminal_le_cap
  individuals := B.individualPrefix N
  individual_bounded i := (B.individual_supported i.val).mono fun _ hx => hx.2
  intensity := B.intensityAbove b hb
  intensity_supported := by
    change ∀ᵐ x ∂B.intensity.restrict (Ioi b), x ∈ Ioc (0 : ℝ) B.cap
    filter_upwards [ae_restrict_of_ae B.intensity_supported] with x hx
    exact ⟨B.terminal.property.trans_lt hx.1,hx.2⟩

end CountableInstance
end ProphetSecretary.Limiting
