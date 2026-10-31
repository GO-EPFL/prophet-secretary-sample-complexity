import ProphetSecretary.Model.Training
import Mathlib.Data.List.OfFn
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurable adaptive training histories

Finite transcripts have the disjoint-union σ-algebra of their finite tuple spaces.
Consequently the visible identity counts and transcript length are measurable. The request
rule's measurability is imposed separately from the pathwise hard budget.
-/

open MeasureTheory

namespace ProphetSecretary.Model

/-- The standard disjoint union of finite tuples of observed identity/value pairs. -/
instance transcriptMeasurableSpace (n : ℕ) : MeasurableSpace (Transcript n) :=
  MeasurableSpace.map (fun h : Σ m : ℕ, Fin m → (Fin n × ℝ) => List.ofFn h.2) inferInstance

instance requestMeasurableSpace (n : ℕ) : MeasurableSpace (Option (Fin n)) := ⊤

instance requestMeasurableSingletonClass (n : ℕ) : MeasurableSingletonClass (Option (Fin n)) :=
  ⟨fun _ => trivial⟩

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- A function of a finite transcript is measurable iff it is measurable at each length. -/
theorem measurable_from_transcript_iff {f : Transcript n → Ω} :
    Measurable f ↔ ∀ m, Measurable (fun h : Fin m → (Fin n × ℝ) => f (List.ofFn h)) := by
  constructor
  · intro hf m s hs
    have h := hf hs
    change @MeasurableSet (Σ m : ℕ, Fin m → (Fin n × ℝ)) _
      ((fun h => List.ofFn h.2) ⁻¹' (f ⁻¹' s)) at h
    exact (MeasurableSpace.measurableSet_iInf.mp h) m
  · intro hf s hs
    change @MeasurableSet (Σ m : ℕ, Fin m → (Fin n × ℝ)) _
      ((fun h => List.ofFn h.2) ⁻¹' (f ⁻¹' s))
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro m
    exact hf m hs

/-- A fixed finite vector of observations is a measurable transcript. -/
theorem measurable_transcript_ofFn (m : ℕ) :
    Measurable (fun h : Fin m → (Fin n × ℝ) => (List.ofFn h : Transcript n)) := by
  intro s hs
  change @MeasurableSet (Σ m : ℕ, Fin m → (Fin n × ℝ)) _
    ((fun h => List.ofFn h.2) ⁻¹' s) at hs
  exact (MeasurableSpace.measurableSet_iInf.mp hs) m

/-- The number of observations is part of the measurable training history. -/
theorem measurable_transcript_length : Measurable (fun h : Transcript n => h.length) := by
  rw [measurable_from_transcript_iff]
  intro m
  simpa only [List.length_ofFn] using (measurable_const : Measurable fun _ : Fin m → (Fin n × ℝ) => m)

/-- A learner knows how many samples of each distribution it has already requested. -/
theorem measurable_requests (i : Fin n) : Measurable (fun h : Transcript n => requests h i) := by
  rw [measurable_from_transcript_iff]
  intro m
  have hids : Measurable (fun h : Fin m → (Fin n × ℝ) => fun j => (h j).1) :=
    measurable_pi_lambda _ fun j => measurable_fst.comp (measurable_pi_apply j)
  have hc : Measurable (fun h : Fin m → Fin n => (List.ofFn h).count i) := measurable_of_finite _
  simpa only [Function.comp_def, requests, List.map_ofFn] using hc.comp hids

/-- The request law may depend measurably on the entire previous transcript and its seed. -/
def MeasurableRequestRule {Seed : Type*} [MeasurableSpace Seed]
    (rule : RequestRule n Seed) : Prop :=
  Measurable (fun z : Seed × Transcript n => rule z.1 z.2)

end ProphetSecretary.Model
