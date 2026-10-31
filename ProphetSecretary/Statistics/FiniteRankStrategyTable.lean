import ProphetSecretary.Model.RankFullSampling
import ProphetSecretary.Probability.FiniteObservationCode
import Mathlib.Data.Fintype.Pi

/-!
# A finite table of rank decisions on a finite value grid

The table lists responses to hypothetical training and observation histories.
Its executed policy indexes only the observed training array and current and
past offers. Zero-valued observations remain present. Cap acceptance and zero
rejection are imposed on every raw input, including off-grid observations.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability

lemma rankObservationCode_injective (n : ℕ) : Function.Injective (@rankObservationCode n) := by
  intro x y h
  cases x <;> cases y <;> simp_all [rankObservationCode]

instance rankObservation_singletons (n : ℕ) : MeasurableSingletonClass (Option (Fin n × ℝ)) := by
  constructor
  intro x
  have heq : {x} = rankObservationCode ⁻¹' {rankObservationCode x} := by
    ext y
    change y=x ↔ rankObservationCode y=rankObservationCode x
    exact (rankObservationCode_injective n).eq_iff.symm
  rw [heq]
  have hm : MeasurableSet ({rankObservationCode x} : Set (Unit ⊕ (Fin n × ℝ))) := by
    cases x with
    | none =>
      have h : MeasurableSet (Sum.inl '' ({()} : Set Unit) : Set (Unit ⊕ (Fin n × ℝ))) :=
        (measurableSet_singleton ()).inl_image
      simpa only [Set.image_singleton,rankObservationCode] using h
    | some z =>
      have h : MeasurableSet (Sum.inr '' ({z} : Set (Fin n × ℝ)) : Set (Unit ⊕ (Fin n × ℝ))) :=
        (measurableSet_singleton z).inr_image
      simpa only [Set.image_singleton,rankObservationCode] using h
  exact (comap_measurable rankObservationCode) hm

abbrev RankGridValue (G : Finset ℝ) := {x : ℝ // x∈G}
abbrev RawRankQuery (n k : ℕ) := Reservoir n k × (Fin n × (Fin n × (ℝ × RankHistory n)))
abbrev GridRankQuery (n k : ℕ) (G : Finset ℝ) :=
  (Fin n → Fin k → RankGridValue G) ×
    (Fin n × (Fin n × (RankGridValue G × (Fin n → Option (Fin n × RankGridValue G)))))

def embedGridRankQuery {n k : ℕ} {G : Finset ℝ} (z : GridRankQuery n k G) : RawRankQuery n k :=
  ((fun i j => (z.1 i j).val),z.2.1,z.2.2.1,z.2.2.2.1.val,
    fun j => (z.2.2.2.2 j).map (fun a => (a.1,a.2.val)))

noncomputable def rankQueryGrid (n k : ℕ) (G : Finset ℝ) : Finset (RawRankQuery n k) :=
  Finset.univ.image (embedGridRankQuery (n := n) (k := k) (G := G))

abbrev RankStrategyTable (n k : ℕ) (G : Finset ℝ) :=
  {z : RawRankQuery n k // z∈rankQueryGrid n k G} → Bool

lemma rankQueryGrid_mem {n k : ℕ} (G : Finset ℝ) (y : Reservoir n k) (x : Fin n → ℝ)
    (hy : ∀ i j, y i j∈G) (hx : ∀ i, x i∈G) (p : Equiv.Perm (Fin n)) (a i : Fin n) :
    (y,a,i,x i,rankHistory p x a)∈rankQueryGrid n k G := by
  let z : GridRankQuery n k G :=
    ((fun i j => ⟨y i j,hy i j⟩),a,i,⟨x i,hx i⟩,
      fun j => if p.symm j<a then some (p.symm j,⟨x j,hx j⟩) else none)
  have hH : (embedGridRankQuery z).2.2.2.2 = rankHistory p x a := by
    funext j
    dsimp only [embedGridRankQuery,z]
    by_cases hj : p.symm j<a <;> simp [rankHistory,hj]
  unfold rankQueryGrid
  apply Finset.mem_image.mpr
  refine ⟨z,Finset.mem_univ _,?_⟩
  change (y,a,i,x i,_)=(y,a,i,x i,_)
  exact congrArg (fun H : RankHistory n => (y,a,i,x i,H)) hH

noncomputable def finiteRankTablePolicy {n k : ℕ} (G : Finset ℝ) (T : RankStrategyTable n k G) :
    RankPolicy (Reservoir n k × Unit) n where
  decide yr q i x H := if x=1 then true else if x=0 then false else
    finiteObservationLookup (rankQueryGrid n k G) false T (yr.1,q,i,x,H)

lemma finiteRankTablePolicy_measurable {n k : ℕ} (G : Finset ℝ) (T : RankStrategyTable n k G) :
    (finiteRankTablePolicy G T).IsMeasurable := by
  let A := (Reservoir n k × Unit) × (Fin n × (Fin n × (ℝ × RankHistory n)))
  have hRaw : Measurable (fun z : A => (z.1.1,z.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hx : Measurable (fun z : A => z.2.2.2.1) := by fun_prop
  have hLookup := (measurable_finiteObservationLookup (rankQueryGrid n k G) false T).comp hRaw
  exact Measurable.ite (measurableSet_eq_fun hx measurable_const) measurable_const
    (Measurable.ite (measurableSet_eq_fun hx measurable_const) measurable_const hLookup)

noncomputable def finiteRankTableLearner {n k : ℕ} (G : Finset ℝ) (T : RankStrategyTable n k G) : RankLearner n k :=
  RankLearner.ofSamplePolicy Unit (Measure.dirac ()) (finiteRankTablePolicy G T) (finiteRankTablePolicy_measurable G T)

lemma finiteRankTableLearner_requests_eq {n k : ℕ} (G : Finset ℝ) (T : RankStrategyTable n k G)
    (y : Reservoir n k) (r : Unit) (i : Fin n) :
    requests (trainingTranscript (finiteRankTableLearner G T).request r y) i = k :=
  RankLearner.ofSamplePolicy_requests_eq Unit (Measure.dirac ()) _ _ y r i

lemma finiteRankTablePolicy_accepts_cap {n k : ℕ} (G : Finset ℝ) (T : RankStrategyTable n k G)
    (y : Reservoir n k) (r : Unit) (q i : Fin n) (H : RankHistory n) :
    (finiteRankTablePolicy G T).decide (y,r) q i 1 H = true := by
  simp [finiteRankTablePolicy]

lemma finiteRankTablePolicy_rejects_zero {n k : ℕ} (G : Finset ℝ) (T : RankStrategyTable n k G)
    (y : Reservoir n k) (r : Unit) (q i : Fin n) (H : RankHistory n) :
    (finiteRankTablePolicy G T).decide (y,r) q i 0 H = false := by
  simp [finiteRankTablePolicy]

lemma finiteRankTableLearner_policy {n k : ℕ} (G : Finset ℝ) (T : RankStrategyTable n k G) :
    (finiteRankTableLearner G T).policy = finiteRankTablePolicy G T := by
  change @RankPolicy.mk (Reservoir n k × Unit) n _ = @RankPolicy.mk (Reservoir n k × Unit) n _
  apply congrArg RankPolicy.mk
  funext yr q i x H
  rcases yr with ⟨y,r⟩
  exact RankLearner.ofSamplePolicy_decide Unit (Measure.dirac ()) (finiteRankTablePolicy G T)
    (finiteRankTablePolicy_measurable G T) y r q i x H

end ProphetSecretary.Statistics
