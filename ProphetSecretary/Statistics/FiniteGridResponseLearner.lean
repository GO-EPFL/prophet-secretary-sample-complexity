import ProphetSecretary.Statistics.FiniteResponsePatching
import ProphetSecretary.Probability.FiniteObservationCode
import Mathlib.Data.Fintype.Pi

/-!
# Actual finite-grid response selection

For fixed finite G, the preliminary h-round sample has only finitely many
possible arrays. A response is chosen for each such array and one fixed fallback
handles every off-grid raw outcome. The resulting learner is measurable and
uses at most h+d samples of each distribution on every outcome.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability
variable {n h d : ℕ}

noncomputable def preliminaryGrid (n h : ℕ) (G : Finset ℝ) : Finset ((Fin n × Fin h) → ℝ) :=
  Fintype.piFinset (fun _ => G)

abbrev GridResponseIndex (n h : ℕ) (G : Finset ℝ) :=
  Option {a : (Fin n × Fin h) → ℝ // a∈preliminaryGrid n h G}

noncomputable def finiteGridResponseLearner (G : Finset ℝ) (L : GridResponseIndex n h G → Learner n d) : Learner n (h+d) :=
  finiteResponseLearner (finiteObservationCode (preliminaryGrid n h G))
    (measurable_finiteObservationCode (preliminaryGrid n h G)) L

lemma finiteGridResponseLearner_hardBudget (G : Finset ℝ) (L : GridResponseIndex n h G → Learner n d)
    (y : Reservoir n (h+d)) (r : FiniteResponseSeeds L) (i : Fin n) :
    requests (trainingTranscript (finiteGridResponseLearner G L).request r y) i≤h+d :=
  (finiteGridResponseLearner G L).hard_budget r y i

lemma finiteGridResponseLearner_decide_on_grid (G : Finset ℝ) (L : GridResponseIndex n h G → Learner n d)
    (y : Reservoir n (h+d)) (hy : preliminaryTrainingArray y∈preliminaryGrid n h G)
    (r : FiniteResponseSeeds L) (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (finiteGridResponseLearner G L).policy.decide (y,r) t i x H=
      (L (some ⟨preliminaryTrainingArray y,hy⟩)).policy.decide
        (responseTrainingReservoir y,r (some ⟨preliminaryTrainingArray y,hy⟩)) t i x H := by
  change (finiteResponseLearner (finiteObservationCode (preliminaryGrid n h G))
    (measurable_finiteObservationCode (preliminaryGrid n h G)) L).policy.decide (y,r) t i x H=_
  rw [finiteResponseLearner_decide,finiteObservationCode_some _ _ hy]

lemma finiteGridResponseLearner_decide_off_grid (G : Finset ℝ) (L : GridResponseIndex n h G → Learner n d)
    (y : Reservoir n (h+d)) (hy : preliminaryTrainingArray y∉preliminaryGrid n h G)
    (r : FiniteResponseSeeds L) (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (finiteGridResponseLearner G L).policy.decide (y,r) t i x H=
      (L none).policy.decide (responseTrainingReservoir y,r none) t i x H := by
  change (finiteResponseLearner (finiteObservationCode (preliminaryGrid n h G))
    (measurable_finiteObservationCode (preliminaryGrid n h G)) L).policy.decide (y,r) t i x H=_
  rw [finiteResponseLearner_decide,finiteObservationCode_none _ _ hy]

lemma trainingCoordinateLaw_grid_support (P : Instance n) (G : Finset ℝ) (h : ℕ)
    (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G) :
    ∀ᵐ a ∂P.trainingCoordinateLaw h, a∈preliminaryGrid n h G := by
  have hAll : ∀ᵐ a ∂P.trainingCoordinateLaw h, ∀ q : Fin n × Fin h, a q∈G :=
    ae_all_iff.mpr fun q => (measurePreserving_eval (fun q : Fin n × Fin h => P.law q.1) q).quasiMeasurePreserving.ae (hG q.1)
  exact hAll.mono fun a ha => Fintype.mem_piFinset.mpr ha

/-- Real preliminary observations lie in the finite response alphabet almost
surely under every grid-supported unknown instance; off-grid behavior stays defined. -/
lemma preliminaryTrainingArray_grid_support (P : Instance n) (G : Finset ℝ) (h d : ℕ)
    (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G) :
    ∀ᵐ y ∂P.reservoirLaw (h+d), preliminaryTrainingArray y∈preliminaryGrid n h G :=
  (preliminaryTrainingArray_measurePreserving P h d).quasiMeasurePreserving.ae (trainingCoordinateLaw_grid_support P G h hG)

end ProphetSecretary.Statistics
