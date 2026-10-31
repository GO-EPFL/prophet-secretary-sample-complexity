import ProphetSecretary.Statistics.FiniteRankStrategyRepresentation
import ProphetSecretary.Probability.FiniteObservedSelection

/-!
# Actual mixtures of finite rank-strategy tables

A table is drawn independently before training. The sample requester is the
full k-per-marginal protocol; the online callback consults only its observed
query. The product-law reordering below proves the exact independent law
needed to average arbitrary integrable table outcomes.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n k : ℕ}

noncomputable def mixedRankTablePolicy (G : Finset ℝ) :
    RankPolicy (Reservoir n k × RankStrategyTable n k G) n where
  decide yr q i x H := (finiteRankTablePolicy G yr.2).decide (yr.1,()) q i x H

lemma mixedRankTablePolicy_measurable (G : Finset ℝ) :
    (mixedRankTablePolicy (n := n) (k := k) G).IsMeasurable := by
  let A := (Reservoir n k × RankStrategyTable n k G) × (Fin n × (Fin n × (ℝ × RankHistory n)))
  have hIndex : Measurable (fun z : A => z.1.2) := measurable_snd.comp measurable_fst
  have hEach (T : RankStrategyTable n k G) : Measurable (fun z : A =>
      (finiteRankTablePolicy G T).decide (z.1.1,()) z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2) :=
    (finiteRankTablePolicy_measurable G T).comp
      (((measurable_fst.comp measurable_fst).prodMk measurable_const).prodMk measurable_snd)
  exact measurable_countable_choice hIndex hEach

noncomputable def mixedRankTableLearner (G : Finset ℝ) (ν : Measure (RankStrategyTable n k G))
    [IsProbabilityMeasure ν] : RankLearner n k :=
  RankLearner.ofSamplePolicy (RankStrategyTable n k G) ν (mixedRankTablePolicy G) (mixedRankTablePolicy_measurable G)

lemma mixedRankTableLearner_requests_eq (G : Finset ℝ) (ν : Measure (RankStrategyTable n k G))
    [IsProbabilityMeasure ν] (y : Reservoir n k) (T : RankStrategyTable n k G) (i : Fin n) :
    requests (trainingTranscript (mixedRankTableLearner G ν).request T y) i = k :=
  RankLearner.ofSamplePolicy_requests_eq _ _ _ _ y T i

lemma mixedRankTableLearner_decide (G : Finset ℝ) (ν : Measure (RankStrategyTable n k G))
    [IsProbabilityMeasure ν] (y : Reservoir n k) (T : RankStrategyTable n k G)
    (q i : Fin n) (x : ℝ) (H : RankHistory n) :
    (mixedRankTableLearner G ν).policy.decide (y,T) q i x H =
      (finiteRankTablePolicy G T).decide (y,()) q i x H :=
  RankLearner.ofSamplePolicy_decide _ _ _ _ y T q i x H

abbrev RankTableInputs (n k : ℕ) := (Fin n → ℝ) × (Equiv.Perm (Fin n) × Reservoir n k)

noncomputable def rankTableInputsLaw (P : Instance n) : Measure (RankTableInputs n k) :=
  P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod (P.reservoirLaw k))

instance rankTableInputsLaw_probability (P : Instance n) : IsProbabilityMeasure (rankTableInputsLaw (k := k) P) := by
  unfold rankTableInputsLaw
  infer_instance

abbrev MixedRankTableWorld (n k : ℕ) (G : Finset ℝ) :=
  (Fin n → ℝ) × (Equiv.Perm (Fin n) × (Reservoir n k × RankStrategyTable n k G))

noncomputable def mixedRankTableWorldLaw (P : Instance n) (G : Finset ℝ)
    (ν : Measure (RankStrategyTable n k G)) : Measure (MixedRankTableWorld n k G) :=
  P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod ((P.reservoirLaw k).prod ν))

instance mixedRankTableWorldLaw_probability (P : Instance n) (G : Finset ℝ)
    (ν : Measure (RankStrategyTable n k G)) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (mixedRankTableWorldLaw P G ν) := by unfold mixedRankTableWorldLaw;infer_instance

/-- The full inputs of every fixed table are independent of the drawn table. -/
lemma mixedRankTable_inputs_measurePreserving (P : Instance n) (G : Finset ℝ)
    (ν : Measure (RankStrategyTable n k G)) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun ω : MixedRankTableWorld n k G => (ω.2.2.2,(ω.1,(ω.2.1,ω.2.2.1))))
      (mixedRankTableWorldLaw P G ν) (ν.prod (rankTableInputsLaw P)) := by
  have h0 := (MeasurePreserving.id P.valuesLaw).prod
    ((measurePreserving_prodAssoc (Instance.uniformPermutationLaw n) (P.reservoirLaw k) ν).symm MeasurableEquiv.prodAssoc)
  have h1 := (measurePreserving_prodAssoc P.valuesLaw
    ((Instance.uniformPermutationLaw n).prod (P.reservoirLaw k)) ν).symm MeasurableEquiv.prodAssoc
  have h2 := Measure.measurePreserving_swap
    (μ := P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod (P.reservoirLaw k))) (ν := ν)
  exact h2.comp (h1.comp h0)

lemma mixedRankTableValue_integrable_and_integral (P : Instance n) (G : Finset ℝ)
    (ν : Measure (RankStrategyTable n k G)) [IsProbabilityMeasure ν]
    (f : RankStrategyTable n k G → RankTableInputs n k → ℝ)
    (hf : ∀ T, Measurable (f T)) (hfI : ∀ T, Integrable (f T) (rankTableInputsLaw P)) :
    Integrable (fun ω : MixedRankTableWorld n k G => f ω.2.2.2 (ω.1,(ω.2.1,ω.2.2.1))) (mixedRankTableWorldLaw P G ν) ∧
    (∫ ω : MixedRankTableWorld n k G, f ω.2.2.2 (ω.1,(ω.2.1,ω.2.2.1)) ∂mixedRankTableWorldLaw P G ν) =
      ∑ T, ν.real {T}*(∫ a, f T a ∂rankTableInputsLaw P) := by
  have h := finiteSelectedValue_integrable_and_integral (mixedRankTableWorldLaw P G ν) ν
    (fun _ : RankStrategyTable n k G => rankTableInputsLaw P)
    (Y := fun ω => ω.2.2.2) (X := fun _ ω => (ω.1,(ω.2.1,ω.2.2.1)))
    (fun _ => mixedRankTable_inputs_measurePreserving P G ν) (s := id) measurable_id hf hfI
  exact ⟨h.1,by simpa [finiteSelectedValue] using h.2⟩

end ProphetSecretary.Statistics
