import ProphetSecretary.Statistics.FinitePriorClassifier
import ProphetSecretary.Probability.FiniteMixtureProducts

/-!
# Actual preliminary/future training block split

An explicit finite index equivalence separates the first h training columns from
all remaining columns, including the distinct ONLINE column. Each hidden atom
has exactly its independent past/future product law; the whole prior is the
constructed finite mixture of those products.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model ProphetSecretary.Probability
variable {n : ℕ}

noncomputable def trainingBlockIndexEquiv (n h d : ℕ) :
    ((Fin n × Fin h) ⊕ (Fin n × Fin (d+1))) ≃ (Fin n × Fin (h+d+1)) :=
  (Equiv.prodSumDistrib (Fin n) (Fin h) (Fin (d+1))).symm.trans
    (Equiv.prodCongr (Equiv.refl (Fin n)) (finSumFinEquiv.trans (finCongr (Nat.add_assoc h d 1).symm)))

noncomputable def splitTrainingBlocks (n h d : ℕ) :
    ValueArray n (h+d) ≃ᵐ (((Fin n × Fin h) → ℝ) × ((Fin n × Fin (d+1)) → ℝ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin n × Fin (h+d+1) => ℝ) (trainingBlockIndexEquiv n h d)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ))

lemma splitTrainingBlocks_measurePreserving (P : Instance n) (h d : ℕ) :
    MeasurePreserving (splitTrainingBlocks n h d) (P.trainingCoordinateLaw (h+d+1))
      ((P.trainingCoordinateLaw h).prod (P.trainingCoordinateLaw (d+1))) := by
  let e := trainingBlockIndexEquiv n h d
  let μ := fun q : Fin n × Fin (h+d+1) => P.law q.1
  let μ' := fun q => μ (e q)
  haveI : ∀ q, IsProbabilityMeasure (μ' q) := fun q => P.probability (e q).1
  have h0 := (measurePreserving_piCongrLeft μ e).symm (MeasurableEquiv.piCongrLeft (fun _ : Fin n × Fin (h+d+1) => ℝ) e)
  exact (measurePreserving_sumPiEquivProdPi μ').comp h0

noncomputable def splitBaseTraining (F : FinitePrior n) (h d : ℕ) :
    BaseWorld F (h+d) ≃ᵐ (Fin F.size × (((Fin n × Fin h) → ℝ) × ((Fin n × Fin (d+1)) → ℝ))) :=
  (MeasurableEquiv.refl (Fin F.size)).prodCongr (splitTrainingBlocks n h d)

lemma splitBaseTraining_measurePreserving (F : FinitePrior n) (h d : ℕ) :
    MeasurePreserving (F.splitBaseTraining h d) (F.law (h+d))
      (finiteMixtureProductLaw F.weight (fun θ => (F.offerInstance θ).trainingCoordinateLaw h)
        (fun θ => (F.offerInstance θ).trainingCoordinateLaw (d+1))) := by
  have hAtom (θ : Fin F.size) : MeasurePreserving (F.splitBaseTraining h d)
      (F.atomLaw (h+d) θ) ((Measure.dirac θ).prod
        (((F.offerInstance θ).trainingCoordinateLaw h).prod ((F.offerInstance θ).trainingCoordinateLaw (d+1)))) :=
    (MeasurePreserving.id (Measure.dirac θ)).prod (splitTrainingBlocks_measurePreserving (F.offerInstance θ) h d)
  refine ⟨(F.splitBaseTraining h d).measurable,?_⟩
  simp only [law,finiteMixtureProductLaw,Measure.map_finset_sum' (F.splitBaseTraining h d).measurable.aemeasurable,Measure.map_smul]
  exact Finset.sum_congr rfl fun θ _ => congrArg (fun μ => F.weight θ • μ) (hAtom θ).map_eq

lemma trainingBlockIndexEquiv_inl (n h d : ℕ) (q : Fin n × Fin h) :
    trainingBlockIndexEquiv n h d (Sum.inl q)=(q.1,prefixColumn (h+d) h (by omega) q.2) := by
  apply Prod.ext
  · rfl
  · apply Fin.ext
    rfl

lemma splitTrainingBlocks_prefix (n h d : ℕ) (a : ValueArray n (h+d)) :
    (splitTrainingBlocks n h d a).1=classifierPrefixRead n (h+d) h (by omega) a := by
  funext q
  change a (trainingBlockIndexEquiv n h d (Sum.inl q))=a (q.1,prefixColumn (h+d) h (by omega) q.2)
  rw [trainingBlockIndexEquiv_inl]

def restorePreliminaryPrefix (n h d : ℕ) (a : (Fin n × Fin h) → ℝ) : ValueArray n (h+d) :=
  fun q => if hq : q.2.val<h then a (q.1,⟨q.2.val,hq⟩) else 0

lemma measurable_restorePreliminaryPrefix (n h d : ℕ) : Measurable (restorePreliminaryPrefix n h d) := by
  apply measurable_pi_lambda
  intro q
  by_cases hq : q.2.val<h
  · simpa only [restorePreliminaryPrefix,dif_pos hq] using measurable_pi_apply (q.1,(⟨q.2.val,hq⟩ : Fin h))
  · simpa only [restorePreliminaryPrefix,dif_neg hq] using
      (measurable_const : Measurable (fun _ : (Fin n × Fin h) → ℝ => (0:ℝ)))

lemma observe_eq_restored_split (F : FinitePrior n) (h d : ℕ) (ω : BaseWorld F (h+d)) :
    F.observe (h+d) 0 h ω=restorePreliminaryPrefix n h d (F.splitBaseTraining h d ω).2.1 := by
  funext q
  have hprefix := splitTrainingBlocks_prefix n h d ω.2
  change F.observe (h+d) 0 h ω q=restorePreliminaryPrefix n h d (splitTrainingBlocks n h d ω.2).1 q
  rw [hprefix]
  have hmem : q∈trainingCoordinates n (h+d) 0 h ↔ q.2.val<h := by
    simp only [trainingCoordinates,Finset.mem_filter,Finset.mem_univ,true_and,zero_add,Nat.min_eq_left (show h≤h+d by omega)]
  by_cases hq : q.2.val<h
  · simp only [observe,ProphetSecretary.Probability.maskCoordinates,if_pos (hmem.mpr hq),restorePreliminaryPrefix,dif_pos hq,classifierPrefixRead]
    congr 1
  · simp only [observe,ProphetSecretary.Probability.maskCoordinates,if_neg (hmem.not.mpr hq),restorePreliminaryPrefix,dif_neg hq]

lemma dataSigma_eq_split_past (F : FinitePrior n) (h d : ℕ) :
    F.dataSigma (h+d) 0 h=(mixturePastSigma (Θ:=Fin F.size)
      (A:=(Fin n × Fin h) → ℝ) (B:=(Fin n × Fin (d+1)) → ℝ)).comap (F.splitBaseTraining h d) := by
  let T := F.splitBaseTraining h d
  have hRestore : F.observe (h+d) 0 h=fun ω => restorePreliminaryPrefix n h d (T ω).2.1 := by
    funext ω
    exact F.observe_eq_restored_split h d ω
  have hRead : (fun ω => (T ω).2.1)=F.classifierPrefix (h+d) h (by omega) := by
    funext ω
    exact splitTrainingBlocks_prefix n h d ω.2
  apply le_antisymm
  · have hPast : @Measurable (BaseWorld F (h+d)) ((Fin n × Fin h) → ℝ)
        (mixturePastSigma.comap T) _ (fun ω => (T ω).2.1) := by
      apply Measurable.of_comap_le
      rw [MeasurableSpace.comap_comp]
      exact le_rfl
    have hObs := (measurable_restorePreliminaryPrefix n h d).comp hPast
    change @Measurable (BaseWorld F (h+d)) (ValueArray n (h+d)) (mixturePastSigma.comap T) _
      (fun ω => restorePreliminaryPrefix n h d (T ω).2.1) at hObs
    rw [←hRestore] at hObs
    exact hObs.comap_le
  · rw [MeasurableSpace.comap_comp]
    have hPast : @Measurable (BaseWorld F (h+d)) ((Fin n × Fin h) → ℝ)
        (F.dataSigma (h+d) 0 h) _ (fun ω => (T ω).2.1) := by
      rw [hRead]
      exact (F.classifierPrefix_stronglyMeasurable (h+d) h (by omega)).measurable
    exact hPast.comap_le

lemma splitTrainingBlocks_online (n h d : ℕ) (a : ValueArray n (h+d)) (i : Fin n) :
    (splitTrainingBlocks n h d a).2 (i,Fin.last d)=a (i,Fin.last (h+d)) := by
  change a (trainingBlockIndexEquiv n h d (Sum.inr (i,Fin.last d)))=a (i,Fin.last (h+d))
  rfl

end ProphetSecretary.Statistics.FinitePrior
