import ProphetSecretary.Limiting.HybridReach

/-!
# Count-hidden Markov thresholds in a finite-intensity hybrid process

A retained arrival carries its identity; an anonymous arrival is represented
by `none`. The threshold reads only retained unseen identities, elapsed time
and the independent seed. Adding retained unseen identities raises thresholds
on the physical time interval. The finite adapters and their pending-time
domination are derived from these actual callbacks.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting
variable {n N : ℕ} {Seed : Type*}

noncomputable def hybridThresholdRule
    (θ : Seed → Finset (Fin n) → ℝ → Option (Fin n) → ℝ) : HybridRule n Seed where
  individual r t i x H _ := decide (θ r (Model.unseen H) t (some i) ≤ x)
  poisson r t x H _ := decide (θ r (Model.unseen H) t none ≤ x)

/-- Threshold monotonicity is required on elapsed times in [0,1] only. -/
def MonotoneHybridThresholds (θ : Seed → Finset (Fin n) → ℝ → Option (Fin n) → ℝ) : Prop :=
  ∀ r t, t ∈ Icc (0 : ℝ) 1 →
    (∀ i A B, i ∈ A → A ⊆ B → θ r A t (some i) ≤ θ r B t (some i)) ∧
    (∀ A B, A ⊆ B → θ r A t none ≤ θ r B t none)

noncomputable def retainedUnseen (A : Finset (Fin (n+N))) : Finset (Fin n) :=
  Finset.univ.filter fun i => i.castAdd N ∈ A

lemma retainedUnseen_mono {A B : Finset (Fin (n+N))} (hAB : A ⊆ B) :
    retainedUnseen A ⊆ retainedUnseen B := by
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hAB (Finset.mem_filter.mp hi).2⟩

lemma retainedUnseen_unseen (H : Model.History (n+N)) :
    retainedUnseen (Model.unseen H) = Model.unseen (retainedHistory H) := by
  ext i
  simp only [retainedUnseen,Model.unseen,retainedHistory,Finset.mem_filter,Finset.mem_univ,true_and]

noncomputable def finiteHybridThreshold
    (θ : Seed → Finset (Fin n) → ℝ → Option (Fin n) → ℝ) (N : ℕ)
    (r : Seed) (A : Finset (Fin (n+N))) (t : ℝ) (k : Fin (n+N)) : ℝ :=
  Fin.addCases (fun i => θ r (retainedUnseen A) t (some i)) (fun _ => θ r (retainedUnseen A) t none) k

lemma hybridThresholdRule_asFinitePolicy
    (θ : Seed → Finset (Fin n) → ℝ → Option (Fin n) → ℝ) (N : ℕ) :
    (hybridThresholdRule θ).asFinitePolicy N = Model.thresholdPolicy (finiteHybridThreshold θ N) := by
  unfold HybridRule.asFinitePolicy Model.thresholdPolicy
  congr 1
  funext r t k x H
  induction k using Fin.addCases with
  | left i => simp only [hybridThresholdRule,finiteHybridThreshold,Fin.addCases_left,retainedUnseen_unseen]
  | right j => simp only [hybridThresholdRule,finiteHybridThreshold,Fin.addCases_right,retainedUnseen_unseen]

lemma finiteHybridThreshold_monotone_on_time
    (θ : Seed → Finset (Fin n) → ℝ → Option (Fin n) → ℝ) (hθ : MonotoneHybridThresholds θ)
    (N : ℕ) (r : Seed) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (k : Fin (n+N)) (A B : Finset (Fin (n+N))) (hk : k ∈ A) (hAB : A ⊆ B) :
    finiteHybridThreshold θ N r A t k ≤ finiteHybridThreshold θ N r B t k := by
  revert hk
  induction k using Fin.addCases with
  | left i =>
    intro hi
    simp only [finiteHybridThreshold,Fin.addCases_left]
    apply (hθ r t ht).1 i _ _ _ (retainedUnseen_mono hAB)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩
  | right j =>
    intro _
    simp only [finiteHybridThreshold,Fin.addCases_right]
    exact (hθ r t ht).2 _ _ (retainedUnseen_mono hAB)

private theorem threshold_pending_domination_on_time
    {m : ℕ} (ψ : Seed → Finset (Fin m) → ℝ → Fin m → ℝ)
    (hψ : ∀ r t, t ∈ Icc (0 : ℝ) 1 → ∀ k A B, k ∈ A → A ⊆ B → ψ r A t k ≤ ψ r B t k)
    (r : Seed) (x u : Fin m → ℝ) (hu : ∀ j, u j ∈ Icc (0 : ℝ) 1) (i : Fin m) :
    (Model.thresholdPolicy ψ).stoppingTime r Finset.univ x u ≤ (Model.thresholdPolicy ψ).pendingTime r x u i := by
  have hsub : (Model.thresholdPolicy ψ).accepted r (Finset.univ.erase i) x u ⊆
      (Model.thresholdPolicy ψ).accepted r Finset.univ x u := by
    intro j hj
    obtain ⟨_,hact⟩ := ((Model.thresholdPolicy ψ).mem_accepted r _ x u j).mp hj
    apply ((Model.thresholdPolicy ψ).mem_accepted r _ x u j).mpr
    refine ⟨Finset.mem_univ _,?_⟩
    simp only [Model.Policy.action,Model.thresholdPolicy,decide_eq_true_eq] at hact ⊢
    exact (hψ r (u j) (hu j) j _ _ (by simp [Model.unseen,Model.history])
      (Model.unseen_subset_pending x u i (u j))).trans hact
  unfold Model.Policy.pendingTime Model.Policy.stoppingTime
  apply Finset.le_min'
  intro t ht
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact (Model.thresholdPolicy ψ).stoppingTime_le_one _ _ _ _
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ht
    exact (Model.thresholdPolicy ψ).stoppingTime_le_of_accepted r Finset.univ x u j (hsub hj)

/-- The actual auxiliary-execution domination follows from threshold
monotonicity and is never postulated as a policy interface. -/
theorem hybridThresholdRule_duration_le_pending
    (θ : Seed → Finset (Fin n) → ℝ → Option (Fin n) → ℝ) (hθ : MonotoneHybridThresholds θ)
    (i : Fin n) (v : HybridWorld n Seed)
    (hu : ∀ k : Fin (n+v.1.1), combinedClocks v.2.2.1 v.1.2 k ∈ Icc (0 : ℝ) 1) :
    (hybridThresholdRule θ).realizedDuration v ≤ (hybridThresholdRule θ).pendingIndividualTime i v := by
  change ((hybridThresholdRule θ).asFinitePolicy v.1.1).stoppingTime _ Finset.univ _ _ ≤
    ((hybridThresholdRule θ).asFinitePolicy v.1.1).pendingTime _ _ _ _
  rw [hybridThresholdRule_asFinitePolicy]
  exact threshold_pending_domination_on_time _ (finiteHybridThreshold_monotone_on_time θ hθ v.1.1)
    v.2.2.2 (combinedValues v.2.1 v.1.2) (combinedClocks v.2.2.1 v.1.2) hu (i.castAdd v.1.1)

end ProphetSecretary.Limiting
