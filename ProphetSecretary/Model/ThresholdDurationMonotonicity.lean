import ProphetSecretary.Model.BellmanResidualBasic

/-!
# Duration decreases when values increase for Markov threshold policies

The actual unseen history is independent of earlier offer values: it retains
identities and arrival times, including zero-valued observations. Consequently
raising a coordinate cannot remove a potential acceptance for a policy whose
threshold reads only unseen identities, time and the independent seed. This
statement is not asserted for general history-dependent policies.
-/
open Set
open scoped Classical
namespace ProphetSecretary.Model
variable {n : ℕ} {Seed : Type*}

lemma thresholdPolicy.accepted_mono_values
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → ℝ)
    (r : Seed) (D : Finset (Fin n)) (x y u : Fin n → ℝ) (hxy : ∀ j, x j ≤ y j) :
    (thresholdPolicy θ).accepted r D x u ⊆ (thresholdPolicy θ).accepted r D y u := by
  intro j hj
  obtain ⟨hjD,hact⟩ := ((thresholdPolicy θ).mem_accepted r D x u j).mp hj
  apply ((thresholdPolicy θ).mem_accepted r D y u j).mpr
  refine ⟨hjD,?_⟩
  simp only [Policy.action,thresholdPolicy,decide_eq_true_eq] at hact ⊢
  rw [unseen_history_values D x y u (u j)] at hact
  exact hact.trans (hxy j)

/-- All earlier and later candidate actions are compared through the derived
unseen-history identity, rather than an assumed future-history interface. -/
theorem thresholdPolicy.stoppingTime_antitone_values
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → ℝ)
    (r : Seed) (D : Finset (Fin n)) (x y u : Fin n → ℝ) (hxy : ∀ j, x j ≤ y j) :
    (thresholdPolicy θ).stoppingTime r D y u ≤ (thresholdPolicy θ).stoppingTime r D x u := by
  have hsub := thresholdPolicy.accepted_mono_values θ r D x y u hxy
  unfold Policy.stoppingTime
  apply Finset.le_min'
  intro t ht
  rcases Finset.mem_insert.mp ht with rfl | ht
  · exact (thresholdPolicy θ).stoppingTime_le_one r D y u
  · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ht
    exact (thresholdPolicy θ).stoppingTime_le_of_accepted r D y u j (hsub hj)

lemma thresholdPolicy.stoppingTime_antitone_candidateValue
    (θ : Seed → Finset (Fin n) → ℝ → Fin n → ℝ)
    (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) (i : Fin n) :
    Antitone (fun a => (thresholdPolicy θ).stoppingTime r D (Function.update x i a) u) := by
  intro a b hab
  apply thresholdPolicy.stoppingTime_antitone_values θ r D _ _ u
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self] using hab
  · simp only [Function.update_of_ne hji,le_refl]

/-- Actual canonical specialization, with the optimizer's design law held fixed. -/
theorem Instance.canonical_stoppingTime_antitone_candidateValue (P : Instance n)
    (hP : MeasureTheory.Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (r : Unit) (x u : Fin n → ℝ) (i : Fin n) :
    Antitone (fun a => (P.valuePolicy hP hw hc).rule.stoppingTime r Finset.univ (Function.update x i a) u) :=
  thresholdPolicy.stoppingTime_antitone_candidateValue _ r Finset.univ x u i

end ProphetSecretary.Model
