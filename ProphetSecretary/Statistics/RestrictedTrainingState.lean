import ProphetSecretary.Statistics.EmpiricalFutureError

/-!
# Restricting training arrays and future coordinates to an unseen state

The coordinate projection is measure preserving for the actual independent
training law and uniform clocks. Empirical formation commutes with restriction
on every real array, including null training outcomes after totalization.
-/

open MeasureTheory ProbabilityTheory
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ}

def restrictTrainingCoordinates (A : Finset (Fin n)) (a : (Fin n × Fin k) → ℝ) :
    (Fin A.card × Fin k) → ℝ := fun q => a (stateEmbedding A q.1, q.2)

lemma measurable_restrictTrainingCoordinates (A : Finset (Fin n)) :
    Measurable (restrictTrainingCoordinates (k := k) A) :=
  measurable_pi_lambda _ (fun q => measurable_pi_apply (stateEmbedding A q.1, q.2))

lemma Instance.restrictTrainingCoordinates_measurePreserving (P : Instance n) (A : Finset (Fin n)) :
    MeasurePreserving (restrictTrainingCoordinates (k := k) A) (P.trainingCoordinateLaw k)
      ((P.restrictTo A).trainingCoordinateLaw k) := by
  let e : (Fin A.card × Fin k) ↪ (Fin n × Fin k) :=
    ⟨fun q => (stateEmbedding A q.1,q.2), by
      intro q r he
      apply Prod.ext
      · exact (stateEmbedding A).injective (congrArg (fun z : Fin n × Fin k => z.1) he)
      · exact congrArg (fun z : Fin n × Fin k => z.2) he⟩
  let μ : (Fin n × Fin k) → Measure ℝ := fun q => P.law q.1
  have hi := iIndepFun.precomp e.injective
    (iIndepFun_pi (μ := μ) (X := fun _ => id) (fun _ => aemeasurable_id))
  have hm := iIndepFun.map_fun_eq_pi_map (fun q => (measurable_pi_apply (e q)).aemeasurable) hi
  have he : (fun q => (Measure.pi μ).map (fun a => a (e q))) = fun q => μ (e q) := by
    funext q
    exact (measurePreserving_eval μ (e q)).map_eq
  change (Measure.pi μ).map (fun a => a ∘ e) =
    Measure.pi (fun q => (Measure.pi μ).map (fun a => a (e q))) at hm
  rw [he] at hm
  exact ⟨measurable_restrictTrainingCoordinates A, hm⟩

lemma totalEmpiricalInstance_restrictTo_coordinates [NeZero k] (A : Finset (Fin n)) (a : (Fin n × Fin k) → ℝ) :
    (totalEmpiricalInstance (reservoirCoordinates.symm a)).restrictTo A =
      totalEmpiricalInstance (reservoirCoordinates.symm (restrictTrainingCoordinates A a)) := by
  apply Instance.eq_of_law_eq
  funext j
  rfl

def restrictTrainingFutureCoordinates (A : Finset (Fin n))
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) :
    (((Fin A.card × Fin k) → ℝ) × (Fin A.card → ℝ)) :=
  (restrictTrainingCoordinates A q.1, q.2 ∘ stateEmbedding A)

lemma Instance.restrictTrainingFutureCoordinates_measurePreserving (P : Instance n) (A : Finset (Fin n)) :
    MeasurePreserving (restrictTrainingFutureCoordinates (k := k) A)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))
      (((P.restrictTo A).trainingCoordinateLaw k).prod (Instance.clocksLaw A.card)) :=
  (P.restrictTrainingCoordinates_measurePreserving A).prod
    (Instance.restrictClocks_measurePreserving (stateEmbedding A))

/-- Fresh state coordinates after observing clocks up to t. The original prefix
is fixed; only training and fresh pending uniforms are random here. -/
noncomputable def normalizedRefreshedStateCoordinates (t : ℝ) (u : Fin n → ℝ)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) :=
  let A := ProphetSecretary.Probability.pendingClockSet t u
  (restrictTrainingCoordinates A q.1,
    fun j : Fin A.card =>
      (ProphetSecretary.Probability.refreshClocks t (u,q.2) (stateEmbedding A j) - t) / (1-t))

lemma normalizedRefreshedStateCoordinates_eq {t : ℝ} (ht : t < 1) (u : Fin n → ℝ) :
    normalizedRefreshedStateCoordinates (k := k) t u =
      restrictTrainingFutureCoordinates (ProphetSecretary.Probability.pendingClockSet t u) := by
  funext q
  apply Prod.ext
  · rfl
  · funext j
    have hj := stateEmbedding_mem (ProphetSecretary.Probability.pendingClockSet t u) j
    have hu := (ProphetSecretary.Probability.mem_pendingClockSet t u _).mp hj
    change (ProphetSecretary.Probability.refreshClocks t (u,q.2)
      (stateEmbedding (ProphetSecretary.Probability.pendingClockSet t u) j) - t) / (1-t) =
        q.2 (stateEmbedding (ProphetSecretary.Probability.pendingClockSet t u) j)
    simp only [ProphetSecretary.Probability.refreshClocks, ProphetSecretary.Probability.refreshClock,
      if_neg (not_lt.mpr hu), Instance.tailClock]
    field_simp [ne_of_gt (sub_pos.mpr ht)]
    ring

/-- The actual reset of pending clocks and restriction of independent samples
has exactly the fresh child-state law, for every fixed observed prefix. -/
lemma Instance.normalizedRefreshedStateCoordinates_measurePreserving (P : Instance n)
    {t : ℝ} (ht : t < 1) (u : Fin n → ℝ) :
    MeasurePreserving (normalizedRefreshedStateCoordinates (k := k) t u)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))
      (((P.restrictTo (ProphetSecretary.Probability.pendingClockSet t u)).trainingCoordinateLaw k).prod
        (Instance.clocksLaw (ProphetSecretary.Probability.pendingClockSet t u).card)) := by
  rw [normalizedRefreshedStateCoordinates_eq ht]
  exact P.restrictTrainingFutureCoordinates_measurePreserving _

end ProphetSecretary.Model
