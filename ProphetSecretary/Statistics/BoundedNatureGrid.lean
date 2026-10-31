import ProphetSecretary.Statistics.RankTableRateProgram
import ProphetSecretary.Model.FiniteAlphabetInstance

/-!
# The actual finite program for bounded-instance learners

The nature family consists of all denominator-N product laws satisfying
the specified mean and positive-count bounds. Reward and each individual
reach are separate nature actions. The optimizing mixture is fixed before
the unknown law and all observations, as in `con:bounded-learner`.
-/

open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n k N : ℕ}

abbrev BoundedNatureCounts (G : Finset ℝ) (hG : ∀ a∈G, 0≤a) (hN : 0<N)
    (μlo μhi ℓ : ℝ) :=
  {a : Fin n → ProbabilityCounts G N //
    μlo≤(probabilityGridInstance (fun a : G => a.val) (fun a => hG a.val a.property) hN a).expectedMaximum ∧
    (probabilityGridInstance (fun a : G => a.val) (fun a => hG a.val a.property) hN a).expectedMaximum≤μhi ∧
    (probabilityGridInstance (fun a : G => a.val) (fun a => hG a.val a.property) hN a).positiveCount≤ℓ}

abbrev BoundedNatureAction (G : Finset ℝ) (hG : ∀ a∈G, 0≤a) (hN : 0<N) (μlo μhi ℓ : ℝ) :=
  BoundedNatureCounts (n:=n) G hG hN μlo μhi ℓ × Option (Fin n)

noncomputable instance boundedNatureAction_fintype (G : Finset ℝ) (hG : ∀ a∈G, 0≤a)
    (hN : 0<N) (μlo μhi ℓ : ℝ) : Fintype (BoundedNatureAction (n:=n) G hG hN μlo μhi ℓ) :=
  Fintype.ofFinite _

noncomputable def boundedNatureInstance (G : Finset ℝ) (hG : ∀ a∈G, 0≤a) (hN : 0<N) (μlo μhi ℓ : ℝ)
    (a : BoundedNatureAction (n:=n) G hG hN μlo μhi ℓ) : Instance n :=
  probabilityGridInstance (fun a : G => a.val) (fun a => hG a.val a.property) hN a.1.val

noncomputable def boundedGridLearner (G : Finset ℝ) (hG : ∀ a∈G, 0≤a) (hN : 0<N) (μlo μhi ℓ : ℝ) : RankLearner n k :=
  rankTableRateLearner G (boundedNatureInstance G hG hN μlo μhi ℓ) (fun a => a.2)

noncomputable def boundedGridRate (G : Finset ℝ) (hG : ∀ a∈G, 0≤a) (hN : 0<N) (μlo μhi ℓ : ℝ) : ℝ :=
  (rankTableRateOptimizer (k:=k) G (boundedNatureInstance (n:=n) G hG hN μlo μhi ℓ) (fun a => a.2)).2

lemma boundedGridRate_mem_Icc (G : Finset ℝ) (hG : ∀ a∈G, 0≤a) (hN : 0<N) (μlo μhi ℓ : ℝ) :
    boundedGridRate (n:=n) (k:=k) G hG hN μlo μhi ℓ∈Icc (0 : ℝ) 1 :=
  (rankTableRateOptimizer_spec (k:=k) G (boundedNatureInstance (n:=n) G hG hN μlo μhi ℓ) (fun a => a.2)).1.2.1

lemma boundedGridLearner_requests_eq (G : Finset ℝ) (hG : ∀ a∈G, 0≤a) (hN : 0<N) (μlo μhi ℓ : ℝ)
    (y : Reservoir n k) (T : RankStrategyTable n k G) (i : Fin n) :
    requests (trainingTranscript (boundedGridLearner G hG hN μlo μhi ℓ).request T y) i=k :=
  rankTableRateLearner_requests_eq G _ _ y T i

lemma boundedGridLearner_accepts_cap (G : Finset ℝ) (hG : ∀ a∈G, 0≤a) (hN : 0<N) (μlo μhi ℓ : ℝ)
    (y : Reservoir n k) (T : RankStrategyTable n k G) (q i : Fin n) (H : RankHistory n) :
    (boundedGridLearner G hG hN μlo μhi ℓ).policy.decide (y,T) q i 1 H=true := by
  change (mixedRankTableLearner G _).policy.decide (y,T) q i 1 H=true
  rw [mixedRankTableLearner_decide]
  exact finiteRankTablePolicy_accepts_cap G T y () q i H

lemma boundedGridLearner_rejects_zero (G : Finset ℝ) (hG : ∀ a∈G, 0≤a) (hN : 0<N) (μlo μhi ℓ : ℝ)
    (y : Reservoir n k) (T : RankStrategyTable n k G) (q i : Fin n) (H : RankHistory n) :
    (boundedGridLearner G hG hN μlo μhi ℓ).policy.decide (y,T) q i 0 H=false := by
  change (mixedRankTableLearner G _).policy.decide (y,T) q i 0 H=false
  rw [mixedRankTableLearner_decide]
  exact finiteRankTablePolicy_rejects_zero G T y () q i H

lemma boundedNatureInstance_supported (G : Finset ℝ) (hG : ∀ a∈G, 0≤a) (hN : 0<N) (μlo μhi ℓ : ℝ)
    (a : BoundedNatureAction (n:=n) G hG hN μlo μhi ℓ) (i : Fin n) :
    ∀ᵐ x ∂(boundedNatureInstance G hG hN μlo μhi ℓ a).law i, x∈G := by
  have hs := finiteAlphabetInstance_supported (fun a : G => a.val) (fun a => hG a.val a.property)
    (fun i => countProbability (a.1.val i)) (fun i => countProbability_simplex hN (a.1.val i)) i
  exact hs.mono (fun _ hx => by obtain ⟨j,rfl⟩ := hx; exact j.property)

lemma boundedGridLearner_target_constraints (G : Finset ℝ) (hG : ∀ a∈G, 0≤a) (hN : 0<N) (μlo μhi ℓ : ℝ)
    (hBound : ∀ x∈G, x≤1) (a : BoundedNatureAction (n:=n) G hG hN μlo μhi ℓ) :
    boundedGridRate (n:=n) (k:=k) G hG hN μlo μhi ℓ*targetBenchmark (boundedNatureInstance G hG hN μlo μhi ℓ a) a.2 ≤
      (boundedGridLearner (k:=k) G hG hN μlo μhi ℓ).targetPayoff (boundedNatureInstance G hG hN μlo μhi ℓ a) a.2 := by
  apply rankTableRateLearner_constraints
  intro b
  exact (boundedNatureInstance G hG hN μlo μhi ℓ b).integrable_maximum_of_bounded
    (fun i => (boundedNatureInstance_supported G hG hN μlo μhi ℓ b i).mono (fun x hx => hBound x hx))

/-- The statistical Bayes response premise is explicit; the program and its
all-outcome sampling and action rules above are unconditional. -/
lemma boundedGridRate_ge_of_bayes (G : Finset ℝ) (hG : ∀ a∈G, 0≤a) (hN : 0<N) (μlo μhi ℓ : ℝ)
    (hBound : ∀ x∈G, x≤1) (hlo : 0<μlo) (hloOne : μlo≤1) {C κ : ℝ}
    (hC : C≤1) (hκ : 0≤κ)
    (hBayes : ∀ p∈stdSimplex ℝ (BoundedNatureAction (n:=n) G hG hN μlo μhi ℓ),
      ∃ L : RankLearner n k,
        (∀ y r q i H, L.policy.decide (y,r) q i 1 H=true) ∧
        (∀ y r q i H, L.policy.decide (y,r) q i 0 H=false) ∧
        -κ≤∑ a, p a*L.targetGamePayoff (boundedNatureInstance G hG hN μlo μhi ℓ a) a.2 C) :
    C-κ/μlo≤boundedGridRate (n:=n) (k:=k) G hG hN μlo μhi ℓ := by
  apply rankTableRateOptimizer_ge_of_bayes G (boundedNatureInstance G hG hN μlo μhi ℓ) (fun a => a.2)
  · intro a
    exact (boundedNatureInstance G hG hN μlo μhi ℓ a).integrable_maximum_of_bounded
      (fun i => (boundedNatureInstance_supported G hG hN μlo μhi ℓ a i).mono (fun x hx => hBound x hx))
  · exact boundedNatureInstance_supported G hG hN μlo μhi ℓ
  · exact hC
  · exact hκ
  · exact hlo
  · rintro ⟨a,j⟩
    cases j with
    | none => exact a.property.1
    | some i => exact hloOne
  · exact hBayes

end ProphetSecretary.Statistics
