import ProphetSecretary.Statistics.FinitePriorBayesResponse
import ProphetSecretary.Statistics.FiniteClockBayesMinimax

/-!
# Finite nature priors as actual hidden-instance experiments

A simplex weight on any finite nature family is relabelled by a finite ordinal.
Offer laws and hidden reward-or-reach targets are unchanged. The weighted game
identity permits the proved finite-prior responses to enter finite minimax,
including a possibly empty nature family.
-/

open MeasureTheory Set
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

noncomputable def naturePrior {n : ℕ} {Θ : Type*} [Fintype Θ]
    (P : Θ → Instance n) (J : Θ → Option (Fin n))
    (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ) : FinitePrior n where
  size := Fintype.card Θ
  weight i := ⟨p ((Fintype.equivFin Θ).symm i),hp.1 _⟩
  weight_sum := by
    apply NNReal.coe_injective
    push_cast
    change (∑ i : Fin (Fintype.card Θ), p ((Fintype.equivFin Θ).symm i))=1
    rw [Equiv.sum_comp]
    exact hp.2
  offerInstance i := P ((Fintype.equivFin Θ).symm i)
  target i := J ((Fintype.equivFin Θ).symm i)

lemma naturePrior_targetGamePayoff {n k : ℕ} {Θ : Type*} [Fintype Θ]
    (P : Θ → Instance n) (J : Θ → Option (Fin n))
    (p : Θ → ℝ) (hp : p∈stdSimplex ℝ Θ) (L : Learner n k) (C : ℝ) :
    (∑ i : Fin (naturePrior P J p hp).size, ((naturePrior P J p hp).weight i : ℝ)*
      L.targetGamePayoff ((naturePrior P J p hp).offerInstance i) ((naturePrior P J p hp).target i) C)=
      ∑ θ : Θ, p θ*L.targetGamePayoff (P θ) (J θ) C := by
  change (∑ i : Fin (Fintype.card Θ), p ((Fintype.equivFin Θ).symm i)*
    L.targetGamePayoff (P ((Fintype.equivFin Θ).symm i)) (J ((Fintype.equivFin Θ).symm i)) C)=_
  exact Equiv.sum_comp (Fintype.equivFin Θ).symm
    (fun θ : Θ => p θ*L.targetGamePayoff (P θ) (J θ) C)

/-- Every finite-prior response for a genuine class of laws supplies the
simplex responses needed by the actual finite clock minimax theorem. -/
theorem finite_clock_learner_of_finitePrior_responses {n k : ℕ} {Θ : Type*} [Fintype Θ]
    (G : Finset ℝ) (P : Θ → Instance n)
    (hP : ∀ θ, Integrable Instance.maximum (P θ).valuesLaw)
    (hG : ∀ θ i, ∀ᵐ x ∂(P θ).law i, x∈G) (J : Θ → Option (Fin n)) (C t : ℝ)
    (Q : Instance n → Option (Fin n) → Prop) (hQ : ∀ θ, Q (P θ) (J θ))
    (hBayes : ∀ F : FinitePrior n, (∀ θ, Q (F.offerInstance θ) (F.target θ)) →
      ∃ L : Learner n k,
        (∀ y r s i H, L.policy.decide (y,r) s i 1 H=true) ∧
        (∀ y r s i H, L.policy.decide (y,r) s i 0 H=false) ∧
        t≤∑ θ : Fin F.size, (F.weight θ : ℝ)*
          L.targetGamePayoff (F.offerInstance θ) (F.target θ) C) :
    ∃ L : Learner n k,
      (∀ y r s i H, L.policy.decide (y,r) s i 1 H=true) ∧
      (∀ y r s i H, L.policy.decide (y,r) s i 0 H=false) ∧
      (∀ (y : Reservoir n k) (r : L.Seed) (i : Fin n), requests (trainingTranscript L.request r y) i=k) ∧
      ∀ θ, t≤L.targetGamePayoff (P θ) (J θ) C := by
  apply finite_clock_learner_of_bayes_responses G P hP hG J C t
  intro p hp
  obtain ⟨L,hCap,hZero,hGame⟩ := hBayes (naturePrior P J p hp)
    (fun i => hQ ((Fintype.equivFin Θ).symm i))
  refine ⟨L,hCap,hZero,?_⟩
  rwa [naturePrior_targetGamePayoff] at hGame

end ProphetSecretary.Statistics
