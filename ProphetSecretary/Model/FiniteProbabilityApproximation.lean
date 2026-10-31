import ProphetSecretary.Model.FiniteSupportInstance
import ProphetSecretary.Model.FiniteAlphabetRounding
import ProphetSecretary.Statistics.RoundingGuaranteeTransfer

/-!
# Downward probability approximation of finite-support instances

Positive atom probabilities are rounded down; their missing mass is moved
to zero. The bounds concern actual independent product laws and actual
learner experiments, with the same learner under both laws. Constants in
the coupling loss are explicit before choosing a probability mesh.
-/

open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Model
open ProphetSecretary.Probability

variable {n k : ℕ}

noncomputable def Instance.roundAtomProbabilities (P : Instance n) (G : Finset ℝ)
    (hNonneg : ∀ x∈G, 0≤x) (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G)
    (N : ℕ) (hN : 0<N) (hz : (0 : ℝ)∈G) : Instance n :=
  finiteAlphabetInstance (fun a : G => a.val) (fun a => hNonneg a.val a.property)
    (fun i => roundedProbability (fun a : G => (P.law i).real {a.val}) N ⟨0,hz⟩)
    (fun i => roundedProbability_simplex _ (finiteSupport_weights_simplex (P.law i) G (hG i)) hN ⟨0,hz⟩)

noncomputable def Instance.atomRoundingLoss (P : Instance n) (G : Finset ℝ) (N : ℕ) (hz : (0 : ℝ)∈G) : ℝ :=
  ∑ i, roundingLoss (fun a : G => (P.law i).real {a.val}) N ⟨0,hz⟩

lemma Instance.atomRoundingLoss_nonnegative (P : Instance n) (G : Finset ℝ)
    (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G) (N : ℕ) (hN : 0<N) (hz : (0 : ℝ)∈G) :
    0≤P.atomRoundingLoss G N hz :=
  Finset.sum_nonneg (fun i _ => roundingLoss_nonnegative _ (finiteSupport_weights_simplex (P.law i) G (hG i)) hN _)

lemma Instance.atomRoundingLoss_le (P : Instance n) (G : Finset ℝ)
    (N : ℕ) (hN : 0<N) (hz : (0 : ℝ)∈G) :
    P.atomRoundingLoss G N hz≤(n : ℝ)*((G.card-1 : ℕ) : ℝ)/(N : ℝ) := by
  calc
    _ ≤ ∑ _i : Fin n, (((G.card-1 : ℕ) : ℝ)/(N : ℝ)) :=
      Finset.sum_le_sum (fun i _ => by
        simpa only [Fintype.card_coe] using
          roundingLoss_le (fun a : G => (P.law i).real {a.val}) N hN ⟨0,hz⟩)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

lemma Instance.roundAtomProbabilities_benchmark_bounds (P : Instance n) (G : Finset ℝ)
    (hBound : ∀ x∈G, x∈Icc (0 : ℝ) 1) (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G)
    (N : ℕ) (hN : 0<N) (hz : (0 : ℝ)∈G) :
    P.expectedMaximum-P.atomRoundingLoss G N hz ≤
        (P.roundAtomProbabilities G (fun x hx => (hBound x hx).1) hG N hN hz).expectedMaximum ∧
    (P.roundAtomProbabilities G (fun x hx => (hBound x hx).1) hG N hN hz).expectedMaximum≤P.expectedMaximum := by
  let p := fun i (a : G) => (P.law i).real {a.val}
  have hp := fun i => finiteSupport_weights_simplex (P.law i) G (hG i)
  have hEq := finiteSupportInstance_eq P G (fun x hx => (hBound x hx).1) hG
  have hError := (abs_le.mp (finiteAlphabetInstance_rounding_maximum_error (fun a : G => a.val)
    (fun a => hBound a.val a.property) p hp N hN ⟨0,hz⟩)).2
  have hUpper := finiteAlphabetInstance_rounding_maximum_le (fun a : G => a.val)
    (fun a => (hBound a.val a.property).1) p hp N hN ⟨0,hz⟩ rfl
  rw [hEq] at hError hUpper
  constructor
  · change P.expectedMaximum-(∑ i, roundingLoss (p i) N ⟨0,hz⟩) ≤ _
    change P.expectedMaximum-
      (P.roundAtomProbabilities G (fun x hx => (hBound x hx).1) hG N hN hz).expectedMaximum ≤
        (∑ i, roundingLoss (p i) N ⟨0,hz⟩) at hError
    linarith only [hError]
  · exact hUpper

lemma Instance.roundAtomProbabilities_tailCount_le (P : Instance n) (G : Finset ℝ)
    (hNonneg : ∀ x∈G, 0≤x) (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G)
    (N : ℕ) (hN : 0<N) (hz : (0 : ℝ)∈G) {b : ℝ} (hb : 0≤b) :
    (P.roundAtomProbabilities G hNonneg hG N hN hz).tailCount b≤P.tailCount b := by
  have h := finiteAlphabetInstance_rounding_tailCount_le (fun a : G => a.val)
    (fun a => hNonneg a.val a.property) (fun i (a : G) => (P.law i).real {a.val})
    (fun i => finiteSupport_weights_simplex (P.law i) G (hG i)) N hN ⟨0,hz⟩ rfl hb
  rwa [finiteSupportInstance_eq P G hNonneg hG] at h

lemma RankLearner.roundAtomProbabilities_reward_error (L : RankLearner n k) (P : Instance n) (G : Finset ℝ)
    (hBound : ∀ x∈G, x∈Icc (0 : ℝ) 1) (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G)
    (N : ℕ) (hN : 0<N) (hz : (0 : ℝ)∈G) :
    |L.expectedReward P-L.expectedReward (P.roundAtomProbabilities G (fun x hx => (hBound x hx).1) hG N hN hz)| ≤
      ((k : ℝ)+1)*P.atomRoundingLoss G N hz := by
  have h := L.rounding_reward_error (fun a : G => a.val) (fun a => hBound a.val a.property)
    (fun i (a : G) => (P.law i).real {a.val})
    (fun i => finiteSupport_weights_simplex (P.law i) G (hG i)) N hN ⟨0,hz⟩
  rwa [finiteSupportInstance_eq P G (fun x hx => (hBound x hx).1) hG] at h

lemma RankLearner.roundAtomProbabilities_reach_error (L : RankLearner n k) (P : Instance n) (G : Finset ℝ)
    (hNonneg : ∀ x∈G, 0≤x) (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G)
    (N : ℕ) (hN : 0<N) (hz : (0 : ℝ)∈G) (i : Fin n) :
    |L.reachProbability P i-L.reachProbability (P.roundAtomProbabilities G hNonneg hG N hN hz) i| ≤
      ((k : ℝ)+1)*P.atomRoundingLoss G N hz := by
  have h := L.rounding_reach_error (fun a : G => a.val) (fun a => hNonneg a.val a.property)
    (fun i (a : G) => (P.law i).real {a.val})
    (fun i => finiteSupport_weights_simplex (P.law i) G (hG i)) N hN ⟨0,hz⟩ i
  rwa [finiteSupportInstance_eq P G hNonneg hG] at h

lemma Instance.roundAtomProbabilities_mem_grid (P : Instance n) (G : Finset ℝ)
    (hNonneg : ∀ x∈G, 0≤x) (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G)
    (N : ℕ) (hN : 0<N) (hz : (0 : ℝ)∈G) :
    ∃ a : Fin n → ProbabilityCounts G N,
      probabilityGridInstance (fun a : G => a.val) (fun a => hNonneg a.val a.property) hN a =
        P.roundAtomProbabilities G hNonneg hG N hN hz :=
  rounded_instance_in_finite_family (fun a : G => a.val) (fun a => hNonneg a.val a.property)
    (fun i (a : G) => (P.law i).real {a.val})
    (fun i => finiteSupport_weights_simplex (P.law i) G (hG i)) hN ⟨0,hz⟩

end ProphetSecretary.Model
