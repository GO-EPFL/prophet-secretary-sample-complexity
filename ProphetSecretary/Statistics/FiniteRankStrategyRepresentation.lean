import ProphetSecretary.Statistics.FiniteRankStrategyTable

/-!
# The finite strategy table induced by a learner's auxiliary seed

A fixed seed determines responses to every possible finite-grid query. The
resulting table is measurable in the seed. Executing it preserves every valid
history, including zero arrivals. The cap/zero conditions are the restrictions
on responses in the paper's finite minimax game.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n k : ℕ}

noncomputable def rankLearnerStrategyTable (L : RankLearner n k) (G : Finset ℝ) (r : L.Seed) : RankStrategyTable n k G :=
  fun z => L.policy.decide (z.val.1,r) z.val.2.1 z.val.2.2.1 z.val.2.2.2.1 z.val.2.2.2.2

lemma measurable_rankLearnerStrategyTable (L : RankLearner n k) (G : Finset ℝ) :
    Measurable (rankLearnerStrategyTable L G) := by
  apply measurable_pi_lambda
  intro z
  exact L.policy_isMeasurable.comp ((measurable_const.prodMk measurable_id).prodMk measurable_const)

lemma finiteRankTablePolicy_eq_decide (L : RankLearner n k) (G : Finset ℝ) (r : L.Seed)
    (y : Reservoir n k) (q i : Fin n) (x : ℝ) (H : RankHistory n)
    (hQuery : (y,q,i,x,H)∈rankQueryGrid n k G)
    (hCap : L.policy.decide (y,r) q i 1 H = true)
    (hZero : L.policy.decide (y,r) q i 0 H = false) :
    (finiteRankTablePolicy G (rankLearnerStrategyTable L G r)).decide (y,()) q i x H =
      L.policy.decide (y,r) q i x H := by
  by_cases hx1 : x=1
  · subst x
    exact (finiteRankTablePolicy_accepts_cap G _ y () q i H).trans hCap.symm
  · by_cases hx0 : x=0
    · subst x
      exact (finiteRankTablePolicy_rejects_zero G _ y () q i H).trans hZero.symm
    · change (if x=1 then true else if x=0 then false else _) = _
      rw [if_neg hx1,if_neg hx0,finiteObservationLookup_on _ _ _ (y,q,i,x,H) hQuery]
      rfl

lemma finiteRankTablePolicy_action (L : RankLearner n k) (G : Finset ℝ) (r : L.Seed)
    (y : Reservoir n k) (x : Fin n → ℝ) (hy : ∀ i j, y i j∈G) (hx : ∀ i, x i∈G)
    (hCap : ∀ q i H, L.policy.decide (y,r) q i 1 H = true)
    (hZero : ∀ q i H, L.policy.decide (y,r) q i 0 H = false)
    (p : Equiv.Perm (Fin n)) (i : Fin n) :
    (finiteRankTablePolicy G (rankLearnerStrategyTable L G r)).action (y,()) p x i =
      L.policy.action (y,r) p x i :=
  finiteRankTablePolicy_eq_decide L G r y (p.symm i) i (x i) (rankHistory p x (p.symm i))
    (rankQueryGrid_mem G y x hy hx p _ _) (hCap _ _ _) (hZero _ _ _)

lemma finiteRankTablePolicy_accepted (L : RankLearner n k) (G : Finset ℝ) (r : L.Seed)
    (y : Reservoir n k) (x : Fin n → ℝ) (hy : ∀ i j, y i j∈G) (hx : ∀ i, x i∈G)
    (hCap : ∀ q i H, L.policy.decide (y,r) q i 1 H = true)
    (hZero : ∀ q i H, L.policy.decide (y,r) q i 0 H = false) (p : Equiv.Perm (Fin n)) :
    (finiteRankTablePolicy G (rankLearnerStrategyTable L G r)).accepted (y,()) p x =
      L.policy.accepted (y,r) p x := by
  ext i
  simp only [RankPolicy.mem_accepted,finiteRankTablePolicy_action L G r y x hy hx hCap hZero]

lemma finiteRankTablePolicy_reaches (L : RankLearner n k) (G : Finset ℝ) (r : L.Seed)
    (y : Reservoir n k) (x : Fin n → ℝ) (hy : ∀ i j, y i j∈G) (hx : ∀ i, x i∈G)
    (hCap : ∀ q i H, L.policy.decide (y,r) q i 1 H = true)
    (hZero : ∀ q i H, L.policy.decide (y,r) q i 0 H = false) (p : Equiv.Perm (Fin n)) (i : Fin n) :
    (finiteRankTablePolicy G (rankLearnerStrategyTable L G r)).Reaches (y,()) p x i ↔
      L.policy.Reaches (y,r) p x i := by
  unfold RankPolicy.Reaches
  rw [finiteRankTablePolicy_accepted L G r y x hy hx hCap hZero]

lemma finiteRankTablePolicy_selects (L : RankLearner n k) (G : Finset ℝ) (r : L.Seed)
    (y : Reservoir n k) (x : Fin n → ℝ) (hy : ∀ i j, y i j∈G) (hx : ∀ i, x i∈G)
    (hCap : ∀ q i H, L.policy.decide (y,r) q i 1 H = true)
    (hZero : ∀ q i H, L.policy.decide (y,r) q i 0 H = false) (p : Equiv.Perm (Fin n)) (i : Fin n) :
    (finiteRankTablePolicy G (rankLearnerStrategyTable L G r)).Selects (y,()) p x i ↔
      L.policy.Selects (y,r) p x i := by
  unfold RankPolicy.Selects
  rw [finiteRankTablePolicy_reaches L G r y x hy hx hCap hZero,
    finiteRankTablePolicy_accepted L G r y x hy hx hCap hZero]

lemma finiteRankTablePolicy_reward (L : RankLearner n k) (G : Finset ℝ) (r : L.Seed)
    (y : Reservoir n k) (x : Fin n → ℝ) (hy : ∀ i j, y i j∈G) (hx : ∀ i, x i∈G)
    (hCap : ∀ q i H, L.policy.decide (y,r) q i 1 H = true)
    (hZero : ∀ q i H, L.policy.decide (y,r) q i 0 H = false) (p : Equiv.Perm (Fin n)) :
    (finiteRankTablePolicy G (rankLearnerStrategyTable L G r)).reward (y,()) p x =
      L.policy.reward (y,r) p x := by
  unfold RankPolicy.reward
  apply Finset.sum_congr rfl
  intro i _
  rw [finiteRankTablePolicy_selects L G r y x hy hx hCap hZero]

end ProphetSecretary.Statistics
